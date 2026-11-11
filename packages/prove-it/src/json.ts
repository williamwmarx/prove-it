import {
  createJavaOverrideError,
  createModuleArgumentError,
  defineStateOperator,
  getJavaClassName,
  getValue,
} from "./builtins";
import type { Builtin } from "./evaluate";
import {
  createRecord,
  createTuple,
  formatValue,
  getSequenceElements,
  isFunctionValue,
  isSetValue,
  rankString,
  toFiniteFunction,
  toFiniteSet,
  type Value,
} from "./values";

export interface FileSystem {
  readFile: ((path: string) => string | undefined) | undefined;
  writeFile: ((path: string, content: string) => void) | undefined;
}

interface ParseContext {
  source?: string;
}

const TO_JSON_SIGNATURE =
  "public static tlc2.value.impl.StringValue tlc2.module.Json.toJson(tlc2.value.IValue) throws java.io.IOException";
const TO_JSON_ARRAY_SIGNATURE =
  "public static tlc2.value.impl.StringValue tlc2.module.Json.toJsonArray(tlc2.value.IValue) throws java.io.IOException";
const TO_JSON_OBJECT_SIGNATURE =
  "public static tlc2.value.impl.StringValue tlc2.module.Json.toJsonObject(tlc2.value.IValue) throws java.io.IOException";
const SERIALIZE_SIGNATURE =
  "public static synchronized tlc2.value.impl.BoolValue tlc2.module.Json.serialize(tlc2.value.impl.StringValue,tlc2.value.impl.Value) throws java.io.IOException";
const ND_SERIALIZE_SIGNATURE =
  "public static synchronized tlc2.value.impl.BoolValue tlc2.module.Json.ndSerialize(tlc2.value.impl.StringValue,tlc2.value.impl.Value) throws java.io.IOException";
const DESERIALIZE_SIGNATURE =
  "public static tlc2.value.IValue tlc2.module.Json.deserialize(tlc2.value.impl.StringValue) throws java.io.IOException";
const ND_DESERIALIZE_SIGNATURE =
  "public static tlc2.value.IValue tlc2.module.Json.ndDeserialize(tlc2.value.impl.StringValue) throws java.io.IOException";

const isRecord = (value: Value) => {
  if (!isFunctionValue(value)) return false;
  const domain = toFiniteFunction(value).domain;
  return domain.length > 0 && domain.every((key) => typeof key === "string");
};

const createUnsupportedError = (method: string, value: Value) =>
  createJavaOverrideError(
    method,
    `Cannot convert value: unsupported value type tlc2.value.impl.${getJavaClassName(value)}`,
  );

const toJsonString = (text: string) =>
  JSON.stringify(text).replaceAll("\u2028", "\\u2028").replaceAll("\u2029", "\\u2029");

const toSetJson = (value: Value, method: string) => {
  if (typeof value === "object" && (value.kind === "InfiniteSet" || value.kind === "SequenceSet")) {
    throw createUnsupportedError(method, value);
  }
  return `[${toFiniteSet(value)
    .elements.map((element) => toJson(element, method))
    .join(",")}]`;
};

const toFunctionJson = (value: Value, method: string) => {
  const functionValue = toFiniteFunction(value);
  const elements = getSequenceElements(functionValue);
  if (elements) return `[${elements.map((element) => toJson(element, method)).join(",")}]`;
  return `{${functionValue.domain
    .map(
      (key, index) =>
        `${toJsonString(typeof key === "string" ? key : formatValue(key))}:${toJson(functionValue.range[index], method)}`,
    )
    .join(",")}}`;
};

const toJson = (value: Value, method: string): string => {
  if (typeof value === "string") return toJsonString(value);
  if (typeof value !== "object") return String(value);
  if (value.kind === "ModelValue") return toJsonString(value.name);
  if (isSetValue(value)) return toSetJson(value, method);
  return toFunctionJson(value, method);
};

const toJsonArray = (value: Value) => {
  if (isSetValue(value)) return toSetJson(value, TO_JSON_ARRAY_SIGNATURE);
  if (!isFunctionValue(value) || isRecord(value))
    throw createUnsupportedError(TO_JSON_ARRAY_SIGNATURE, value);
  return toFunctionJson(value, TO_JSON_ARRAY_SIGNATURE);
};

const toJsonObject = (value: Value) => {
  if (!isFunctionValue(value)) throw createUnsupportedError(TO_JSON_OBJECT_SIGNATURE, value);
  return toFunctionJson(value, TO_JSON_OBJECT_SIGNATURE);
};

// The text of each number JSON.parse read, which the parse holds in its place.
const numberSources = new WeakMap<object, string>();

const INTEGER_PATTERN = /^-?\d+$/;

// TLC reads a JSON number by its text with Integer.parseInt, as it converts the value: a 32-bit
// integer, -0 as 0, and fails on any other.
const toInteger = (source: string, method: string) => {
  const integer = Number(source);
  if (!INTEGER_PATTERN.test(source) || integer < -(2 ** 31) || integer >= 2 ** 31) {
    throw createJavaOverrideError(
      method,
      `Cannot convert value: expected a 32-bit integer JSON number, but found ${source}`,
    );
  }
  return integer || 0;
};

const fromJson = (json: unknown, method: string): Value => {
  if (typeof json === "boolean") return json;
  if (typeof json === "string") return rankString(json);
  if (Array.isArray(json)) return createTuple(json.map((element) => fromJson(element, method)));
  if (json !== null && typeof json === "object") {
    const source = numberSources.get(json);
    if (source !== undefined) return toInteger(source, method);
    return createRecord(
      Object.entries(json).map(([key, field]): [string, Value] => [
        rankString(key),
        fromJson(field, method),
      ]),
    );
  }
  throw createJavaOverrideError(
    method,
    `Cannot convert value: unsupported JSON value ${String(json)}`,
  );
};

const parseJson = (text: string, method: string) => {
  if (text.trim() === "") return fromJson(null, method);
  try {
    return fromJson(
      JSON.parse(text, (_, value: unknown, context?: ParseContext) => {
        if (typeof value !== "number") return value;
        const number = {};
        numberSources.set(number, context?.source ?? String(value));
        return number;
      }),
      method,
    );
  } catch (error) {
    if (!(error instanceof SyntaxError)) throw error;
    throw createJavaOverrideError(method, error.message);
  }
};

const getPath = (value: Value, method: string) => {
  if (typeof value !== "string") {
    throw createJavaOverrideError(
      method,
      `Cannot cast tlc2.value.impl.${getJavaClassName(value)} to tlc2.value.impl.StringValue`,
    );
  }
  return value;
};

const readText = (files: FileSystem, path: string, method: string) => {
  const text = files.readFile?.(path);
  if (text === undefined) {
    throw createJavaOverrideError(method, `${path} (No such file or directory)`);
  }
  return text;
};

export const createJsonOperators = (files: FileSystem): Builtin[] => [
  defineStateOperator("ToJson", 1, (args) =>
    rankString(toJson(getValue(args, 0, "ToJson"), TO_JSON_SIGNATURE)),
  ),
  defineStateOperator("ToJsonArray", 1, (args) =>
    rankString(toJsonArray(getValue(args, 0, "ToJsonArray"))),
  ),
  defineStateOperator("ToJsonObject", 1, (args) =>
    rankString(toJsonObject(getValue(args, 0, "ToJsonObject"))),
  ),
  defineStateOperator("JsonSerialize", 2, (args) => {
    const path = getPath(getValue(args, 0, "JsonSerialize"), SERIALIZE_SIGNATURE);
    const value = getValue(args, 1, "JsonSerialize");
    if (!getSequenceElements(value) && !isRecord(value)) {
      throw createModuleArgumentError("second", "JsonSerialize", "sequence or record", value);
    }
    files.writeFile?.(path, toJson(value, SERIALIZE_SIGNATURE));
    return true;
  }),
  defineStateOperator("ndJsonSerialize", 2, (args) => {
    const path = getPath(getValue(args, 0, "ndJsonSerialize"), ND_SERIALIZE_SIGNATURE);
    const value = getValue(args, 1, "ndJsonSerialize");
    const elements = getSequenceElements(value);
    if (!elements) {
      throw createModuleArgumentError("second", "ndJsonSerialize", "sequence", value);
    }
    files.writeFile?.(
      path,
      elements.map((element) => `${toJson(element, ND_SERIALIZE_SIGNATURE)}\n`).join(""),
    );
    return true;
  }),
  defineStateOperator("JsonDeserialize", 1, (args) => {
    const path = getPath(getValue(args, 0, "JsonDeserialize"), DESERIALIZE_SIGNATURE);
    return parseJson(readText(files, path, DESERIALIZE_SIGNATURE), DESERIALIZE_SIGNATURE);
  }),
  defineStateOperator("ndJsonDeserialize", 1, (args) => {
    const path = getPath(getValue(args, 0, "ndJsonDeserialize"), ND_DESERIALIZE_SIGNATURE);
    return createTuple(
      readText(files, path, ND_DESERIALIZE_SIGNATURE)
        .split(/\r\n|\r|\n/)
        .map((line) => line.trim())
        .filter((line) => line !== "")
        .map((line) => parseJson(line, ND_DESERIALIZE_SIGNATURE)),
    );
  }),
];
