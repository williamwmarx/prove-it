import type { Definition, Expression, Module, SourceLocation } from "./ast";
import { TlaSyntaxError, TlaUnsupportedError } from "./errors";

interface PoolEntry {
  tag: number;
  text: string;
  value: number;
  first: number;
  second: number;
}

interface JavaMethod {
  name: string;
  arity: number;
  // Method#toString, which TLC prints as the signature of an override.
  signature: string;
  code: Uint8Array | undefined;
}

// A public static method of the class named after a module, which TLC reports as it loads the
// class, with whether it overrides an operator.
export interface JavaOverride {
  module: string;
  operator: string;
  signature: string;
  isMatched: boolean;
}

interface ObjectReference {
  className: string;
  value: Expression | undefined;
}

type StackItem = number | string | Expression | ObjectReference;

const CLASS_MAGIC = 0xcafebabe;
const ACCESS_PUBLIC = 0x0001;
const ACCESS_STATIC = 0x0008;
const VALUE_PACKAGE = "tlc2/value/impl/";

// The constant pool tags of the JVM specification, section 4.4.
const POOL_TAG = {
  utf8: 1,
  integer: 3,
  float: 4,
  long: 5,
  double: 6,
  class: 7,
  string: 8,
  fieldRef: 9,
  methodRef: 10,
  interfaceMethodRef: 11,
  nameAndType: 12,
  methodHandle: 15,
  methodType: 16,
  dynamic: 17,
  invokeDynamic: 18,
  module: 19,
  package: 20,
};

// The newest class file version the front end reads, Java 25's.
const MAXIMUM_MAJOR_VERSION = 69;
// ACC_INTERFACE, ACC_ABSTRACT, ACC_ANNOTATION, ACC_ENUM and ACC_MODULE: a class that isn't a plain
// one.
const UNPLAIN_CLASS = 0x0200 | 0x0400 | 0x2000 | 0x4000 | 0x8000;
// The Java names TLC maps to an operator's (TLARegistry.mapName), which its standard modules'
// classes register: an override of one of these names overrides that operator.
const REGISTERED_NAMES = new Set([
  "BagCup",
  "BagDiff",
  "CombineFcn",
  "Concat",
  "Divide",
  "DotDot",
  "Expt",
  "GEQ",
  "GT",
  "LE",
  "LT",
  "MakeFcn",
  "Minus",
  "Mod",
  "Neg",
  "Plus",
  "SqSubseteq",
  "Times",
]);

// The annotations Method#getAnnotation finds that make TLC skip a method of the class named after a
// module, which only a TLCOverrides index loads.
const SKIPPING_ANNOTATIONS = new Set([
  "Ltlc2/overrides/TLAPlusOperator;",
  "Ltlc2/overrides/Evaluation;",
]);

const PAIRED_TAGS = new Set([
  POOL_TAG.fieldRef,
  POOL_TAG.methodRef,
  POOL_TAG.interfaceMethodRef,
  POOL_TAG.nameAndType,
  POOL_TAG.dynamic,
  POOL_TAG.invokeDynamic,
]);

const createUnreadError = (reason: string) =>
  new TlaUnsupportedError(`${reason}, which tla-ts cannot run`);

// The JVM opcodes that an override returning a constant value uses.
const OPCODE = {
  iconstM1: 0x02,
  iconst0: 0x03,
  iconst5: 0x08,
  bipush: 0x10,
  sipush: 0x11,
  ldc: 0x12,
  ldcW: 0x13,
  dup: 0x59,
  areturn: 0xb0,
  getstatic: 0xb2,
  invokespecial: 0xb7,
  invokestatic: 0xb8,
  new: 0xbb,
};

const createReader = (bytes: Uint8Array) => {
  const view = new DataView(bytes.buffer, bytes.byteOffset, bytes.byteLength);
  const cursor = { offset: 0 };
  const advance = (length: number) => {
    const start = cursor.offset;
    cursor.offset += length;
    return start;
  };
  return {
    readUint8: () => view.getUint8(advance(1)),
    readUint16: () => view.getUint16(advance(2)),
    readUint32: () => view.getUint32(advance(4)),
    readInt32: () => view.getInt32(advance(4)),
    readBytes: (length: number) => bytes.subarray(advance(length), cursor.offset),
  };
};

const PRIMITIVE_TYPES = new Map([
  ["B", "byte"],
  ["C", "char"],
  ["D", "double"],
  ["F", "float"],
  ["I", "int"],
  ["J", "long"],
  ["S", "short"],
  ["Z", "boolean"],
  ["V", "void"],
]);

// The modifiers Method#toString prints, in the order of Modifier#toString.
const METHOD_MODIFIERS: [number, string][] = [
  [0x0001, "public"],
  [0x0004, "protected"],
  [0x0002, "private"],
  [0x0400, "abstract"],
  [0x0008, "static"],
  [0x0010, "final"],
  [0x0020, "synchronized"],
  [0x0100, "native"],
  [0x0800, "strictfp"],
];

const getTypeNames = (descriptor: string) =>
  [...descriptor.matchAll(/(\[*)(?:L([^;]*);|([BCDFIJSZV]))/g)].map(
    (match) =>
      `${match[2]?.replaceAll("/", ".") ?? PRIMITIVE_TYPES.get(match[3])}${"[]".repeat(match[1].length)}`,
  );

const getClassName = (pool: PoolEntry[], index: number) => pool[pool[index].first].text;

type Reader = ReturnType<typeof createReader>;

// Reads past an annotation's element_value (JVM specification, section 4.7.16.1).
const skipElementValue = (reader: Reader): void => {
  const tag = String.fromCharCode(reader.readUint8());
  if (tag === "e") reader.readUint32();
  else if (tag === "@") readAnnotation(reader);
  else if (tag === "[")
    for (let count = reader.readUint16(); count > 0; count--) skipElementValue(reader);
  else reader.readUint16();
};

// An annotation's type, past its elements.
const readAnnotation = (reader: Reader) => {
  const typeIndex = reader.readUint16();
  for (let count = reader.readUint16(); count > 0; count--) {
    reader.readUint16();
    skipElementValue(reader);
  }
  return typeIndex;
};

const getJavaClassName = (pool: PoolEntry[], index: number) =>
  getClassName(pool, index).replaceAll("/", ".");

// The public static methods of a class file and their bytecode, in the order of the class file.
// Class#getDeclaredMethods orders them by where HotSpot allocated the symbols of their names.
const readClassFile = (bytes: Uint8Array, hasIndex: boolean) => {
  const reader = createReader(bytes);
  if (reader.readUint32() !== CLASS_MAGIC)
    throw new TlaSyntaxError("A module override is not a class file");
  reader.readUint16();
  if (reader.readUint16() > MAXIMUM_MAJOR_VERSION)
    throw createUnreadError("A Java class file of a version the front end doesn't read");
  const pool: PoolEntry[] = [];
  const poolSize = reader.readUint16();
  const decoder = new TextDecoder();
  for (let index = 1; index < poolSize; index++) {
    const tag = reader.readUint8();
    const entry = { tag, text: "", value: 0, first: 0, second: 0 };
    pool[index] = entry;
    if (tag === POOL_TAG.utf8) entry.text = decoder.decode(reader.readBytes(reader.readUint16()));
    else if (tag === POOL_TAG.integer) entry.value = reader.readInt32();
    else if (tag === POOL_TAG.float) reader.readUint32();
    else if (tag === POOL_TAG.long || tag === POOL_TAG.double) {
      reader.readBytes(8);
      index++;
    } else if (
      tag === POOL_TAG.class ||
      tag === POOL_TAG.string ||
      tag === POOL_TAG.methodType ||
      tag === POOL_TAG.module ||
      tag === POOL_TAG.package
    ) {
      entry.first = reader.readUint16();
    } else if (tag === POOL_TAG.methodHandle) {
      reader.readUint8();
      entry.first = reader.readUint16();
    } else if (PAIRED_TAGS.has(tag)) {
      entry.first = reader.readUint16();
      entry.second = reader.readUint16();
    } else {
      throw createUnreadError("A Java class file's constant the front end doesn't read");
    }
  }
  // Java runs a class's static initializer, its fields' and its superclasses', before it calls an
  // override, which the front end doesn't run: it reads only a plain class with none.
  if ((reader.readUint16() & UNPLAIN_CLASS) !== 0)
    throw createUnreadError("A Java override class that isn't a plain class");
  const className = getJavaClassName(pool, reader.readUint16());
  if (pool[pool[reader.readUint16()]?.first]?.text !== "java/lang/Object")
    throw createUnreadError("A Java override class with a superclass");
  if (reader.readUint16() !== 0)
    throw createUnreadError("A Java override class that implements an interface");
  if (reader.readUint16() !== 0) throw createUnreadError("A Java override class with fields");
  const methods: JavaMethod[] = [];
  for (let remaining = reader.readUint16(); remaining > 0; remaining--) {
    const access = reader.readUint16();
    const name = pool[reader.readUint16()].text;
    const descriptor = pool[reader.readUint16()].text;
    const parametersEnd = descriptor.indexOf(")");
    const parameters = getTypeNames(descriptor.slice(1, parametersEnd));
    if (name === "<clinit>")
      throw createUnreadError("A Java override class with a static initializer");
    const attributes = Array.from({ length: reader.readUint16() }, () => ({
      name: pool[reader.readUint16()].text,
      reader: createReader(reader.readBytes(reader.readUint32())),
    }));
    const annotations = attributes.find(
      (attribute) => attribute.name === "RuntimeVisibleAnnotations",
    )?.reader;
    const annotationTypes = annotations
      ? Array.from(
          { length: annotations.readUint16() },
          () => pool[readAnnotation(annotations)].text,
        )
      : [];
    // processModuleOverrides skips a method annotated as an operator a TLCOverrides index loads,
    // which a class TLC finds beside the spec could be.
    if (annotationTypes.some((type) => SKIPPING_ANNOTATIONS.has(type))) {
      if (hasIndex)
        throw createUnreadError("A Java override class TLC may load through a TLCOverrides index");
      continue;
    }
    if (attributes.some((attribute) => attribute.name.includes("Annotation")))
      throw createUnreadError("A Java override class with annotations");
    const isOverride = (access & ACCESS_PUBLIC) !== 0 && (access & ACCESS_STATIC) !== 0;
    if (!isOverride) continue;
    const code = attributes.find((attribute) => attribute.name === "Code")?.reader;
    // A Code attribute holds max_stack and max_locals before the length of the bytecode.
    code?.readBytes(4);
    const thrown = attributes.find((attribute) => attribute.name === "Exceptions")?.reader;
    const exceptions = thrown
      ? Array.from({ length: thrown.readUint16() }, () =>
          getJavaClassName(pool, thrown.readUint16()),
        )
      : [];
    const modifiers = METHOD_MODIFIERS.filter(([flag]) => (access & flag) !== 0).map(
      ([, modifier]) => modifier,
    );
    const returnType = getTypeNames(descriptor.slice(parametersEnd + 1))[0];
    const throwsClause = exceptions.length === 0 ? "" : ` throws ${exceptions.join(",")}`;
    const bytecode = code?.readBytes(code.readUint32());
    methods.push({
      name,
      arity: parameters.length,
      code: bytecode,
      signature: `${modifiers.join(" ")} ${returnType} ${className}.${name}(${parameters.join(",")})${throwsClause}`,
    });
  }
  for (let attributes = reader.readUint16(); attributes > 0; attributes--) {
    const name = pool[reader.readUint16()].text;
    reader.readBytes(reader.readUint32());
    if (name.includes("Annotation"))
      throw createUnreadError("A Java override class with annotations");
  }
  // TLC loads every public static method of a name, the one it loads last overriding the others,
  // in the order the JVM lists them, and maps a registered name to an operator's.
  methods.forEach((method, position) => {
    if (methods.slice(0, position).some((other) => other.name === method.name))
      throw createUnreadError("A Java override class with methods of one name");
    if (REGISTERED_NAMES.has(method.name))
      throw createUnreadError("A Java override of a name TLC maps to an operator's");
  });
  return { pool, methods };
};

const getMemberReference = (pool: PoolEntry[], index: number) => {
  const reference = pool[index];
  const nameAndType = pool[reference.second];
  return {
    className: getClassName(pool, reference.first),
    // The member's name and its descriptor.
    name: `${pool[nameAndType.first].text}${pool[nameAndType.second].text}`,
  };
};

// Runs the bytecode of an override that returns a constant TLC value, such as
// BoolValue.ValTrue, IntValue.gen(3), or new StringValue("a"), and returns that value as a
// literal. The instructions it runs, from the first to the first return, don't branch or throw, so
// no exception handler runs.
const getReturnedLiteral = (
  method: JavaMethod,
  pool: PoolEntry[],
  className: string,
  location: SourceLocation,
) => {
  const createUnsupportedError = () =>
    new TlaUnsupportedError(
      `The Java override ${className}.${method.name} computes its value, which tla-ts cannot run`,
    );
  const code = method.code;
  if (!code) throw createUnsupportedError();
  const stack: StackItem[] = [];
  const pop = () => {
    const item = stack.pop();
    if (item === undefined) throw createUnsupportedError();
    return item;
  };
  const getConstant = (index: number) => {
    const entry = pool[index];
    if (entry.tag === POOL_TAG.integer) return entry.value;
    if (entry.tag === POOL_TAG.string) return pool[entry.first].text;
    throw createUnsupportedError();
  };
  for (let offset = 0; offset < code.length;) {
    const opcode = code[offset];
    const getIndex = () => (code[offset + 1] << 8) | code[offset + 2];
    if (opcode >= OPCODE.iconstM1 && opcode <= OPCODE.iconst5) {
      stack.push(opcode - OPCODE.iconst0);
      offset += 1;
    } else if (opcode === OPCODE.bipush) {
      stack.push((code[offset + 1] << 24) >> 24);
      offset += 2;
    } else if (opcode === OPCODE.sipush) {
      stack.push((getIndex() << 16) >> 16);
      offset += 3;
    } else if (opcode === OPCODE.ldc) {
      stack.push(getConstant(code[offset + 1]));
      offset += 2;
    } else if (opcode === OPCODE.ldcW) {
      stack.push(getConstant(getIndex()));
      offset += 3;
    } else if (opcode === OPCODE.dup) {
      // Only of an object, as `new` makes one for its constructor.
      const top = pop();
      if (typeof top !== "object" || !("className" in top) || top.value)
        throw createUnsupportedError();
      stack.push(top, top);
      offset += 1;
    } else if (opcode === OPCODE.getstatic) {
      const field = getMemberReference(pool, getIndex());
      if (field.className !== `${VALUE_PACKAGE}BoolValue`) throw createUnsupportedError();
      const name = new Map([
        ["ValTrueLtlc2/value/impl/BoolValue;", "TRUE"],
        ["ValFalseLtlc2/value/impl/BoolValue;", "FALSE"],
      ]).get(field.name);
      if (name === undefined) throw createUnsupportedError();
      stack.push({
        kind: "Identifier",
        name,
        location,
      });
      offset += 3;
    } else if (opcode === OPCODE.invokestatic) {
      const callee = getMemberReference(pool, getIndex());
      const value = pop();
      if (
        callee.className !== `${VALUE_PACKAGE}IntValue` ||
        callee.name !== "gen(I)Ltlc2/value/impl/IntValue;"
      ) {
        throw createUnsupportedError();
      }
      if (typeof value !== "number") throw createUnsupportedError();
      stack.push({ kind: "Number", value, location });
      offset += 3;
    } else if (opcode === OPCODE.new) {
      stack.push({ className: getClassName(pool, getIndex()), value: undefined });
      offset += 3;
    } else if (opcode === OPCODE.invokespecial) {
      const constructor = getMemberReference(pool, getIndex());
      const text = pop();
      const instance = pop();
      const isStringValue =
        constructor.className === `${VALUE_PACKAGE}StringValue` &&
        constructor.name === "<init>(Ljava/lang/String;)V" &&
        typeof text === "string" &&
        typeof instance === "object" &&
        "className" in instance;
      if (!isStringValue) throw createUnsupportedError();
      instance.value = { kind: "String", value: text, location };
      offset += 3;
    } else if (opcode === OPCODE.areturn) {
      // Of the only value.
      const returned = pop();
      if (typeof returned !== "object" || stack.length > 0) throw createUnsupportedError();
      if ("className" in returned) {
        if (!returned.value) throw createUnsupportedError();
        return returned.value;
      }
      return returned;
    } else {
      throw createUnsupportedError();
    }
  }
  throw createUnsupportedError();
};

// TLC loads a class named after each module and replaces each operator of the module that the
// root module sees with the public static method of the same name and arity. It reports whether
// each method matched an operator. TLC also loads the overrides a tlc2.overrides.TLCOverrides index
// class lists, from beside the spec as from the class path.
export const overrideDefinitions = (
  module: Module,
  loadClass: ((name: string) => Uint8Array | undefined) | undefined,
  isRoot: boolean,
): { module: Module; overrides: JavaOverride[] } => {
  const bytes = loadClass?.(module.name);
  if (!bytes) return { module, overrides: [] };
  const classFile = readClassFile(bytes, loadClass?.("tlc2.overrides.TLCOverrides") !== undefined);
  const arities = new Map(
    module.definitions
      .filter((definition) => isRoot || !definition.isLocal || definition.isRecursive)
      .map((definition) => [
        definition.name,
        definition.kind === "Operator" ? definition.params.length : 0,
      ]),
  );
  const isMatched = (method: JavaMethod) => arities.get(method.name) === method.arity;
  const definitions = module.definitions.map((definition): Definition => {
    if (definition.kind !== "Operator") return definition;
    const method = classFile.methods.find(
      (candidate) => candidate.name === definition.name && isMatched(candidate),
    );
    if (!method) return definition;
    // TLC evaluates each argument, in order, before it calls the method (OpValue.eval), so an
    // argument that fails or prints does so, which a literal in the operator's place skips.
    if (method.arity > 0) {
      throw new TlaUnsupportedError(
        `The Java override ${module.name}.${method.name} has parameters, whose arguments TLC evaluates, which tla-ts cannot run`,
      );
    }
    return {
      ...definition,
      body: getReturnedLiteral(method, classFile.pool, module.name, definition.location),
    };
  });
  return {
    module: { ...module, definitions },
    overrides: classFile.methods.map((method) => ({
      module: module.name,
      operator: method.name,
      signature: method.signature,
      isMatched: isMatched(method),
    })),
  };
};
