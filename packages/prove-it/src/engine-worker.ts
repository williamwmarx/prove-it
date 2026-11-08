// A thread of the engine's parallel search (engine/parallel.ts). It builds the spec's environment
// from the source the coordinator sends, then, once the coordinator shares its store, compiles the
// spec against the shared ids and expands states level by level.

import type { Expression } from "./ast";
import type { ModelConfig } from "./config";
import { tlc } from "./engine/compile";
import { createEngineContext, type EngineProperties, toEngineProperties } from "./engine/context";
import { attachSearch, type GoMessage, serveLevels } from "./engine/parallel";
import { attachSharedStore } from "./engine/store";
import { createEnvironment } from "./environment";
import type { EvaluationScope } from "./evaluate";
import { createSearch } from "./search";
import { createTlcOrder } from "./tlc/order";
import type { TlcVersion } from "./tlc/version";
import { setStringOrder, setValueVersion } from "./values";
import { getParentPort } from "./worker";

export interface EngineStartMessage {
  type: "start";
  source: string;
  config: ModelConfig;
  modules: [string, string | undefined][];
  isWarningEnabled: boolean;
  version: TlcVersion | undefined;
  // A word the worker adds one to once its environment is built.
  started: SharedArrayBuffer;
}

const port = await getParentPort();

interface Prepared {
  environment: ReturnType<typeof createEnvironment>["environment"];
  config: ModelConfig;
  init: Expression;
  next: Expression;
  scope: EvaluationScope | undefined;
  isWarningEnabled: boolean;
  properties: EngineProperties;
}

const prepare = (start: EngineStartMessage): Prepared | undefined => {
  const modules = new Map(start.modules);
  const loadModule = (name: string) => modules.get(name);
  const order = createTlcOrder(start.source, loadModule, undefined, start.version);
  setStringOrder(order.getStringOrder(start.config));
  setValueVersion(start.version);
  const environment = createEnvironment(start.config, {
    source: start.source,
    loadModule,
    order,
    print: () => {},
    files: { readFile: undefined, writeFile: undefined },
    isWarningEnabled: start.isWarningEnabled,
    version: start.version,
  }).environment;
  const search = createSearch(start.config, environment, () =>
    order.getDeclarationOrder("variable"),
  );
  const init = search?.spec.init;
  const next = search?.spec.next;
  const properties = search && toEngineProperties(search.properties);
  if (init === undefined || next === undefined || !properties) return undefined;
  return {
    environment,
    config: start.config,
    init,
    next,
    scope: search.spec.scope,
    isWarningEnabled: start.isWarningEnabled,
    properties,
  };
};

const state: { prepared?: Prepared; go?: GoMessage } = {};

const serve = () => {
  const prepared = state.prepared;
  const go = state.go;
  if (!prepared || !go) return;
  attachSharedStore(go.store);
  // A worker keeps none of what TLCGet reads, and its successors print out of TLC's order.
  tlc.isShared = true;
  const context = createEngineContext(
    prepared.environment,
    prepared.config,
    { init: prepared.init, next: prepared.next, scope: prepared.scope },
    prepared.isWarningEnabled,
    prepared.properties,
    false,
  );
  serveLevels(context, attachSearch(go.search));
};

// A worker that can't build or compile the spec stays out of the search, which runs without it.
port.addEventListener("message", (event) => {
  const message = event.data as EngineStartMessage | GoMessage;
  try {
    if (message.type === "start") {
      state.prepared = prepare(message);
      if (state.prepared) Atomics.add(new Int32Array(message.started), 0, 1);
    } else {
      state.go = message;
    }
    serve();
  } catch {
    state.prepared = undefined;
  }
});
port.start?.();
