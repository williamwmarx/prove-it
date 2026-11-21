This development tool records parent-class facts for the native compiler's explicit
`ParentProfile::ModeledTlcMasterJdk21` contract. It runs only when regenerating metadata;
normal native compilation and execution need no Java installation or jar.

The contract is TLC master `d8fb231de4e4b5d02c1b2ed1ac759c086f694021` and the
Linux x86_64 Eclipse Temurin `21.0.13+9-LTS` runtime, before user class initialization
or any user mutation of the parent loader. It excludes extra parent classpath entries,
agents, patched modules, and the jar manifest's optional `CommunityModules-deps.jar` and
`CommunityModules.jar` companions. A default-looking command line does not establish
this contract. Opaque launches, legacy 1.7.4, generic source callers, and phases after
unverified user initialization remain unknown.

At the index owner's resolved execution boundary, the owner establishes this contract before
user initialization. A quiet verified index, all providers without class initializers, and
absence of earlier named override execution are one sufficient witness. Alternatively, it
can capture all exact-name parent facts before any user initialization and carry those
immutable facts only across a verified prefix that cannot mutate the parent namespace.
Strictly verified printing-only initializers can preserve such facts; their visible effects
and execution order still require a separate proof. No new modeled-profile query is allowed
after unverified initialization. Pure fact capture does not authorize moving class-file
reads or initializer effects across TLC's execution boundaries. Presence probes and early
constant/legacy errors must not invoke file attribution or parent-loader discovery. This
API performs neither. An optional origin callback defaults to no witness and is consulted
only at the resolved execution boundary.

`TLAClass.loadClass` creates a URLClassLoader with the system loader as parent and then
falls back to `Class.forName`; it is parent-first. Thus selected resolver bytes do not
establish which class Java would load. An exact TLC jar class entry returns `Present`
to block absence, without promising successful linking or initialization. A package in
any JDK system module returns `Unknown`, even if a particular class is absent. Only an
absent TLC entry and absent JDK package prove `Absent` under the complete contract.
The JDK descriptor packages include packages without class entries, so deriving this list
from class paths alone would omit 28 packages in this pinned image.

Pinned `Proxy.java:838-852,904-919` and `ReflectUtil.PROXY_PACKAGE` also create packages
`jdk.proxy<decimal>` and `com.sun.proxy.jdk.proxy<decimal>` outside the static module
package list. These exact generated namespaces stay unknown. Other unsupported binary
name forms (including slash paths, array descriptors, and Unicode identifiers outside
this bounded parser) cannot gain an absence certificate. Known exact jar entries such as
`package-info` still block absence.

Regenerate from `packages/prove-it`:

```sh
bun scripts/java-parent.ts --jar /path/to/tla2tools.jar --jdk /path/to/pinned-jdk --tlc-source /path/to/pinned-tlaplus
```

The tool checks the source commit and JDK build/vendor/platform, enumerates every `.class`
entry of the actual jar, and obtains all system-module package descriptors from the
actual pinned JDK. It cross-checks the module list against `release`. Generated
`crates/tla-front/src/java_parent/provenance.json` records jar, runtime image, release,
all 69 jmods, module package lists, source witnesses, and manifest hashes. The only
excluded class entries are two module descriptors, which are not class-loader binary
names. Other multi-release classes or duplicate class entries stop generation.

The API is allocation-free binary search over static tables. The static names and slice
entries occupy less than 160 KiB on a 64-bit target. No file reads, environment reads,
classpath prefix guesses, runtime Java subprocesses, or new runtime dependencies occur.
