# Inkproof.Tools

Part of Inkproof. Released under the Apache 2.0 license; see `LICENSE`.

Development tooling for Inkproof libraries: `api-lock`, the test harness and driver, and the axiom check. Require it from the library's `test` subproject (it needs no other dependency), never from the library itself. The one exception is `InkproofTools.ApiLock.Reader`, which imports nothing and may be linked by an application that reads `API.lock`.

```lean
require «inkproof-tools» from git "https://github.com/paulbutcher/inkproof-tools" @ "v0.2.1"
```

## What it does

- Record a library's public API (declarations and theorem statements) in `API.lock`, to review and diff: `lake exe api-lock`, `scripts/api-lock.sh`, `InkproofTools.ApiLock.run`, `apiLines`.
- Read the lines of an `API.lock` back, without Lean: `InkproofTools.ApiLock.parseTheorem` (name and statement of a theorem line), `declares` (does a line declare a full or namespace-relative name), `declaresInSource` (the same for a Lean source line, with binders, no colon or leading attributes), `declaresInSourceAt` (does a source line, read inside given namespaces, declare a full name), `qualify`, `candidates`.
- Run a library's tests natively and under Lasm from one driver: `lake exe inkproof-test-driver`, `InkproofTools.Test.runAll`, `runStep`, `lasmStep`, `runTests`.
- Write test cases, property tests with a seeded random generator, and a check that a platform runs the expected build: `InkproofTools.Test.TestCase`, `check`, `forAll`, `Rng`, `platformTest`.
- Check that a library declares axioms only in its axioms module and uses no others: `InkproofTools.AxiomCheck.check`, `violations`.
- Check that dependencies are pinned to release tags: `scripts/check-pins.sh`.

## api-lock

After `lake build`, `lake exe api-lock <root module>...` prints the public API of each root and its submodules. Keep the output in `API.lock`; `scripts/api-lock.sh [<root module>...]` builds and prints it (default: this library's modules). List the modules of a library, since a root with no module of its own, such as `InkproofTools`, matches only submodules that are named.

## Test driver

In the test subproject, require this package, make `Main.lean` the root of an executable called `tests`, and make the `@[test_driver]` script run `lake exe inkproof-test-driver` from that directory. `Main` builds its cases from `InkproofTools.Test.Harness` and includes `platformTest (args.contains "--expect-wasm")`.

## Axiom check

In a module of the test package that imports the library:

```lean
import InkproofTools.AxiomCheck
import MyLib

open Lean Elab Command

run_cmd liftCoreM (InkproofTools.AxiomCheck.check `MyLib (some `MyLib.Axioms))
```

Compiling it fails on an axiom declared outside `MyLib.Axioms`, on a declaration using an axiom not declared there or in Lean, and when no module starts with `MyLib`. Omit the second argument if the library has no axioms. A third argument lists the axioms modules of libraries depended on, such as ``[`Inkproof.Core.Axioms]``, whose axioms are also allowed.
