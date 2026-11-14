# Inkproof.Tools

Part of Inkproof. Released under the Apache 2.0 license; see `LICENSE`.

Development tooling for Inkproof libraries: `api-lock`, the test harness and driver, and the axiom check. Require it from the library's `test` subproject (it needs no other dependency), never from the library itself.

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

Compiling it fails on an axiom declared outside `MyLib.Axioms`, on a declaration using an axiom not declared there or in Lean, and when no module starts with `MyLib`. Omit the second argument if the library has no axioms.
