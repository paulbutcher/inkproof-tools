# Inkproof.Tools design

Development tooling shared by every Inkproof library. It depends on nothing, imports only Lean, and is used from a library's test package and scripts, never from its library code. Nothing here knows about any one library.

- `InkproofTools.ApiLock` and the `api-lock` executable print one line per public declaration (kind, full name and type, sorted) of the given root modules and their submodules, leaving out `Internal` modules, private and derived declarations. The command line and line format are a contract with every library's `API.lock`: changing either changes them all.
- `InkproofTools.Test.Harness` and `Platform` hold the test cases, a deterministic random source, `forAll` and the platform check. They import nothing from Lean beyond core, so a Lasm build links them.
- `InkproofTools.Test.Driver` and the `inkproof-test-driver` executable build a test subproject, run its `tests` executable natively, then compile and run the same `Main.lean` under Lasm (skipped with a warning if Lasm is not installed, an error under `INKPROOF_REQUIRE_LASM=1`).
- `InkproofTools.AxiomCheck` is the shared axiom check. `violations env root axiomsModule` lists the problems in the modules whose names start with `root`: an axiom declared outside `axiomsModule` (any axiom, if none is given), a declaration depending on an axiom that is neither Lean's own nor in `axiomsModule`, and no declarations at all, so the check cannot pass vacuously. `check` fails with them.
- Tests live in the `test` subproject. `lake test` builds it, runs `Main.lean`, and compares `api-lock` on a fixture with `ApiLockFixture.expected`. The axiom check is tested at compile time on fixtures, one clean and one not.
