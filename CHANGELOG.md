# Changelog

## v0.4.0

`InkproofTools.ApiLock.declaresInSource` says whether a line of Lean source declares a theorem, with binders after the name or none.

## v0.3.0

A reader for the lines `api-lock` writes, `InkproofTools.ApiLock.Reader`, which imports only Lean core.

## v0.2.1

The api-lock executable resolves modules when a top-level namespace is split over several packages.

## v0.2.0

The axiom check accepts axioms declared in the axioms modules of dependencies.

## v0.1.0

InkproofTools (api-lock, test harness and driver) moved here from inkproof-core, with a shared axiom check.
