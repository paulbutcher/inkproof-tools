/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import InkproofToolsTest.AxiomFixture.Clean.Theorems
import InkproofToolsTest.AxiomFixture.Consumer.Theorems
import InkproofToolsTest.AxiomFixture.Dirty.Uses
import InkproofTools.AxiomCheck

/-! Compiling this module fails unless `AxiomCheck` accepts the clean fixture and reports each kind
of problem in the others. -/

open Lean Elab Command InkproofTools.AxiomCheck

private def fixture : Name := `InkproofToolsTest.AxiomFixture

run_cmd do
  let env ← getEnv
  let clean := fixture ++ `Clean
  unless (← liftCoreM (violations env clean (some (clean ++ `Axioms)))).isEmpty do
    throwError "a library confined to its axioms module was rejected"
  liftCoreM (check clean (some (clean ++ `Axioms)))

run_cmd do
  let env ← getEnv
  let dirty := fixture ++ `Dirty
  let problems ← liftCoreM (violations env dirty (some (dirty ++ `Axioms)))
  unless problems.size == 3 do
    throwError "expected the stray axiom, and each declaration depending on it, to be reported, got {problems}"

run_cmd do
  let env ← getEnv
  let clean := fixture ++ `Clean
  if (← liftCoreM (violations env clean)).isEmpty then
    throwError "axioms were accepted although none are allowed"

run_cmd do
  let env ← getEnv
  let consumer := fixture ++ `Consumer
  let dep := fixture ++ `Dep ++ `Axioms
  unless (← liftCoreM (violations env consumer none [dep])).isEmpty do
    throwError "an axiom from a dependency's axioms module was rejected"
  liftCoreM (check consumer none [dep])
  if (← liftCoreM (violations env consumer)).isEmpty then
    throwError "an axiom from a dependency was accepted without naming its module"

run_cmd do
  let env ← getEnv
  let dirty := fixture ++ `Dirty
  let dep := fixture ++ `Dep ++ `Axioms
  unless (← liftCoreM (violations env dirty (some (dirty ++ `Axioms)) [dep])).size == 3 do
    throwError "naming a dependency's axioms module excused an axiom declared under the root"

run_cmd do
  let env ← getEnv
  if (← liftCoreM (violations env `InkproofToolsTest.NoSuchLibrary)).isEmpty then
    throwError "a namespace with no declarations passed"
