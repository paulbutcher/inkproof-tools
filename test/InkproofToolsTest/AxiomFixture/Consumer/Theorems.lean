/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import InkproofToolsTest.AxiomFixture.Dep.Axioms

theorem Consumer.usesDep (n : Nat) : n + 0 = n := Dep.assumed n
