/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import InkproofToolsTest.AxiomFixture.Clean.Axioms

theorem Clean.usesAssumed (n : Nat) : n + 0 = n := Clean.assumed n

theorem Clean.plain : 1 + 1 = 2 := rfl
