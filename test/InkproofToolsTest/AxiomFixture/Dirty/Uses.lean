/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import InkproofToolsTest.AxiomFixture.Dirty.Stray

theorem Dirty.usesStray (n : Nat) : n = n + 0 := Dirty.stray n
