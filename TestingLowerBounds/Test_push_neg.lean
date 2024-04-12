-- This file is only needed as an example for the `push_neg` tactic

import Mathlib.Order.Filter.Basic

example (f : Filter Nat) (h : ∃ᶠ x in f, x = 0) : ¬ ∀ᶠ x in f, x ≠ 0 := by
  push_neg
  -- push_neg does nothing
  -- ⊢ ¬∀ᶠ (x : ℕ) in f, x ≠ 0
  apply Filter.not_eventually.mpr
  -- ⊢ ∃ᶠ (x : ℕ) in f, ¬x ≠ 0
  push_neg
  exact h

-- simp can handle this situation alone
example (f : Filter Nat) (h : ∃ᶠ x in f, x = 0) : ¬ ∀ᶠ x in f, x ≠ 0 := by
  simp
  exact h
