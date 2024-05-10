/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import TestingLowerBounds.ForMathlib.EReal
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!

# Logarithm and exponential in the extended reals

## Main definitions

* `EReal.log : ℝ≥0∞ → EReal`
* `EReal.exp : EReal → ℝ≥0∞`

## Main statements

* `EReal.log_exp : EReal.log (EReal.exp x) = x`
* `EReal.exp_log : EReal.exp (EReal.log x) = x`

-/

open scoped ENNReal

namespace EReal

section Log

noncomputable
def log : ℝ≥0∞ → EReal
| ∞ => ⊤
| x => if x = 0 then ⊥ else Real.log x.toReal

@[simp] lemma log_zero : log 0 = ⊥ := by simp [log]
@[simp] lemma log_top : log ∞ = ⊤ := by simp [log]

lemma log_ofReal (x : ℝ) : log (ENNReal.ofReal x) = if x ≤ 0 then ⊥ else ↑(Real.log x) := by
  simp only [log, ENNReal.none_eq_top, ENNReal.ofReal_ne_top, IsEmpty.forall_iff,
    ENNReal.ofReal_eq_zero, coe_ennreal_ofReal]
  split_ifs with h_nonpos
  · rfl
  · rw [ENNReal.toReal_ofReal]
    exact (not_le.mp h_nonpos).le

lemma log_ofReal_of_pos {x : ℝ} (hx : 0 < x) : log (ENNReal.ofReal x) = Real.log x := by
  rw [log_ofReal, if_neg]
  exact not_le.mpr hx

end Log

section Exp

noncomputable
def exp : EReal → ℝ≥0∞
| ⊥ => 0
| ⊤ => ∞
| (x : ℝ) => ENNReal.ofReal (Real.exp x)

@[simp] lemma exp_bot : exp ⊥ = 0 := by simp [exp]
@[simp] lemma exp_top : exp ⊤ = ∞ := by simp [exp]

@[simp] lemma exp_coe (x : ℝ) : exp x = ENNReal.ofReal (Real.exp x) := by
  have h : (x : EReal) = some (some x) := rfl
  simp [h, exp]

end Exp

section LogExp

@[simp] lemma log_exp (x : EReal) : log (exp x) = x := by
  induction' x using EReal.rec with x
  · simp
  · rw [exp_coe, log_ofReal, if_neg (not_le.mpr (Real.exp_pos _)), Real.log_exp]
  · simp

@[simp] lemma exp_log (x : ℝ≥0∞) : exp (log x) = x := by
  by_cases hx_top : x = ∞
  · simp [hx_top]
  by_cases hx_zero : x = 0
  · simp [hx_zero]
  have hx_pos : 0 < x.toReal := ENNReal.toReal_pos hx_zero hx_top
  rw [← ENNReal.ofReal_toReal hx_top, log_ofReal_of_pos hx_pos, exp_coe, Real.exp_log hx_pos]

end LogExp

end EReal
