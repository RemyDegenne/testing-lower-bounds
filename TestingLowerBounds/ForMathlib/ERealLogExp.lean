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

/-- Logarithm as a function from `ℝ≥0∞` to `EReal`. -/
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

@[simp] lemma log_eq_bot_iff {x : ℝ≥0∞} : log x = ⊥ ↔ x = 0 := by
  refine ⟨fun h ↦ ?_, fun hx ↦ by simp [hx]⟩
  by_contra hx_ne_zero
  by_cases hx_top : x = ∞
  · simp [hx_top] at h
  have hx_pos : 0 < x.toReal := ENNReal.toReal_pos hx_ne_zero hx_top
  rw [← ENNReal.ofReal_toReal hx_top, log_ofReal_of_pos hx_pos] at h
  simp at h

@[simp] lemma log_eq_top_iff {x : ℝ≥0∞} : log x = ⊤ ↔ x = ∞ := by
  refine ⟨fun h ↦ ?_, fun hx ↦ by simp [hx]⟩
  by_contra hx_ne_top
  by_cases hx_zero : x = 0
  · simp [hx_zero] at h
  have hx_pos : 0 < x.toReal := ENNReal.toReal_pos hx_zero hx_ne_top
  rw [← ENNReal.ofReal_toReal hx_ne_top, log_ofReal_of_pos hx_pos] at h
  simp at h

lemma log_mono {a b : ℝ≥0∞} (h : a ≤ b) : log a ≤ log b := by
  by_cases hb_top : b = ∞
  · simp [hb_top]
  have ha_ne_top : a ≠ ∞ := by
    refine fun ha ↦ hb_top (top_le_iff.mp ?_)
    rwa [ha] at h
  by_cases ha_zero : a = 0
  · simp [ha_zero]
  have hb_ne_zero : b ≠ 0 := by
    refine fun hb ↦ ha_zero (le_antisymm ?_ zero_le')
    rwa [hb] at h
  have ha_pos : 0 < a.toReal := ENNReal.toReal_pos ha_zero ha_ne_top
  have hb_pos : 0 < b.toReal := ENNReal.toReal_pos hb_ne_zero hb_top
  rw [← ENNReal.ofReal_toReal ha_ne_top, ← ENNReal.ofReal_toReal hb_top,
    log_ofReal_of_pos ha_pos, log_ofReal_of_pos hb_pos]
  norm_cast
  rwa [Real.log_le_log_iff ha_pos hb_pos, ENNReal.toReal_le_toReal ha_ne_top hb_top]

lemma log_inv (x : ℝ≥0∞) : log x⁻¹ = - log x := by
  by_cases hx_top : x = ∞
  · simp [hx_top]
  by_cases hx_zero : x = 0
  · simp [hx_zero]
  have hx_pos : 0 < x.toReal := ENNReal.toReal_pos hx_zero hx_top
  rw [← ENNReal.ofReal_toReal hx_top, log_ofReal_of_pos hx_pos, ← ENNReal.ofReal_inv_of_pos hx_pos,
    log_ofReal_of_pos (by positivity)]
  norm_cast
  rw [Real.log_inv]

lemma log_mul (a b : ℝ≥0∞) : log (a * b) = log a + log b := by
  by_cases ha_zero : a = 0
  · simp [ha_zero]
  by_cases hb_zero : b = 0
  · simp [hb_zero]
  by_cases ha_top : a = ∞
  · rw [ha_top, log_top, EReal.top_add_of_ne_bot, ENNReal.top_mul hb_zero, log_top]
    rwa [ne_eq, log_eq_bot_iff]
  by_cases hb_top : b = ∞
  · rw [hb_top, log_top, EReal.add_top_of_ne_bot, ENNReal.mul_top ha_zero, log_top]
    rwa [ne_eq, log_eq_bot_iff]
  have ha_pos : 0 < a.toReal := ENNReal.toReal_pos ha_zero ha_top
  have hb_pos : 0 < b.toReal := ENNReal.toReal_pos hb_zero hb_top
  rw [← ENNReal.ofReal_toReal ha_top,← ENNReal.ofReal_toReal hb_top,
    ← ENNReal.ofReal_mul ENNReal.toReal_nonneg, log_ofReal_of_pos, log_ofReal_of_pos ha_pos,
    log_ofReal_of_pos hb_pos, Real.log_mul ha_pos.ne' hb_pos.ne']
  · norm_cast
  · positivity

end Log

section Exp

/-- Exponential as a function from `EReal` to `ℝ≥0∞`. -/
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

@[simp] lemma exp_eq_zero_iff {x : EReal} : exp x = 0 ↔ x = ⊥ := by
  induction' x using EReal.rec with x <;> simp [Real.exp_pos]

@[simp] lemma exp_eq_top_iff {x : EReal} : exp x = ∞ ↔ x = ⊤ := by
  induction' x using EReal.rec with x <;> simp

lemma exp_mono {a b : EReal} (h : a ≤ b) : exp a ≤ exp b := by
  induction' a using EReal.rec with a
  · simp
  · induction' b using EReal.rec with b
    · simp at h
    · rw [exp_coe, exp_coe]
      exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp_of_le (mod_cast h))
    · simp
  · rw [top_le_iff] at h
    simp [h.symm, exp_top, top_le_iff]

lemma exp_neg (x : EReal) : exp (-x) = (exp x)⁻¹ := by
  induction' x using EReal.rec with x
  · simp
  · rw [exp_coe, ← EReal.coe_neg, exp_coe, ← ENNReal.ofReal_inv_of_pos (Real.exp_pos _)]
    congr
    rw [Real.exp_neg]
  · simp

lemma exp_add (x y : EReal) : exp (x + y) = exp x * exp y := by
  induction' x using EReal.rec with x
  · simp
  · induction' y using EReal.rec with y
    · simp
    · simp only [← EReal.coe_add, exp_coe]
      rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), Real.exp_add]
    · simp only [coe_add_top, exp_top, exp_coe]
      rw [ENNReal.mul_top]
      simp [Real.exp_pos]
  · induction' y using EReal.rec with y
    · simp
    · simp only [top_add_coe, exp_top, exp_coe]
      rw [ENNReal.top_mul]
      simp [Real.exp_pos]
    · simp

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

@[simp]
lemma log_le_iff {a b : ℝ≥0∞} : log a ≤ log b ↔ a ≤ b := by
  refine ⟨fun h ↦ ?_, log_mono⟩
  rw [← exp_log a, ← exp_log b]
  exact exp_mono h

@[simp]
lemma exp_le_iff {a b : EReal} : exp a ≤ exp b ↔ a ≤ b := by
  conv_rhs => rw [← log_exp a, ← log_exp b, log_le_iff]

/-- `EReal.log` and its inverse `Ereal.exp` are an order isomorphism between `ℝ≥0∞` and `EReal`. -/
noncomputable
def logOrderIso : ℝ≥0∞ ≃o EReal where
  toFun := log
  invFun := exp
  left_inv x := exp_log x
  right_inv x := log_exp x
  map_rel_iff' := by simp only [Equiv.coe_fn_mk, log_le_iff, forall_const]

lemma continuous_log : Continuous log := logOrderIso.continuous

lemma continuous_exp : Continuous exp := logOrderIso.symm.continuous

lemma measurable_log : Measurable log := continuous_log.measurable

lemma measurable_exp : Measurable exp := continuous_exp.measurable

lemma _root_.Measurable.ereal_log {α : Type*} {_ : MeasurableSpace α}
    {f : α → ℝ≥0∞} (hf : Measurable f) :
    Measurable fun x ↦ log (f x) := measurable_log.comp hf

lemma _root_.Measurable.ereal_exp {α : Type*} {_ : MeasurableSpace α}
    {f : α → EReal} (hf : Measurable f) :
    Measurable fun x ↦ exp (f x) := measurable_exp.comp hf

end LogExp

end EReal
