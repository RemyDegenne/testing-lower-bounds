/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import TestingLowerBounds.FDiv.DivFunction.DerivAtTop

/-! # Conjugate of a divergence function

For a divergence function `f`, its conjugate is `x ↦ x * f x⁻¹`, extended by `f.derivAtTop` at `0`
(the limit of `f y / y` as `y → ∞`, see `tendsto_div_nhdsLT_top`) and by `∞ * f 0` at `∞`.
-/

open Real MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

namespace DivFunction

variable {f : DivFunction}

/-- The conjugate function `x ↦ x * f x⁻¹`, with value `f.derivAtTop` at `0`. -/
noncomputable def conjFun (f : DivFunction) (x : ℝ≥0∞) : ℝ≥0∞ :=
  if x = 0 then f.derivAtTop else x * f x⁻¹

@[simp] lemma conjFun_zero : f.conjFun 0 = f.derivAtTop := by simp [conjFun]

lemma conjFun_of_ne_zero {x : ℝ≥0∞} (hx : x ≠ 0) : f.conjFun x = x * f x⁻¹ := by
  simp [conjFun, hx]

@[simp] lemma conjFun_top : f.conjFun ∞ = ∞ * f 0 := by simp [conjFun]

@[simp] lemma conjFun_one : f.conjFun 1 = 0 := by simp [conjFun]

lemma continuous_conjFun : Continuous f.conjFun := by
  rw [continuous_iff_continuousAt]
  intro x
  rcases eq_or_ne x 0 with rfl | hx0
  · have h_inv : Tendsto (fun y : ℝ≥0∞ ↦ y⁻¹) (𝓝[>] 0) (𝓝[<] ∞) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · simpa using (continuous_inv.tendsto (0 : ℝ≥0∞)).mono_left nhdsWithin_le_nhds
      · exact eventually_nhdsWithin_of_forall fun y hy ↦ ENNReal.inv_lt_top.2 hy
    have h : ContinuousWithinAt f.conjFun (Ioi 0) 0 := by
      rw [ContinuousWithinAt, conjFun_zero]
      refine (f.tendsto_div_nhdsLT_top.comp h_inv).congr' ?_
      filter_upwards [self_mem_nhdsWithin] with y (hy : 0 < y)
      simp [conjFun, hy.ne', div_eq_mul_inv, mul_comm]
    rw [continuousWithinAt_Ioi_iff_Ici] at h
    have h_univ : Ici (0 : ℝ≥0∞) = univ := by ext; simp
    rwa [h_univ, continuousWithinAt_univ] at h
  rcases eq_or_ne x ∞ with rfl | hx_top
  · by_cases hf0 : f 0 = 0
    · have h_ev : f.conjFun =ᶠ[𝓝 ∞] fun _ ↦ f.conjFun ∞ := by
        filter_upwards [Ioi_mem_nhds ENNReal.one_lt_top] with y (hy : 1 < y)
        rw [conjFun_of_ne_zero (zero_lt_one.trans hy).ne', conjFun_top, hf0, mul_zero,
          f.apply_eq_zero_of_le_one hf0 (ENNReal.inv_le_one.2 hy.le), mul_zero]
      exact continuousAt_const.congr_of_eventuallyEq h_ev
    · have h : Tendsto (fun y ↦ y * f y⁻¹) (𝓝 ∞) (𝓝 (∞ * f ∞⁻¹)) :=
        ENNReal.Tendsto.mul tendsto_id (Or.inl ENNReal.top_ne_zero)
          ((f.continuous.tendsto _).comp (continuous_inv.tendsto ∞)) (Or.inl (by simpa using hf0))
      rw [ContinuousAt, conjFun_top]
      simp only [ENNReal.inv_top] at h
      refine Tendsto.congr' ?_ h
      filter_upwards [eventually_ne_nhds ENNReal.top_ne_zero] with y hy
      exact (conjFun_of_ne_zero hy).symm
  · have h : Tendsto (fun y ↦ y * f y⁻¹) (𝓝 x) (𝓝 (x * f x⁻¹)) :=
      ENNReal.Tendsto.mul tendsto_id (Or.inl hx0)
        ((f.continuous.tendsto _).comp (continuous_inv.tendsto x)) (Or.inr hx_top)
    rw [ContinuousAt, conjFun_of_ne_zero hx0]
    refine Tendsto.congr' ?_ h
    filter_upwards [eventually_ne_nhds hx0] with y hy
    exact (conjFun_of_ne_zero hy).symm

lemma conjFun_mul_le_aux {a b : ℝ≥0} (hab : a + b = 1) (hb : b ≠ 0) (y : ℝ≥0∞) :
    f.conjFun (b * y) ≤ a * f.derivAtTop + b * f.conjFun y := by
  have hb' : (b : ℝ≥0∞) ≠ 0 := by exact_mod_cast hb
  have hb1 : (b : ℝ≥0∞) ≤ 1 := by exact_mod_cast (le_add_self.trans hab.le)
  have hab' : (a : ℝ≥0∞) + b = 1 := by exact_mod_cast hab
  rcases eq_or_ne y 0 with rfl | hy0
  · simp only [mul_zero, conjFun_zero]
    rw [← add_mul, hab', one_mul]
  rcases eq_or_ne y ∞ with rfl | hy_top
  · rw [ENNReal.mul_top hb', conjFun_top]
    by_cases hf0 : f 0 = 0
    · simp [hf0]
    · rw [ENNReal.top_mul hf0, ENNReal.mul_top hb', add_top]
  have hby0 : (b : ℝ≥0∞) * y ≠ 0 := mul_ne_zero hb' hy0
  have hby_top : (b : ℝ≥0∞) * y ≠ ∞ := ENNReal.mul_ne_top ENNReal.coe_ne_top hy_top
  rw [conjFun_of_ne_zero hby0, conjFun_of_ne_zero hy0]
  have h_le : y⁻¹ ≤ ((b : ℝ≥0∞) * y)⁻¹ := ENNReal.inv_le_inv.2 (mul_le_of_le_one_left' hb1)
  have h := f.le_add_derivAtTop h_le
  have h_alg : (b : ℝ≥0∞) * y * (((b : ℝ≥0∞) * y)⁻¹ - y⁻¹) = a := by
    rw [ENNReal.mul_inv (Or.inl hb') (Or.inl ENNReal.coe_ne_top),
      ENNReal.mul_sub (fun _ _ ↦ hby_top), mul_mul_mul_comm,
      ENNReal.mul_inv_cancel hb' ENNReal.coe_ne_top, ENNReal.mul_inv_cancel hy0 hy_top, one_mul,
      mul_assoc, ENNReal.mul_inv_cancel hy0 hy_top, mul_one]
    exact (ENNReal.eq_sub_of_add_eq ENNReal.coe_ne_top hab').symm
  calc (b : ℝ≥0∞) * y * f ((b : ℝ≥0∞) * y)⁻¹
      ≤ (b : ℝ≥0∞) * y * (f y⁻¹ + f.derivAtTop * (((b : ℝ≥0∞) * y)⁻¹ - y⁻¹)) := by gcongr
    _ = b * (y * f y⁻¹) + f.derivAtTop * ((b : ℝ≥0∞) * y * (((b : ℝ≥0∞) * y)⁻¹ - y⁻¹)) := by
        ring
    _ = a * f.derivAtTop + b * (y * f y⁻¹) := by rw [h_alg, add_comm, mul_comm]

lemma conjFun_add_le_of_ne_zero {x y : ℝ≥0∞} (hx : x ≠ 0) (hy : y ≠ 0) {a b : ℝ≥0}
    (ha : a ≠ 0) (hb : b ≠ 0) (hab : a + b = 1) :
    f.conjFun (a * x + b * y) ≤ a * f.conjFun x + b * f.conjFun y := by
  have ha' : (a : ℝ≥0∞) ≠ 0 := by exact_mod_cast ha
  have hb' : (b : ℝ≥0∞) ≠ 0 := by exact_mod_cast hb
  have hab' : (a : ℝ≥0∞) + b = 1 := by exact_mod_cast hab
  rcases eq_or_ne x ∞ with rfl | hx_top
  · rw [ENNReal.mul_top ha', top_add, conjFun_top]
    by_cases hf0 : f 0 = 0
    · simp [hf0]
    · rw [ENNReal.top_mul hf0, ENNReal.mul_top ha', top_add]
  rcases eq_or_ne y ∞ with rfl | hy_top
  · rw [ENNReal.mul_top hb', add_top, conjFun_top]
    by_cases hf0 : f 0 = 0
    · simp [hf0]
    · rw [ENNReal.top_mul hf0, ENNReal.mul_top hb', add_top]
  set z := (a : ℝ≥0∞) * x + b * y with hz
  have hz0 : z ≠ 0 := by simp [hz, ha', hx]
  have hz_top : z ≠ ∞ := by simp [hz, ENNReal.mul_eq_top, hx_top, hy_top]
  rw [conjFun_of_ne_zero hz0, conjFun_of_ne_zero hx, conjFun_of_ne_zero hy]
  set l₁ : ℝ≥0 := ((a : ℝ≥0∞) * x / z).toNNReal with hl₁
  set l₂ : ℝ≥0 := ((b : ℝ≥0∞) * y / z).toNNReal with hl₂
  have hl₁' : (l₁ : ℝ≥0∞) = a * x / z :=
    ENNReal.coe_toNNReal (ENNReal.div_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top hx_top) hz0)
  have hl₂' : (l₂ : ℝ≥0∞) = b * y / z :=
    ENNReal.coe_toNNReal (ENNReal.div_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top hy_top) hz0)
  have hl : l₁ + l₂ = 1 := by
    rw [← ENNReal.coe_inj, ENNReal.coe_add, hl₁', hl₂', ENNReal.coe_one, ENNReal.div_add_div_same,
      ← hz, ENNReal.div_self hz0 hz_top]
  have h_arg : z⁻¹ = l₁ • x⁻¹ + l₂ • y⁻¹ := by
    simp only [ENNReal.smul_def, smul_eq_mul, hl₁', hl₂', div_eq_mul_inv]
    calc z⁻¹ = (a + b) * z⁻¹ := by rw [hab', one_mul]
      _ = a * (x * x⁻¹) * z⁻¹ + b * (y * y⁻¹) * z⁻¹ := by
          rw [ENNReal.mul_inv_cancel hx hx_top, ENNReal.mul_inv_cancel hy hy_top, mul_one, mul_one,
            add_mul]
      _ = a * x * z⁻¹ * x⁻¹ + b * y * z⁻¹ * y⁻¹ := by ring
  have h_conv := f.convexOn.2 (mem_univ x⁻¹) (mem_univ y⁻¹) zero_le zero_le hl
  rw [← h_arg] at h_conv
  simp only [ENNReal.smul_def, smul_eq_mul, hl₁', hl₂'] at h_conv
  calc z * f z⁻¹ ≤ z * (a * x / z * f x⁻¹ + b * y / z * f y⁻¹) := by gcongr
    _ = (a * x * (z * z⁻¹)) * f x⁻¹ + (b * y * (z * z⁻¹)) * f y⁻¹ := by
        simp only [div_eq_mul_inv]; ring
    _ = a * (x * f x⁻¹) + b * (y * f y⁻¹) := by rw [ENNReal.mul_inv_cancel hz0 hz_top]; ring

lemma convexOn_conjFun : ConvexOn ℝ≥0 univ f.conjFun := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab ↦ ?_⟩
  simp only [ENNReal.smul_def, smul_eq_mul]
  rcases eq_or_ne a 0 with rfl | ha0
  · rw [zero_add] at hab
    subst hab
    simp
  rcases eq_or_ne b 0 with rfl | hb0
  · rw [add_zero] at hab
    subst hab
    simp
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [mul_zero, zero_add, conjFun_zero]
    exact f.conjFun_mul_le_aux hab hb0 y
  rcases eq_or_ne y 0 with rfl | hy0
  · rw [mul_zero, add_zero, conjFun_zero, add_comm]
    exact f.conjFun_mul_le_aux (by rwa [add_comm]) ha0 x
  exact f.conjFun_add_le_of_ne_zero hx0 hy0 ha0 hb0 hab

/-- Conjugate of a divergence function: `x ↦ x * f x⁻¹`, with value `f.derivAtTop` at `0`. -/
noncomputable
def conj (f : DivFunction) : DivFunction where
  toFun := f.conjFun
  one := conjFun_one
  convexOn' := convexOn_conjFun
  continuous' := continuous_conjFun

@[simp] lemma conj_apply (f : DivFunction) (x : ℝ≥0∞) :
    f.conj x = if x = 0 then f.derivAtTop else x * f x⁻¹ := rfl

end DivFunction

end ProbabilityTheory
