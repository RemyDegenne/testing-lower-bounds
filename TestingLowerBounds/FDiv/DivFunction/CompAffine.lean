/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import TestingLowerBounds.FDiv.DivFunction.DerivAtTop

/-! # Composition of a divergence function with an affine map

For a divergence function `f` and `a b : ℝ≥0` with `a + b = 1`, the function `x ↦ f (a * x + b)`
is again a divergence function, which we call `f.compAffine a b hab`.
Its derivative at infinity is `a * f.derivAtTop`.
-/

@[expose] public section

open Filter Set
open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

namespace DivFunction

variable {f : DivFunction} {a b : ℝ≥0}

lemma convexOn_comp_affine (f : DivFunction) (a b : ℝ≥0) :
    ConvexOn ℝ≥0 univ (fun x : ℝ≥0∞ ↦ f (a * x + b)) := by
  refine ⟨convex_univ, fun x _ y _ l m _ _ hlm ↦ ?_⟩
  have hlm' : (l : ℝ≥0∞) + m = 1 := by exact_mod_cast hlm
  simp only [ENNReal.smul_def, smul_eq_mul]
  have h_eq : (a : ℝ≥0∞) * (l * x + m * y) + b = l * (a * x + b) + m * (a * y + b) := by
    calc (a : ℝ≥0∞) * (l * x + m * y) + b = a * (l * x + m * y) + (l + m) * b := by
          rw [hlm', one_mul]
      _ = l * (a * x + b) + m * (a * y + b) := by ring
  rw [h_eq]
  have h := f.convexOn.2 (mem_univ (a * x + b)) (mem_univ (a * y + b)) zero_le zero_le hlm
  simpa only [ENNReal.smul_def, smul_eq_mul] using h

lemma continuous_comp_affine (f : DivFunction) (a b : ℝ≥0) :
    Continuous (fun x : ℝ≥0∞ ↦ f (a * x + b)) :=
  f.continuous.comp (((ENNReal.continuous_const_mul ENNReal.coe_ne_top)).add continuous_const)

/-- The divergence function `x ↦ f (a * x + b)`, for `a + b = 1`. -/
noncomputable
def compAffine (f : DivFunction) (a b : ℝ≥0) (hab : a + b = 1) : DivFunction where
  toFun x := f (a * x + b)
  one := by
    have hab' : (a : ℝ≥0∞) + b = 1 := by exact_mod_cast hab
    simp [hab']
  convexOn' := f.convexOn_comp_affine a b
  continuous' := f.continuous_comp_affine a b

@[simp] lemma compAffine_apply (hab : a + b = 1) (x : ℝ≥0∞) :
    f.compAffine a b hab x = f (a * x + b) := rfl

@[simp] lemma derivAtTop_compAffine (hab : a + b = 1) :
    (f.compAffine a b hab).derivAtTop = a * f.derivAtTop := by
  have : (𝓝[<] (∞ : ℝ≥0∞)).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, ENNReal.zero_lt_top⟩
  refine tendsto_nhds_unique (f.compAffine a b hab).tendsto_div_nhdsLT_top ?_
  rcases eq_or_ne a 0 with rfl | ha
  · have hb : b = 1 := by simpa using hab
    subst hb
    simp
  have ha' : (a : ℝ≥0∞) ≠ 0 := by exact_mod_cast ha
  -- `a * y + b` tends to `∞` from below
  have h_aff : Tendsto (fun y : ℝ≥0∞ ↦ a * y + b) (𝓝[<] ∞) (𝓝[<] ∞) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have h := ((ENNReal.continuous_const_mul (a := (a : ℝ≥0∞)) ENNReal.coe_ne_top).add
        (continuous_const (y := (b : ℝ≥0∞)))).tendsto ∞
      simp only [Pi.add_apply, ENNReal.mul_top ha', top_add] at h
      exact h.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with y (hy : y < ∞)
      exact ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top ENNReal.coe_lt_top hy, ENNReal.coe_lt_top⟩
  -- `(a * y + b) / y` tends to `a`
  have h_ratio : Tendsto (fun y : ℝ≥0∞ ↦ (a * y + b) / y) (𝓝[<] ∞) (𝓝 a) := by
    have h_inv : Tendsto (fun y : ℝ≥0∞ ↦ (b : ℝ≥0∞) * y⁻¹) (𝓝[<] ∞) (𝓝 0) := by
      have h := ENNReal.Tendsto.const_mul
        (((continuous_inv.tendsto (∞ : ℝ≥0∞))).mono_left (nhdsWithin_le_nhds (s := Iio ∞)))
        (a := (b : ℝ≥0∞)) (Or.inr ENNReal.coe_ne_top)
      simpa using h
    have h_add := (tendsto_const_nhds (x := (a : ℝ≥0∞))).add h_inv
    rw [add_zero] at h_add
    refine h_add.congr' ?_
    filter_upwards [Ioo_mem_nhdsLT ENNReal.zero_lt_top] with y hy
    rw [ENNReal.add_div, ENNReal.mul_div_cancel_right hy.1.ne' hy.2.ne, div_eq_mul_inv]
  have h := ENNReal.Tendsto.mul (f.tendsto_div_nhdsLT_top.comp h_aff) (Or.inr ENNReal.coe_ne_top)
    h_ratio (Or.inl ha')
  rw [mul_comm]
  refine h.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT ENNReal.zero_lt_top] with y hy
  have h0 : (a : ℝ≥0∞) * y + b ≠ 0 := by
    simp [ha', hy.1.ne']
  have h_top : (a : ℝ≥0∞) * y + b ≠ ∞ :=
    (ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top ENNReal.coe_lt_top hy.2, ENNReal.coe_lt_top⟩).ne
  simp only [Function.comp_apply, compAffine_apply, div_eq_mul_inv]
  rw [mul_assoc, ← mul_assoc _ (a * y + b), ENNReal.inv_mul_cancel h0 h_top, one_mul]

end DivFunction

end ProbabilityTheory
