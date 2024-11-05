/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import TestingLowerBounds.FDiv.DivFunction

/-!

# f-Divergences functions

-/

open Real MeasureTheory Filter Set MeasurableSpace

open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μ ν : Measure α}
  {f : ℝ → ℝ}

namespace DivFunction

section OfReal

-- todo: the derivative conditions are useful for lemmas but not in the def
/-- Build a `DivFunction` from a function `f : ℝ → ℝ` which is convex on `Ioi 0` and satisfies
`f 1 = 0` and `leftDeriv f 1 ≤ 0`, `0 ≤ rightDeriv f 1`. -/
noncomputable
def ofReal (f : ℝ → ℝ) (hf : ConvexOn ℝ (Ioi 0) f)
    (hf_one : f 1 = 0) (hf_ld : leftDeriv f 1 ≤ 0) (hf_rd : 0 ≤ rightDeriv f 1) : DivFunction where
  toFun x :=
    -- give values at 0 and ∞ to ensure continuity
    if x = 0 then Function.rightLim (fun x ↦ ENNReal.ofReal (f x)) 0
    else if x = ∞ then limsup (fun x ↦ ENNReal.ofReal (f x)) atTop
    else ENNReal.ofReal (f x.toReal)
  one := by simp [hf_one]
  convexOn' := sorry
  continuous' := sorry

noncomputable
abbrev ofRealOfNonneg (f : ℝ → ℝ) (hf : ConvexOn ℝ (Ioi 0) f)
    (hf_one : f 1 = 0) (hf_nonneg : ∀ x, 0 < x → 0 ≤ f x) : DivFunction :=
  ofReal f hf hf_one
    (hf.leftDeriv_nonpos_of_isMinOn (fun x hx ↦ by simp [hf_one, hf_nonneg x hx]) (by simp))
    (hf.rightDeriv_nonneg_of_isMinOn (fun x hx ↦ by simp [hf_one, hf_nonneg x hx]) (by simp))

variable {hf : ConvexOn ℝ (Ioi 0) f} {hf_one : f 1 = 0}
  {hf_ld : leftDeriv f 1 ≤ 0} {hf_rd : 0 ≤ rightDeriv f 1}

section OfRealApply

@[simp]
lemma ofReal_apply_zero :
    ofReal f hf hf_one hf_ld hf_rd 0 = Function.rightLim (fun x ↦ ENNReal.ofReal (f x)) 0 := by
  simp [ofReal]

lemma ofReal_apply_zero_of_continuousWithinAt (hf_cont : ContinuousWithinAt f (Ioi 0) 0) :
    ofReal f hf hf_one hf_ld hf_rd 0 = ENNReal.ofReal (f 0) := by
  simp only [ofReal_apply_zero]
  refine rightLim_eq_of_tendsto NeBot.ne' ?_
  refine ContinuousWithinAt.tendsto ?_
  exact (ENNReal.continuous_ofReal.tendsto _).comp hf_cont.tendsto

@[simp]
lemma ofReal_apply_top :
    ofReal f hf hf_one hf_ld hf_rd ∞ = limsup (fun x ↦ ENNReal.ofReal (f x)) atTop := by
  simp [ofReal]

lemma ofReal_apply {x : ℝ≥0∞} (hx_zero : x ≠ 0) (hx_top : x ≠ ∞) :
    ofReal f hf hf_one hf_ld hf_rd x = ENNReal.ofReal (f x.toReal) := by
  simp [ofReal, hx_zero, hx_top]

lemma ofReal_apply_of_continuousWithinAt (hf_cont : ContinuousWithinAt f (Ioi 0) 0)
    {x : ℝ≥0∞} (hx : x ≠ ∞) :
    ofReal f hf hf_one hf_ld hf_rd x = ENNReal.ofReal (f x.toReal) := by
  by_cases hx0 : x = 0
  · simp [hx0, ofReal_apply_zero_of_continuousWithinAt hf_cont]
  · exact ofReal_apply hx0 hx

lemma realFun_ofReal_apply {x : ℝ} (hx : 0 < x) :
    (ofReal f hf hf_one hf_ld hf_rd).realFun x = f x := by
  rw [realFun, ofReal_apply, ENNReal.toReal_ofReal, ENNReal.toReal_ofReal hx.le]
  · exact hf.nonneg_of_todo' hf_one hf_ld hf_rd ENNReal.toReal_nonneg
  · simp [hx]
  · simp

end OfRealApply

section DerivAtTop

lemma derivAtTop_ofReal :
    (ofReal f hf hf_one hf_ld hf_rd).derivAtTop
      = limsup (fun x ↦ ENNReal.ofReal (rightDeriv f x)) atTop := by
  sorry

lemma derivAtTop_ofReal_of_tendsto_atTop (h : Tendsto (rightDeriv f) atTop atTop) :
    (ofReal f hf hf_one hf_ld hf_rd).derivAtTop = ∞ := by
  sorry

end DerivAtTop

section Integral

lemma lintegral_ofReal_eq_top_of_not_integrable [SigmaFinite μ] [IsFiniteMeasure ν]
    (h_int : ¬ Integrable (fun x ↦ f (μ.rnDeriv ν x).toReal) ν) :
    ∫⁻ x, ofReal f hf hf_one hf_ld hf_rd (μ.rnDeriv ν x) ∂ν = ∞ := by
  refine lintegral_eq_top_of_not_integrable_realFun ?_
  suffices ¬ IntegrableOn
      (fun x ↦ (ofReal f hf hf_one hf_ld hf_rd).realFun (μ.rnDeriv ν x).toReal)
      {x | μ.rnDeriv ν x ≠ 0} ν from
    fun h ↦ this h.integrableOn
  rw [← integrableOn_univ] at h_int
  have : (univ : Set α) = {x | μ.rnDeriv ν x ≠ 0} ∪ {x | μ.rnDeriv ν x = 0} :=
    (compl_union_self _).symm
  rw [this, integrableOn_union] at h_int
  have h_int_zero : IntegrableOn (fun x ↦ f (μ.rnDeriv ν x).toReal) {x | μ.rnDeriv ν x = 0} ν := by
    refine (integrableOn_congr_fun ?_ ?_).mpr
      ((integrableOn_const (C := f 0)).mpr (.inr (measure_lt_top _ _)))
    · intro x hx
      simp only [mem_setOf_eq] at hx
      simp [hx]
    · exact μ.measurable_rnDeriv ν (measurableSet_singleton 0)
  simp [h_int_zero] at h_int
  convert h_int using 1
  refine integrableOn_congr_fun_ae ((ae_restrict_iff' ?_).mpr ?_)
  · exact (μ.measurable_rnDeriv ν (measurableSet_singleton 0)).compl
  filter_upwards [μ.rnDeriv_ne_top ν] with x hx_top hx_zero
  rw [DivFunction.realFun_ofReal_apply]
  exact ENNReal.toReal_pos hx_zero hx_top

lemma lintegral_ofReal' [SigmaFinite μ] [SigmaFinite ν] (hμν : μ ≪ ν)
    (h : ν {x | μ.rnDeriv ν x = 0} ≠ ∞) :
    ∫⁻ x, ofReal f hf hf_one hf_ld hf_rd (μ.rnDeriv ν x) ∂ν
      = ∫⁻ x, ENNReal.ofReal (f (μ.rnDeriv ν x).toReal) ∂ν
        - ENNReal.ofReal (f 0) * ν {x | μ.rnDeriv ν x = 0}
        + Function.rightLim (fun x ↦ ENNReal.ofReal (f x)) 0 * ν {x | μ.rnDeriv ν x = 0} := by
  let s := {x | μ.rnDeriv ν x = 0}
  have hs : MeasurableSet s := μ.measurable_rnDeriv ν (measurableSet_singleton 0)
  rw [← lintegral_add_compl _ hs]
  have hs_zero : ∀ x ∈ s, μ.rnDeriv ν x = 0 := fun _ hx ↦ hx
  have h1 : ∫⁻ x in s, ofReal f hf hf_one hf_ld hf_rd (μ.rnDeriv ν x) ∂ν
      = Function.rightLim (fun x ↦ ENNReal.ofReal (f x)) 0 * ν {x | μ.rnDeriv ν x = 0} := by
    have : ∀ x ∈ s, ofReal f hf hf_one hf_ld hf_rd (μ.rnDeriv ν x)
        = Function.rightLim (fun x ↦ ENNReal.ofReal (f x)) 0 := by
      intro x hx
      simp [hs_zero x hx]
    rw [setLIntegral_congr_fun hs (ae_of_all _ this)]
    simp
  have h2 : ∫⁻ x in sᶜ, ofReal f hf hf_one hf_ld hf_rd (μ.rnDeriv ν x) ∂ν
      = ∫⁻ x in sᶜ, ENNReal.ofReal (f (μ.rnDeriv ν x).toReal) ∂ν := by
    have h_ne_top := μ.rnDeriv_ne_top ν
    sorry
  have h3 : ∫⁻ x in s, ENNReal.ofReal (f (μ.rnDeriv ν x).toReal) ∂ν
      = ENNReal.ofReal (f 0) * ν {x | μ.rnDeriv ν x = 0} := by
    have : ∀ x ∈ s, ENNReal.ofReal (f (μ.rnDeriv ν x).toReal)
        = ENNReal.ofReal (f 0) := by
      intro x hx
      simp [hs_zero x hx]
    rw [setLIntegral_congr_fun hs (ae_of_all _ this)]
    simp
  rw [h1, h2, ← h3]
  conv_rhs => rw [← lintegral_add_compl _ hs (μ := ν), add_comm]
  congr 1
  rw [h3, ENNReal.add_sub_cancel_left]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top h

lemma lintegral_ofReal [SigmaFinite μ] [IsFiniteMeasure ν] (hμν : μ ≪ ν) :
    ∫⁻ x, DivFunction.ofReal f hf hf_one hf_ld hf_rd (μ.rnDeriv ν x) ∂ν
      = ∫⁻ x, ENNReal.ofReal (f (μ.rnDeriv ν x).toReal) ∂ν
        - ENNReal.ofReal (f 0) * ν {x | μ.rnDeriv ν x = 0}
        + Function.rightLim (fun x ↦ ENNReal.ofReal (f x)) 0 * ν {x | μ.rnDeriv ν x = 0} :=
  DivFunction.lintegral_ofReal' hμν (measure_ne_top _ _)

lemma lintegral_ofReal_of_continuous [SigmaFinite μ] [SigmaFinite ν]
    (hf_cont : ContinuousWithinAt f (Ioi 0) 0) :
    ∫⁻ x, DivFunction.ofReal f hf hf_one hf_ld hf_rd (μ.rnDeriv ν x) ∂ν
      = ∫⁻ x, ENNReal.ofReal (f (μ.rnDeriv ν x).toReal) ∂ν := by
  let s := {x | μ.rnDeriv ν x = 0}
  have hs : MeasurableSet s := μ.measurable_rnDeriv ν (measurableSet_singleton 0)
  rw [← lintegral_add_compl _ hs, ← lintegral_add_compl _ hs (μ := ν)]
  have hs_zero : ∀ x ∈ s, μ.rnDeriv ν x = 0 := fun _ hx ↦ hx
  have h1 : ∫⁻ x in s, ofReal f hf hf_one hf_ld hf_rd (μ.rnDeriv ν x) ∂ν
      = ENNReal.ofReal (f 0) * ν {x | μ.rnDeriv ν x = 0} := by
    have : ∀ x ∈ s, ofReal f hf hf_one hf_ld hf_rd (μ.rnDeriv ν x) = ENNReal.ofReal (f 0) := by
      intro x hx
      rw [hs_zero x hx, ofReal_apply_zero_of_continuousWithinAt hf_cont]
    rw [setLIntegral_congr_fun hs (ae_of_all _ this)]
    simp
  have h2 : ∫⁻ x in sᶜ, ofReal f hf hf_one hf_ld hf_rd (μ.rnDeriv ν x) ∂ν
      = ∫⁻ x in sᶜ, ENNReal.ofReal (f (μ.rnDeriv ν x).toReal) ∂ν := by
    have h_ne_top := μ.rnDeriv_ne_top ν
    sorry
  have h3 : ∫⁻ x in s, ENNReal.ofReal (f (μ.rnDeriv ν x).toReal) ∂ν
      = ENNReal.ofReal (f 0) * ν {x | μ.rnDeriv ν x = 0} := by
    have : ∀ x ∈ s, ENNReal.ofReal (f (μ.rnDeriv ν x).toReal) = ENNReal.ofReal (f 0) := by
      intro x hx
      simp [hs_zero x hx]
    rw [setLIntegral_congr_fun hs (ae_of_all _ this)]
    simp
  rw [h1, h2, h3]

lemma lintegral_ofReal_eq_integral_of_continuous [SigmaFinite μ] [SigmaFinite ν]
    (hf_cont : ContinuousWithinAt f (Ioi 0) 0)
    (h_int : Integrable (fun x ↦ f (μ.rnDeriv ν x).toReal) ν) :
    ∫⁻ x, DivFunction.ofReal f hf hf_one hf_ld hf_rd (μ.rnDeriv ν x) ∂ν
      = ENNReal.ofReal (∫ x, f (μ.rnDeriv ν x).toReal ∂ν) := by
  rw [DivFunction.lintegral_ofReal_of_continuous hf_cont,
    ofReal_integral_eq_lintegral_ofReal h_int]
  refine ae_of_all _ fun x ↦ ?_
  suffices ∀ x, 0 ≤ x → 0 ≤ f x from this _ ENNReal.toReal_nonneg
  exact fun _ ↦ hf.nonneg_of_todo' hf_one hf_ld hf_rd

end Integral

end OfReal

section OfConvexOn

lemma _root_.ConvexOn.sub_one (hf : ConvexOn ℝ (Ioi 0) f) :
    ConvexOn ℝ (Ioi 0) fun x ↦ f x - f 1 - rightDeriv f 1 * (x - 1) := by
  have h_eq x : f x - f 1 - rightDeriv f 1 * (x - 1)
      = f x + (- rightDeriv f 1) * x + (- f 1 + rightDeriv f 1) := by ring
  simp_rw [h_eq, add_assoc]
  refine hf.add ?_
  refine ConvexOn.add ?_ (convexOn_const _ (convex_Ioi _))
  exact (ConvexOn.const_mul_id _).subset (subset_univ _) (convex_Ioi _)

lemma rightDeriv_sub_one (hf : DifferentiableWithinAt ℝ f (Ioi 1) 1) :
    rightDeriv (fun x ↦ f x - f 1 - rightDeriv f 1 * (x - 1)) 1 = 0 := by
  have h_eq x : f x - f 1 - rightDeriv f 1 * (x - 1)
      = f x + (- rightDeriv f 1) * x + (- f 1 + rightDeriv f 1) := by ring
  simp_rw [h_eq]
  rw [rightDeriv_add_const_apply, rightDeriv_add_linear_apply hf]
  · ring
  · exact hf.add ((differentiableWithinAt_const _).mul differentiableWithinAt_id)

lemma _root_.ConvexOn.rightDeriv_sub_one (hf : ConvexOn ℝ (Ioi 0) f) :
    rightDeriv (fun x ↦ f x - f 1 - rightDeriv f 1 * (x - 1)) 1 = 0 :=
  DivFunction.rightDeriv_sub_one (hf.differentiableWithinAt_Ioi_of_mem_interior (by simp))

-- todo: give a default value 0 when f is not convex?
/-- Build a `DivFunction` from a function `f : ℝ → ℝ` which is convex on `Ioi 0`. -/
noncomputable
def ofConvexOn (f : ℝ → ℝ) (hf : ConvexOn ℝ (Ioi 0) f) : DivFunction :=
  ofReal (fun x ↦ f x - f 1 - rightDeriv f 1 * (x - 1)) hf.sub_one (by simp)
    (by
      refine (hf.sub_one.leftDeriv_le_rightDeriv_of_mem_interior ?_).trans hf.rightDeriv_sub_one.le
      simp only [interior_Ioi, mem_Ioi, zero_lt_one])
    hf.rightDeriv_sub_one.symm.le

section OfConvexOnApply

variable {hf : ConvexOn ℝ (Ioi 0) f}

@[simp]
lemma ofConvexOn_apply_zero :
    ofConvexOn f hf 0
      = Function.rightLim (fun x ↦ ENNReal.ofReal (f x - f 1 - rightDeriv f 1 * (x - 1))) 0 := by
  simp [ofConvexOn]

lemma ofConvexOn_apply_zero_of_continuousWithinAt (hf_cont : ContinuousWithinAt f (Ioi 0) 0) :
    ofConvexOn f hf 0 = ENNReal.ofReal (f 0 - f 1 + rightDeriv f 1) := by
  rw [ofConvexOn, ofReal_apply_zero_of_continuousWithinAt]
  · simp
  · simp_rw [← sub_add_eq_sub_sub]
    refine hf_cont.sub ?_
    sorry

@[simp]
lemma ofConvexOn_apply_top :
    ofConvexOn f hf ∞
      = limsup (fun x ↦ ENNReal.ofReal (f x - f 1 - rightDeriv f 1 * (x - 1))) atTop := by
  simp [ofConvexOn]

lemma ofConvexOn_apply {x : ℝ≥0∞} (hx_zero : x ≠ 0) (hx_top : x ≠ ∞) :
    ofConvexOn f hf x = ENNReal.ofReal (f x.toReal - f 1 - rightDeriv f 1 * (x.toReal - 1)) := by
  simp [ofConvexOn, ofReal_apply, hx_zero, hx_top]

end OfConvexOnApply

end OfConvexOn

variable {f g : DivFunction}

section DerivAtTop

lemma derivAtTop_ofConvexOn {f : ℝ → ℝ} {hf : ConvexOn ℝ (Ioi 0) f} :
    (ofConvexOn f hf).derivAtTop
      = limsup (fun x ↦ ENNReal.ofReal (rightDeriv f x - rightDeriv f 1)) atTop := by
  rw [ofConvexOn, derivAtTop_ofReal]
  sorry

lemma derivAtTop_ofConvexOn_of_tendsto_atTop {f : ℝ → ℝ} {hf : ConvexOn ℝ (Ioi 0) f}
    (h : Tendsto (rightDeriv f) atTop atTop) :
    (ofConvexOn f hf).derivAtTop = ∞ := by
  rw [ofConvexOn, derivAtTop_ofReal_of_tendsto_atTop]
  sorry

end DerivAtTop

end DivFunction

variable {f : DivFunction}

end ProbabilityTheory
