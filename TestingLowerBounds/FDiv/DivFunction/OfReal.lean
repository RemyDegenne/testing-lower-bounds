/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import TestingLowerBounds.FDiv.DivFunction.DerivAtTop

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
    (hf_one : f 1 = 0) : DivFunction where
  toFun x :=
    -- give values at 0 and ∞ to ensure continuity
    if x = 0 then Function.rightLim (fun x ↦ ENNReal.ofReal (f x)) 0
    else if x = ∞ then limsup (fun x ↦ ENNReal.ofReal (f x)) atTop
    else ENNReal.ofReal (f x.toReal)
  one := by simp [hf_one]
  convexOn' := sorry
  continuous' := by
    have h_cont := hf.continuousOn isOpen_Ioi
    refine continuous_iff_continuousAt.mpr fun x ↦ ?_
    by_cases hx0 : x = 0
    · sorry
    by_cases hx_top : x = ∞
    · sorry
    sorry

variable {hf : ConvexOn ℝ (Ioi 0) f} {hf_one : f 1 = 0}

section OfRealApply

@[simp]
lemma ofReal_apply_zero :
    ofReal f hf hf_one 0 = Function.rightLim (fun x ↦ ENNReal.ofReal (f x)) 0 := by
  simp [ofReal]

lemma ofReal_apply_zero_of_continuousWithinAt (hf_cont : ContinuousWithinAt f (Ioi 0) 0) :
    ofReal f hf hf_one 0 = ENNReal.ofReal (f 0) := by
  simp only [ofReal_apply_zero]
  refine rightLim_eq_of_tendsto NeBot.ne' ?_
  refine ContinuousWithinAt.tendsto ?_
  exact (ENNReal.continuous_ofReal.tendsto _).comp hf_cont.tendsto

@[simp]
lemma ofReal_apply_top :
    ofReal f hf hf_one ∞ = limsup (fun x ↦ ENNReal.ofReal (f x)) atTop := by
  simp [ofReal]

lemma ofReal_apply_top_of_tendsto_atTop (h : Tendsto f atTop atTop) :
    ofReal f hf hf_one ∞ = ∞ := by
  rw [ofReal_apply_top]
  refine Tendsto.limsup_eq ?_
  rwa [ENNReal.tendsto_ofReal_nhds_top]

lemma ofReal_apply {x : ℝ≥0∞} (hx_zero : x ≠ 0) (hx_top : x ≠ ∞) :
    ofReal f hf hf_one x = ENNReal.ofReal (f x.toReal) := by
  simp [ofReal, hx_zero, hx_top]

lemma ofReal_apply_of_continuousWithinAt (hf_cont : ContinuousWithinAt f (Ioi 0) 0)
    {x : ℝ≥0∞} (hx : x ≠ ∞) :
    ofReal f hf hf_one x = ENNReal.ofReal (f x.toReal) := by
  by_cases hx0 : x = 0
  · simp [hx0, ofReal_apply_zero_of_continuousWithinAt hf_cont]
  · exact ofReal_apply hx0 hx

lemma realFun_ofReal_apply (hf_nonneg : ∀ x, 0 ≤ x → 0 ≤ f x)
    {x : ℝ} (hx : 0 < x) :
    (ofReal f hf hf_one).realFun x = f x := by
  rw [realFun, ofReal_apply, ENNReal.toReal_ofReal, ENNReal.toReal_ofReal hx.le]
  · exact hf_nonneg _ ENNReal.toReal_nonneg
  · simp [hx]
  · simp

end OfRealApply

section DerivAtTop

lemma derivAtTop_ofReal :
    (ofReal f hf hf_one).derivAtTop
      = limsup (fun x ↦ ENNReal.ofReal (rightDeriv f x)) atTop := by
  rw [derivAtTop]
  sorry

lemma derivAtTop_ofReal_ne_top
    (h_lim : limsup (fun x ↦ ENNReal.ofReal (rightDeriv f x)) atTop ≠ ∞) :
    (ofReal f hf hf_one).derivAtTop ≠ ∞ := by
  rwa [derivAtTop_ofReal]

lemma derivAtTop_ofReal_of_tendsto_atTop (h : Tendsto (rightDeriv f) atTop atTop) :
    (ofReal f hf hf_one).derivAtTop = ∞ := by
  sorry

end DerivAtTop

section Integral

lemma lintegral_ofReal_eq_top_of_not_integrable [SigmaFinite μ] [IsFiniteMeasure ν]
    (hf_nonneg : ∀ x, 0 ≤ x → 0 ≤ f x)
    (h_int : ¬ Integrable (fun x ↦ f (μ.rnDeriv ν x).toReal) ν) :
    ∫⁻ x, ofReal f hf hf_one (μ.rnDeriv ν x) ∂ν = ∞ := by
  refine lintegral_eq_top_of_not_integrable_realFun ?_
  suffices ¬ IntegrableOn
      (fun x ↦ (ofReal f hf hf_one).realFun (μ.rnDeriv ν x).toReal)
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
  rw [DivFunction.realFun_ofReal_apply hf_nonneg]
  exact ENNReal.toReal_pos hx_zero hx_top

lemma lintegral_ofReal' [SigmaFinite μ] [SigmaFinite ν] (h : ν {x | μ.rnDeriv ν x = 0} ≠ ∞) :
    ∫⁻ x, ofReal f hf hf_one (μ.rnDeriv ν x) ∂ν
      = ∫⁻ x, ENNReal.ofReal (f (μ.rnDeriv ν x).toReal) ∂ν
        - ENNReal.ofReal (f 0) * ν {x | μ.rnDeriv ν x = 0}
        + Function.rightLim (fun x ↦ ENNReal.ofReal (f x)) 0 * ν {x | μ.rnDeriv ν x = 0} := by
  let s := {x | μ.rnDeriv ν x = 0}
  have hs : MeasurableSet s := μ.measurable_rnDeriv ν (measurableSet_singleton 0)
  rw [← lintegral_add_compl _ hs]
  have hs_zero : ∀ x ∈ s, μ.rnDeriv ν x = 0 := fun _ hx ↦ hx
  have h1 : ∫⁻ x in s, ofReal f hf hf_one (μ.rnDeriv ν x) ∂ν
      = Function.rightLim (fun x ↦ ENNReal.ofReal (f x)) 0 * ν {x | μ.rnDeriv ν x = 0} := by
    have : ∀ x ∈ s, ofReal f hf hf_one (μ.rnDeriv ν x)
        = Function.rightLim (fun x ↦ ENNReal.ofReal (f x)) 0 := by
      intro x hx
      simp [hs_zero x hx]
    rw [setLIntegral_congr_fun hs (ae_of_all _ this)]
    simp
  have h2 : ∫⁻ x in sᶜ, ofReal f hf hf_one (μ.rnDeriv ν x) ∂ν
      = ∫⁻ x in sᶜ, ENNReal.ofReal (f (μ.rnDeriv ν x).toReal) ∂ν := by
    refine setLIntegral_congr_fun hs.compl ?_
    filter_upwards [μ.rnDeriv_ne_top ν] with x hx_top hx
    rw [ofReal_apply hx hx_top]
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

lemma lintegral_ofReal [SigmaFinite μ] [IsFiniteMeasure ν] :
    ∫⁻ x, DivFunction.ofReal f hf hf_one (μ.rnDeriv ν x) ∂ν
      = ∫⁻ x, ENNReal.ofReal (f (μ.rnDeriv ν x).toReal) ∂ν
        - ENNReal.ofReal (f 0) * ν {x | μ.rnDeriv ν x = 0}
        + Function.rightLim (fun x ↦ ENNReal.ofReal (f x)) 0 * ν {x | μ.rnDeriv ν x = 0} :=
  DivFunction.lintegral_ofReal' (measure_ne_top _ _)

lemma lintegral_ofReal_of_continuous [SigmaFinite μ] [SigmaFinite ν]
    (hf_cont : ContinuousWithinAt f (Ioi 0) 0) :
    ∫⁻ x, DivFunction.ofReal f hf hf_one (μ.rnDeriv ν x) ∂ν
      = ∫⁻ x, ENNReal.ofReal (f (μ.rnDeriv ν x).toReal) ∂ν := by
  let s := {x | μ.rnDeriv ν x = 0}
  have hs : MeasurableSet s := μ.measurable_rnDeriv ν (measurableSet_singleton 0)
  rw [← lintegral_add_compl _ hs, ← lintegral_add_compl _ hs (μ := ν)]
  have hs_zero : ∀ x ∈ s, μ.rnDeriv ν x = 0 := fun _ hx ↦ hx
  have h1 : ∫⁻ x in s, ofReal f hf hf_one (μ.rnDeriv ν x) ∂ν
      = ENNReal.ofReal (f 0) * ν {x | μ.rnDeriv ν x = 0} := by
    have : ∀ x ∈ s, ofReal f hf hf_one (μ.rnDeriv ν x) = ENNReal.ofReal (f 0) := by
      intro x hx
      rw [hs_zero x hx, ofReal_apply_zero_of_continuousWithinAt hf_cont]
    rw [setLIntegral_congr_fun hs (ae_of_all _ this)]
    simp
  have h2 : ∫⁻ x in sᶜ, ofReal f hf hf_one (μ.rnDeriv ν x) ∂ν
      = ∫⁻ x in sᶜ, ENNReal.ofReal (f (μ.rnDeriv ν x).toReal) ∂ν := by
    refine setLIntegral_congr_fun hs.compl ?_
    filter_upwards [μ.rnDeriv_ne_top ν] with x hx_top hx
    rw [ofReal_apply hx hx_top]
  have h3 : ∫⁻ x in s, ENNReal.ofReal (f (μ.rnDeriv ν x).toReal) ∂ν
      = ENNReal.ofReal (f 0) * ν {x | μ.rnDeriv ν x = 0} := by
    have : ∀ x ∈ s, ENNReal.ofReal (f (μ.rnDeriv ν x).toReal) = ENNReal.ofReal (f 0) := by
      intro x hx
      simp [hs_zero x hx]
    rw [setLIntegral_congr_fun hs (ae_of_all _ this)]
    simp
  rw [h1, h2, h3]

lemma lintegral_ofReal_eq_integral_of_continuous [SigmaFinite μ] [SigmaFinite ν]
    (hf_nonneg : ∀ x, 0 ≤ x → 0 ≤ f x)
    (hf_cont : ContinuousWithinAt f (Ioi 0) 0)
    (h_int : Integrable (fun x ↦ f (μ.rnDeriv ν x).toReal) ν) :
    ∫⁻ x, DivFunction.ofReal f hf hf_one (μ.rnDeriv ν x) ∂ν
      = ENNReal.ofReal (∫ x, f (μ.rnDeriv ν x).toReal ∂ν) := by
  rw [DivFunction.lintegral_ofReal_of_continuous hf_cont,
    ofReal_integral_eq_lintegral_ofReal h_int]
  refine ae_of_all _ fun x ↦ hf_nonneg _ ENNReal.toReal_nonneg

lemma measurable_comp_rnDeriv_of_convexOn_of_continuous [SigmaFinite μ] [SigmaFinite ν]
    {f : ℝ → ℝ} (hf : ConvexOn ℝ (Ioi 0) f) (h_cont : ContinuousWithinAt f (Ioi 0) 0) :
    Measurable (fun x ↦ f (μ.rnDeriv ν x).toReal) := by
  have : (fun x ↦ f (μ.rnDeriv ν x).toReal)
      = (fun x : Ici (0 : ℝ) ↦ f x)
        ∘ (fun x ↦ ⟨(μ.rnDeriv ν x).toReal, ENNReal.toReal_nonneg⟩) := rfl
  rw [this]
  have h1 : Measurable (fun x : Ici (0 : ℝ) ↦ f x) := by
    refine Continuous.measurable ?_
    change Continuous ((Ici 0).restrict f)
    rw [← continuousOn_iff_continuous_restrict]
    have h_Ioi : ContinuousOn f (Ioi 0) := hf.continuousOn isOpen_Ioi
    rw [ContinuousOn]
    intro x hx
    by_cases h0 : x = 0
    · rw [h0, ← continuousWithinAt_Ioi_iff_Ici]
      exact h_cont
    · have h := h_Ioi.continuousWithinAt (lt_of_le_of_ne hx (Ne.symm h0))
      refine (h.continuousAt ?_).continuousWithinAt
      exact Ioi_mem_nhds (lt_of_le_of_ne hx (Ne.symm h0))
  exact h1.comp (μ.measurable_rnDeriv ν).ennreal_toReal.subtype_mk

lemma lintegral_ofReal_ne_top_iff_integrable_of_continuous [SigmaFinite μ] [IsFiniteMeasure ν]
    (hf_nonneg : ∀ x, 0 ≤ x → 0 ≤ f x)
    (h_cont : ContinuousWithinAt f (Ioi 0) 0) :
    ∫⁻ x, ofReal f hf hf_one (μ.rnDeriv ν x) ∂ν ≠ ∞
      ↔ Integrable (fun x ↦ f (μ.rnDeriv ν x).toReal) ν := by
  rw [lintegral_ofReal_of_continuous h_cont, lintegral_ofReal_ne_top_iff_integrable_of_nonneg]
  · refine Measurable.aestronglyMeasurable ?_
    exact measurable_comp_rnDeriv_of_convexOn_of_continuous hf h_cont
  · exact ae_of_all _ fun x ↦ hf_nonneg _ ENNReal.toReal_nonneg

lemma lintegral_ofReal_eq_top_iff_not_integrable_of_continuous [SigmaFinite μ] [IsFiniteMeasure ν]
    (hf_nonneg : ∀ x, 0 ≤ x → 0 ≤ f x)
    (h_cont : ContinuousWithinAt f (Ioi 0) 0) :
    ∫⁻ x, ofReal f hf hf_one (μ.rnDeriv ν x) ∂ν = ∞
      ↔ ¬ Integrable (fun x ↦ f (μ.rnDeriv ν x).toReal) ν := by
  rw [← lintegral_ofReal_ne_top_iff_integrable_of_continuous hf_nonneg h_cont, not_not]

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
  have : rightDeriv (fun x ↦ f x - f 1 - rightDeriv f 1 * (x - 1))
      = fun x ↦ rightDeriv f x - rightDeriv f 1 := by
    have h_eq : (fun x ↦ f x - f 1 - rightDeriv f 1 * (x - 1))
        = fun x ↦ f x + (- rightDeriv f 1) * x + (- f 1 + rightDeriv f 1) := by ext; ring
    rw [h_eq]
    ext x
    rw [rightDeriv_add_const_apply, rightDeriv_add_linear_apply, sub_eq_add_neg]
    · sorry
    · sorry
  rw [this]
  exact tendsto_atTop_add_const_right atTop (-rightDeriv f 1) h

end DerivAtTop

end DivFunction

variable {f : DivFunction}

end ProbabilityTheory
