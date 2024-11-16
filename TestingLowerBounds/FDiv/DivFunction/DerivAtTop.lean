/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
import TestingLowerBounds.FDiv.DivFunction.RightDeriv

/-!

# f-Divergences functions

-/

open Real MeasureTheory Filter Set MeasurableSpace

open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μ ν : Measure α}

namespace DivFunction

variable {f g : DivFunction}

noncomputable
def derivAtTop (f : DivFunction) : ℝ≥0∞ := (limsup f.rightDerivStieltjes atTop).toENNReal

lemma limsup_rightDerivStieltjes_atTop_nonneg :
    0 ≤ limsup f.rightDerivStieltjes atTop := by
  sorry

lemma tendsto_rightDerivStieltjes_atTop :
    Tendsto f.rightDerivStieltjes atTop (𝓝 f.derivAtTop) := by
  rw [derivAtTop, EReal.coe_toENNReal limsup_rightDerivStieltjes_atTop_nonneg]
  sorry

@[simp]
lemma derivAtTop_zero : derivAtTop (0 : DivFunction) = 0 := by
  simp only [derivAtTop, rightDerivStieltjes_zero]
  rw [EReal.toENNReal_eq_zero_iff]
  have : (fun x ↦ if x < (0 : ℝ) then (⊥ : EReal) else 0) =ᶠ[atTop] fun _ ↦ 0 := by
    filter_upwards [eventually_ge_atTop 0] with x hx
    rw [if_neg (not_lt.mpr hx)]
  rw [limsup_congr this]
  simp

lemma derivAtTop_congr (h : f =ᶠ[atTop] g) : f.derivAtTop = g.derivAtTop := by
  rw [derivAtTop, derivAtTop]
  congr 1
  refine limsup_congr ?_
  sorry
  -- refine ENNReal.eventuallyEq_of_toReal_eventuallyEq ?_ ?_ ?_
  -- filter_upwards [h] with x hx
  -- rw [hx]

lemma derivAtTop_congr_nonneg (h : ∀ x, f x = g x) : f.derivAtTop = g.derivAtTop :=
  derivAtTop_congr (.of_forall h)

lemma tendsto_derivAtTop : Tendsto (fun x ↦ f x / x) atTop (𝓝 f.derivAtTop) := by
  sorry

@[simp]
lemma derivAtTop_add : (f + g).derivAtTop = f.derivAtTop + g.derivAtTop := by
  suffices Tendsto (fun x ↦ (f + g) x / x) atTop (𝓝 (f.derivAtTop + g.derivAtTop)) from
    tendsto_nhds_unique tendsto_derivAtTop this
  simp only [add_apply]
  sorry

@[simp]
lemma derivAtTop_smul {c : ℝ≥0} : (c • f).derivAtTop = c * f.derivAtTop := sorry

lemma le_add_derivAtTop {x y : ℝ≥0∞} (hyx : y ≤ x) :
    f x ≤ f y + f.derivAtTop * (x - y) := by
  sorry

lemma le_add_derivAtTop'' (x y : ℝ≥0∞) :
    f (x + y) ≤ f x + f.derivAtTop * y := by
  sorry

lemma le_add_derivAtTop' (x : ℝ≥0∞) {u : ℝ≥0∞} (hu' : u ≤ 1) :
    f x ≤ f (x * u) + f.derivAtTop * x * (1 - u) := by
  have : x = x * u + x * (1 - u) := by
    rw [← mul_add]
    rw [add_tsub_cancel_of_le hu', mul_one]
  conv_lhs => rw [this]
  refine (le_add_derivAtTop'' (x * u) (x * (1 - u))).trans ?_
  rw [mul_assoc]

lemma lintegral_comp_rnDeriv_ne_top (μ ν : Measure α) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (hf_zero : f 0 ≠ ∞) (hf_deriv : f.derivAtTop ≠ ∞) :
    ∫⁻ x, f (μ.rnDeriv ν x) ∂ν ≠ ∞ := by
  sorry
  -- obtain ⟨c, c', h⟩ : ∃ c c', ∀ x, _ → c * x + c' ≤ (f x).toReal :=
  --   f.convexOn_toReal.exists_affine_le (convex_Ici 0)
  -- refine integrable_of_le_of_le (f := fun x ↦ f (μ.rnDeriv ν x).toReal)
  --   (g₁ := fun x ↦ c * (μ.rnDeriv ν x).toReal + c')
  --   (g₂ := fun x ↦ (derivAtTop f).toReal * (μ.rnDeriv ν x).toReal + f 0)
  --   ?_ ?_ ?_ ?_ ?_
  -- · exact (hf.comp_measurable (μ.measurable_rnDeriv ν).ennreal_toReal).aestronglyMeasurable
  -- · exact ae_of_all _ (fun x ↦ h _ ENNReal.toReal_nonneg)
  -- · refine ae_of_all _ (fun x ↦ ?_)
  --   have h := le_add_derivAtTop'' hf_cvx hf_deriv le_rfl
  --     (ENNReal.toReal_nonneg : 0 ≤ (μ.rnDeriv ν x).toReal)
  --   rwa [zero_add, add_comm] at h
  -- · refine (Integrable.const_mul ?_ _).add (integrable_const _)
  --   exact Measure.integrable_toReal_rnDeriv
  -- · refine (Integrable.const_mul ?_ _).add (integrable_const _)
  --   exact Measure.integrable_toReal_rnDeriv

end DivFunction

variable {f : DivFunction}

end ProbabilityTheory
