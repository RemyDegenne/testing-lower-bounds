/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Calculus.MeanValue

/-!

# f-Divergences

## Main definitions

* `FooBar`

## Main statements

* `fooBar_unique`

## Notation

## Implementation details

Most results will require these conditions on `f`:
`(hf_cvx : ConvexOn ℝ (Set.Ici 0) f) (hf_cont : ContinuousOn f (Set.Ici 0)) (hf_one : f 1 = 0)`

## References

* [F. Bar, *Quuxes*][bibkey]

## Tags

Foobars, barfoos
-/

open Real MeasureTheory

open scoped ENNReal

namespace ProbabilityTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ ν : Measure α} {f : ℝ → ℝ}

/-- f-Divergence of two measures, real-valued. -/
noncomputable
def fDivReal (f : ℝ → ℝ) (μ ν : Measure α) : ℝ := ∫ x, f (μ.rnDeriv ν x).toReal ∂ν

open Classical in
/-- f-Divergence of two measures, with value in `ℝ≥0∞`. Suitable for probability measures. -/
noncomputable
def fDiv (f : ℝ → ℝ) (μ ν : Measure α) : ℝ≥0∞ :=
  if Integrable (fun x ↦ f (μ.rnDeriv ν x).toReal) ν then ENNReal.ofReal (fDivReal f μ ν) else ∞

lemma le_fDivReal [IsFiniteMeasure μ] [IsProbabilityMeasure ν]
    (hf_cvx : ConvexOn ℝ (Set.Ici 0) f) (hf_cont : ContinuousOn f (Set.Ici 0))
    (hf_int : Integrable (fun x ↦ f (μ.rnDeriv ν x).toReal) ν) (hμν : μ ≪ ν) :
    f (μ Set.univ).toReal ≤ fDivReal f μ ν := by
  calc f (μ Set.univ).toReal
    = f (∫ x, (μ.rnDeriv ν x).toReal ∂ν) := by rw [Measure.integral_toReal_rnDeriv hμν]
  _ ≤ ∫ x, f (μ.rnDeriv ν x).toReal ∂ν := by
    rw [← average_eq_integral, ← average_eq_integral]
    exact ConvexOn.map_average_le hf_cvx hf_cont isClosed_Ici (by simp)
      Measure.integrable_toReal_rnDeriv hf_int
  _ = ∫ x, f (μ.rnDeriv ν x).toReal ∂ν := rfl

lemma fDivReal_nonneg [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hf_cvx : ConvexOn ℝ (Set.Ici 0) f) (hf_cont : ContinuousOn f (Set.Ici 0)) (hf_one : f 1 = 0)
    (hf_int : Integrable (fun x ↦ f (μ.rnDeriv ν x).toReal) ν) (hμν : μ ≪ ν) :
    0 ≤ fDivReal f μ ν :=
  calc 0 = f (μ Set.univ).toReal := by simp [hf_one]
  _ ≤ ∫ x, f (μ.rnDeriv ν x).toReal ∂ν := le_fDivReal hf_cvx hf_cont hf_int hμν

lemma fDivReal_self (hf_one : f 1 = 0) (μ : Measure α) [SigmaFinite μ] : fDivReal f μ μ = 0 := by
  have h : (fun x ↦ f (μ.rnDeriv μ x).toReal) =ᵐ[μ] 0 := by
    filter_upwards [Measure.rnDeriv_self μ] with x hx
    rw [hx, ENNReal.one_toReal, hf_one]
    rfl
  rw [fDivReal, integral_congr_ae h]
  simp

end ProbabilityTheory
