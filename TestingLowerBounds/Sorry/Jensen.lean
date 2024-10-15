/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.MeasureTheory.Decomposition.Lebesgue
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

/-!

# Jensen's inequality for the conditional expectation

-/

open MeasureTheory Set

namespace ProbabilityTheory

variable {α β : Type*} {m mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {μ ν : Measure α} {f g : ℝ → ℝ}

/-- A specialized version of **Jensen's inequality** for the conditional expectation. -/
lemma _root_.ConvexOn.apply_condexp_le (hm : m ≤ mα)
    (hf : StronglyMeasurable f)
    (hf_cvx : ConvexOn ℝ (Ici 0) f) (hf_cont : ContinuousOn f (Ici 0))
    {g : α → ℝ} (hg : Measurable g) (hg_pos : 0 ≤ g)
    (h_int1 : Integrable g ν) (h_int2 : Integrable (fun x ↦ f (g x)) ν) :
    (fun x ↦ f ((ν[g | m]) x)) ≤ᵐ[ν.trim hm] ν[fun x ↦ f (g x) | m] := by
  sorry

lemma f_condexp_rnDeriv_le [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hm : m ≤ mα)
    (hf : StronglyMeasurable f)
    (hf_cvx : ConvexOn ℝ (Ici 0) f) (hf_cont : ContinuousOn f (Ici 0))
    (h_int : Integrable (fun x ↦ f (μ.rnDeriv ν x).toReal) ν) :
    (fun x ↦ f ((ν[fun x ↦ (μ.rnDeriv ν x).toReal | m]) x))
      ≤ᵐ[ν.trim hm] ν[fun x ↦ f (μ.rnDeriv ν x).toReal | m] :=
  hf_cvx.apply_condexp_le hm hf hf_cont (μ.measurable_rnDeriv ν).ennreal_toReal
    (fun _ ↦ ENNReal.toReal_nonneg) Measure.integrable_toReal_rnDeriv h_int

end ProbabilityTheory
