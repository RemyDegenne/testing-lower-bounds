import Mathlib.MeasureTheory.Decomposition.RadonNikodym

namespace MeasureTheory
open scoped ENNReal

variable {α E : Type*} [MeasurableSpace α] {μ ν : Measure α} [NormedAddCommGroup E] [NormedSpace ℝ E]

-- PR this, just after `integral_rnDeriv_smul`
lemma setIntegral_rnDeriv_smul [Measure.HaveLebesgueDecomposition μ ν] (hμν : μ ≪ ν)
    [SigmaFinite μ] {f : α → E} {s : Set α} (hs : MeasurableSet s) :
    ∫ x in s, (μ.rnDeriv ν x).toReal • f x ∂ν = ∫ x in s, f x ∂μ := by
  simp_rw [← integral_indicator hs, Set.indicator_smul, integral_rnDeriv_smul hμν]

-- PR this, just after `integral_zero_measure`
@[simp]
theorem setIntegral_zero_measure
    (f : α → E) {μ : Measure α} {s : Set α} (hs : μ s = 0) :
    ∫ x in s, f x ∂μ = 0 := Measure.restrict_eq_zero.mpr hs ▸ integral_zero_measure f

--PR these two lemmas to mathlib, just under `lintegral_eq_zero_iff`
theorem setLIntegral_eq_zero_iff' {s : Set α} (hs : MeasurableSet s)
    {f : α → ℝ≥0∞} (hf : AEMeasurable f (μ.restrict s)) :
    ∫⁻ a in s, f a ∂μ = 0 ↔ ∀ᵐ x ∂μ, x ∈ s → f x = 0 :=
  (lintegral_eq_zero_iff' hf).trans (ae_restrict_iff' hs)

theorem setLIntegral_eq_zero_iff {s : Set α} (hs : MeasurableSet s) {f : α → ℝ≥0∞}
    (hf : Measurable f) : ∫⁻ a in s, f a ∂μ = 0 ↔ ∀ᵐ x ∂μ, x ∈ s → f x = 0 :=
  setLIntegral_eq_zero_iff' hs hf.aemeasurable

end MeasureTheory
