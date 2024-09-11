import Mathlib.MeasureTheory.Integral.Bochner

open Filter

namespace MeasureTheory

--PRed, see #15459
lemma Integrable.of_isEmpty {α β : Type*} [MeasurableSpace α] [NormedAddCommGroup β]
    [IsEmpty α] (f : α → β) (μ : Measure α) : Integrable f μ := Integrable.of_finite μ f

--PRed, see #15459
@[simp]
lemma integral_of_isEmpty {α β : Type*} [MeasurableSpace α] [NormedAddCommGroup β]
    [NormedSpace ℝ β] [IsEmpty α] (f : α → β) (μ : Measure α) : ∫ x, f x ∂μ = 0 :=
  integral_eq_zero_of_ae <| .of_forall (IsEmpty.forall_iff.mpr True.intro)

end MeasureTheory
