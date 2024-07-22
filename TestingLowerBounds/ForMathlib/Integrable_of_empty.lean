import Mathlib.MeasureTheory.Integral.Bochner

open Filter

--TODO: put this in mathlib, maybe just after:
-- #check Integrable.of_finite

namespace MeasureTheory

lemma Integrable.of_isEmpty {α β : Type*} [MeasurableSpace α] [NormedAddCommGroup β]
    [IsEmpty α] (f : α → β) (μ : Measure α) : Integrable f μ := Integrable.of_finite μ f

@[simp]
lemma Integrable.of_isEmpty_codomain {α β : Type*} [MeasurableSpace α] [NormedAddCommGroup β]
    [IsEmpty β] (f : α → β) (μ : Measure α) : Integrable f μ :=
  have : IsEmpty α := f.isEmpty
  Integrable.of_isEmpty f μ

--TODO: put this in mathlib, maybe just after:
-- #check integral_eq_zero_of_ae

@[simp]
lemma integral_of_isEmpty {α β : Type*} [MeasurableSpace α] [NormedAddCommGroup β]
    [NormedSpace ℝ β] [IsEmpty α] (f : α → β) (μ : Measure α) : ∫ x, f x ∂μ = 0 :=
  integral_eq_zero_of_ae <| eventually_of_forall (IsEmpty.forall_iff.mpr True.intro)

end MeasureTheory
