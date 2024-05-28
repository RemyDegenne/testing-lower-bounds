import Mathlib.MeasureTheory.Integral.Bochner

open MeasureTheory

open Real MeasureTheory Filter MeasurableSpace
open scoped ENNReal NNReal Topology BigOperators

--TODO: put this in mathlib, maybe just after:
#check Integrable.of_finite

@[simp]
lemma Integrable.of_empty {α β : Type*} [MeasurableSpace α] [NormedAddCommGroup β] [IsEmpty α]
    (f : α → β) (μ : Measure α) : Integrable f μ := Integrable.of_finite μ f

@[simp]
lemma Integrable.of_empty_codomain {α β : Type*} [MeasurableSpace α] [NormedAddCommGroup β] [IsEmpty β]
    {f : α → β} {μ : Measure α} : Integrable f μ := by
  have : IsEmpty α := f.isEmpty
  exact Integrable.of_empty f μ

--TODO: put this in mathlib, maybe just after:
#check integral_eq_zero_of_ae

@[simp]
lemma MeasureTheory.integral_of_empty {α β : Type*} [MeasurableSpace α] [NormedAddCommGroup β]
    [NormedSpace ℝ β] [IsEmpty α] (f : α → β) (μ : Measure α) : (∫ x, f x ∂μ) = 0 :=
  integral_eq_zero_of_ae <| eventually_of_forall (IsEmpty.forall_iff.mpr True.intro)
