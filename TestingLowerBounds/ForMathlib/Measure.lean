import Mathlib.MeasureTheory.Measure.Sub

namespace MeasureTheory

variable {α β : Type*} {m mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μ ν : Measure α}

lemma measure_univ_le_add_compl (s : Set α) : μ Set.univ ≤ μ s + μ sᶜ := by
  rw [← Set.union_compl_self s]
  exact measure_union_le s sᶜ

-- PR this, just after `Measure.sub_add_cancel_of_le`
lemma Measure.add_sub_cancel [IsFiniteMeasure ν] : μ + ν - ν = μ := by
  ext1 s hs
  rw [sub_apply hs (Measure.le_add_left (le_refl _)), add_apply,
    ENNReal.add_sub_cancel_right (measure_ne_top ν s)]

end MeasureTheory
