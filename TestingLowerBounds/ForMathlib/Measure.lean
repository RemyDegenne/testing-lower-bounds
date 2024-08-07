import Mathlib.MeasureTheory.Measure.Sub

namespace MeasureTheory

variable {α β : Type*} {m mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μ ν : Measure α}

--PRed, see #15467
lemma measure_univ_le_add_compl (s : Set α) : μ Set.univ ≤ μ s + μ sᶜ :=
  s.union_compl_self ▸ measure_union_le s sᶜ

--PRed, see  #15468
lemma Measure.add_sub_cancel [IsFiniteMeasure ν] : μ + ν - ν = μ := by
  ext1 s hs
  rw [sub_apply hs (Measure.le_add_left (le_refl _)), add_apply,
    ENNReal.add_sub_cancel_right (measure_ne_top ν s)]

end MeasureTheory
