import Mathlib.MeasureTheory.Measure.Trim
import Mathlib.MeasureTheory.Constructions.Prod.Basic

namespace MeasureTheory

variable {α β : Type*} {m mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μ ν : Measure α}

lemma measure_univ_le_add_compl (s : Set α) : μ Set.univ ≤ μ s + μ sᶜ := by
  rw [← Set.union_compl_self s]
  exact measure_union_le s sᶜ

end MeasureTheory
