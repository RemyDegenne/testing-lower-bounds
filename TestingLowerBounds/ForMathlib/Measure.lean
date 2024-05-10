import Mathlib.MeasureTheory.Measure.Trim
import Mathlib.MeasureTheory.Constructions.Prod.Basic

namespace MeasureTheory

variable {α β : Type*} {m mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μ ν : Measure α}

lemma measure_univ_le_add_compl (s : Set α) : μ Set.univ ≤ μ s + μ sᶜ := by
  rw [← Set.union_compl_self s]
  exact measure_union_le s sᶜ

@[simp]
lemma Measure.fst_map_swap (μ : Measure (α × β)) : (μ.map Prod.swap).fst = μ.snd := by
  ext s hs
  rw [Measure.fst, Measure.map_map measurable_fst measurable_swap, Measure.snd_apply hs,
    Measure.map_apply (measurable_fst.comp measurable_swap) hs]
  congr

@[simp]
lemma Measure.snd_map_swap (μ : Measure (α × β)) : (μ.map Prod.swap).snd = μ.fst := by
  ext s hs
  rw [Measure.snd, Measure.map_map measurable_snd measurable_swap, Measure.fst_apply hs,
    Measure.map_apply (measurable_snd.comp measurable_swap) hs]
  congr

lemma Measure.AbsolutelyContinuous.add_left {μ₁ μ₂ ν : Measure α} (h₁ : μ₁ ≪ ν) (h₂ : μ₂ ≪ ν) :
    μ₁ + μ₂ ≪ ν := Measure.AbsolutelyContinuous.add_left_iff.mpr ⟨h₁, h₂⟩

lemma Measure.trim_add (μ ν : Measure α) (hm : m ≤ mα) :
    (μ + ν).trim hm = μ.trim hm + ν.trim hm := by
  refine @Measure.ext _ m _ _ (fun s hs ↦ ?_)
  simp only [Measure.coe_add, Pi.add_apply, trim_measurableSet_eq hm hs]

end MeasureTheory
