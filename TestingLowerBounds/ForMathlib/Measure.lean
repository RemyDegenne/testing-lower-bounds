import Mathlib.MeasureTheory.Measure.Trim

namespace MeasureTheory

variable {α β : Type*} {m mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μ ν : Measure α}

lemma Measure.AbsolutelyContinuous.add_left {μ₁ μ₂ ν : Measure α}
    (h₁ : μ₁ ≪ ν) (h₂ : μ₂ ≪ ν) :
    μ₁ + μ₂ ≪ ν := Measure.AbsolutelyContinuous.add_left_iff.mpr ⟨h₁, h₂⟩

lemma Measure.trim_add (μ ν : Measure α) (hm : m ≤ mα) :
    (μ + ν).trim hm = μ.trim hm + ν.trim hm := by
  refine @Measure.ext _ m _ _ (fun s hs ↦ ?_)
  simp only [Measure.add_toOuterMeasure, OuterMeasure.coe_add, Pi.add_apply,
    trim_measurableSet_eq hm hs]

end MeasureTheory
