import Mathlib.MeasureTheory.Constructions.Prod.Basic

namespace MeasureTheory.Measure

variable {α β : Type*} {m0 : MeasurableSpace α} {m1 : MeasurableSpace β}
  {μ : Measure α} {ρ : Measure (α × β)}

--TODO: remove. Already exists in Mathlib.MeasureTheory.Measure.AEMeasurable
instance [SFinite μ] (f : α → β) : SFinite (μ.map f) := by
  by_cases hf : AEMeasurable f μ
  · rw [← sum_sFiniteSeq μ, map_sum]
    · infer_instance
    · rwa [sum_sFiniteSeq]
  · rw [map_of_not_aemeasurable hf]
    infer_instance

--this should go in `Mathlib.MeasureTheory.Constructions.Prod.Basic`, just before `fst.instIsFiniteMeasure`
instance [SFinite ρ] : SFinite ρ.fst := by
  rw [fst]
  infer_instance

--this should go in `Mathlib.MeasureTheory.Constructions.Prod.Basic`, just before `snd.instIsFiniteMeasure`
instance [SFinite ρ] : SFinite ρ.snd := by
  rw [snd]
  infer_instance

end MeasureTheory.Measure
