import Mathlib.MeasureTheory.Measure.Typeclasses
import Mathlib.MeasureTheory.Measure.AEMeasurable

import Mathlib.MeasureTheory.Constructions.Prod.Basic

namespace MeasureTheory.Measure

-- open Measure

variable {α β δ ι : Type*}
variable {m0 : MeasurableSpace α} [MeasurableSpace β] {μ ν ν₁ ν₂: Measure α}
  {s t : Set α} {ρ : Measure (α × β)}

--TODO: put this in `Mathlib.MeasureTheory.Measure.Typeclasses`, inside the `SFinite` section
instance {m : MeasurableSpace α} (μ : Measure α) [SFinite μ] (f : α → β) : SFinite (μ.map f) := by
  by_cases hf : AEMeasurable f μ
  · rw [← sum_sFiniteSeq μ, map_sum]
    · infer_instance
    · rwa [sum_sFiniteSeq]
  · rw [map_of_not_aemeasurable hf]
    infer_instance
namespace Measure

--this should go in `Mathlib.MeasureTheory.Constructions.Prod.Basic`, just before `fst.instIsFiniteMeasure`
instance [SFinite ρ] : SFinite ρ.fst := by
  rw [fst]
  infer_instance

--this should go in `Mathlib.MeasureTheory.Constructions.Prod.Basic`, just before `snd.instIsFiniteMeasure`
instance [SFinite ρ] : SFinite ρ.snd := by
  rw [snd]
  infer_instance
