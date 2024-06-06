import Mathlib.MeasureTheory.Measure.Typeclasses
import Mathlib.MeasureTheory.Measure.AEMeasurable

import Mathlib.MeasureTheory.Constructions.Prod.Basic


namespace MeasureTheory

variable {α β δ ι : Type*}
variable {m0 : MeasurableSpace α} [MeasurableSpace β] {μ ν ν₁ ν₂: Measure α}
  {s t : Set α} {ρ : Measure (α × β)}

--it would have been nice to put this in `Mathlib.MeasureTheory.Measure.Typeclasses`, inside the `SFinite` section, but we need `AEMeasurable.mono_measure` to prove it, and this would create a circular import
@[instance]
theorem Measure.isSFiniteMeasure_map {m : MeasurableSpace α} (μ : Measure α) [SFinite μ]
    (f : α → β) : SFinite (μ.map f) := by
  by_cases hf : AEMeasurable f μ
  · constructor
    use fun n ↦ (sFiniteSeq μ n).map f
    constructor
    · intro n
      infer_instance
    · ext s hs
      rw [sum_apply (fun n ↦ map f (sFiniteSeq μ n)) hs, map_apply_of_aemeasurable hf hs]
      have (i : ℕ) : AEMeasurable f (sFiniteSeq μ i) := by
        apply AEMeasurable.mono_measure hf
        nth_rw 2 [← sum_sFiniteSeq μ]
        exact le_sum _ _
      simp_rw [map_apply_of_aemeasurable (this _) hs]
      rw [← sum_apply_of_countable (fun n ↦ sFiniteSeq μ n) _, sum_sFiniteSeq]
  · rw [map_of_not_aemeasurable hf]
    exact instSFiniteOfNatMeasure

namespace Measure

--this should go in `Mathlib.MeasureTheory.Constructions.Prod.Basic`, just before `fst.instIsFiniteMeasure`
instance [SFinite ρ] : SFinite ρ.fst := by
  rw [fst]
  infer_instance

--this should go in `Mathlib.MeasureTheory.Constructions.Prod.Basic`, just before `snd.instIsFiniteMeasure`
instance [SFinite ρ] : SFinite ρ.snd := by
  rw [snd]
  infer_instance
