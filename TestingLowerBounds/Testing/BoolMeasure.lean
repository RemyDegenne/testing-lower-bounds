/-
Copyright (c) 2024 Lorenzo Luccioli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lorenzo Luccioli
-/
import Mathlib.MeasureTheory.Measure.WithDensity

open MeasureTheory

open scoped ENNReal NNReal

namespace Bool

--rename this and put it in a better place
lemma cases_set_bool (s : Set Bool) :
    s = ∅ ∨ s = {true} ∨ s = {false} ∨ s = {true, false} := by
  by_cases h1 : true ∈ s <;> by_cases h2 : false ∈ s
  · refine Or.inr (Or.inr (Or.inr ?_))
    ext x
    induction x <;> simp [h1, h2]
  · refine Or.inr (Or.inl ?_)
    ext x
    induction x <;> simp [h1, h2]
  · refine Or.inr (Or.inr (Or.inl ?_))
    ext x
    induction x <;> simp [h1, h2]
  · left
    ext x
    induction x <;> simp [h1, h2]

@[ext]
lemma _root_.MeasureTheory.Measure.measure_bool_ext {π₁ π₂ : Measure Bool}
    (h_false : π₁ {false} = π₂ {false}) (h_true : π₁ {true} = π₂ {true}) : π₁ = π₂ := by
  ext s
  obtain (rfl | rfl | rfl | rfl) := Bool.cases_set_bool s
    <;> try simp only [measure_empty, h_true, h_false]
  rw [Set.insert_eq, measure_union, measure_union, h_true, h_false] <;> simp

lemma lintegral_bool {f : Bool → ℝ≥0∞} (π : Measure Bool) :
    ∫⁻ x, f x ∂π = f false * π {false} + f true * π {true} := by
  rw [← setLIntegral_univ, Bool.univ_eq, lintegral_insert (of_decide_eq_false (by exact rfl)),
    lintegral_singleton]

lemma iInf_bool {α : Type*} [CompleteLinearOrder α] (s : Bool → α) :
    ⨅ b, s b = min (s false) (s true) := by
  refine le_antisymm (le_min_iff.mpr ⟨iInf_le _ _, iInf_le _ _⟩) ?_
  simp

lemma iSup_bool {α : Type*} [CompleteLinearOrder α] (s : Bool → α) :
    ⨆ b, s b = max (s false) (s true) := by
  refine le_antisymm ?_ (max_le_iff.mpr ⟨le_iSup _ _, le_iSup _ _⟩)
  simp [le_total]

section BoolMeasure
--maybe it could be useful to have a notation for the construction of a measure on bool from the two values, for example:
noncomputable
def boolMeasure (a b : ℝ≥0∞) : Measure Bool := a • Measure.dirac false + b • Measure.dirac true

@[simp]
lemma boolMeasure_apply_false (a b : ℝ≥0∞) : boolMeasure a b {false} = a := by simp [boolMeasure]

@[simp]
lemma boolMeasure_apply_true (a b : ℝ≥0∞) : boolMeasure a b {true} = b := by simp [boolMeasure]

lemma measure_eq_boolMeasure (π : Measure Bool) : π = boolMeasure (π {false}) (π {true}) := by
  ext <;> simp

lemma boolMeasure_withDensity (π : Measure Bool) (f : Bool → ℝ≥0∞) :
    π.withDensity f = boolMeasure (f false * π {false}) (f true * π {true}) := by
  ext <;> simp [lintegral_dirac, mul_comm]

end BoolMeasure

end Bool
