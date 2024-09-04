/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
import Mathlib.MeasureTheory.Measure.GiryMonad

/-!

# Measure.bind results

-/

assert_not_exists Probability.Kernel

namespace MeasureTheory

variable {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}

@[simp]
lemma Measure.bind_const (μ : Measure α) (ν : Measure β) :
    μ.bind (fun _ ↦ ν) = μ Set.univ • ν := by
  ext s hs
  rw [bind_apply hs measurable_const, lintegral_const, smul_apply, smul_eq_mul, mul_comm]

lemma Measure.bind_dirac_eq_map (μ : Measure α) {f : α → β} (hf : Measurable f) :
    μ.bind (fun x ↦ Measure.dirac (f x)) = μ.map f := by
  ext s hs
  rw [bind_apply hs]
  swap; · exact measurable_dirac.comp hf
  simp_rw [dirac_apply' _ hs]
  rw [← lintegral_map _ hf, lintegral_indicator_one hs]
  exact measurable_const.indicator hs

end MeasureTheory
