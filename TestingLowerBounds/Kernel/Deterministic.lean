/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
import Mathlib.Probability.Kernel.Basic

/-!

# Basic deterministic kernels

-/

open MeasureTheory

namespace ProbabilityTheory.Kernel

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}

section Discard

@[simp]
lemma _root_.MeasureTheory.Measure.comp_discard (μ : Measure α) :
    μ.bind (discard α) = μ .univ • (Measure.dirac ()) := by
  ext s hs
  simp [Measure.bind_apply hs (aemeasurable (discard α))]
  ring

end Discard

end ProbabilityTheory.Kernel
