/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
import Mathlib.Probability.Kernel.Posterior
import TestingLowerBounds.Testing.BoolMeasure

/-!
# Kernel with two values

Results about `Kernel.boolKernel μ ν`, the kernel from `Bool` that sends `false` to `μ` and `true`
to `ν`.

-/

open MeasureTheory

open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {𝒳 : Type*} {m𝒳 : MeasurableSpace 𝒳} {μ ν : Measure 𝒳}

lemma sum_smul_rnDeriv_boolKernel (μ ν : Measure 𝒳) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (π : Measure Bool) [IsFiniteMeasure π] :
    (π {true} • ν.rnDeriv (Kernel.boolKernel μ ν ∘ₘ π)
      + π {false} • (μ.rnDeriv (Kernel.boolKernel μ ν ∘ₘ π)))
      =ᵐ[Kernel.boolKernel μ ν ∘ₘ π] 1 := by
  have h1 := ν.rnDeriv_smul_left_of_ne_top (Kernel.boolKernel μ ν ∘ₘ π)
    (measure_ne_top π {true})
  have h2 := μ.rnDeriv_smul_left_of_ne_top (Kernel.boolKernel μ ν ∘ₘ π)
    (measure_ne_top π {false})
  have : IsFiniteMeasure (π {true} • ν) := ν.smul_finite (measure_ne_top _ _)
  have : IsFiniteMeasure (π {false} • μ) := μ.smul_finite (measure_ne_top _ _)
  have h3 := (π {true} • ν).rnDeriv_add  (π {false} • μ) (Kernel.boolKernel μ ν ∘ₘ π)
  have h4 := (Kernel.boolKernel μ ν ∘ₘ π).rnDeriv_self
  filter_upwards [h1, h2, h3, h4] with a h1 h2 h3 h4
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.one_apply] at h1 h2 h3 h4 ⊢
  rw [← h1, ← h2, ← h3, ← boolKernel_comp_measure, h4]

lemma sum_smul_rnDeriv_boolKernel' (μ ν : Measure 𝒳) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (π : Measure Bool) [IsFiniteMeasure π] :
    ∀ᵐ x ∂(Kernel.boolKernel μ ν ∘ₘ π), π {true} * ν.rnDeriv (Kernel.boolKernel μ ν ∘ₘ π) x
      + π {false} * μ.rnDeriv (Kernel.boolKernel μ ν ∘ₘ π) x = 1 := by
  filter_upwards [sum_smul_rnDeriv_boolKernel μ ν π] with x hx
  simpa using hx

end ProbabilityTheory
