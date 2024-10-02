/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
import Mathlib.Probability.Kernel.RadonNikodym

/-!
# Radon-Nikodym derivative and Lebesgue decomposition for kernels

-/

open MeasureTheory MeasurableSpace Set

open scoped ENNReal

namespace ProbabilityTheory.Kernel

variable {α γ : Type*} {mα : MeasurableSpace α} {mγ : MeasurableSpace γ}
  {μ ν : Measure α} {κ η : Kernel α γ}

section Unique

variable {ξ : Kernel α γ} {f : α → γ → ℝ≥0∞}

lemma eq_rnDeriv_measure [IsFiniteKernel η] (h : κ = η.withDensity f + ξ)
    (hf : Measurable (Function.uncurry f)) (hξ : ∀ a, ξ a ⟂ₘ η a) (a : α) :
    f a =ᵐ[η a] ∂(κ a)/∂(η a) := by
  have : κ a = ξ a + (η a).withDensity (f a) := by
    rw [h, coe_add, Pi.add_apply, η.withDensity_apply hf, add_comm]
  exact (κ a).eq_rnDeriv₀ (hf.comp measurable_prod_mk_left).aemeasurable (hξ a) this

lemma eq_singularPart_measure [IsFiniteKernel η]
    (h : κ = η.withDensity f + ξ)
    (hf : Measurable (Function.uncurry f)) (hξ : ∀ a, ξ a ⟂ₘ η a) (a : α) :
    ξ a = (κ a).singularPart (η a) := by
  have : κ a = ξ a + (η a).withDensity (f a) := by
    rw [h, coe_add, Pi.add_apply, η.withDensity_apply hf, add_comm]
  exact (κ a).eq_singularPart (hf.comp measurable_prod_mk_left) (hξ a) this

variable [CountableOrCountablyGenerated α γ]

lemma rnDeriv_eq_rnDeriv_measure (κ ν : Kernel α γ) [IsFiniteKernel κ] [IsFiniteKernel ν] (a : α) :
    rnDeriv κ ν a =ᵐ[ν a] ∂(κ a)/∂(ν a) :=
  eq_rnDeriv_measure (rnDeriv_add_singularPart κ ν).symm (measurable_rnDeriv κ ν)
    (mutuallySingular_singularPart κ ν) a

lemma singularPart_eq_singularPart_measure [IsFiniteKernel κ] [IsFiniteKernel η] (a : α) :
    singularPart κ η a = (κ a).singularPart (η a) :=
  eq_singularPart_measure (rnDeriv_add_singularPart κ η).symm (measurable_rnDeriv κ η)
    (mutuallySingular_singularPart κ η) a

lemma eq_rnDeriv [IsFiniteKernel κ] [IsFiniteKernel η] (h : κ = η.withDensity f + ξ)
    (hf : Measurable (Function.uncurry f)) (hξ : ∀ a, ξ a ⟂ₘ η a) (a : α) :
    f a =ᵐ[η a] rnDeriv κ η a :=
  (eq_rnDeriv_measure h hf hξ a).trans (rnDeriv_eq_rnDeriv_measure _ _ a).symm

lemma eq_singularPart [IsFiniteKernel κ] [IsFiniteKernel η] (h : κ = η.withDensity f + ξ)
    (hf : Measurable (Function.uncurry f)) (hξ : ∀ a, ξ a ⟂ₘ η a) (a : α) :
    ξ a = singularPart κ η a :=
  (eq_singularPart_measure h hf hξ a).trans (singularPart_eq_singularPart_measure a).symm

end Unique

variable [CountableOrCountablyGenerated α γ]

instance instIsFiniteKernel_withDensity_rnDeriv [hκ : IsFiniteKernel κ] [IsFiniteKernel η] :
    IsFiniteKernel (withDensity η (rnDeriv κ η)) := by
  constructor
  refine ⟨hκ.bound, hκ.bound_lt_top, fun a ↦ ?_⟩
  rw [Kernel.withDensity_apply', setLIntegral_univ]
  swap; · exact measurable_rnDeriv κ η
  rw [lintegral_congr_ae (rnDeriv_eq_rnDeriv_measure _ _ a), ← setLIntegral_univ]
  exact (Measure.setLIntegral_rnDeriv_le _).trans (measure_le_bound _ _ _)

instance instIsFiniteKernel_singularPart [hκ : IsFiniteKernel κ] [IsFiniteKernel η] :
    IsFiniteKernel (singularPart κ η) := by
  constructor
  refine ⟨hκ.bound, hκ.bound_lt_top, fun a ↦ ?_⟩
  have h : withDensity η (rnDeriv κ η) a univ + singularPart κ η a univ = κ a univ := by
    conv_rhs => rw [← rnDeriv_add_singularPart κ η]
    simp
  exact (self_le_add_left _ _).trans (h.le.trans (measure_le_bound _ _ _))

end ProbabilityTheory.Kernel
