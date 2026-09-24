/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
module

public import Mathlib.Probability.Kernel.Composition.RadonNikodym
public import TestingLowerBounds.ForMathlib.RnDeriv

/-!
# Radon-Nikodym derivative and Lebesgue decomposition for kernels

Corollaries of the Mathlib results `rnDeriv_measure_compProd_left`, `rnDeriv_compProd`,
`rnDeriv_measure_compProd_right` and `rnDeriv_measure_compProd`, in "a.e. a, a.e. b" form.

-/

@[expose] public section

open MeasureTheory MeasurableSpace Set

open scoped ENNReal

namespace ProbabilityTheory.Kernel

variable {α γ : Type*} {mα : MeasurableSpace α} {mγ : MeasurableSpace γ}
  {μ ν : Measure α} {κ η : Kernel α γ}

lemma ae_eq_compProd_of_forall_ae_eq {β : Type*} {_ : MeasurableSpace β} [AddGroup β]
    [MeasurableSingletonClass β] [MeasurableSub₂ β]
    (μ : Measure α) (κ : Kernel α γ) {f g : α → γ → β}
    (hf : Measurable (Function.uncurry f)) (hg : Measurable (Function.uncurry g))
    (h : ∀ a, f a =ᵐ[κ a] g a) :
    (fun p ↦ f p.1 p.2) =ᵐ[μ ⊗ₘ κ] (fun p ↦ g p.1 p.2) :=
  ae_compProd_of_ae_ae (measurableSet_eq_fun hf hg)
    (ae_of_all _ (fun a ↦ measure_mono_null (fun x ↦ by simp) (h a)))

lemma ENNReal.ae_eq_compProd_of_forall_ae_eq
    (μ : Measure α) (κ : Kernel α γ) {f g : α → γ → ℝ≥0∞}
    (hf : Measurable (Function.uncurry f)) (hg : Measurable (Function.uncurry g))
    (h : ∀ a, f a =ᵐ[κ a] g a) :
    (fun p ↦ f p.1 p.2) =ᵐ[μ ⊗ₘ κ] (fun p ↦ g p.1 p.2) :=
  ae_compProd_of_ae_ae (measurableSet_eq_fun hf hg)
    (ae_of_all _ (fun a ↦ measure_mono_null (fun x ↦ by simp) (h a)))

lemma rnDeriv_measure_compProd_left' (μ ν : Measure α) (κ : Kernel α γ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteKernel κ] :
    ∀ᵐ a ∂ν, (fun b ↦ (∂(μ ⊗ₘ κ)/∂(ν ⊗ₘ κ)) (a, b))
      =ᵐ[κ a] fun _ ↦ (∂μ/∂ν) a :=
  Measure.ae_ae_of_ae_compProd <| rnDeriv_measure_compProd_left μ ν κ

lemma rnDeriv_compProd' [IsFiniteMeasure μ] [IsFiniteKernel κ] [IsFiniteKernel η]
    (h_ac : μ ⊗ₘ κ ≪ μ ⊗ₘ η) (ν : Measure α) [IsFiniteMeasure ν] :
    ∀ᵐ a ∂ν, (fun b ↦ μ.rnDeriv ν a * (μ ⊗ₘ κ).rnDeriv (μ ⊗ₘ η) (a, b))
      =ᵐ[η a] fun b ↦ (μ ⊗ₘ κ).rnDeriv (ν ⊗ₘ η) (a, b) :=
  Measure.ae_ae_of_ae_compProd <| (rnDeriv_compProd h_ac ν).symm

variable [CountableOrCountablyGenerated α γ]

lemma rnDeriv_measure_compProd_right' (μ : Measure α) (κ η : Kernel α γ)
    [IsFiniteMeasure μ] [IsFiniteKernel κ] [IsFiniteKernel η] :
    ∀ᵐ a ∂μ, (fun x ↦ (∂(μ ⊗ₘ κ)/∂(μ ⊗ₘ η)) (a, x))
      =ᵐ[η a] fun x ↦ (∂κ a/∂η a) x := by
  have h a := κ.rnDeriv_eq_rnDeriv_measure (η := η) (a := a)
  have h' := Measure.ae_ae_of_ae_compProd <| rnDeriv_measure_compProd_right μ κ η
  filter_upwards [h'] with a ha
  filter_upwards [ha, h a] with b hb1 hb2
  rw [hb1, hb2]

lemma rnDeriv_measure_compProd' (μ ν : Measure α) (κ η : Kernel α γ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteKernel κ] [IsFiniteKernel η] :
    ∀ᵐ a ∂ν, (fun b ↦ (∂(μ ⊗ₘ κ)/∂(ν ⊗ₘ η)) (a, b))
      =ᵐ[η a] fun b ↦ (∂μ/∂ν) a * (∂κ a/∂η a) b := by
  have h a := κ.rnDeriv_eq_rnDeriv_measure (η := η) (a := a)
  have h' := Measure.ae_ae_of_ae_compProd <| rnDeriv_measure_compProd μ ν κ η
  filter_upwards [h'] with a ha
  filter_upwards [ha, h a] with b hb1 hb2
  rw [hb1, hb2]

end ProbabilityTheory.Kernel
