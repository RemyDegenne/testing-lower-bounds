/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import TestingLowerBounds.ForMathlib.RadonNikodym
import TestingLowerBounds.ForMathlib.RnDeriv
import TestingLowerBounds.MeasureCompProd

/-!
# Radon-Nikodym derivative of the composition of a measure and a kernel

-/

open MeasureTheory MeasurableSpace Set

open scoped ENNReal

namespace ProbabilityTheory

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {μ ν : Measure α} {κ η : Kernel α β}

lemma toReal_rnDeriv_comp_eq_condexp_compProd [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμν : μ ≪ ν)
    [IsFiniteKernel κ] [IsFiniteKernel η] (hκη : ∀ᵐ x ∂μ, κ x ≪ η x) :
    (fun ab ↦ ((κ ∘ₘ μ).rnDeriv (η ∘ₘ ν) ab.2).toReal)
      =ᵐ[ν ⊗ₘ η] (ν ⊗ₘ η)[fun ab ↦ ((μ ⊗ₘ κ).rnDeriv (ν ⊗ₘ η) ab).toReal | mβ.comap Prod.snd] := by
  have h_ac : μ ⊗ₘ κ ≪ ν ⊗ₘ η := Measure.absolutelyContinuous_compProd hμν hκη
  refine Filter.EventuallyEq.trans ?_ (Measure.toReal_rnDeriv_map h_ac measurable_snd)
  refine ae_of_all _ (fun ab ↦ ?_)
  simp only
  congr <;> rw [← Measure.snd, Measure.snd_compProd]

lemma toReal_rnDeriv_comp_eq_condexp_compProd_right [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμν : μ ≪ ν) (κ : Kernel α β) [IsFiniteKernel κ] :
    (fun ab ↦ ((κ ∘ₘ μ).rnDeriv (κ ∘ₘ ν) ab.2).toReal)
      =ᵐ[ν ⊗ₘ κ] (ν ⊗ₘ κ)[fun ab ↦ ((μ ⊗ₘ κ).rnDeriv (ν ⊗ₘ κ) ab).toReal | mβ.comap Prod.snd] := by
  refine toReal_rnDeriv_comp_eq_condexp_compProd hμν ?_
  exact ae_of_all _ (fun x ↦ Measure.AbsolutelyContinuous.rfl)

lemma toReal_rnDeriv_comp [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμν : μ ≪ ν)
    [IsFiniteKernel κ] :
    (fun ab ↦ ((κ ∘ₘ μ).rnDeriv (κ ∘ₘ ν) ab.2).toReal)
      =ᵐ[ν ⊗ₘ κ] (ν ⊗ₘ κ)[fun ab ↦ (μ.rnDeriv ν ab.1).toReal | mβ.comap Prod.snd] := by
  refine (toReal_rnDeriv_comp_eq_condexp_compProd_right hμν κ).trans (condexp_congr_ae ?_)
  filter_upwards [Kernel.rnDeriv_measure_compProd_left μ ν κ] with x hx
  rw [hx]

theorem _root_.Measurable.setLIntegral_kernel_prod_right' [IsSFiniteKernel κ]
    {f : α × β → ℝ≥0∞} (hf : Measurable f) {s : Set β} (hs : MeasurableSet s) :
    Measurable fun a => ∫⁻ b in s, f (a, b) ∂κ a := by
  simp_rw [← Kernel.lintegral_restrict κ hs]; exact hf.lintegral_kernel_prod_right'

lemma rnDeriv_compProd [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμν : μ ≪ ν) [IsFiniteKernel κ] [IsFiniteKernel η] (h_ac : μ ⊗ₘ κ ≪ μ ⊗ₘ η) :
    (fun p ↦ μ.rnDeriv ν p.1 * (μ ⊗ₘ κ).rnDeriv (μ ⊗ₘ η) p)
      =ᵐ[ν ⊗ₘ η] (μ ⊗ₘ κ).rnDeriv (ν ⊗ₘ η) := by
  have h_ac1 : μ ⊗ₘ κ ≪ ν ⊗ₘ η := Measure.absolutelyContinuous_compProd_of_compProd hμν h_ac
  have h_meas : Measurable fun p ↦ (∂μ/∂ν) p.1 * (∂μ ⊗ₘ κ/∂μ ⊗ₘ η) p :=
    ((Measure.measurable_rnDeriv _ _).comp measurable_fst).mul (Measure.measurable_rnDeriv _ _)
  have h_eq t₁ t₂ : MeasurableSet t₁ → MeasurableSet t₂ →
      ∫⁻ p in t₁ ×ˢ t₂, (∂μ/∂ν) p.1 * (∂μ ⊗ₘ κ/∂μ ⊗ₘ η) p ∂ν ⊗ₘ η
        = ∫⁻ p in t₁ ×ˢ t₂, (∂μ ⊗ₘ κ/∂ν ⊗ₘ η) p ∂ν ⊗ₘ η := by
    intro ht₁ ht₂
    rw [Measure.setLIntegral_compProd h_meas ht₁ ht₂]
    simp only
    have : ∀ a, ∫⁻ b in t₂, (∂μ/∂ν) a * (∂μ ⊗ₘ κ/∂μ ⊗ₘ η) (a, b) ∂η a
        = (∂μ/∂ν) a * ∫⁻ b in t₂, (∂μ ⊗ₘ κ/∂μ ⊗ₘ η) (a, b) ∂η a := fun a ↦ by
      rw [lintegral_const_mul]
      exact (Measure.measurable_rnDeriv _ _).comp measurable_prod_mk_left
    simp_rw [this]
    rw [setLIntegral_rnDeriv_mul hμν _ ht₁]
    swap
    · exact ((Measure.measurable_rnDeriv _ _).setLIntegral_kernel_prod_right' ht₂).aemeasurable
    rw [← Measure.setLIntegral_compProd (Measure.measurable_rnDeriv _ _) ht₁ ht₂,
      Measure.setLIntegral_rnDeriv h_ac1, Measure.setLIntegral_rnDeriv h_ac]
  refine ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite h_meas ?_ ?_
  · exact Measure.measurable_rnDeriv _ _
  · intro s hs _
    apply induction_on_inter generateFrom_prod.symm isPiSystem_prod _ _ _ _ hs
    · simp
    · rintro _ ⟨t₁, ht₁, t₂, ht₂, rfl⟩
      exact h_eq t₁ t₂ ht₁ ht₂
    · intro t ht ht_eq
      have h_ne_top : ∫⁻ p in t, (∂μ ⊗ₘ κ/∂ν ⊗ₘ η) p ∂ν ⊗ₘ η ≠ ⊤ := by
        rw [Measure.setLIntegral_rnDeriv]
        · exact measure_ne_top _ _
        · exact h_ac1
      rw [setLintegral_compl ht h_ne_top, setLintegral_compl ht, ht_eq]
      swap; · rw [ht_eq]; exact h_ne_top
      congr 1
      have h := h_eq .univ .univ .univ .univ
      simp only [univ_prod_univ, Measure.restrict_univ] at h
      exact h
    · intro f' hf_disj hf_meas hf_eq
      rw [lintegral_iUnion hf_meas hf_disj, lintegral_iUnion hf_meas hf_disj]
      congr with i
      exact hf_eq i

end ProbabilityTheory
