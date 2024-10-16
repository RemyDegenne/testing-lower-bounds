/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
import Mathlib.Probability.Kernel.RadonNikodym
import TestingLowerBounds.ForMathlib.KernelFstSnd

/-!
# Radon-Nikodym derivative and Lebesgue decomposition for kernels

-/

open ProbabilityTheory MeasurableSpace Set

open scoped ENNReal

namespace MeasureTheory.Measure

variable {α γ : Type*} {mα : MeasurableSpace α} {mγ : MeasurableSpace γ}
  {μ ν : Measure α} {κ η : Kernel α γ}

lemma absolutelyContinuous_compProd_left_iff
    [SFinite μ] [SFinite ν] [IsFiniteKernel κ] [∀ a, NeZero (κ a)] :
    μ ⊗ₘ κ ≪ ν ⊗ₘ κ ↔ μ ≪ ν :=
  ⟨absolutelyContinuous_of_compProd, fun h ↦ absolutelyContinuous_compProd_left h _⟩

lemma mutuallySingular_compProd_left (hμν : μ ⟂ₘ ν) (κ η : Kernel α γ) :
    μ ⊗ₘ κ ⟂ₘ ν ⊗ₘ η := by
  by_cases hμ : SFinite μ
  swap; · rw [compProd_of_not_sfinite _ _ hμ]; simp
  by_cases hν : SFinite ν
  swap; · rw [compProd_of_not_sfinite _ _ hν]; simp
  by_cases hκ : IsSFiniteKernel κ
  swap; · rw [compProd_of_not_isSFiniteKernel _ _ hκ]; simp
  by_cases hη : IsSFiniteKernel η
  swap; · rw [compProd_of_not_isSFiniteKernel _ _ hη]; simp
  refine ⟨hμν.nullSet ×ˢ univ, hμν.measurableSet_nullSet.prod .univ, ?_⟩
  rw [compProd_apply_prod hμν.measurableSet_nullSet .univ, compl_prod_eq_union]
  simp only [MutuallySingular.restrict_nullSet, lintegral_zero_measure, compl_univ,
    prod_empty, union_empty, true_and]
  rw [compProd_apply_prod hμν.measurableSet_nullSet.compl .univ]
  simp

lemma mutuallySingular_of_mutuallySingular_compProd {ξ : Measure α}
    [SFinite μ] [SFinite ν] [IsSFiniteKernel κ] [IsSFiniteKernel η]
    (h : μ ⊗ₘ κ ⟂ₘ ν ⊗ₘ η) (hμ : ξ ≪ μ) (hν : ξ ≪ ν) :
    ∀ᵐ x ∂ξ, κ x ⟂ₘ η x := by
  have hs : MeasurableSet h.nullSet := h.measurableSet_nullSet
  have hμ_zero : (μ ⊗ₘ κ) h.nullSet = 0 := h.measure_nullSet
  have hν_zero : (ν ⊗ₘ η) h.nullSetᶜ = 0 := h.measure_compl_nullSet
  rw [compProd_apply, lintegral_eq_zero_iff'] at hμ_zero hν_zero
  · filter_upwards [hμ hμ_zero, hν hν_zero] with x hxμ hxν
    exact ⟨Prod.mk x ⁻¹' h.nullSet, measurable_prod_mk_left hs, ⟨hxμ, hxν⟩⟩
  · exact Kernel.measurable_kernel_prod_mk_left hs.compl |>.aemeasurable
  · exact Kernel.measurable_kernel_prod_mk_left hs |>.aemeasurable
  · exact hs.compl
  · exact hs

lemma mutuallySingular_compProd_iff_of_same_right (μ ν : Measure α) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (κ : Kernel α γ) [IsFiniteKernel κ] [hκ : ∀ x, NeZero (κ x)] :
    μ ⊗ₘ κ ⟂ₘ ν ⊗ₘ κ ↔ μ ⟂ₘ ν := by
  refine ⟨fun h ↦ ?_, fun h ↦ mutuallySingular_compProd_left h _ _⟩
  rw [← withDensity_rnDeriv_eq_zero]
  have hh := mutuallySingular_of_mutuallySingular_compProd h ?_ ?_ (ξ  := ν.withDensity (∂μ/∂ν))
  rotate_left
  · exact absolutelyContinuous_of_le (μ.withDensity_rnDeriv_le ν)
  · exact withDensity_absolutelyContinuous _ _
  simp_rw [MutuallySingular.self_iff, (hκ _).ne] at hh
  exact ae_eq_bot.mp (Filter.eventually_false_iff_eq_bot.mp hh)

lemma absolutelyContinuous_of_add_of_mutuallySingular {ν₁ ν₂ : Measure α}
    (h_ms : μ ⟂ₘ ν₂) (h : μ ≪ ν₁ + ν₂) : μ ≪ ν₁ := by
  refine AbsolutelyContinuous.mk fun s hs hs_zero ↦ ?_
  let t := h_ms.nullSet
  have ht : MeasurableSet t := h_ms.measurableSet_nullSet
  have htμ : μ t = 0 := h_ms.measure_nullSet
  have htν₂ : ν₂ tᶜ = 0 := h_ms.measure_compl_nullSet
  have : μ s = μ (s ∩ tᶜ) := by
    conv_lhs => rw [← inter_union_compl s t]
    rw [measure_union, measure_inter_null_of_null_right _ htμ, zero_add]
    · exact (disjoint_compl_right.inter_right' _ ).inter_left' _
    · exact hs.inter ht.compl
  rw [this]
  refine h ?_
  simp only [Measure.coe_add, Pi.add_apply, add_eq_zero]
  exact ⟨measure_inter_null_of_null_left _ hs_zero, measure_inter_null_of_null_right _ htν₂⟩

lemma absolutelyContinuous_compProd_of_compProd [SFinite ν] [IsSFiniteKernel η]
    (hμν : μ ≪ ν) (hκη : μ ⊗ₘ κ ≪ μ ⊗ₘ η) :
    μ ⊗ₘ κ ≪ ν ⊗ₘ η := by
  by_cases hμ : SFinite μ
  swap; · rw [compProd_of_not_sfinite _ _ hμ]; simp
  refine AbsolutelyContinuous.mk fun s hs hs_zero ↦ ?_
  suffices (μ ⊗ₘ η) s = 0 from hκη this
  rw [measure_zero_iff_ae_nmem, ae_compProd_iff hs.compl] at hs_zero ⊢
  exact hμν.ae_le hs_zero

lemma absolutelyContinuous_compProd_of_compProd'
    [SigmaFinite μ] [SigmaFinite ν] [IsSFiniteKernel κ] [IsSFiniteKernel η]
    (hκη : μ ⊗ₘ κ ≪ ν ⊗ₘ η) :
    μ ⊗ₘ κ ≪ μ ⊗ₘ η := by
  rw [ν.haveLebesgueDecomposition_add μ, compProd_add_left, add_comm] at hκη
  have h := absolutelyContinuous_of_add_of_mutuallySingular ?_ hκη
  · refine h.trans ?_
    refine absolutelyContinuous_compProd_left ?_ _
    exact withDensity_absolutelyContinuous _ _
  · refine mutuallySingular_compProd_left ?_ _ _
    exact (mutuallySingular_singularPart _ _).symm

lemma absolutelyContinuous_compProd_iff'
    [SigmaFinite μ] [SigmaFinite ν] [IsSFiniteKernel κ] [IsSFiniteKernel η] [∀ x, NeZero (κ x)] :
    μ ⊗ₘ κ ≪ ν ⊗ₘ η ↔ μ ≪ ν ∧ μ ⊗ₘ κ ≪ μ ⊗ₘ η :=
  ⟨fun h ↦ ⟨absolutelyContinuous_of_compProd h, absolutelyContinuous_compProd_of_compProd' h⟩,
    fun h ↦ absolutelyContinuous_compProd_of_compProd h.1 h.2⟩

variable [CountableOrCountablyGenerated α γ]

lemma mutuallySingular_compProd_right
    (μ ν : Measure α) {κ η : Kernel α γ} [IsFiniteKernel κ] [IsFiniteKernel η]
    (hκη : ∀ᵐ a ∂μ, κ a ⟂ₘ η a) :
    μ ⊗ₘ κ ⟂ₘ ν ⊗ₘ η := by
  by_cases hμ : SFinite μ
  swap; · rw [compProd_of_not_sfinite _ _ hμ]; simp
  by_cases hν : SFinite ν
  swap; · rw [compProd_of_not_sfinite _ _ hν]; simp
  let s := κ.mutuallySingularSet η
  have hs : MeasurableSet s := Kernel.measurableSet_mutuallySingularSet κ η
  symm
  refine ⟨s, hs, ?_⟩
  rw [compProd_apply hs, compProd_apply hs.compl]
  have h_eq a : Prod.mk a ⁻¹' s = Kernel.mutuallySingularSetSlice κ η a := rfl
  have h1 a : η a (Prod.mk a ⁻¹' s) = 0 := by rw [h_eq, Kernel.measure_mutuallySingularSetSlice]
  have h2 : ∀ᵐ a ∂ μ, κ a (Prod.mk a ⁻¹' s)ᶜ = 0 := by
    filter_upwards [hκη] with a ha
    rw [h_eq, ← Kernel.withDensity_rnDeriv_eq_zero_iff_measure_eq_zero κ η a,
      Kernel.withDensity_rnDeriv_eq_zero_iff_mutuallySingular]
    exact ha
  simp [h1, lintegral_congr_ae h2]

lemma mutuallySingular_compProd_right'
    (μ ν : Measure α) {κ η : Kernel α γ} [IsFiniteKernel κ] [IsFiniteKernel η]
    (hκη : ∀ᵐ a ∂ν, κ a ⟂ₘ η a) :
    μ ⊗ₘ κ ⟂ₘ ν ⊗ₘ η := by
  by_cases hμ : SFinite μ
  swap; · rw [compProd_of_not_sfinite _ _ hμ]; simp
  by_cases hν : SFinite ν
  swap; · rw [compProd_of_not_sfinite _ _ hν]; simp
  refine (mutuallySingular_compProd_right _ _ ?_).symm
  simp_rw [MutuallySingular.comm, hκη]

lemma mutuallySingular_compProd_iff_of_same_left (μ : Measure α) [SFinite μ]
    (κ η : Kernel α γ) [IsFiniteKernel κ] [IsFiniteKernel η] :
    μ ⊗ₘ κ ⟂ₘ μ ⊗ₘ η ↔ ∀ᵐ a ∂μ, κ a ⟂ₘ η a := by
  refine ⟨fun h ↦ ?_, fun h ↦ mutuallySingular_compProd_right _ _ h⟩
  exact mutuallySingular_of_mutuallySingular_compProd h (fun _ a ↦ a) (fun _ a ↦ a)

section MeasureCompProd

lemma absolutelyContinuous_kernel_of_compProd
    [SFinite μ] [SFinite ν] [IsFiniteKernel κ] [IsFiniteKernel η]
    (h : μ ⊗ₘ κ ≪ ν ⊗ₘ η) :
    ∀ᵐ a ∂μ, κ a ≪ η a := by
  suffices ∀ᵐ a ∂μ, κ.singularPart η a = 0 by
    filter_upwards [this] with a ha
    rwa [Kernel.singularPart_eq_zero_iff_absolutelyContinuous] at ha
  rw [← κ.rnDeriv_add_singularPart η, compProd_add_right, AbsolutelyContinuous.add_left_iff] at h
  have : μ ⊗ₘ κ.singularPart η ⟂ₘ ν ⊗ₘ η :=
    mutuallySingular_compProd_right μ ν (.of_forall <| Kernel.mutuallySingular_singularPart _ _)
  have h_zero : μ ⊗ₘ κ.singularPart η = 0 :=
    eq_zero_of_absolutelyContinuous_of_mutuallySingular h.2 this
  simp_rw [← measure_univ_eq_zero]
  refine (lintegral_eq_zero_iff (Kernel.measurable_coe _ .univ)).mp ?_
  rw [← setLIntegral_univ, ← compProd_apply_prod .univ .univ, h_zero]
  simp

lemma absolutelyContinuous_compProd_iff
    [SFinite μ] [SFinite ν] [IsFiniteKernel κ] [IsFiniteKernel η] [∀ a, NeZero (κ a)] :
    μ ⊗ₘ κ ≪ ν ⊗ₘ η ↔ μ ≪ ν ∧ ∀ᵐ a ∂μ, κ a ≪ η a :=
  ⟨fun h ↦ ⟨absolutelyContinuous_of_compProd h, absolutelyContinuous_kernel_of_compProd h⟩,
    fun h ↦ absolutelyContinuous_compProd h.1 h.2⟩

lemma absolutelyContinuous_compProd_right_iff
    {μ : Measure α} {κ η : Kernel α γ} [SFinite μ] [IsFiniteKernel κ] [IsFiniteKernel η] :
    μ ⊗ₘ κ ≪ μ ⊗ₘ η ↔ ∀ᵐ a ∂μ, κ a ≪ η a :=
  ⟨absolutelyContinuous_kernel_of_compProd, fun h ↦ absolutelyContinuous_compProd_right h⟩

end MeasureCompProd

end MeasureTheory.Measure

open MeasureTheory

lemma ProbabilityTheory.Kernel.absolutelyContinuous_compProd_iff
    {α β γ : Type*} {_ : MeasurableSpace α} {_ : MeasurableSpace β} {_ : MeasurableSpace γ}
    [CountableOrCountablyGenerated β γ] {κ₁ η₁ : Kernel α β}
    {κ₂ η₂ : Kernel (α × β) γ} [IsSFiniteKernel κ₁] [IsSFiniteKernel η₁] [IsFiniteKernel κ₂]
    [IsFiniteKernel η₂] (a : α) [∀ b, NeZero (κ₂ (a, b))] :
    (κ₁ ⊗ₖ κ₂) a ≪ (η₁ ⊗ₖ η₂) a ↔ κ₁ a ≪ η₁ a ∧ ∀ᵐ b ∂κ₁ a, κ₂ (a, b) ≪ η₂ (a, b) := by
  simp_rw [Kernel.compProd_apply_eq_compProd_snd', Measure.absolutelyContinuous_compProd_iff,
    Kernel.snd'_apply]
