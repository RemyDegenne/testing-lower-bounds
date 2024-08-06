/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
import TestingLowerBounds.ForMathlib.RadonNikodym
import TestingLowerBounds.Kernel.Basic
import TestingLowerBounds.Kernel.Monoidal


/-!

# Results about the composition-product of measures

## Main definitions

* `FooBar`

## Main statements

* `fooBar_unique`

## Notation

## Implementation details

-/

open Real MeasureTheory Filter

open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

variable {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}
  {μ ν : Measure α} {κ η : Kernel α β} {f g : ℝ → ℝ}

/-- Composition of a measure and a kernel.

Defined using `MeasureTheory.Measure.bind` -/
--scoped[ProbabilityTheory] infixl:100 " ∘ₘ " => fun μ κ ↦ MeasureTheory.Measure.bind κ μ

scoped[ProbabilityTheory] notation3 κ " ∘ₘ " μ:100 => MeasureTheory.Measure.bind μ κ

lemma Measure.comp_assoc {μ : Measure α} {κ : Kernel α β} {η : Kernel β γ} :
    η ∘ₘ (κ ∘ₘ μ) = (η ∘ₖ κ) ∘ₘ μ :=
  Measure.bind_bind (Kernel.measurable _) (Kernel.measurable _)

lemma Measure.comp_deterministic_eq_map {f : α → β} (hf : Measurable f) :
    Kernel.deterministic f hf ∘ₘ μ = μ.map f := by
  ext s hs
  rw [Measure.bind_apply hs (Kernel.measurable _), Measure.map_apply hf hs]
  simp only [Kernel.deterministic_apply' hf _ hs]
  rw [lintegral_indicator_const_comp hf hs, one_mul]

lemma Measure.comp_id : Kernel.id ∘ₘ μ = μ := by
  rw [Kernel.id, Measure.comp_deterministic_eq_map, Measure.map_id]

lemma Measure.comp_eq_snd_compProd (μ : Measure α) [SFinite μ]
    (κ : Kernel α β) [IsSFiniteKernel κ] :
    κ ∘ₘ μ = (μ ⊗ₘ κ).snd := by
  ext s hs
  rw [Measure.bind_apply hs (Kernel.measurable _), Measure.snd_apply hs,
    Measure.compProd_apply]
  · rfl
  · exact measurable_snd hs

lemma Measure.fst_compProd (μ : Measure α) [SFinite μ] (κ : Kernel α β) [IsMarkovKernel κ] :
    (μ ⊗ₘ κ).fst = μ := by
  ext s
  rw [Measure.compProd, Measure.fst, ← Kernel.fst_apply, Kernel.fst_compProd, Kernel.const_apply]

lemma Measure.snd_compProd (μ : Measure α) [SFinite μ] (κ : Kernel α β) [IsSFiniteKernel κ] :
    (μ ⊗ₘ κ).snd = κ ∘ₘ μ := (Measure.comp_eq_snd_compProd μ κ).symm

lemma Measure.compProd_eq_comp (μ : Measure α) [SFinite μ] (κ : Kernel α β) [IsSFiniteKernel κ] :
    μ ⊗ₘ κ = (Kernel.id ×ₖ κ) ∘ₘ μ := by
  rw [Measure.compProd, Kernel.compProd_prodMkLeft_eq_comp]
  rfl

lemma Measure.compProd_id [SFinite μ] : μ ⊗ₘ Kernel.id = μ.map (fun x ↦ (x, x)) := by
  rw [Measure.compProd_eq_comp, Kernel.id, Kernel.deterministic_prod_deterministic,
    Measure.comp_deterministic_eq_map]
  rfl

/-- The composition product of a measure and a constant kernel is the product between the two
measures. -/
@[simp]
lemma Measure.compProd_const {ν : Measure β} [SFinite μ] [SFinite ν] :
    μ ⊗ₘ (Kernel.const α ν) = μ.prod ν := by
  ext s hs
  rw [Measure.compProd_apply hs, Measure.prod_apply hs]
  simp_rw [Kernel.const_apply]

@[simp]
lemma Measure.comp_const {ν : Measure β} :
    (Kernel.const α ν) ∘ₘ μ = μ Set.univ • ν := by
  ext s hs
  simp_rw [Measure.bind_apply hs (Kernel.measurable _), Kernel.const_apply, lintegral_const]
  simp [mul_comm]

lemma Measure.compProd_apply_toReal [SFinite μ] [IsFiniteKernel κ]
    {s : Set (α × β)} (hs : MeasurableSet s) :
    ((μ ⊗ₘ κ) s).toReal = ∫ x, (κ x (Prod.mk x ⁻¹' s)).toReal ∂μ := by
  rw [Measure.compProd_apply hs, integral_eq_lintegral_of_nonneg_ae]
  rotate_left
  · exact ae_of_all _ (fun x ↦ by positivity)
  · exact (Kernel.measurable_kernel_prod_mk_left hs).ennreal_toReal.aestronglyMeasurable
  congr with x
  rw [ENNReal.ofReal_toReal (measure_ne_top _ _)]

lemma Measure.compProd_univ_toReal [SFinite μ] [IsFiniteKernel κ] :
    ((μ ⊗ₘ κ) Set.univ).toReal = ∫ x, (κ x Set.univ).toReal ∂μ :=
  compProd_apply_toReal MeasurableSet.univ

lemma Measure.fst_sum {ι : Type*} (μ : ι → Measure (α × β)) :
    (Measure.sum μ).fst = Measure.sum (fun n ↦ (μ n).fst) := by
  ext s hs
  rw [Measure.fst_apply hs, Measure.sum_apply, Measure.sum_apply _ hs]
  · congr with i
    rw [Measure.fst_apply hs]
  · exact measurable_fst hs

lemma Measure.snd_sum {ι : Type*} (μ : ι → Measure (α × β)) :
    (Measure.sum μ).snd = Measure.sum (fun n ↦ (μ n).snd) := by
  ext s hs
  rw [Measure.snd_apply hs, Measure.sum_apply, Measure.sum_apply _ hs]
  · congr with i
    rw [Measure.snd_apply hs]
  · exact measurable_snd hs

instance {μ : Measure (α × β)} [SFinite μ] : SFinite μ.fst :=
  ⟨fun n ↦ (sFiniteSeq μ n).fst, inferInstance, by rw [← Measure.fst_sum, sum_sFiniteSeq μ]⟩

instance {μ : Measure (α × β)} [SFinite μ] : SFinite μ.snd :=
  ⟨fun n ↦ (sFiniteSeq μ n).snd, inferInstance, by rw [← Measure.snd_sum, sum_sFiniteSeq μ]⟩

instance {μ : Measure α} [SFinite μ] {κ : Kernel α β} [IsSFiniteKernel κ] : SFinite (κ ∘ₘ μ) := by
  rw [Measure.comp_eq_snd_compProd]
  infer_instance

instance {μ : Measure α} [IsFiniteMeasure μ] {κ : Kernel α β} [IsFiniteKernel κ] :
    IsFiniteMeasure (κ ∘ₘ μ) := by
  rw [Measure.comp_eq_snd_compProd]
  infer_instance

instance {μ : Measure α} [IsProbabilityMeasure μ] {κ : Kernel α β} [IsMarkovKernel κ] :
    IsProbabilityMeasure (κ ∘ₘ μ) := by
  rw [Measure.comp_eq_snd_compProd]
  infer_instance

lemma Measure.fst_swap_compProd [SFinite μ] [IsSFiniteKernel κ] :
    ((μ ⊗ₘ κ).map Prod.swap).fst = κ ∘ₘ μ := by
  simp [Measure.comp_eq_snd_compProd]

section ParallelComp

namespace Kernel

variable {δ : Type*} {mδ : MeasurableSpace δ}

lemma _root_.MeasureTheory.Measure.prod_comp_right
    (μ : Measure α) (ν : Measure β) [SFinite ν]
    (κ : Kernel β γ) [IsSFiniteKernel κ] :
    μ.prod (κ ∘ₘ ν) = (Kernel.id ∥ₖ κ) ∘ₘ (μ.prod ν) := by
  ext s hs
  rw [Measure.prod_apply hs, Measure.bind_apply hs (Kernel.measurable _)]
  simp_rw [Measure.bind_apply (measurable_prod_mk_left hs) (Kernel.measurable _)]
  rw [MeasureTheory.lintegral_prod]
  swap; · exact (Kernel.measurable_coe _ hs).aemeasurable
  congr with a
  congr with b
  rw [parallelComp_apply, Kernel.id_apply, Measure.prod_apply hs, lintegral_dirac']
  exact measurable_measure_prod_mk_left hs

lemma _root_.MeasureTheory.Measure.prod_comp_left
    (μ : Measure α) [SFinite μ] (ν : Measure β) [SFinite ν]
    (κ : Kernel α γ) [IsSFiniteKernel κ] :
    (κ ∘ₘ μ).prod ν = (κ ∥ₖ Kernel.id) ∘ₘ (μ.prod ν) := by
  have h1 : (κ ∘ₘ μ).prod ν = (ν.prod (κ ∘ₘ μ)).map Prod.swap := by
    rw [Measure.prod_swap]
  have h2 : (κ ∥ₖ Kernel.id) ∘ₘ (μ.prod ν) = ((Kernel.id ∥ₖ κ) ∘ₘ (ν.prod μ)).map Prod.swap := by
    calc (κ ∥ₖ Kernel.id) ∘ₘ (μ.prod ν)
    _ = (κ ∥ₖ Kernel.id) ∘ₘ ((ν.prod μ).map Prod.swap) := by rw [Measure.prod_swap]
    _ = (κ ∥ₖ Kernel.id) ∘ₘ ((swap _ _) ∘ₘ (ν.prod μ)) := by
      rw [swap, Measure.comp_deterministic_eq_map]
    _ = (swap _ _) ∘ₘ ((Kernel.id ∥ₖ κ) ∘ₘ (ν.prod μ)) := by
      rw [Measure.comp_assoc, Measure.comp_assoc, swap_parallelComp]
    _ = ((Kernel.id ∥ₖ κ) ∘ₘ (ν.prod μ)).map Prod.swap := by
      rw [swap, Measure.comp_deterministic_eq_map]
  rw [← Measure.prod_comp_right, ← h1] at h2
  exact h2.symm

lemma parallelComp_comp_right {α' : Type*} {_ : MeasurableSpace α'}
    (κ : Kernel α β) [IsSFiniteKernel κ]
    (η : Kernel α' γ) [IsSFiniteKernel η] (ξ : Kernel γ δ) [IsSFiniteKernel ξ] :
    κ ∥ₖ (ξ ∘ₖ η) = (Kernel.id ∥ₖ ξ) ∘ₖ (κ ∥ₖ η) := by
  ext a
  rw [parallelComp_apply, comp_apply, comp_apply, parallelComp_apply, Measure.prod_comp_right]

lemma parallelComp_comp_left {α' : Type*} {_ : MeasurableSpace α'}
    (κ : Kernel α β) [IsSFiniteKernel κ]
    (η : Kernel α' γ) [IsSFiniteKernel η] (ξ : Kernel γ δ) [IsSFiniteKernel ξ] :
    (ξ ∘ₖ η) ∥ₖ κ = (ξ ∥ₖ Kernel.id) ∘ₖ (η ∥ₖ κ) := by
  ext a
  rw [parallelComp_apply, comp_apply, comp_apply, parallelComp_apply, Measure.prod_comp_left]

lemma parallelComp_comm (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel γ δ) [IsSFiniteKernel η] :
    (Kernel.id ∥ₖ κ) ∘ₖ (η ∥ₖ Kernel.id) = (η ∥ₖ Kernel.id) ∘ₖ (Kernel.id ∥ₖ κ) := by
  rw [← parallelComp_comp_right, ← parallelComp_comp_left, comp_id, comp_id]

end Kernel

end ParallelComp

section AbsolutelyContinuous

lemma Measure.absolutelyContinuous_comp {μ ν : Measure α} {κ η : Kernel α γ}
    [SFinite μ] [SFinite ν] [IsSFiniteKernel κ] [IsSFiniteKernel η]
    (hμν : μ ≪ ν) (hκη : ∀ᵐ a ∂μ, κ a ≪ η a) :
    κ ∘ₘ μ ≪ η ∘ₘ ν := by
  simp_rw [Measure.comp_eq_snd_compProd, Measure.snd]
  exact Measure.AbsolutelyContinuous.map (Kernel.Measure.absolutelyContinuous_compProd hμν hκη)
    measurable_snd

lemma Measure.absolutelyContinuous_comp_left {μ ν : Measure α} [SFinite μ] [SFinite ν]
    (hμν : μ ≪ ν) (κ : Kernel α γ) [IsSFiniteKernel κ]  :
    κ ∘ₘ μ ≪ κ ∘ₘ ν :=
  absolutelyContinuous_comp hμν (ae_of_all μ fun _ _ a ↦ a)

lemma Measure.absolutelyContinuous_comp_right (μ : Measure α) {κ η : Kernel α γ}
    [SFinite μ] [IsSFiniteKernel κ] [IsSFiniteKernel η]
    (hκη : ∀ᵐ a ∂μ, κ a ≪ η a) :
    κ ∘ₘ μ ≪ η ∘ₘ μ :=
  Measure.absolutelyContinuous_comp μ.absolutelyContinuous_refl hκη

end AbsolutelyContinuous

section SingularPart

lemma singularPart_compProd'' [MeasurableSpace.CountableOrCountablyGenerated α β]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ η : Kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η] :
    (μ ⊗ₘ κ).singularPart (ν ⊗ₘ η)
      = μ.singularPart ν ⊗ₘ Kernel.withDensity η (Kernel.rnDeriv κ η)
        + μ.singularPart ν ⊗ₘ Kernel.singularPart κ η
        + ν.withDensity (∂μ/∂ν) ⊗ₘ Kernel.singularPart κ η := by
  conv_lhs => rw [← Kernel.rnDeriv_add_singularPart κ η, Measure.compProd_add_right,
    μ.haveLebesgueDecomposition_add ν]
  simp_rw [Measure.compProd_add_left, Measure.singularPart_add]
  have : (ν.withDensity (∂μ/∂ν) ⊗ₘ Kernel.withDensity η (Kernel.rnDeriv κ η)).singularPart
      (ν ⊗ₘ η) = 0 := by
    refine Measure.singularPart_eq_zero_of_ac (Kernel.Measure.absolutelyContinuous_compProd ?_ ?_)
    · exact withDensity_absolutelyContinuous _ _
    · exact ae_of_all _ (Kernel.withDensity_absolutelyContinuous _)
  rw [this, add_zero, ← add_assoc]
  congr
  · rw [Measure.singularPart_eq_self]
    exact Kernel.Measure.mutuallySingular_compProd_left (Measure.mutuallySingular_singularPart μ ν)
      (Kernel.withDensity η (Kernel.rnDeriv κ η)) η
  · rw [Measure.singularPart_eq_self]
    exact Kernel.Measure.mutuallySingular_compProd_left (Measure.mutuallySingular_singularPart μ ν)
      (Kernel.singularPart κ η) η
  · rw [Measure.singularPart_eq_self]
    exact Kernel.Measure.mutuallySingular_compProd_right (ν.withDensity (∂μ/∂ν)) ν
      (eventually_of_forall <| Kernel.mutuallySingular_singularPart _ _)

lemma singularPart_compProd [MeasurableSpace.CountableOrCountablyGenerated α β]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ η : Kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η] :
    (μ ⊗ₘ κ).singularPart (ν ⊗ₘ η)
      = μ.singularPart ν ⊗ₘ Kernel.withDensity η (Kernel.rnDeriv κ η)
        + μ ⊗ₘ Kernel.singularPart κ η := by
  rw [singularPart_compProd'']
  have : (μ ⊗ₘ Kernel.singularPart κ η) = (μ.singularPart ν ⊗ₘ Kernel.singularPart κ η)
        + (ν.withDensity (∂μ/∂ν) ⊗ₘ Kernel.singularPart κ η) := by
    rw [← Measure.compProd_add_left, ← μ.haveLebesgueDecomposition_add ν]
  rw [this]
  abel

lemma singularPart_compProd' [MeasurableSpace.CountableOrCountablyGenerated α β]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ η : Kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η] :
    (μ ⊗ₘ κ).singularPart (ν ⊗ₘ η)
      = μ.singularPart ν ⊗ₘ κ + ν.withDensity (∂μ/∂ν) ⊗ₘ Kernel.singularPart κ η := by
  rw [singularPart_compProd'']
  have : μ.singularPart ν ⊗ₘ κ
      = μ.singularPart ν ⊗ₘ Kernel.withDensity η (Kernel.rnDeriv κ η)
        + μ.singularPart ν ⊗ₘ Kernel.singularPart κ η := by
    rw [← Measure.compProd_add_right]
    congr
    exact (Kernel.rnDeriv_add_singularPart κ η).symm
  rw [this]

lemma singularPart_compProd_left [MeasurableSpace.CountableOrCountablyGenerated α β]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ : Kernel α β) [IsFiniteKernel κ] :
    (μ ⊗ₘ κ).singularPart (ν ⊗ₘ κ) = μ.singularPart ν ⊗ₘ κ := by
  rw [singularPart_compProd', Kernel.singularPart_self]
  simp [Measure.singularPart_zero]

lemma singularPart_compProd_right [MeasurableSpace.CountableOrCountablyGenerated α β]
    (μ : Measure α) [IsFiniteMeasure μ]
    (κ η : Kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η] :
    (μ ⊗ₘ κ).singularPart (μ ⊗ₘ η) = μ ⊗ₘ Kernel.singularPart κ η := by
  rw [singularPart_compProd, Measure.singularPart_self]
  simp [Measure.singularPart_zero]

end SingularPart

section Integrable

variable {E : Type*}

-- todo find better name
theorem _root_.MeasureTheory.Integrable.compProd_mk_left_ae' [NormedAddCommGroup E]
    [SFinite μ] [IsSFiniteKernel κ] ⦃f : α × β → E⦄
    (hf : Integrable f (μ ⊗ₘ κ)) :
    ∀ᵐ x ∂μ, Integrable (fun y ↦ f (x, y)) (κ x) :=
  hf.compProd_mk_left_ae

theorem _root_.MeasureTheory.Integrable.integral_norm_compProd' [NormedAddCommGroup E]
    [SFinite μ] [IsSFiniteKernel κ] ⦃f : α × β → E⦄
    (hf : Integrable f (μ ⊗ₘ κ)) :
    Integrable (fun x ↦ ∫ y, ‖f (x, y)‖ ∂(κ x)) μ :=
  hf.integral_norm_compProd

theorem _root_.MeasureTheory.Integrable.integral_compProd' [NormedAddCommGroup E]
    [SFinite μ] [IsSFiniteKernel κ] ⦃f : α × β → E⦄ [NormedSpace ℝ E]
    (hf : Integrable f (μ ⊗ₘ κ)) :
    Integrable (fun x ↦ ∫ y, f (x, y) ∂(κ x)) μ :=
  hf.integral_compProd

variable [MeasurableSpace.CountableOrCountablyGenerated α β]

lemma f_compProd_congr (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ η : Kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η] :
    ∀ᵐ a ∂ν, (fun b ↦ f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) (a, b)).toReal)
      =ᵐ[η a] fun b ↦ f ((∂μ/∂ν) a * (∂κ a/∂η a) b).toReal := by
  have h_eq_compProd := Kernel.rnDeriv_measure_compProd' μ ν κ η
  filter_upwards [h_eq_compProd] with a ha
  filter_upwards [ha] with b hb
  rw [hb]

lemma integral_f_compProd_congr (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ η : Kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η] :
    (fun a ↦ ∫ b, f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) (a, b)).toReal ∂(η a))
      =ᵐ[ν] fun a ↦ ∫ b, f ((∂μ/∂ν) a * (∂κ a/∂η a) b).toReal ∂(η a) := by
  filter_upwards [f_compProd_congr μ ν κ η] with a ha using integral_congr_ae ha

lemma integral_f_compProd_right_congr (μ : Measure α) [IsFiniteMeasure μ]
    (κ η : Kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η] :
    (fun a ↦ ∫ b, f ((∂μ ⊗ₘ κ/∂μ ⊗ₘ η) (a, b)).toReal ∂(η a))
      =ᵐ[μ] fun a ↦ ∫ b, f ((∂κ a/∂η a) b).toReal ∂(η a) := by
  filter_upwards [integral_f_compProd_congr μ μ κ η, Measure.rnDeriv_self μ] with a ha h_eq_one
  rw [ha]
  simp_rw [h_eq_one, one_mul]

lemma integral_f_compProd_left_congr (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ : Kernel α β) [IsFiniteKernel κ]  :
    (fun a ↦ ∫ b, f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ κ) (a, b)).toReal ∂(κ a))
      =ᵐ[ν] fun a ↦ (κ a Set.univ).toReal * f ((∂μ/∂ν) a).toReal := by
  filter_upwards [integral_f_compProd_congr (f := f) μ ν κ κ] with a ha
  have h_one := (κ a).rnDeriv_self
  rw [ha, ← smul_eq_mul,  ← integral_const]
  refine integral_congr_ae ?_
  filter_upwards [h_one] with b hb
  simp [hb]

lemma integrable_f_rnDeriv_of_integrable_compProd [IsFiniteMeasure μ] [IsFiniteKernel κ]
    [IsFiniteKernel η] (hf : StronglyMeasurable f)
    (hf_int : Integrable (fun x ↦ f ((μ ⊗ₘ κ).rnDeriv (μ ⊗ₘ η) x).toReal) (μ ⊗ₘ η)) :
    ∀ᵐ a ∂μ, Integrable (fun x ↦ f ((κ a).rnDeriv (η a) x).toReal) (η a) := by
  rw [Measure.integrable_compProd_iff] at hf_int
  swap
  · exact (hf.comp_measurable (Measure.measurable_rnDeriv _ _).ennreal_toReal).aestronglyMeasurable
  have h := Kernel.rnDeriv_measure_compProd_right' μ κ η
  filter_upwards [h, hf_int.1] with a ha1 ha2
  refine (integrable_congr ?_).mp ha2
  filter_upwards [ha1] with b hb
  rw [hb]

lemma integrable_f_rnDeriv_compProd_iff [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [IsFiniteKernel κ] [IsFiniteKernel η] (hf : StronglyMeasurable f)
    (h_cvx : ConvexOn ℝ (Set.Ici 0) f) :
    Integrable (fun x ↦ f ((μ ⊗ₘ κ).rnDeriv (ν ⊗ₘ η) x).toReal) (ν ⊗ₘ η)
      ↔ (∀ᵐ a ∂ν, Integrable (fun x ↦ f ((∂μ/∂ν) a * (∂κ a/∂η a) x).toReal) (η a))
        ∧ Integrable (fun a ↦ ∫ b, f ((∂μ/∂ν) a * (∂κ a/∂η a) b).toReal ∂(η a)) ν := by
  have h_ae_eq : ∀ᵐ a ∂ν, (fun y ↦ f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) (a, y)).toReal)
      =ᵐ[η a] fun x ↦ f ((∂μ/∂ν) a * (∂κ a/∂η a) x).toReal := f_compProd_congr μ ν κ η
  refine ⟨fun h ↦ ?_, fun ⟨h1, h2⟩ ↦ ?_⟩
  · have h_int := h.integral_compProd'
    rw [Measure.integrable_compProd_iff] at h
    swap
    · exact (hf.comp_measurable
        (Measure.measurable_rnDeriv _ _).ennreal_toReal).aestronglyMeasurable
    constructor
    · filter_upwards [h.1, h_ae_eq] with a ha1 ha2
      exact (integrable_congr ha2).mp ha1
    · refine (integrable_congr ?_).mp h_int
      filter_upwards [h_ae_eq] with a ha
      exact integral_congr_ae ha
  · rw [Measure.integrable_compProd_iff]
    swap
    · exact (hf.comp_measurable
        (Measure.measurable_rnDeriv _ _).ennreal_toReal).aestronglyMeasurable
    constructor
    · filter_upwards [h1, h_ae_eq] with a ha1 ha2
      exact (integrable_congr ha2).mpr ha1
    · rw [← integrable_congr (integral_f_compProd_congr μ ν κ η)] at h2
      -- todo: cut into two parts, depending on sign of f.
      -- on the positive part, use h2.
      -- on the negative part, use `f x ≥ a * x + b` by convexity, then since both measures are
      -- finite the integral is finite.
      sorry

lemma integrable_f_rnDeriv_compProd_right_iff [IsFiniteMeasure μ]
    [IsFiniteKernel κ] [IsFiniteKernel η] (hf : StronglyMeasurable f)
    (h_cvx : ConvexOn ℝ (Set.Ici 0) f) :
    Integrable (fun x ↦ f ((μ ⊗ₘ κ).rnDeriv (μ ⊗ₘ η) x).toReal) (μ ⊗ₘ η)
      ↔ (∀ᵐ a ∂μ, Integrable (fun x ↦ f ((∂κ a/∂η a) x).toReal) (η a))
        ∧ Integrable (fun a ↦ ∫ b, f ((∂κ a/∂η a) b).toReal ∂(η a)) μ := by
  rw [integrable_f_rnDeriv_compProd_iff hf h_cvx]
  have h_one := μ.rnDeriv_self
  refine ⟨fun ⟨h1, h2⟩ ↦ ⟨?_, ?_⟩, fun ⟨h1, h2⟩ ↦ ⟨?_, ?_⟩⟩
  · filter_upwards [h1, h_one] with a ha1 ha2
    simpa [ha2] using ha1
  · refine (integrable_congr ?_).mpr h2
    filter_upwards [h_one] with a ha
    simp [ha]
  · filter_upwards [h1, h_one] with a ha1 ha2
    simpa [ha2] using ha1
  · refine (integrable_congr ?_).mpr h2
    filter_upwards [h_one] with a ha
    simp [ha]

end Integrable

lemma compProd_apply_toReal [SFinite μ] [IsFiniteKernel κ]
    {s : Set (α × β)} (hs : MeasurableSet s) :
    ((μ ⊗ₘ κ) s).toReal = ∫ x, (κ x (Prod.mk x ⁻¹' s)).toReal ∂μ := by
  rw [Measure.compProd_apply hs, integral_eq_lintegral_of_nonneg_ae]
  rotate_left
  · exact ae_of_all _ (fun x ↦ by positivity)
  · exact (Kernel.measurable_kernel_prod_mk_left hs).ennreal_toReal.aestronglyMeasurable
  congr with x
  rw [ENNReal.ofReal_toReal (measure_ne_top _ _)]

lemma compProd_univ_toReal [SFinite μ] [IsFiniteKernel κ] :
    ((μ ⊗ₘ κ) Set.univ).toReal = ∫ x, (κ x Set.univ).toReal ∂μ :=
  compProd_apply_toReal MeasurableSet.univ

lemma Measure.compProd_apply_univ [SFinite μ] [IsMarkovKernel κ] :
    (μ ⊗ₘ κ) Set.univ = μ (Set.univ) := by
  rw [Measure.compProd_apply MeasurableSet.univ]
  simp

lemma Measure.comp_apply_univ [IsMarkovKernel κ] :
    (κ ∘ₘ μ) Set.univ = μ (Set.univ) := by
  rw [Measure.bind_apply MeasurableSet.univ (Kernel.measurable κ)]
  simp

instance [SFinite μ] [IsSFiniteKernel κ] : SFinite (κ ∘ₘ μ) := by
  rw [Measure.comp_eq_snd_compProd]
  infer_instance

instance [IsFiniteMeasure μ] [IsFiniteKernel κ] : IsFiniteMeasure (κ ∘ₘ μ) := by
  rw [Measure.comp_eq_snd_compProd]
  infer_instance

instance [IsProbabilityMeasure μ] [IsMarkovKernel κ] : IsProbabilityMeasure (κ ∘ₘ μ) := by
  rw [Measure.comp_eq_snd_compProd]
  infer_instance

--this is already PRed to mathlib, see #14471, when it gets merged and we bump, remove this
instance [hμ : SFinite μ] (a : ℝ≥0∞) : SFinite (a • μ) := by
  sorry

lemma Measure.compProd_smul_left (a : ℝ≥0∞) [SFinite μ] [IsSFiniteKernel κ] :
    (a • μ) ⊗ₘ κ = a • (μ ⊗ₘ κ) := by
  ext s hs
  simp only [Measure.compProd_apply hs, lintegral_smul_measure, Measure.smul_apply, smul_eq_mul]

lemma Measure.comp_smul_left (a : ℝ≥0∞) : κ ∘ₘ (a • μ) = a • (κ ∘ₘ μ) := by
  ext s hs
  simp only [Measure.bind_apply hs (Kernel.measurable _), lintegral_smul_measure,
    Measure.smul_apply, smul_eq_mul]

end ProbabilityTheory
