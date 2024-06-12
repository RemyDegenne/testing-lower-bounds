/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
import TestingLowerBounds.ForMathlib.RadonNikodym
import TestingLowerBounds.Kernel.Basic
import TestingLowerBounds.Kernel.Monoidal
import TestingLowerBounds.ForMathlib.SFinite


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
  {μ ν : Measure α} {κ η : kernel α β} {f g : ℝ → ℝ}

/-- Composition of a measure and a kernel.

Defined using `MeasureTheory.Measure.bind` -/
scoped[ProbabilityTheory] infixl:100 " ∘ₘ " => MeasureTheory.Measure.bind

lemma Measure.comp_assoc {μ : Measure α} [SFinite μ]
    {κ : kernel α β} [IsSFiniteKernel κ] {η : kernel β γ} [IsSFiniteKernel η] :
    μ ∘ₘ κ ∘ₘ η = μ ∘ₘ (η ∘ₖ κ) :=
  Measure.bind_bind (kernel.measurable _) (kernel.measurable _)

lemma Measure.comp_deterministic_eq_map {f : α → β} (hf : Measurable f) :
    μ ∘ₘ kernel.deterministic f hf = μ.map f := by
  ext s hs
  rw [Measure.bind_apply hs (kernel.measurable _), Measure.map_apply hf hs]
  simp only [kernel.deterministic_apply' hf _ hs]
  rw [lintegral_indicator_const_comp hf hs, one_mul]

lemma Measure.comp_id : μ ∘ₘ kernel.id = μ := by
  rw [kernel.id, Measure.comp_deterministic_eq_map, Measure.map_id]

lemma Measure.comp_eq_snd_compProd (μ : Measure α) [SFinite μ]
    (κ : kernel α β) [IsSFiniteKernel κ] :
    μ ∘ₘ κ = (μ ⊗ₘ κ).snd := by
  ext s hs
  rw [Measure.bind_apply hs (kernel.measurable _), Measure.snd_apply hs,
    Measure.compProd_apply]
  · rfl
  · exact measurable_snd hs

lemma Measure.fst_compProd (μ : Measure α) [SFinite μ] (κ : kernel α β) [IsMarkovKernel κ] :
    (μ ⊗ₘ κ).fst = μ := by
  ext s
  rw [Measure.compProd, Measure.fst, ← kernel.fst_apply, kernel.fst_compProd, kernel.const_apply]

lemma Measure.snd_compProd (μ : Measure α) [SFinite μ] (κ : kernel α β) [IsSFiniteKernel κ] :
    (μ ⊗ₘ κ).snd = μ ∘ₘ κ := (Measure.comp_eq_snd_compProd μ κ).symm

lemma Measure.compProd_eq_comp (μ : Measure α) [SFinite μ] (κ : kernel α β) [IsSFiniteKernel κ] :
    μ ⊗ₘ κ = μ ∘ₘ (kernel.id ×ₖ κ) := by
  rw [Measure.compProd, kernel.compProd_prodMkLeft_eq_comp]
  rfl

lemma Measure.compProd_id [SFinite μ] : μ ⊗ₘ kernel.id = μ.map (fun x ↦ (x, x)) := by
  rw [Measure.compProd_eq_comp, kernel.id, kernel.deterministic_prod_deterministic,
    Measure.comp_deterministic_eq_map]
  rfl

/-- The composition product of a measure and a constant kernel is the product between the two
measures. -/
@[simp]
lemma Measure.compProd_const {ν : Measure β} [SFinite μ] [SFinite ν] :
    μ ⊗ₘ (kernel.const α ν) = μ.prod ν := by
  ext s hs
  rw [Measure.compProd_apply hs, Measure.prod_apply hs]
  simp_rw [kernel.const_apply]

lemma Measure.compProd_apply_toReal [SFinite μ] [IsFiniteKernel κ]
    {s : Set (α × β)} (hs : MeasurableSet s) :
    ((μ ⊗ₘ κ) s).toReal = ∫ x, (κ x (Prod.mk x ⁻¹' s)).toReal ∂μ := by
  rw [Measure.compProd_apply hs, integral_eq_lintegral_of_nonneg_ae]
  rotate_left
  · exact ae_of_all _ (fun x ↦ by positivity)
  · exact (kernel.measurable_kernel_prod_mk_left hs).ennreal_toReal.aestronglyMeasurable
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

instance {μ : Measure α} [SFinite μ] {κ : kernel α β} [IsSFiniteKernel κ] : SFinite (μ ∘ₘ κ) := by
  rw [Measure.comp_eq_snd_compProd]
  infer_instance

instance {μ : Measure α} [IsFiniteMeasure μ] {κ : kernel α β} [IsFiniteKernel κ] :
    IsFiniteMeasure (μ ∘ₘ κ) := by
  rw [Measure.comp_eq_snd_compProd]
  infer_instance

instance {μ : Measure α} [IsProbabilityMeasure μ] {κ : kernel α β} [IsMarkovKernel κ] :
    IsProbabilityMeasure (μ ∘ₘ κ) := by
  rw [Measure.comp_eq_snd_compProd]
  infer_instance

@[simp]
lemma Measure.fst_map_swap {μ : Measure (α × β)} : (μ.map Prod.swap).fst = μ.snd := by
  rw [Measure.fst, Measure.map_map measurable_fst measurable_swap]
  congr

@[simp]
lemma Measure.snd_map_swap {μ : Measure (α × β)} : (μ.map Prod.swap).snd = μ.fst := by
  rw [Measure.snd, Measure.map_map measurable_snd measurable_swap]
  congr

@[simp]
lemma Measure.fst_swap_compProd [SFinite μ] [IsSFiniteKernel κ] :
    ((μ ⊗ₘ κ).map Prod.swap).fst = μ ∘ₘ κ := by
  rw [Measure.comp_eq_snd_compProd]
  simp

section ParallelComp

namespace kernel

variable {δ : Type*} {mδ : MeasurableSpace δ}

lemma _root_.MeasureTheory.Measure.prod_comp_right
    (μ : Measure α) [SFinite μ] (ν : Measure β) [SFinite ν]
    (κ : kernel β γ) [IsSFiniteKernel κ] :
    μ.prod (ν ∘ₘ κ) = (μ.prod ν) ∘ₘ (kernel.id ∥ₖ κ) := by
  ext s hs
  rw [Measure.prod_apply hs, Measure.bind_apply hs (kernel.measurable _)]
  simp_rw [Measure.bind_apply (measurable_prod_mk_left hs) (kernel.measurable _)]
  rw [MeasureTheory.lintegral_prod]
  swap; · exact (kernel.measurable_coe _ hs).aemeasurable
  congr with a
  congr with b
  rw [parallelComp_apply, kernel.id_apply, Measure.prod_apply hs, lintegral_dirac']
  exact measurable_measure_prod_mk_left hs

lemma _root_.MeasureTheory.Measure.prod_comp_left
    (μ : Measure α) [SFinite μ] (ν : Measure β) [SFinite ν]
    (κ : kernel α γ) [IsSFiniteKernel κ] :
    (μ ∘ₘ κ).prod ν = (μ.prod ν) ∘ₘ (κ ∥ₖ kernel.id) := by
  have h1 : (μ ∘ₘ κ).prod ν = (ν.prod (μ ∘ₘ κ)).map Prod.swap := by
    rw [Measure.prod_swap]
  have h2 : (μ.prod ν) ∘ₘ (κ ∥ₖ kernel.id) = ((ν.prod μ) ∘ₘ (kernel.id ∥ₖ κ)).map Prod.swap := by
    calc (μ.prod ν) ∘ₘ (κ ∥ₖ kernel.id)
    _ = ((ν.prod μ).map Prod.swap) ∘ₘ (κ ∥ₖ kernel.id) := by rw [Measure.prod_swap]
    _ = (ν.prod μ) ∘ₘ (swap _ _) ∘ₘ (κ ∥ₖ kernel.id) := by
      rw [swap, Measure.comp_deterministic_eq_map]
    _ = (ν.prod μ) ∘ₘ (kernel.id ∥ₖ κ) ∘ₘ (swap _ _) := by
      rw [Measure.comp_assoc, Measure.comp_assoc, swap_parallelComp]
    _ = ((ν.prod μ) ∘ₘ (kernel.id ∥ₖ κ)).map Prod.swap := by
      rw [swap, Measure.comp_deterministic_eq_map]
  rw [← Measure.prod_comp_right, ← h1] at h2
  exact h2.symm

lemma parallelComp_comp_right {α' : Type*} {_ : MeasurableSpace α'}
    (κ : kernel α β) [IsSFiniteKernel κ]
    (η : kernel α' γ) [IsSFiniteKernel η] (ξ : kernel γ δ) [IsSFiniteKernel ξ] :
    κ ∥ₖ (ξ ∘ₖ η) = (kernel.id ∥ₖ ξ) ∘ₖ (κ ∥ₖ η) := by
  ext a
  rw [parallelComp_apply, comp_apply, comp_apply, parallelComp_apply, Measure.prod_comp_right]

lemma parallelComp_comp_left {α' : Type*} {_ : MeasurableSpace α'}
    (κ : kernel α β) [IsSFiniteKernel κ]
    (η : kernel α' γ) [IsSFiniteKernel η] (ξ : kernel γ δ) [IsSFiniteKernel ξ] :
    (ξ ∘ₖ η) ∥ₖ κ = (ξ ∥ₖ kernel.id) ∘ₖ (η ∥ₖ κ) := by
  ext a
  rw [parallelComp_apply, comp_apply, comp_apply, parallelComp_apply, Measure.prod_comp_left]

lemma parallelComp_comm (κ : kernel α β) [IsSFiniteKernel κ] (η : kernel γ δ) [IsSFiniteKernel η] :
    (kernel.id ∥ₖ κ) ∘ₖ (η ∥ₖ kernel.id) = (η ∥ₖ kernel.id) ∘ₖ (kernel.id ∥ₖ κ) := by
  rw [← parallelComp_comp_right, ← parallelComp_comp_left, comp_id, comp_id]

end kernel

end ParallelComp

section SingularPart

lemma singularPart_compProd'' [MeasurableSpace.CountableOrCountablyGenerated α β]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ η : kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η] :
    (μ ⊗ₘ κ).singularPart (ν ⊗ₘ η)
      = μ.singularPart ν ⊗ₘ kernel.withDensity η (kernel.rnDeriv κ η)
        + μ.singularPart ν ⊗ₘ kernel.singularPart κ η
        + ν.withDensity (∂μ/∂ν) ⊗ₘ kernel.singularPart κ η := by
  conv_lhs => rw [← kernel.rnDeriv_add_singularPart κ η, Measure.compProd_add_right,
    μ.haveLebesgueDecomposition_add ν]
  simp_rw [Measure.compProd_add_left, Measure.singularPart_add]
  have : (ν.withDensity (∂μ/∂ν) ⊗ₘ kernel.withDensity η (kernel.rnDeriv κ η)).singularPart
      (ν ⊗ₘ η) = 0 := by
    refine Measure.singularPart_eq_zero_of_ac (kernel.Measure.absolutelyContinuous_compProd ?_ ?_)
    · exact withDensity_absolutelyContinuous _ _
    · exact ae_of_all _ (kernel.withDensity_absolutelyContinuous _)
  rw [this, add_zero, ← add_assoc]
  congr
  · rw [Measure.singularPart_eq_self]
    exact kernel.Measure.mutuallySingular_compProd_left (Measure.mutuallySingular_singularPart μ ν)
      (kernel.withDensity η (kernel.rnDeriv κ η)) η
  · rw [Measure.singularPart_eq_self]
    exact kernel.Measure.mutuallySingular_compProd_left (Measure.mutuallySingular_singularPart μ ν)
      (kernel.singularPart κ η) η
  · rw [Measure.singularPart_eq_self]
    exact kernel.Measure.mutuallySingular_compProd_right (ν.withDensity (∂μ/∂ν)) ν
      (eventually_of_forall <| kernel.mutuallySingular_singularPart _ _)

lemma singularPart_compProd [MeasurableSpace.CountableOrCountablyGenerated α β]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ η : kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η] :
    (μ ⊗ₘ κ).singularPart (ν ⊗ₘ η)
      = μ.singularPart ν ⊗ₘ kernel.withDensity η (kernel.rnDeriv κ η)
        + μ ⊗ₘ kernel.singularPart κ η := by
  rw [singularPart_compProd'']
  have : (μ ⊗ₘ kernel.singularPart κ η) = (μ.singularPart ν ⊗ₘ kernel.singularPart κ η)
        + (ν.withDensity (∂μ/∂ν) ⊗ₘ kernel.singularPart κ η) := by
    rw [← Measure.compProd_add_left, ← μ.haveLebesgueDecomposition_add ν]
  rw [this]
  abel

lemma singularPart_compProd' [MeasurableSpace.CountableOrCountablyGenerated α β]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ η : kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η] :
    (μ ⊗ₘ κ).singularPart (ν ⊗ₘ η)
      = μ.singularPart ν ⊗ₘ κ + ν.withDensity (∂μ/∂ν) ⊗ₘ kernel.singularPart κ η := by
  rw [singularPart_compProd'']
  have : μ.singularPart ν ⊗ₘ κ
      = μ.singularPart ν ⊗ₘ kernel.withDensity η (kernel.rnDeriv κ η)
        + μ.singularPart ν ⊗ₘ kernel.singularPart κ η := by
    rw [← Measure.compProd_add_right]
    congr
    exact (kernel.rnDeriv_add_singularPart κ η).symm
  rw [this]

lemma singularPart_compProd_left [MeasurableSpace.CountableOrCountablyGenerated α β]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ : kernel α β) [IsFiniteKernel κ] :
    (μ ⊗ₘ κ).singularPart (ν ⊗ₘ κ) = μ.singularPart ν ⊗ₘ κ := by
  rw [singularPart_compProd', kernel.singularPart_self]
  simp [Measure.singularPart_zero]

lemma singularPart_compProd_right [MeasurableSpace.CountableOrCountablyGenerated α β]
    (μ : Measure α) [IsFiniteMeasure μ]
    (κ η : kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η] :
    (μ ⊗ₘ κ).singularPart (μ ⊗ₘ η) = μ ⊗ₘ kernel.singularPart κ η := by
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
    [SFinite μ] [IsSFiniteKernel κ] ⦃f : α × β → E⦄ [NormedSpace ℝ E] [CompleteSpace E]
    (hf : Integrable f (μ ⊗ₘ κ)) :
    Integrable (fun x ↦ ∫ y, f (x, y) ∂(κ x)) μ :=
  hf.integral_compProd

variable [MeasurableSpace.CountableOrCountablyGenerated α β]

lemma f_compProd_congr (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ η : kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η] :
    ∀ᵐ a ∂ν, (fun b ↦ f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) (a, b)).toReal)
      =ᵐ[η a] fun b ↦ f ((∂μ/∂ν) a * (∂κ a/∂η a) b).toReal := by
  have h_eq_compProd := kernel.rnDeriv_measure_compProd' μ ν κ η
  filter_upwards [h_eq_compProd] with a ha
  filter_upwards [ha] with b hb
  rw [hb]

lemma integral_f_compProd_congr (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ η : kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η] :
    (fun a ↦ ∫ b, f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) (a, b)).toReal ∂(η a))
      =ᵐ[ν] fun a ↦ ∫ b, f ((∂μ/∂ν) a * (∂κ a/∂η a) b).toReal ∂(η a) := by
  filter_upwards [f_compProd_congr μ ν κ η] with a ha using integral_congr_ae ha

lemma integral_f_compProd_right_congr (μ : Measure α) [IsFiniteMeasure μ]
    (κ η : kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η] :
    (fun a ↦ ∫ b, f ((∂μ ⊗ₘ κ/∂μ ⊗ₘ η) (a, b)).toReal ∂(η a))
      =ᵐ[μ] fun a ↦ ∫ b, f ((∂κ a/∂η a) b).toReal ∂(η a) := by
  filter_upwards [integral_f_compProd_congr μ μ κ η, Measure.rnDeriv_self μ] with a ha h_eq_one
  rw [ha]
  simp_rw [h_eq_one, one_mul]

lemma integral_f_compProd_left_congr (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ : kernel α β) [IsFiniteKernel κ]  :
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
  have h := kernel.rnDeriv_measure_compProd_right' μ κ η
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

/--The composition product of a measure and a constant kernel is the product between the two
measures.-/
@[simp]
lemma compProd_const {ν : Measure β} [SFinite ν] [SFinite μ] :
    μ ⊗ₘ (kernel.const α ν) = μ.prod ν := by
  ext s hs
  rw [Measure.compProd_apply hs, Measure.prod_apply hs]
  simp_rw [kernel.const_apply]

lemma compProd_apply_toReal [SFinite μ] [IsFiniteKernel κ]
    {s : Set (α × β)} (hs : MeasurableSet s) :
    ((μ ⊗ₘ κ) s).toReal = ∫ x, (κ x (Prod.mk x ⁻¹' s)).toReal ∂μ := by
  rw [Measure.compProd_apply hs, integral_eq_lintegral_of_nonneg_ae]
  rotate_left
  · exact ae_of_all _ (fun x ↦ by positivity)
  · exact (kernel.measurable_kernel_prod_mk_left hs).ennreal_toReal.aestronglyMeasurable
  congr with x
  rw [ENNReal.ofReal_toReal (measure_ne_top _ _)]

lemma compProd_univ_toReal [SFinite μ] [IsFiniteKernel κ] :
    ((μ ⊗ₘ κ) Set.univ).toReal = ∫ x, (κ x Set.univ).toReal ∂μ :=
  compProd_apply_toReal MeasurableSet.univ

instance [SFinite μ] [IsSFiniteKernel κ] : SFinite (μ ∘ₘ κ) := by
  rw [Measure.comp_eq_snd_compProd]
  infer_instance

instance [IsFiniteMeasure μ] [IsFiniteKernel κ] : IsFiniteMeasure (μ ∘ₘ κ) := by
  rw [Measure.comp_eq_snd_compProd]
  infer_instance

instance [IsProbabilityMeasure μ] [IsMarkovKernel κ] : IsProbabilityMeasure (μ ∘ₘ κ) := by
  rw [Measure.comp_eq_snd_compProd]
  infer_instance

end ProbabilityTheory
