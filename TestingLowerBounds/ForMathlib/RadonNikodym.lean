/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
import Mathlib.Probability.Kernel.MeasureCompProd
import Mathlib.Probability.Kernel.RadonNikodym
import TestingLowerBounds.ForMathlib.KernelFstSnd
import TestingLowerBounds.ForMathlib.CountableOrCountablyGenerated

/-!
# Radon-Nikodym derivative and Lebesgue decomposition for kernels

-/

open MeasureTheory Set Filter

open scoped NNReal ENNReal MeasureTheory Topology ProbabilityTheory

namespace ProbabilityTheory.kernel

variable {α γ : Type*} {mα : MeasurableSpace α} {mγ : MeasurableSpace γ}
  [MeasurableSpace.CountableOrCountablyGenerated α γ] {κ η : kernel α γ}

lemma singularPart_self (κ : kernel α γ) [IsFiniteKernel κ] :
    kernel.singularPart κ κ = 0 := by
  ext a : 1
  rw [zero_apply, singularPart_eq_zero_iff_absolutelyContinuous]

-- ok
lemma Measure.absolutelyContinuous_compProd_left {μ ν : Measure α} [SFinite μ] [SFinite ν]
    (hμν : μ ≪ ν) (κ : kernel α γ) [IsSFiniteKernel κ]  :
    μ ⊗ₘ κ ≪ ν ⊗ₘ κ := by
  refine Measure.AbsolutelyContinuous.mk fun s hs hs_zero ↦ ?_
  rw [Measure.compProd_apply hs, lintegral_eq_zero_iff (measurable_kernel_prod_mk_left hs)]
    at hs_zero ⊢
  exact hμν.ae_eq hs_zero

-- ok
lemma Measure.absolutelyContinuous_compProd_right (μ : Measure α) {κ η : kernel α γ}
    [SFinite μ] [IsSFiniteKernel κ] [IsSFiniteKernel η]
    (hκη : ∀ᵐ a ∂μ, κ a ≪ η a) :
    μ ⊗ₘ κ ≪ μ ⊗ₘ η := by
  refine Measure.AbsolutelyContinuous.mk fun s hs hs_zero ↦ ?_
  rw [Measure.compProd_apply hs, lintegral_eq_zero_iff (measurable_kernel_prod_mk_left hs)]
    at hs_zero ⊢
  filter_upwards [hs_zero, hκη] with a ha_zero ha_ac using ha_ac ha_zero

-- PRed a version with `∀ᵐ a ∂ν, κ a ≪ η a`
lemma Measure.absolutelyContinuous_compProd {μ ν : Measure α} {κ η : kernel α γ}
    [SFinite μ] [SFinite ν] [IsSFiniteKernel κ] [IsSFiniteKernel η]
    (hμν : μ ≪ ν) (hκη : ∀ᵐ a ∂μ, κ a ≪ η a) :
    μ ⊗ₘ κ ≪ ν ⊗ₘ η :=
  (Measure.absolutelyContinuous_compProd_right μ hκη).trans
    (Measure.absolutelyContinuous_compProd_left hμν _)

lemma Measure.mutuallySingular_compProd_left {μ ν : Measure α} [SFinite μ] [SFinite ν]
    (hμν : μ ⟂ₘ ν) (κ η : kernel α γ) [IsSFiniteKernel κ] [IsSFiniteKernel η] :
    μ ⊗ₘ κ ⟂ₘ ν ⊗ₘ η := by
  let s := hμν.nullSet
  have hs_prod : MeasurableSet (s ×ˢ (univ : Set γ)) :=
    hμν.measurableSet_nullSet.prod MeasurableSet.univ
  refine ⟨s ×ˢ univ, hs_prod, ?_⟩
  rw [Measure.compProd_apply_prod hμν.measurableSet_nullSet MeasurableSet.univ, compl_prod_eq_union]
  simp only [Measure.MutuallySingular.restrict_nullSet, lintegral_zero_measure, compl_univ,
    prod_empty, union_empty, true_and]
  rw [Measure.compProd_apply_prod hμν.measurableSet_nullSet.compl MeasurableSet.univ]
  simp

lemma Measure.mutuallySingular_compProd_right (μ ν : Measure α) [SFinite μ] [SFinite ν]
    {κ η : kernel α γ} [IsFiniteKernel κ] [IsFiniteKernel η] (hκη : ∀ᵐ a ∂μ, κ a ⟂ₘ η a) :
    μ ⊗ₘ κ ⟂ₘ ν ⊗ₘ η := by
  let s := mutuallySingularSet κ η
  have hs : MeasurableSet s := measurableSet_mutuallySingularSet κ η
  symm
  refine ⟨s, hs, ?_⟩
  rw [Measure.compProd_apply hs, Measure.compProd_apply hs.compl]
  have h_eq (a : α) : Prod.mk a ⁻¹' s = mutuallySingularSetSlice κ η a := rfl
  have h1 : ∀ a, η a (Prod.mk a ⁻¹' s) = 0 := by
    intro a
    rw [h_eq, measure_mutuallySingularSetSlice]
  have h2 : ∀ᵐ a ∂ μ, κ a (Prod.mk a ⁻¹' s)ᶜ = 0 := by
    filter_upwards [hκη] with a ha
    rw [h_eq, ← withDensity_rnDeriv_eq_zero_iff_measure_eq_zero κ η a,
      withDensity_rnDeriv_eq_zero_iff_mutuallySingular]
    exact ha
  simp [h1, lintegral_congr_ae h2]

lemma Measure.mutuallySingular_compProd_right' (μ ν : Measure α) [SFinite μ] [SFinite ν]
    {κ η : kernel α γ} [IsFiniteKernel κ] [IsFiniteKernel η] (hκη : ∀ᵐ a ∂ν, κ a ⟂ₘ η a) :
    μ ⊗ₘ κ ⟂ₘ ν ⊗ₘ η := by
  rw [Measure.MutuallySingular.comm]
  apply Measure.mutuallySingular_compProd_right
  simp_rw [Measure.MutuallySingular.comm, hκη]

lemma Measure.mutuallySingular_of_mutuallySingular_compProd {μ ν ξ : Measure α} {κ η : kernel α γ}
    [SFinite μ] [SFinite ν] [IsSFiniteKernel κ] [IsSFiniteKernel η]
    (h : μ ⊗ₘ κ ⟂ₘ ν ⊗ₘ η) (hμ : ξ ≪ μ) (hν : ξ ≪ ν) :
    ∀ᵐ x ∂ξ, κ x ⟂ₘ η x := by
  let s := h.nullSet
  have hs := h.measurableSet_nullSet
  have hμ_zero:= h.measure_nullSet
  have hν_zero := h.measure_compl_nullSet
  rw [Measure.compProd_apply, MeasureTheory.lintegral_eq_zero_iff'] at hμ_zero hν_zero
  rotate_left
  · exact measurable_kernel_prod_mk_left hs.compl |>.aemeasurable
  · exact measurable_kernel_prod_mk_left hs |>.aemeasurable
  · exact hs.compl
  · exact hs
  filter_upwards [hμ hμ_zero, hν hν_zero] with x hxμ hxν
  exact ⟨Prod.mk x ⁻¹' s, measurable_prod_mk_left hs, ⟨hxμ, hxν⟩⟩

lemma Measure.mutuallySingular_compProd_iff_of_same_left (μ : Measure α) [SFinite μ]
    (κ η : kernel α γ) [IsFiniteKernel κ] [IsFiniteKernel η] :
    μ ⊗ₘ κ ⟂ₘ μ ⊗ₘ η ↔ ∀ᵐ a ∂μ, κ a ⟂ₘ η a := by
  refine ⟨fun h ↦ ?_, fun h ↦ mutuallySingular_compProd_right _ _ h⟩
  exact mutuallySingular_of_mutuallySingular_compProd h (fun _ a ↦ a) (fun _ a ↦ a)

lemma Measure.mutuallySingular_compProd_iff_of_same_right (μ ν : Measure α) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (κ : kernel α γ) [IsFiniteKernel κ] [hκ : ∀ x, NeZero (κ x)] :
    μ ⊗ₘ κ ⟂ₘ ν ⊗ₘ κ ↔ μ ⟂ₘ ν := by
  refine ⟨fun h ↦ ?_, fun h ↦ mutuallySingular_compProd_left h _ _⟩
  rw [← Measure.withDensity_rnDeriv_eq_zero]
  have hh := mutuallySingular_of_mutuallySingular_compProd h ?_ ?_ (ξ  := ν.withDensity (∂μ/∂ν))
  rotate_left
  · exact Measure.absolutelyContinuous_of_le (Measure.withDensity_rnDeriv_le μ ν)
  · exact MeasureTheory.withDensity_absolutelyContinuous _ _
  simp_rw [Measure.MutuallySingular.self_iff, (hκ _).ne] at hh
  exact ae_eq_bot.mp (Filter.eventually_false_iff_eq_bot.mp hh)

lemma ae_compProd_of_ae_fst {μ : Measure α} (κ : kernel α γ)
    [SFinite μ] [IsSFiniteKernel κ] {p : α → Prop} (hp : MeasurableSet {x | p x})
    (h : ∀ᵐ a ∂μ, p a) :
    ∀ᵐ x ∂(μ ⊗ₘ κ), p x.1 := by
  refine ae_compProd_of_ae_ae (measurable_fst hp) ?_
  filter_upwards [h] with a ha
  simp [ha]

lemma ae_eq_compProd_of_ae_eq_fst {β : Type*} {_ : MeasurableSpace β} [AddGroup β]
    [MeasurableSingletonClass β] [MeasurableSub₂ β]
    (μ : Measure α) (κ : kernel α γ)
    [SFinite μ] [IsSFiniteKernel κ] {f g : α → β}
    (hf : Measurable f) (hg : Measurable g) (h : f =ᵐ[μ] g) :
    (fun p ↦ f p.1) =ᵐ[μ ⊗ₘ κ] (fun p ↦ g p.1) :=
  ae_compProd_of_ae_fst κ (measurableSet_eq_fun hf hg) h

lemma ae_eq_compProd_of_forall_ae_eq {β : Type*} {_ : MeasurableSpace β} [AddGroup β]
    [MeasurableSingletonClass β] [MeasurableSub₂ β]
    (μ : Measure α) (κ : kernel α γ)
    [SFinite μ] [IsSFiniteKernel κ] {f g : α → γ → β}
    (hf : Measurable (Function.uncurry f)) (hg : Measurable (Function.uncurry g))
    (h : ∀ a, f a =ᵐ[κ a] g a) :
    (fun p ↦ f p.1 p.2) =ᵐ[μ ⊗ₘ κ] (fun p ↦ g p.1 p.2) :=
  ae_compProd_of_ae_ae (measurableSet_eq_fun hf hg)
    (ae_of_all _ (fun a ↦ measure_mono_null (fun x ↦ by simp) (h a)))

lemma ENNReal.ae_eq_compProd_of_ae_eq_fst (μ : Measure α) (κ : kernel α γ)
    [SFinite μ] [IsSFiniteKernel κ] {f g : α → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) (h : f =ᵐ[μ] g) :
    (fun p ↦ f p.1) =ᵐ[μ ⊗ₘ κ] (fun p ↦ g p.1) :=
  ae_compProd_of_ae_fst κ (measurableSet_eq_fun' hf hg) h

lemma ENNReal.ae_eq_compProd_of_forall_ae_eq
    (μ : Measure α) (κ : kernel α γ)
    [SFinite μ] [IsSFiniteKernel κ] {f g : α → γ → ℝ≥0∞}
    (hf : Measurable (Function.uncurry f)) (hg : Measurable (Function.uncurry g))
    (h : ∀ a, f a =ᵐ[κ a] g a) :
    (fun p ↦ f p.1 p.2) =ᵐ[μ ⊗ₘ κ] (fun p ↦ g p.1 p.2) :=
  ae_compProd_of_ae_ae (measurableSet_eq_fun' hf hg)
    (ae_of_all _ (fun a ↦ measure_mono_null (fun x ↦ by simp) (h a)))

section Unique

variable {ξ : kernel α γ} {f : α → γ → ℝ≥0∞}

lemma eq_rnDeriv_measure [IsFiniteKernel η] (h : κ = kernel.withDensity η f + ξ)
    (hf : Measurable (Function.uncurry f)) (hξ : ∀ a, ξ a ⟂ₘ η a) (a : α) :
    f a =ᵐ[η a] ∂(κ a)/∂(η a) := by
  have : κ a = ξ a + (η a).withDensity (f a) := by
    rw [h, coeFn_add, Pi.add_apply, kernel.withDensity_apply _ hf, add_comm]
  exact (κ a).eq_rnDeriv₀ (hf.comp measurable_prod_mk_left).aemeasurable (hξ a) this

lemma eq_singularPart_measure [IsFiniteKernel η]
    (h : κ = kernel.withDensity η f + ξ)
    (hf : Measurable (Function.uncurry f)) (hξ : ∀ a, ξ a ⟂ₘ η a) (a : α) :
    ξ a = (κ a).singularPart (η a) := by
  have : κ a = ξ a + (η a).withDensity (f a) := by
    rw [h, coeFn_add, Pi.add_apply, kernel.withDensity_apply _ hf, add_comm]
  exact (κ a).eq_singularPart (hf.comp measurable_prod_mk_left) (hξ a) this

lemma rnDeriv_eq_rnDeriv_measure (κ ν : kernel α γ) [IsFiniteKernel κ] [IsFiniteKernel ν] (a : α) :
    rnDeriv κ ν a =ᵐ[ν a] ∂(κ a)/∂(ν a) :=
  eq_rnDeriv_measure (rnDeriv_add_singularPart κ ν).symm (measurable_rnDeriv κ ν)
    (mutuallySingular_singularPart κ ν) a

lemma singularPart_eq_singularPart_measure [IsFiniteKernel κ] [IsFiniteKernel η] (a : α) :
    singularPart κ η a = (κ a).singularPart (η a) :=
  eq_singularPart_measure (rnDeriv_add_singularPart κ η).symm (measurable_rnDeriv κ η)
    (mutuallySingular_singularPart κ η) a

lemma eq_rnDeriv [IsFiniteKernel κ] [IsFiniteKernel η] (h : κ = kernel.withDensity η f + ξ)
    (hf : Measurable (Function.uncurry f)) (hξ : ∀ a, ξ a ⟂ₘ η a) (a : α) :
    f a =ᵐ[η a] rnDeriv κ η a :=
  (eq_rnDeriv_measure h hf hξ a).trans (rnDeriv_eq_rnDeriv_measure _ _ a).symm

lemma eq_singularPart [IsFiniteKernel κ] [IsFiniteKernel η] (h : κ = kernel.withDensity η f + ξ)
    (hf : Measurable (Function.uncurry f)) (hξ : ∀ a, ξ a ⟂ₘ η a) (a : α) :
    ξ a = singularPart κ η a :=
  (eq_singularPart_measure h hf hξ a).trans (singularPart_eq_singularPart_measure a).symm

end Unique

lemma measurable_singularPart (κ η : kernel α γ) [IsFiniteKernel κ] [IsFiniteKernel η] :
    Measurable (fun a ↦ (κ a).singularPart (η a)) := by
  refine Measure.measurable_of_measurable_coe _ (fun s hs ↦ ?_)
  simp_rw [← kernel.singularPart_eq_singularPart_measure, kernel.singularPart_def κ η]
  exact kernel.measurable_coe _ hs

lemma rnDeriv_pos [IsFiniteKernel κ] [IsFiniteKernel η] {a : α} (ha : κ a ≪ η a) :
    ∀ᵐ x ∂(κ a), 0 < rnDeriv κ η a x := by
  filter_upwards [ha.ae_le (rnDeriv_eq_rnDeriv_measure κ η a), Measure.rnDeriv_pos ha] with x heq hpos
  rwa [heq]

lemma rnDeriv_ne_top (κ η : kernel α γ) [IsFiniteKernel κ] [IsFiniteKernel η] {a : α} :
    ∀ᵐ x ∂(η a), rnDeriv κ η a x ≠ ⊤ := by
  filter_upwards [rnDeriv_eq_rnDeriv_measure κ η a, Measure.rnDeriv_ne_top (κ a) _] with x heq htop
  rwa [heq]

lemma rnDeriv_toReal_pos [IsFiniteKernel κ] [IsFiniteKernel η] {a : α} (h : κ a ≪ η a) :
    ∀ᵐ x ∂(κ a), 0 < (rnDeriv κ η a x).toReal := by
  filter_upwards [rnDeriv_pos h, h.ae_le (rnDeriv_ne_top κ _)] with x h0 htop
  simp_all only [pos_iff_ne_zero, ne_eq, ENNReal.toReal_pos, not_false_eq_true, and_self]

instance instIsFiniteKernel_withDensity_rnDeriv [hκ : IsFiniteKernel κ] [IsFiniteKernel η] :
    IsFiniteKernel (withDensity η (rnDeriv κ η)) := by
  constructor
  refine ⟨hκ.bound, hκ.bound_lt_top, fun a ↦ ?_⟩
  rw [kernel.withDensity_apply', set_lintegral_univ]
  swap; · exact measurable_rnDeriv κ η
  rw [lintegral_congr_ae (rnDeriv_eq_rnDeriv_measure _ _ a), ← set_lintegral_univ]
  exact (Measure.set_lintegral_rnDeriv_le _).trans (measure_le_bound _ _ _)

instance instIsFiniteKernel_singularPart [hκ : IsFiniteKernel κ] [IsFiniteKernel η] :
    IsFiniteKernel (singularPart κ η) := by
  constructor
  refine ⟨hκ.bound, hκ.bound_lt_top, fun a ↦ ?_⟩
  have h : withDensity η (rnDeriv κ η) a univ + singularPart κ η a univ = κ a univ := by
    conv_rhs => rw [← rnDeriv_add_singularPart κ η]
    simp
  exact (self_le_add_left _ _).trans (h.le.trans (measure_le_bound _ _ _))

lemma rnDeriv_add (κ ν η : kernel α γ) [IsFiniteKernel κ] [IsFiniteKernel ν] [IsFiniteKernel η]
    (a : α) :
    rnDeriv (κ + ν) η a =ᵐ[η a] rnDeriv κ η a + rnDeriv ν η a := by
  filter_upwards [rnDeriv_eq_rnDeriv_measure (κ + ν) η a, rnDeriv_eq_rnDeriv_measure κ η a,
    rnDeriv_eq_rnDeriv_measure ν η a, Measure.rnDeriv_add (κ a) (ν a) (η a)] with x h1 h2 h3 h4
  rw [h1, Pi.add_apply, h2, h3, coeFn_add, Pi.add_apply, h4, Pi.add_apply]

lemma rnDeriv_singularPart (κ ν : kernel α γ) [IsFiniteKernel κ] [IsFiniteKernel ν] (a : α) :
    rnDeriv (singularPart κ ν) ν a =ᵐ[ν a] 0 := by
  filter_upwards [rnDeriv_eq_rnDeriv_measure (singularPart κ ν) ν a,
    (Measure.rnDeriv_eq_zero _ _).mpr (mutuallySingular_singularPart κ ν a)] with x h1 h2
  rw [h1, h2]

lemma withDensity_rnDeriv_eq
    {κ η : kernel α γ} [IsFiniteKernel κ] [IsFiniteKernel η] {a : α} (h : κ a ≪ η a) :
    kernel.withDensity η (kernel.rnDeriv κ η) a = κ a := by
  rw [kernel.withDensity_apply]
  swap; · exact kernel.measurable_rnDeriv _ _
  have h_ae := kernel.rnDeriv_eq_rnDeriv_measure κ η a
  rw [MeasureTheory.withDensity_congr_ae h_ae, Measure.withDensity_rnDeriv_eq _ _ h]

lemma rnDeriv_withDensity
    (κ : kernel α γ) [IsFiniteKernel κ] {f : α → γ → ℝ≥0∞} [IsFiniteKernel (withDensity κ f)]
    (hf : Measurable (Function.uncurry f)) (a : α) :
    kernel.rnDeriv (kernel.withDensity κ f) κ a =ᵐ[κ a] f a := by
  have h_ae := kernel.rnDeriv_eq_rnDeriv_measure (kernel.withDensity κ f) κ a
  have hf' : ∀ a, Measurable (f a) := fun _ ↦ hf.of_uncurry_left
  filter_upwards [h_ae, Measure.rnDeriv_withDensity (κ a) (hf' a)] with x hx1 hx2
  rw [hx1, kernel.withDensity_apply _ hf, hx2]

lemma withDensity_rnDeriv_le (κ η : kernel α γ) [IsFiniteKernel κ] [IsFiniteKernel η] (a : α) :
    kernel.withDensity η (kernel.rnDeriv κ η) a ≤ κ a := by
  refine Measure.le_intro (fun s hs _ ↦ ?_)
  rw [kernel.withDensity_apply']
  swap; · exact kernel.measurable_rnDeriv _ _
  rw [set_lintegral_congr_fun hs
    ((kernel.rnDeriv_eq_rnDeriv_measure κ η a).mono (fun x hx _ ↦ hx)), ← withDensity_apply _ hs]
  exact Measure.withDensity_rnDeriv_le _ _ _

section MeasureCompProd

lemma set_lintegral_prod_rnDeriv {μ ν : Measure α} {κ η : kernel α γ}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteKernel κ] [IsFiniteKernel η]
    (hμν : μ ≪ ν) (hκη : ∀ᵐ a ∂ν, κ a ≪ η a)
    {s : Set α} (hs : MeasurableSet s) {t : Set γ} (ht : MeasurableSet t) :
    ∫⁻ x in s, ∫⁻ y in t, (∂μ/∂ν) x * rnDeriv κ η x y ∂(η x) ∂ν = (μ ⊗ₘ κ) (s ×ˢ t) := by
  have : ∀ᵐ x ∂ν, ∫⁻ y in t, (∂μ/∂ν) x * rnDeriv κ η x y ∂(η x)
      = (∂μ/∂ν) x * κ x t := by
    filter_upwards [hκη] with x hx
    calc ∫⁻ y in t, (∂μ/∂ν) x * rnDeriv κ η x y ∂(η x)
      = (∂μ/∂ν) x * ∫⁻ y in t, rnDeriv κ η x y ∂(η x) := by
          rw [lintegral_const_mul]
          exact measurable_rnDeriv_right κ η x
    _ = (∂μ/∂ν) x * ∫⁻ y in t, (∂(κ x)/∂(η x)) y ∂(η x) := by
          congr 1
          refine lintegral_congr_ae (ae_restrict_of_ae ?_)
          exact rnDeriv_eq_rnDeriv_measure _ _ x
    _ = (∂μ/∂ν) x * κ x t := by
          congr
          rw [Measure.set_lintegral_rnDeriv hx]
  rw [lintegral_congr_ae (ae_restrict_of_ae this),
    set_lintegral_rnDeriv_mul hμν (kernel.measurable_coe _ ht).aemeasurable hs,
    Measure.compProd_apply_prod hs ht]

lemma rnDeriv_measure_compProd_aux {μ ν : Measure α} {κ η : kernel α γ}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteKernel κ] [IsFiniteKernel η]
    (hμν : μ ≪ ν) (hκη : ∀ᵐ a ∂ν, κ a ≪ η a) :
    ∂(μ ⊗ₘ κ)/∂(ν ⊗ₘ η) =ᵐ[ν ⊗ₘ η] fun p ↦ (∂μ/∂ν) p.1 * rnDeriv κ η p.1 p.2 := by
  have h_meas : Measurable fun p : α × γ ↦ (∂μ/∂ν) p.1 * rnDeriv κ η p.1 p.2 :=
    ((Measure.measurable_rnDeriv _ _).comp measurable_fst).mul (measurable_rnDeriv _ _)
  suffices ∀ s, MeasurableSet s → ∫⁻ p in s, (∂(μ ⊗ₘ κ)/∂(ν ⊗ₘ η)) p ∂(ν ⊗ₘ η)
      = ∫⁻ p in s, (∂μ/∂ν) p.1 * rnDeriv κ η p.1 p.2 ∂(ν ⊗ₘ η) from
    ae_eq_of_forall_set_lintegral_eq_of_sigmaFinite (Measure.measurable_rnDeriv _ _) h_meas
      fun s hs _ ↦ this s hs
  have h_left : ∀ s, MeasurableSet s → ∫⁻ p in s, (∂(μ ⊗ₘ κ)/∂(ν ⊗ₘ η)) p ∂(ν ⊗ₘ η)
      = (μ ⊗ₘ κ) s := by
    intro s _
    rw [Measure.set_lintegral_rnDeriv]
    exact Measure.absolutelyContinuous_compProd hμν (hμν hκη)
  have : ∀ s t, MeasurableSet s → MeasurableSet t →
      ∫⁻ x in s, ∫⁻ y in t, (∂μ/∂ν) x * rnDeriv κ η x y ∂(η x) ∂ν = (μ ⊗ₘ κ) (s ×ˢ t) :=
    fun _ _ hs ht ↦ set_lintegral_prod_rnDeriv hμν hκη hs ht
  intro s hs
  apply MeasurableSpace.induction_on_inter generateFrom_prod.symm isPiSystem_prod _ _ _ _ hs
  · simp
  · rintro _ ⟨t₁, ht₁, t₂, ht₂, rfl⟩
    simp only [mem_setOf_eq] at ht₁ ht₂
    rw [h_left (t₁ ×ˢ t₂) (ht₁.prod ht₂), Measure.set_lintegral_compProd h_meas ht₁ ht₂,
      this t₁ t₂ ht₁ ht₂]
  · intro t ht ht_eq
    calc ∫⁻ p in tᶜ, (∂μ ⊗ₘ κ/∂ν ⊗ₘ η) p ∂ν ⊗ₘ η
      = ∫⁻ p, (∂μ ⊗ₘ κ/∂ν ⊗ₘ η) p ∂ν ⊗ₘ η - ∫⁻ p in t, (∂μ ⊗ₘ κ/∂ν ⊗ₘ η) p ∂ν ⊗ₘ η := by
          refine (ENNReal.sub_eq_of_add_eq ?_ ?_).symm
          · rw [h_left _ ht]
            exact measure_ne_top _ _
          · rw [add_comm, lintegral_add_compl _ ht]
    _ = ∫⁻ p, (∂μ ⊗ₘ κ/∂ν ⊗ₘ η) p ∂ν ⊗ₘ η
        - ∫⁻ p in t, (∂μ/∂ν) p.1 * rnDeriv κ η p.1 p.2 ∂ν ⊗ₘ η := by rw [ht_eq]
    _ = (μ ⊗ₘ κ) univ
        - ∫⁻ p in t, (∂μ/∂ν) p.1 * rnDeriv κ η p.1 p.2 ∂ν ⊗ₘ η := by
          have h := h_left univ MeasurableSet.univ
          rw [set_lintegral_univ] at h
          rw [h]
    _ = ∫⁻ x, ∫⁻ y, (∂μ/∂ν) x * rnDeriv κ η x y ∂η x ∂ν
        - ∫⁻ p in t, (∂μ/∂ν) p.1 * rnDeriv κ η p.1 p.2 ∂ν ⊗ₘ η := by
          have h := this univ univ MeasurableSet.univ MeasurableSet.univ
          simp only [Measure.restrict_univ, univ_prod_univ] at h
          rw [← h]
    _ = ∫⁻ p, (∂μ/∂ν) p.1 * rnDeriv κ η p.1 p.2 ∂ν ⊗ₘ η
        - ∫⁻ p in t, (∂μ/∂ν) p.1 * rnDeriv κ η p.1 p.2 ∂ν ⊗ₘ η := by
          congr
          rw [Measure.lintegral_compProd h_meas]
    _ = ∫⁻ p in tᶜ, (∂μ/∂ν) p.1 * rnDeriv κ η p.1 p.2 ∂ν ⊗ₘ η := by
          refine ENNReal.sub_eq_of_add_eq ?_ ?_
          · rw [← ht_eq, h_left _ ht]
            exact measure_ne_top _ _
          rw [add_comm, lintegral_add_compl _ ht]
  · intro f' hf_disj hf_meas hf_eq
    rw [lintegral_iUnion hf_meas hf_disj, lintegral_iUnion hf_meas hf_disj]
    congr with i
    exact hf_eq i

lemma todo1 (μ ν : Measure α) (κ η : kernel α γ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteKernel κ] [IsFiniteKernel η] :
    ∂(ν.withDensity (∂μ/∂ν) ⊗ₘ withDensity η (rnDeriv κ η))/∂(ν ⊗ₘ η)
      =ᵐ[ν ⊗ₘ η] ∂(μ ⊗ₘ κ)/∂(ν ⊗ₘ η) := by
  let μ' := ν.withDensity (∂μ/∂ν)
  let κ' := withDensity η (rnDeriv κ η)
  have h1 : μ = μ' + μ.singularPart ν := by
    conv_lhs => rw [μ.haveLebesgueDecomposition_add ν, add_comm]
  have h2 : μ ⊗ₘ κ = μ' ⊗ₘ κ' + (μ.singularPart ν) ⊗ₘ κ + μ' ⊗ₘ (singularPart κ η) := by
    conv_lhs => rw [h1, Measure.compProd_add_left]
    conv_lhs => conv in μ' ⊗ₘ κ => rw [← rnDeriv_add_singularPart κ η]
    rw [Measure.compProd_add_right, add_assoc, add_comm (μ' ⊗ₘ singularPart κ η), ← add_assoc]
  rw [h2]
  have h_add := Measure.rnDeriv_add (μ' ⊗ₘ κ' + μ.singularPart ν ⊗ₘ κ)
    (μ' ⊗ₘ (singularPart κ η)) (ν ⊗ₘ η)
  have h_add' := Measure.rnDeriv_add (μ' ⊗ₘ κ') (μ.singularPart ν ⊗ₘ κ) (ν ⊗ₘ η)
  have h01 : ∂(μ.singularPart ν ⊗ₘ κ)/∂(ν ⊗ₘ η) =ᵐ[ν ⊗ₘ η] 0 := by
    rw [Measure.rnDeriv_eq_zero]
    exact Measure.mutuallySingular_compProd_left (Measure.mutuallySingular_singularPart _ _) κ η
  have h02 : ∂(μ' ⊗ₘ (singularPart κ η))/∂(ν ⊗ₘ η) =ᵐ[ν ⊗ₘ η] 0 := by
    rw [Measure.rnDeriv_eq_zero]
    exact Measure.mutuallySingular_compProd_right μ' ν
      (eventually_of_forall <| mutuallySingular_singularPart _ _)
  filter_upwards [h_add, h_add', h01, h02] with a h_add h_add' h01 h02
  rw [h_add, Pi.add_apply, h_add', Pi.add_apply, h01, h02]
  simp

lemma todo2 (μ ν : Measure α) (κ η : kernel α γ)
    [IsFiniteMeasure ν] [IsFiniteKernel κ] [IsFiniteKernel η] :
    (fun p ↦ (∂(ν.withDensity (∂μ/∂ν))/∂ν) p.1 * rnDeriv (withDensity η (rnDeriv κ η)) η p.1 p.2)
      =ᵐ[ν ⊗ₘ η] (fun p ↦ (∂μ/∂ν) p.1 * rnDeriv κ η p.1 p.2) := by
  let μ' := ν.withDensity (∂μ/∂ν)
  let κ' := withDensity η (rnDeriv κ η)
  refine EventuallyEq.mul ?_ ?_
  · have h := Measure.rnDeriv_withDensity ν (Measure.measurable_rnDeriv μ ν)
    rw [EventuallyEq, ae_iff] at h ⊢
    exact ENNReal.ae_eq_compProd_of_ae_eq_fst ν η (Measure.measurable_rnDeriv μ' ν)
      (Measure.measurable_rnDeriv μ ν) h
  · have : ∀ a, rnDeriv κ' η a =ᵐ[η a] rnDeriv κ η a := by
      intro a
      rw [← rnDeriv_add_singularPart κ η]
      filter_upwards [rnDeriv_add κ' (singularPart κ η) η a,
        rnDeriv_singularPart κ η a] with x hx1 hx2
      rw [hx1, Pi.add_apply, hx2, Pi.zero_apply, add_zero]
    exact ENNReal.ae_eq_compProd_of_forall_ae_eq _ _ (measurable_rnDeriv κ' η)
      (measurable_rnDeriv κ η) this

lemma rnDeriv_measure_compProd (μ ν : Measure α) (κ η : kernel α γ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteKernel κ] [IsFiniteKernel η] :
    ∂(μ ⊗ₘ κ)/∂(ν ⊗ₘ η) =ᵐ[ν ⊗ₘ η] fun p ↦ (∂μ/∂ν) p.1 * rnDeriv κ η p.1 p.2 := by
  let μ' := ν.withDensity (∂μ/∂ν)
  let κ' := withDensity η (rnDeriv κ η)
  suffices ∂(μ' ⊗ₘ κ')/∂(ν ⊗ₘ η) =ᵐ[ν ⊗ₘ η] fun p ↦ (∂μ'/∂ν) p.1 * rnDeriv κ' η p.1 p.2 from
    (todo1 μ ν κ η).symm.trans (this.trans (todo2 μ ν κ η))
  refine rnDeriv_measure_compProd_aux ?_ ?_
  · exact MeasureTheory.withDensity_absolutelyContinuous _ _
  · exact ae_of_all _ (fun _ ↦ withDensity_absolutelyContinuous _ _)

lemma rnDeriv_measure_compProd' (μ ν : Measure α) (κ η : kernel α γ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteKernel κ] [IsFiniteKernel η] :
    ∀ᵐ a ∂ν, (fun b ↦ (∂(μ ⊗ₘ κ)/∂(ν ⊗ₘ η)) (a, b))
      =ᵐ[η a] fun b ↦ (∂μ/∂ν) a * (∂κ a/∂η a) b := by
  have h := rnDeriv_eq_rnDeriv_measure κ η
  have h' := Measure.ae_ae_of_ae_compProd <| rnDeriv_measure_compProd μ ν κ η
  filter_upwards [h'] with a ha
  filter_upwards [ha, h a] with b hb1 hb2
  rw [hb1, hb2]

lemma rnDeriv_self (κ : kernel α γ) [IsFiniteKernel κ] (a : α) :
    rnDeriv κ κ a =ᵐ[κ a] 1 :=
  (rnDeriv_eq_rnDeriv_measure κ κ a).trans (Measure.rnDeriv_self _)

lemma rnDeriv_measure_compProd_left (μ ν : Measure α) (κ : kernel α γ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteKernel κ] :
    ∂(μ ⊗ₘ κ)/∂(ν ⊗ₘ κ) =ᵐ[ν ⊗ₘ κ] fun p ↦ (∂μ/∂ν) p.1 := by
  have h : (fun p ↦ rnDeriv κ κ p.1 p.2) =ᵐ[ν ⊗ₘ κ] (fun p ↦ (1 : α → γ → ℝ≥0∞) p.1 p.2) :=
    ENNReal.ae_eq_compProd_of_forall_ae_eq ν κ (measurable_rnDeriv _ _) measurable_const
      (rnDeriv_self κ)
  filter_upwards [rnDeriv_measure_compProd μ ν κ κ, h] with p hp1 hp2
  rw [hp1, hp2]
  simp

lemma rnDeriv_measure_compProd_right (μ : Measure α) (κ η : kernel α γ)
    [IsFiniteMeasure μ] [IsFiniteKernel κ] [IsFiniteKernel η] :
    ∂(μ ⊗ₘ κ)/∂(μ ⊗ₘ η) =ᵐ[μ ⊗ₘ η] fun p ↦ rnDeriv κ η p.1 p.2 := by
  have h : (fun p ↦ (∂μ/∂μ) p.1) =ᵐ[μ ⊗ₘ η] (fun p ↦ (1 : α → ℝ≥0∞) p.1) :=
    ENNReal.ae_eq_compProd_of_ae_eq_fst μ η (Measure.measurable_rnDeriv _ _)
      measurable_const (Measure.rnDeriv_self _)
  filter_upwards [rnDeriv_measure_compProd μ μ κ η, h] with p hp1 hp2
  rw [hp1, hp2]
  simp

lemma rnDeriv_measure_compProd_right' (μ : Measure α) (κ η : kernel α γ)
    [IsFiniteMeasure μ] [IsFiniteKernel κ] [IsFiniteKernel η] :
    ∀ᵐ a ∂μ, (fun x ↦ (∂(μ ⊗ₘ κ)/∂(μ ⊗ₘ η)) (a, x))
      =ᵐ[η a] fun x ↦ (∂κ a/∂η a) x := by
  have h := rnDeriv_eq_rnDeriv_measure κ η
  have h' := Measure.ae_ae_of_ae_compProd <| rnDeriv_measure_compProd_right μ κ η
  filter_upwards [h'] with a ha
  filter_upwards [ha, h a] with b hb1 hb2
  rw [hb1, hb2]

lemma Measure.absolutelyContinuous_of_compProd {μ ν : Measure α} {κ η : kernel α γ}
    [SFinite μ] [SFinite ν] [IsSFiniteKernel κ] [IsSFiniteKernel η] [h_zero : ∀ a, NeZero (κ a)]
    (h : μ ⊗ₘ κ ≪ ν ⊗ₘ η) :
    μ ≪ ν := by
  refine Measure.AbsolutelyContinuous.mk (fun s hs hs0 ↦ ?_)
  have h1 : (ν ⊗ₘ η) (s ×ˢ univ) = 0 := by
    rw [Measure.compProd_apply_prod hs MeasurableSet.univ]
    exact set_lintegral_measure_zero _ _ hs0
  have h2 := h h1
  rw [Measure.compProd_apply_prod hs MeasurableSet.univ, lintegral_eq_zero_iff] at h2
  swap; · exact kernel.measurable_coe _ MeasurableSet.univ
  by_contra hμs
  have : NeBot (ae (μ.restrict s)) := by simp [hμs]
  obtain ⟨a, ha⟩ : ∃ a, κ a univ = 0 := h2.exists
  refine absurd ha ?_
  simp only [Measure.measure_univ_eq_zero]
  exact (h_zero a).out

lemma Measure.absolutelyContinuous_kernel_of_compProd {μ ν : Measure α} {κ η : kernel α γ}
    [SFinite μ] [SFinite ν] [IsFiniteKernel κ] [IsFiniteKernel η]
    (h : μ ⊗ₘ κ ≪ ν ⊗ₘ η) :
    ∀ᵐ a ∂μ, κ a ≪ η a := by
  suffices ∀ᵐ a ∂μ, kernel.singularPart κ η a = 0 by
    filter_upwards [this] with a ha
    rwa [singularPart_eq_zero_iff_absolutelyContinuous] at ha
  rw [← rnDeriv_add_singularPart κ η, Measure.compProd_add_right,
    Measure.AbsolutelyContinuous.add_left_iff] at h
  have : μ ⊗ₘ singularPart κ η ⟂ₘ ν ⊗ₘ η :=
    Measure.mutuallySingular_compProd_right μ ν
      (eventually_of_forall <| mutuallySingular_singularPart _ _)
  have h_zero : μ ⊗ₘ singularPart κ η = 0 :=
    Measure.eq_zero_of_absolutelyContinuous_of_mutuallySingular h.2 this
  simp_rw [← Measure.measure_univ_eq_zero]
  refine (lintegral_eq_zero_iff (kernel.measurable_coe _ MeasurableSet.univ)).mp ?_
  rw [← set_lintegral_univ, ← Measure.compProd_apply_prod MeasurableSet.univ MeasurableSet.univ,
    h_zero]
  simp

lemma Measure.absolutelyContinuous_compProd_iff
    {μ ν : Measure α} {κ η : kernel α γ}
    [SFinite μ] [SFinite ν] [IsFiniteKernel κ] [IsFiniteKernel η] [∀ a, NeZero (κ a)] :
    μ ⊗ₘ κ ≪ ν ⊗ₘ η ↔ μ ≪ ν ∧ ∀ᵐ a ∂μ, κ a ≪ η a :=
  ⟨fun h ↦ ⟨Measure.absolutelyContinuous_of_compProd h,
      absolutelyContinuous_kernel_of_compProd h⟩,
    fun h ↦ Measure.absolutelyContinuous_compProd h.1 h.2⟩

lemma Measure.absolutelyContinuous_compProd_left_iff
    {μ ν : Measure α} {κ : kernel α γ}
    [SFinite μ] [SFinite ν] [IsFiniteKernel κ] [h_zero : ∀ a, NeZero (κ a)] :
    μ ⊗ₘ κ ≪ ν ⊗ₘ κ ↔ μ ≪ ν := by
  rw [Measure.absolutelyContinuous_compProd_iff]
  simp only [and_iff_left_iff_imp]
  exact fun _ ↦ ae_of_all _ (fun _ ↦ Measure.AbsolutelyContinuous.rfl)

lemma Measure.absolutelyContinuous_compProd_right_iff
    {μ : Measure α} {κ η : kernel α γ} [SFinite μ] [IsFiniteKernel κ] [IsFiniteKernel η] :
    μ ⊗ₘ κ ≪ μ ⊗ₘ η ↔ ∀ᵐ a ∂μ, κ a ≪ η a :=
  ⟨absolutelyContinuous_kernel_of_compProd, Measure.absolutelyContinuous_compProd_right _⟩

end MeasureCompProd

lemma absolutelyContinuous_compProd_iff {β : Type*} [MeasurableSpace β]
    [MeasurableSpace.CountableOrCountablyGenerated β γ] {κ₁ η₁ : kernel α β}
    {κ₂ η₂ : kernel (α × β) γ} [IsSFiniteKernel κ₁] [IsSFiniteKernel η₁] [IsFiniteKernel κ₂]
    [IsFiniteKernel η₂] (a : α) [∀ b, NeZero (κ₂ (a, b))] :
    (κ₁ ⊗ₖ κ₂) a ≪ (η₁ ⊗ₖ η₂) a ↔ κ₁ a ≪ η₁ a ∧ ∀ᵐ b ∂κ₁ a, κ₂ (a, b) ≪ η₂ (a, b) := by
  simp_rw [kernel.compProd_apply_eq_compProd_snd', kernel.Measure.absolutelyContinuous_compProd_iff,
    kernel.snd'_apply]

end ProbabilityTheory.kernel
