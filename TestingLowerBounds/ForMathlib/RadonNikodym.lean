/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
import TestingLowerBounds.ForMathlib.AbsolutelyContinuous
import TestingLowerBounds.ForMathlib.RnDeriv

/-!
# Radon-Nikodym derivative and Lebesgue decomposition for kernels

-/

open MeasureTheory MeasurableSpace Set

open scoped ENNReal

namespace ProbabilityTheory.Kernel

variable {α γ : Type*} {mα : MeasurableSpace α} {mγ : MeasurableSpace γ}
  {μ ν : Measure α} {κ η : Kernel α γ}

lemma ae_compProd_of_ae_fst (κ : Kernel α γ) {p : α → Prop} (hp : MeasurableSet {x | p x})
    (h : ∀ᵐ a ∂μ, p a) :
    ∀ᵐ x ∂(μ ⊗ₘ κ), p x.1 := by
  refine ae_compProd_of_ae_ae (measurable_fst hp) ?_
  filter_upwards [h] with a ha
  simp [ha]

lemma ae_eq_compProd_of_ae_eq_fst {β : Type*} {_ : MeasurableSpace β} [AddGroup β]
    [MeasurableSingletonClass β] [MeasurableSub₂ β]
    (μ : Measure α) (κ : Kernel α γ) {f g : α → β}
    (hf : Measurable f) (hg : Measurable g) (h : f =ᵐ[μ] g) :
    (fun p ↦ f p.1) =ᵐ[μ ⊗ₘ κ] (fun p ↦ g p.1) :=
  ae_compProd_of_ae_fst κ (measurableSet_eq_fun hf hg) h

lemma ae_eq_compProd_of_forall_ae_eq {β : Type*} {_ : MeasurableSpace β} [AddGroup β]
    [MeasurableSingletonClass β] [MeasurableSub₂ β]
    (μ : Measure α) (κ : Kernel α γ) {f g : α → γ → β}
    (hf : Measurable (Function.uncurry f)) (hg : Measurable (Function.uncurry g))
    (h : ∀ a, f a =ᵐ[κ a] g a) :
    (fun p ↦ f p.1 p.2) =ᵐ[μ ⊗ₘ κ] (fun p ↦ g p.1 p.2) :=
  ae_compProd_of_ae_ae (measurableSet_eq_fun hf hg)
    (ae_of_all _ (fun a ↦ measure_mono_null (fun x ↦ by simp) (h a)))

lemma ENNReal.ae_eq_compProd_of_ae_eq_fst (μ : Measure α) (κ : Kernel α γ) {f g : α → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) (h : f =ᵐ[μ] g) :
    (fun p ↦ f p.1) =ᵐ[μ ⊗ₘ κ] (fun p ↦ g p.1) :=
  ae_compProd_of_ae_fst κ (measurableSet_eq_fun' hf hg) h

lemma ENNReal.ae_eq_compProd_of_forall_ae_eq
    (μ : Measure α) (κ : Kernel α γ) {f g : α → γ → ℝ≥0∞}
    (hf : Measurable (Function.uncurry f)) (hg : Measurable (Function.uncurry g))
    (h : ∀ a, f a =ᵐ[κ a] g a) :
    (fun p ↦ f p.1 p.2) =ᵐ[μ ⊗ₘ κ] (fun p ↦ g p.1 p.2) :=
  ae_compProd_of_ae_ae (measurableSet_eq_fun' hf hg)
    (ae_of_all _ (fun a ↦ measure_mono_null (fun x ↦ by simp) (h a)))

lemma rnDeriv_measure_compProd_left_of_ac {μ ν : Measure α} (hμν : μ ≪ ν) (κ : Kernel α γ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteKernel κ] :
    ∂(μ ⊗ₘ κ)/∂(ν ⊗ₘ κ) =ᵐ[ν ⊗ₘ κ] fun p ↦ (∂μ/∂ν) p.1 := by
  refine ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite ?_ ?_ (fun s hs _ ↦ ?_)
  · exact Measure.measurable_rnDeriv _ _
  · exact (Measure.measurable_rnDeriv _ _).comp measurable_fst
  have h_key t₁ t₂ : MeasurableSet t₁ → MeasurableSet t₂ →
      ∫⁻ x in t₁ ×ˢ t₂, (∂μ ⊗ₘ κ/∂ν ⊗ₘ κ) x ∂ν ⊗ₘ κ = ∫⁻ x in t₁ ×ˢ t₂, (∂μ/∂ν) x.1 ∂ν ⊗ₘ κ := by
    intro ht₁ ht₂
    rw [Measure.setLIntegral_rnDeriv (Measure.absolutelyContinuous_compProd_left hμν _)]
    rw [Measure.setLIntegral_compProd _ ht₁ ht₂]
    swap; · exact (Measure.measurable_rnDeriv _ _).comp measurable_fst
    simp only [MeasureTheory.lintegral_const, MeasurableSet.univ, Measure.restrict_apply,
      univ_inter]
    rw [setLIntegral_rnDeriv_mul hμν (κ.measurable_coe ht₂).aemeasurable ht₁,
      Measure.compProd_apply_prod ht₁ ht₂]
  apply induction_on_inter generateFrom_prod.symm isPiSystem_prod _ _ _ _ hs
  · simp
  · rintro _ ⟨t₁, ht₁, t₂, ht₂, rfl⟩
    exact h_key t₁ t₂ ht₁ ht₂
  · intro t ht ht_eq
    rw [setLintegral_compl ht, ht_eq, setLintegral_compl ht]
    · congr 1
      specialize h_key .univ .univ .univ .univ
      simpa only [univ_prod_univ, Measure.restrict_univ] using h_key
    · rw [← ht_eq]
      exact ((Measure.setLIntegral_rnDeriv_le _).trans_lt (measure_lt_top _ _)).ne
    · exact ((Measure.setLIntegral_rnDeriv_le _).trans_lt (measure_lt_top _ _)).ne
  · intro f' hf_disj hf_meas hf_eq
    rw [lintegral_iUnion hf_meas hf_disj, lintegral_iUnion hf_meas hf_disj]
    congr with i
    exact hf_eq i

lemma todo (μ ν : Measure α) (κ η : Kernel α γ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteKernel κ] [IsFiniteKernel η] :
    ∂(ν.withDensity (μ.rnDeriv ν) ⊗ₘ κ)/∂(ν ⊗ₘ η) =ᵐ[ν ⊗ₘ η] ∂(μ ⊗ₘ κ)/∂(ν ⊗ₘ η) := by
  conv_rhs => rw [Measure.haveLebesgueDecomposition_add μ ν]
  rw [Measure.compProd_add_left]
  have h := Measure.rnDeriv_add' (μ.singularPart ν ⊗ₘ κ) (ν.withDensity (μ.rnDeriv ν) ⊗ₘ κ)
    (ν ⊗ₘ η)
  have h2 : ∂μ.singularPart ν ⊗ₘ κ/∂ν ⊗ₘ η =ᵐ[ν ⊗ₘ η] 0 := by
    refine Measure.rnDeriv_eq_zero_of_mutuallySingular ?_ ?_
    · exact Measure.mutuallySingular_compProd_left (μ.mutuallySingular_singularPart _) _ _
    · exact Measure.AbsolutelyContinuous.rfl
  filter_upwards [h, h2] with x hx hx2
  simp [hx, hx2]

lemma rnDeriv_measure_compProd_left (μ ν : Measure α) (κ : Kernel α γ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteKernel κ] :
    ∂(μ ⊗ₘ κ)/∂(ν ⊗ₘ κ) =ᵐ[ν ⊗ₘ κ] fun p ↦ (∂μ/∂ν) p.1 := by
  refine (todo μ ν κ κ).symm.trans ?_
  refine (rnDeriv_measure_compProd_left_of_ac
    (MeasureTheory.withDensity_absolutelyContinuous ν (μ.rnDeriv ν)) κ).trans ?_
  refine ENNReal.ae_eq_compProd_of_ae_eq_fst _ _ ?_ ?_ ?_
  · exact Measure.measurable_rnDeriv _ _
  · exact Measure.measurable_rnDeriv _ _
  · exact Measure.rnDeriv_withDensity ν (Measure.measurable_rnDeriv _ _)

lemma rnDeriv_measure_compProd_left' (μ ν : Measure α) (κ : Kernel α γ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteKernel κ] :
    ∀ᵐ a ∂ν, (fun b ↦ (∂(μ ⊗ₘ κ)/∂(ν ⊗ₘ κ)) (a, b))
      =ᵐ[κ a] fun _ ↦ (∂μ/∂ν) a := by
  have h' := Measure.ae_ae_of_ae_compProd <| rnDeriv_measure_compProd_left μ ν κ
  exact h'

lemma rnDeriv_compProd [IsFiniteMeasure μ] [IsFiniteKernel κ] [IsFiniteKernel η]
    (h_ac : μ ⊗ₘ κ ≪ μ ⊗ₘ η) (ν : Measure α) [IsFiniteMeasure ν] :
    (fun p ↦ μ.rnDeriv ν p.1 * (μ ⊗ₘ κ).rnDeriv (μ ⊗ₘ η) p)
      =ᵐ[ν ⊗ₘ η] (μ ⊗ₘ κ).rnDeriv (ν ⊗ₘ η) := by
  refine Filter.EventuallyEq.trans ?_ (Measure.rnDeriv_mul_rnDeriv h_ac)
  filter_upwards [Kernel.rnDeriv_measure_compProd_left μ ν η] with p hp
  rw [Pi.mul_apply, hp, mul_comm]

lemma rnDeriv_compProd' [IsFiniteMeasure μ] [IsFiniteKernel κ] [IsFiniteKernel η]
    (h_ac : μ ⊗ₘ κ ≪ μ ⊗ₘ η) (ν : Measure α) [IsFiniteMeasure ν] :
    ∀ᵐ a ∂ν, (fun b ↦ μ.rnDeriv ν a * (μ ⊗ₘ κ).rnDeriv (μ ⊗ₘ η) (a, b))
      =ᵐ[η a] fun b ↦ (μ ⊗ₘ κ).rnDeriv (ν ⊗ₘ η) (a, b) :=
  Measure.ae_ae_of_ae_compProd <| rnDeriv_compProd h_ac ν

variable [CountableOrCountablyGenerated α γ]

section MeasureCompProd

lemma todo' (μ ν : Measure α) (κ η : Kernel α γ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteKernel κ] [IsFiniteKernel η] :
    ∂(μ ⊗ₘ withDensity η (rnDeriv κ η))/∂(ν ⊗ₘ η) =ᵐ[ν ⊗ₘ η] ∂(μ ⊗ₘ κ)/∂(ν ⊗ₘ η) := by
  let κ' := withDensity η (rnDeriv κ η)
  have h2 : μ ⊗ₘ κ = μ ⊗ₘ κ' + μ ⊗ₘ (singularPart κ η) := by
    conv_lhs => conv in μ ⊗ₘ κ => rw [← rnDeriv_add_singularPart κ η]
    rw [Measure.compProd_add_right]
  rw [h2]
  have h_add := Measure.rnDeriv_add (μ ⊗ₘ κ') (μ ⊗ₘ (singularPart κ η)) (ν ⊗ₘ η)
  have h02 : ∂(μ ⊗ₘ (singularPart κ η))/∂(ν ⊗ₘ η) =ᵐ[ν ⊗ₘ η] 0 := by
    rw [Measure.rnDeriv_eq_zero]
    exact Measure.mutuallySingular_compProd_right μ ν
      (.of_forall <| mutuallySingular_singularPart _ _)
  filter_upwards [h_add, h02] with a h_add h02
  rw [h_add, Pi.add_apply, h02]
  simp

lemma todo1 (μ ν : Measure α) (κ η : Kernel α γ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteKernel κ] [IsFiniteKernel η] :
    ∂(ν.withDensity (∂μ/∂ν) ⊗ₘ withDensity η (rnDeriv κ η))/∂(ν ⊗ₘ η)
      =ᵐ[ν ⊗ₘ η] ∂(μ ⊗ₘ κ)/∂(ν ⊗ₘ η) := (todo' _ ν κ η).trans (todo μ ν κ η)

lemma todo2 (μ ν : Measure α) (κ η : Kernel α γ)
    [IsFiniteMeasure ν] [IsFiniteKernel κ] [IsFiniteKernel η] :
    (fun p ↦ (∂(ν.withDensity (∂μ/∂ν))/∂ν) p.1 * rnDeriv (withDensity η (rnDeriv κ η)) η p.1 p.2)
      =ᵐ[ν ⊗ₘ η] (fun p ↦ (∂μ/∂ν) p.1 * rnDeriv κ η p.1 p.2) := by
  let μ' := ν.withDensity (∂μ/∂ν)
  let κ' := withDensity η (rnDeriv κ η)
  refine Filter.EventuallyEq.mul ?_ ?_
  · have h := ν.rnDeriv_withDensity (μ.measurable_rnDeriv ν)
    rw [Filter.EventuallyEq, ae_iff] at h ⊢
    exact ENNReal.ae_eq_compProd_of_ae_eq_fst ν η (μ'.measurable_rnDeriv ν)
      (μ.measurable_rnDeriv ν) h
  · have : ∀ a, rnDeriv κ' η a =ᵐ[η a] rnDeriv κ η a := by
      intro a
      rw [← rnDeriv_add_singularPart κ η]
      filter_upwards [rnDeriv_add κ' (singularPart κ η) η a,
        rnDeriv_singularPart κ η a] with x hx1 hx2
      rw [hx1, Pi.add_apply, hx2, Pi.zero_apply, add_zero]
    exact ENNReal.ae_eq_compProd_of_forall_ae_eq _ _ (measurable_rnDeriv κ' η)
      (measurable_rnDeriv κ η) this

lemma setLIntegral_rnDeriv_right [IsFiniteKernel κ] [IsFiniteKernel η] {a : α} (hκη : κ a ≪ η a)
    (t : Set γ) :
    ∫⁻ b in t, κ.rnDeriv η a b ∂η a = (κ a) t := by
  have h := κ.rnDeriv_eq_rnDeriv_measure (η := η) (a := a)
  rw [lintegral_congr_ae (ae_restrict_of_ae h), Measure.setLIntegral_rnDeriv hκη]

lemma setLIntegral_rnDeriv_compProd
    [IsFiniteMeasure μ] [IsFiniteKernel κ] [IsFiniteKernel η] (hκη : ∀ᵐ a ∂μ, κ a ≪ η a)
    {s : Set α} (hs : MeasurableSet s) {t : Set γ} (ht : MeasurableSet t) :
    ∫⁻ p in s ×ˢ t, rnDeriv κ η p.1 p.2 ∂(μ ⊗ₘ η) = (μ ⊗ₘ κ) (s ×ˢ t) := by
  rw [Measure.setLIntegral_compProd (measurable_rnDeriv _ _) hs ht,
    Measure.compProd_apply_prod hs ht]
  refine setLIntegral_congr_fun hs ?_
  filter_upwards [hκη] with a ha _ using setLIntegral_rnDeriv_right ha t

lemma rnDeriv_measure_compProd_right_of_ac (μ : Measure α) {κ η : Kernel α γ}
    (h_ac : ∀ᵐ a ∂μ, κ a ≪ η a)
    [IsFiniteMeasure μ] [IsFiniteKernel κ] [IsFiniteKernel η] :
    ∂(μ ⊗ₘ κ)/∂(μ ⊗ₘ η) =ᵐ[μ ⊗ₘ η] fun p ↦ rnDeriv κ η p.1 p.2 := by
  refine ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite (Measure.measurable_rnDeriv _ _)
    (measurable_rnDeriv _ _) fun s hs _ ↦ ?_
  have h_eq (t₁ : Set α) (ht₁ : MeasurableSet t₁) (t₂ : Set γ) (ht₂ : MeasurableSet t₂) :
      ∫⁻ p in t₁ ×ˢ t₂, (∂μ ⊗ₘ κ/∂μ ⊗ₘ η) p ∂μ ⊗ₘ η
        = ∫⁻ p in t₁ ×ˢ t₂, κ.rnDeriv η p.1 p.2 ∂μ ⊗ₘ η := by
    rw [Measure.setLIntegral_rnDeriv, setLIntegral_rnDeriv_compProd h_ac ht₁ ht₂]
    exact Measure.absolutelyContinuous_compProd_right h_ac
  apply induction_on_inter generateFrom_prod.symm isPiSystem_prod _ _ _ _ hs
  · simp
  · rintro _ ⟨t₁, ht₁, t₂, ht₂, rfl⟩
    simp only [mem_setOf_eq] at ht₁ ht₂
    exact h_eq t₁ ht₁ t₂ ht₂
  · intro t ht ht_eq
    have h := h_eq .univ .univ .univ .univ
    simp only [univ_prod_univ, Measure.restrict_univ] at h
    rw [setLintegral_compl ht, setLintegral_compl ht, h, ht_eq]
    · rw [← ht_eq, Measure.setLIntegral_rnDeriv (Measure.absolutelyContinuous_compProd_right h_ac)]
      exact measure_ne_top _ _
    · rw [Measure.setLIntegral_rnDeriv (Measure.absolutelyContinuous_compProd_right h_ac)]
      exact measure_ne_top _ _
  · intro f' hf_disj hf_meas hf_eq
    rw [lintegral_iUnion hf_meas hf_disj, lintegral_iUnion hf_meas hf_disj]
    congr with i
    exact hf_eq i

lemma rnDeriv_measure_compProd_right (μ : Measure α) (κ η : Kernel α γ)
    [IsFiniteMeasure μ] [IsFiniteKernel κ] [IsFiniteKernel η] :
    ∂(μ ⊗ₘ κ)/∂(μ ⊗ₘ η) =ᵐ[μ ⊗ₘ η] fun p ↦ rnDeriv κ η p.1 p.2 := by
  let κ' := withDensity η (rnDeriv κ η)
  suffices ∂(μ ⊗ₘ κ')/∂(μ ⊗ₘ η) =ᵐ[μ ⊗ₘ η] fun p ↦ rnDeriv κ' η p.1 p.2 by
    refine (todo' μ μ κ η).symm.trans (this.trans ?_)
    refine ENNReal.ae_eq_compProd_of_forall_ae_eq μ η (measurable_rnDeriv _ _)
      (measurable_rnDeriv _ _) fun a ↦ ?_
    exact rnDeriv_withDensity (measurable_rnDeriv _ _) _
  exact rnDeriv_measure_compProd_right_of_ac μ
    (ae_of_all _ (fun _ ↦ withDensity_absolutelyContinuous _ _))

lemma rnDeriv_measure_compProd_right' (μ : Measure α) (κ η : Kernel α γ)
    [IsFiniteMeasure μ] [IsFiniteKernel κ] [IsFiniteKernel η] :
    ∀ᵐ a ∂μ, (fun x ↦ (∂(μ ⊗ₘ κ)/∂(μ ⊗ₘ η)) (a, x))
      =ᵐ[η a] fun x ↦ (∂κ a/∂η a) x := by
  have h a := κ.rnDeriv_eq_rnDeriv_measure (η := η) (a := a)
  have h' := Measure.ae_ae_of_ae_compProd <| rnDeriv_measure_compProd_right μ κ η
  filter_upwards [h'] with a ha
  filter_upwards [ha, h a] with b hb1 hb2
  rw [hb1, hb2]

lemma rnDeriv_measure_compProd (μ ν : Measure α) (κ η : Kernel α γ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteKernel κ] [IsFiniteKernel η] :
    ∂(μ ⊗ₘ κ)/∂(ν ⊗ₘ η) =ᵐ[ν ⊗ₘ η] fun p ↦ (∂μ/∂ν) p.1 * rnDeriv κ η p.1 p.2 := by
  let κ' := withDensity η (rnDeriv κ η)
  suffices ∂(μ ⊗ₘ κ')/∂(ν ⊗ₘ η) =ᵐ[ν ⊗ₘ η] fun p ↦ (∂μ/∂ν) p.1 * rnDeriv κ' η p.1 p.2 by
    refine (todo' μ ν κ η).symm.trans (this.trans ?_)
    refine Filter.EventuallyEq.rfl.mul ?_
    refine ENNReal.ae_eq_compProd_of_forall_ae_eq ν η (measurable_rnDeriv _ _)
      (measurable_rnDeriv _ _) fun a ↦ ?_
    exact rnDeriv_withDensity (measurable_rnDeriv _ _) _
  have hκη : ∀ᵐ a ∂μ, κ' a ≪ η a := ae_of_all _ (fun _ ↦ withDensity_absolutelyContinuous _ _)
  refine (rnDeriv_compProd (Measure.absolutelyContinuous_compProd_right hκη) ν).symm.trans ?_
  have h_eq := rnDeriv_measure_compProd_right μ κ' η
  rw [Filter.EventuallyEq, Measure.ae_compProd_iff] at h_eq ⊢
  refine Measure.ae_eq_mul_rnDeriv_of_ae_eq h_eq
  · refine measurableSet_eq_fun' ?_ ?_
    · exact ((Measure.measurable_rnDeriv _ _).comp measurable_fst).mul
        (Measure.measurable_rnDeriv _ _)
    · exact ((Measure.measurable_rnDeriv _ _).comp measurable_fst).mul (measurable_rnDeriv _ _)
  · exact measurableSet_eq_fun' (Measure.measurable_rnDeriv _ _) (measurable_rnDeriv _ _)

lemma rnDeriv_measure_compProd' (μ ν : Measure α) (κ η : Kernel α γ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteKernel κ] [IsFiniteKernel η] :
    ∀ᵐ a ∂ν, (fun b ↦ (∂(μ ⊗ₘ κ)/∂(ν ⊗ₘ η)) (a, b))
      =ᵐ[η a] fun b ↦ (∂μ/∂ν) a * (∂κ a/∂η a) b := by
  have h a := κ.rnDeriv_eq_rnDeriv_measure (η := η) (a := a)
  have h' := Measure.ae_ae_of_ae_compProd <| rnDeriv_measure_compProd μ ν κ η
  filter_upwards [h'] with a ha
  filter_upwards [ha, h a] with b hb1 hb2
  rw [hb1, hb2]

-- lemma setLIntegral_prod_rnDeriv
--     [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteKernel κ] [IsFiniteKernel η]
--     (hμν : μ ≪ ν) (hκη : ∀ᵐ a ∂ν, κ a ≪ η a)
--     {s : Set α} (hs : MeasurableSet s) {t : Set γ} (ht : MeasurableSet t) :
--     ∫⁻ x in s, ∫⁻ y in t, (∂μ/∂ν) x * rnDeriv κ η x y ∂(η x) ∂ν = (μ ⊗ₘ κ) (s ×ˢ t) := by
--   have : ∀ᵐ x ∂ν, ∫⁻ y in t, (∂μ/∂ν) x * rnDeriv κ η x y ∂(η x)
--       = (∂μ/∂ν) x * κ x t := by
--     filter_upwards [hκη] with x hx
--     calc ∫⁻ y in t, (∂μ/∂ν) x * rnDeriv κ η x y ∂(η x)
--       = (∂μ/∂ν) x * ∫⁻ y in t, rnDeriv κ η x y ∂(η x) := by
--           rw [lintegral_const_mul]
--           exact measurable_rnDeriv_right κ η x
--     _ = (∂μ/∂ν) x * ∫⁻ y in t, (∂(κ x)/∂(η x)) y ∂(η x) := by
--           congr 1
--           refine lintegral_congr_ae (ae_restrict_of_ae ?_)
--           exact rnDeriv_eq_rnDeriv_measure
--     _ = (∂μ/∂ν) x * κ x t := by
--           congr
--           rw [Measure.setLIntegral_rnDeriv hx]
--   rw [lintegral_congr_ae (ae_restrict_of_ae this), Measure.compProd_apply_prod hs ht,
--     setLIntegral_rnDeriv_mul hμν (κ.measurable_coe ht).aemeasurable hs]

end MeasureCompProd

end ProbabilityTheory.Kernel
