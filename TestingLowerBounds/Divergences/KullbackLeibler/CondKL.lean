/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
module

public import Mathlib.InformationTheory.KullbackLeibler.ChainRule
public import TestingLowerBounds.Divergences.KullbackLeibler.KullbackLeibler
public import TestingLowerBounds.FDiv.CondFDiv
public import TestingLowerBounds.FDiv.DPIJensen

/-!
# Conditional Kullback-Leibler divergence

## Main definitions

* `condKL κ η μ`: the conditional Kullback-Leibler divergence of the kernels `κ` and `η` with
  respect to `μ`, `∫⁻ a, klDiv (κ a) (η a) ∂μ`.

## Main statements

* `condKL_ne_top_iff`: finiteness of the conditional divergence.
* `klDiv_compProd_eq_add_condKL`, `klDiv_fst_add_condKL`: chain rules for the Kullback-Leibler
  divergence.
* `condKL_compProd_kernel`: chain rule for the conditional divergence.
* `klDiv_prod_two`, `klDiv_pi`: tensorization.

These results need `CountableOrCountablyGenerated` assumptions to express the conditional
divergence through Radon-Nikodym derivatives of kernels, except for the tensorization results,
which follow from Mathlib's chain rule `InformationTheory.klDiv_compProd_eq_add`.

-/

@[expose] public section

open Real MeasureTheory Filter MeasurableSpace InformationTheory

open scoped ENNReal NNReal Topology BigOperators

namespace ProbabilityTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ ν : Measure α}

section Conditional

variable {β γ : Type*} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ} {κ η : Kernel α β}

/-- Equivalence between two possible versions of the first condition for the finiteness of the
conditional KL divergence, the second version is the preferred one. -/
lemma klDiv_ae_ne_top_iff : (∀ᵐ a ∂μ, klDiv (κ a) (η a) ≠ ∞) ↔
    (∀ᵐ a ∂μ, κ a ≪ η a) ∧ (∀ᵐ a ∂μ, Integrable (llr (κ a) (η a)) (κ a)) := by
  simp_rw [klDiv_ne_top_iff, eventually_and]

open Classical in
/--
Kullback-Leibler divergence between two kernels κ and η conditional to a measure μ.
It is defined as KL(κ, η | μ) := ∫ x, KL(κ x, η x) dμ.
-/
noncomputable
def condKL (κ η : Kernel α β) (μ : Measure α) : ℝ≥0∞ :=
  ∫⁻ a, klDiv (κ a) (η a) ∂μ

lemma condKL_eq_condFDiv [IsFiniteKernel κ] [IsFiniteKernel η] :
    condKL κ η μ = condFDiv klDivFun κ η μ := by
  simp_rw [condKL, condFDiv, klDiv_eq_fDiv]

section CondKLEq

variable [CountableOrCountablyGenerated α β] [IsFiniteKernel κ] [IsFiniteKernel η]

@[simp]
lemma condKL_of_not_ae_ne_top (h : ¬ ∀ᵐ a ∂μ, klDiv (κ a) (η a) ≠ ∞) :
    condKL κ η μ = ∞ := by
  rw [condKL]
  by_contra h'
  exact h ((ae_lt_top (measurable_klDiv _ _) h').mono fun x hx ↦ hx.ne)

@[simp]
lemma condKL_of_not_ae_ac (h : ¬ ∀ᵐ a ∂μ, κ a ≪ η a) :
    condKL κ η μ = ∞ := by
  rw [condKL_eq_condFDiv]
  exact condFDiv_of_not_ae_ac derivAtTop_klDivFun h

lemma condKL_ne_top_iff :
    condKL κ η μ ≠ ∞
    ↔ (∀ᵐ a ∂μ, κ a ≪ η a) ∧ (∀ᵐ a ∂μ, Integrable (llr (κ a) (η a)) (κ a))
      ∧ Integrable (fun a ↦ (klDiv (κ a) (η a)).toReal) μ := by
  rw [← and_assoc, ← klDiv_ae_ne_top_iff]
  refine ⟨fun h ↦ ?_, fun ⟨h_ae, h_int⟩ ↦ ?_⟩
  · have h_ae : ∀ᵐ a ∂μ, klDiv (κ a) (η a) ≠ ∞ :=
      (ae_lt_top (measurable_klDiv κ η) h).mono fun _ ha ↦ ha.ne
    exact ⟨h_ae, (integrable_toReal_iff (measurable_klDiv κ η).aemeasurable h_ae).mpr h⟩
  · exact (integrable_toReal_iff (measurable_klDiv κ η).aemeasurable h_ae).mp h_int

lemma condKL_eq_top_iff :
    condKL κ η μ = ∞
      ↔ ¬ (∀ᵐ a ∂μ, κ a ≪ η a) ∨ ¬ (∀ᵐ a ∂μ, Integrable (llr (κ a) (η a)) (κ a))
        ∨ ¬ Integrable (fun a ↦ (klDiv (κ a) (η a)).toReal) μ := by
  rw [← not_iff_not, ← ne_eq, condKL_ne_top_iff]
  tauto

lemma toReal_condKL_eq_integral (h : condKL κ η μ ≠ ∞) :
    (condKL κ η μ).toReal = ∫ a, (klDiv (κ a) (η a)).toReal ∂μ := by
  rw [condKL, integral_toReal (measurable_klDiv _ _).aemeasurable]
  exact ae_lt_top (measurable_klDiv _ _) h

end CondKLEq

@[simp]
lemma condKL_self (κ : Kernel α β) (μ : Measure α) [IsFiniteKernel κ] : condKL κ κ μ = 0 := by
  simp [condKL]

@[simp]
lemma condKL_zero_left [IsFiniteKernel η] :
    condKL 0 η μ = ∫⁻ a, η a Set.univ ∂μ := by simp [condKL_eq_condFDiv]

lemma condKL_zero_right [CountableOrCountablyGenerated α β]
    [IsFiniteKernel κ] (h : ∃ᵐ a ∂μ, κ a ≠ 0) :
    condKL κ 0 μ = ∞ := by
  rw [condKL_of_not_ae_ac]
  simp [h]

@[simp]
lemma condKL_zero_measure : condKL κ η 0 = 0 := by simp [condKL]

@[simp]
lemma condKL_isEmpty_left [IsEmpty α] : condKL κ η μ = 0 := by simp [condKL]

@[simp]
lemma condKL_const {ξ : Measure β} [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    condKL (Kernel.const β μ) (Kernel.const β ν) ξ = (klDiv μ ν) * ξ .univ := by
  rw [condKL_eq_condFDiv, klDiv_eq_fDiv]
  exact condFDiv_const

section CompProd

/-- The conditional KL divergence with respect to a composition-product `μ ⊗ₘ ξ` is an iterated
conditional KL divergence. -/
lemma condKL_measure_compProd [CountableOrCountablyGenerated (α × β) γ] [SFinite μ]
    {ξ : Kernel α β} [IsSFiniteKernel ξ] {κ η : Kernel (α × β) γ} [IsFiniteKernel κ]
    [IsFiniteKernel η] :
    condKL κ η (μ ⊗ₘ ξ) = ∫⁻ x, condKL (κ.sectR x) (η.sectR x) (ξ x) ∂μ := by
  simp_rw [condKL_eq_condFDiv, condFDiv_measure_compProd]

lemma klDiv_compProd_eq_condKL [CountableOrCountablyGenerated α β]
    [IsFiniteMeasure μ] [IsFiniteKernel κ] [IsFiniteKernel η] :
    klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η) = condKL κ η μ := by
  rw [klDiv_eq_fDiv, condKL_eq_condFDiv]
  exact fDiv_compProd_right μ κ η

section ChainRule

/-- The **chain rule** for the KL divergence. -/
lemma klDiv_compProd_eq_add_condKL [CountableOrCountablyGenerated α β]
    [IsMarkovKernel κ] [IsMarkovKernel η] [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    klDiv (μ ⊗ₘ κ) (ν ⊗ₘ η) = klDiv μ ν + condKL κ η μ := by
  rw [klDiv_compProd_eq_add, klDiv_compProd_eq_condKL]

/-- The **chain rule** for the KL divergence. -/
lemma klDiv_fst_add_condKL [StandardBorelSpace β] [Nonempty β] {μ ν : Measure (α × β)}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    klDiv μ.fst ν.fst + condKL μ.condKernel ν.condKernel μ.fst = klDiv μ ν := by
  rw [← klDiv_compProd_eq_add_condKL, μ.disintegrate, ν.disintegrate]

/-- The **chain rule** for the conditional KL divergence. -/
lemma condKL_compProd_kernel [CountableOrCountablyGenerated α β]
    [CountableOrCountablyGenerated (α × β) γ] {κ₁ η₁ : Kernel α β}
    {κ₂ η₂ : Kernel (α × β) γ} [IsFiniteKernel κ₁] [IsFiniteKernel η₁] [IsMarkovKernel κ₂]
    [IsMarkovKernel η₂] [SFinite μ] :
    condKL (κ₁ ⊗ₖ κ₂) (η₁ ⊗ₖ η₂) μ = condKL κ₁ η₁ μ + condKL κ₂ η₂ (μ ⊗ₘ κ₁) := by
  rcases isEmpty_or_nonempty α with hα | hα
  · simp
  have := countableOrCountablyGenerated_right_of_prod_left_of_nonempty (α := α) (β := β) (γ := γ)
  rw [condKL_measure_compProd, condKL, condKL, ← lintegral_add_left (measurable_klDiv _ _)]
  refine lintegral_congr fun a ↦ ?_
  rw [Kernel.compProd_apply_eq_compProd_sectR, Kernel.compProd_apply_eq_compProd_sectR,
    klDiv_compProd_eq_add_condKL]

end ChainRule

end CompProd

end Conditional

section DataProcessingInequality

variable {β : Type*} {mβ : MeasurableSpace β} {κ η : Kernel α β}

lemma klDiv_comp_left_le [CountableOrCountablyGenerated α β]
    (μ : Measure α) [IsFiniteMeasure μ]
    (κ η : Kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η] :
    klDiv (κ ∘ₘ μ) (η ∘ₘ μ) ≤ condKL κ η μ := by
  rw [klDiv_eq_fDiv, condKL_eq_condFDiv]
  exact fDiv_comp_left_le μ κ η

end DataProcessingInequality

section Tensorization

variable {β : Type*} {mβ : MeasurableSpace β}

/-- The Kullback-Leibler divergence between two products with the same first factor. -/
lemma klDiv_prod_right [IsFiniteMeasure μ] {ξ ψ : Measure β} [IsFiniteMeasure ξ]
    [IsFiniteMeasure ψ] :
    klDiv (μ.prod ξ) (μ.prod ψ) = μ .univ * klDiv ξ ψ := by
  rcases eq_zero_or_neZero μ with rfl | hμ
  · simp
  have hμ0 : μ .univ ≠ 0 := by simp [NeZero.ne μ]
  have h_prod (ρ : Measure β) [SFinite ρ] : μ.prod ρ = μ .univ • ((μ .univ)⁻¹ • μ).prod ρ := by
    rw [← Measure.prod_smul_left, smul_smul, ENNReal.mul_inv_cancel hμ0 (measure_ne_top _ _),
      one_smul]
  have h_emb : MeasurableEmbedding (Prod.swap : β × α → α × β) :=
    MeasurableEquiv.prodComm.measurableEmbedding
  rw [h_prod ξ, h_prod ψ, klDiv_smul_same' (measure_ne_top μ .univ), ← Measure.prod_swap (μ := ξ),
    ← Measure.prod_swap (μ := ψ), klDiv_eq_fDiv, klDiv_eq_fDiv,
    fDiv_map_measurableEmbedding h_emb, fDiv_prod_left]

lemma klDiv_prod_two' {ξ ψ : Measure β} [IsProbabilityMeasure ξ] [IsProbabilityMeasure ψ]
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    klDiv (μ.prod ξ) (ν.prod ψ) = klDiv μ ν + klDiv ξ ψ * (μ .univ) := by
  rw [← Measure.compProd_const, ← Measure.compProd_const, klDiv_compProd_eq_add,
    Measure.compProd_const, Measure.compProd_const, klDiv_prod_right, mul_comm]

/-- Tensorization property for KL divergence -/
lemma klDiv_prod_two {ξ ψ : Measure β} [IsProbabilityMeasure ξ] [IsProbabilityMeasure ψ]
    [IsProbabilityMeasure μ] [IsFiniteMeasure ν] :
    klDiv (μ.prod ξ) (ν.prod ψ) = klDiv μ ν + klDiv ξ ψ := by
  simp only [klDiv_prod_two', measure_univ, mul_one]

lemma klDiv_pi {ι : Type*} [hι : Fintype ι] {β : ι → Type*} [∀ i, MeasurableSpace (β i)]
    {μ ν : (i : ι) → Measure (β i)}
    [∀ i, IsProbabilityMeasure (μ i)] [∀ i, IsProbabilityMeasure (ν i)] :
    klDiv (Measure.pi μ) (Measure.pi ν) = ∑ i, klDiv (μ i) (ν i) := by
  refine Fintype.induction_empty_option (P := fun ι ↦ ∀ {β : ι → Type u_4}
    [(i : ι) → MeasurableSpace (β i)]
    {μ ν : (i : ι) → Measure (β i)} [∀ (i : ι), IsProbabilityMeasure (μ i)]
    [∀ (i : ι), IsProbabilityMeasure (ν i)],
    klDiv (Measure.pi μ) (Measure.pi ν) = ∑ i : ι, klDiv (μ i) (ν i) ) ?_ ?_ ?_ ι
  · intro ι ι' hι' e h β _ μ ν _ _
    let hι : Fintype ι := Fintype.ofEquiv _ e.symm
    specialize h (β := fun i ↦ β (e i)) (μ := fun i ↦ μ (e i)) (ν := fun i ↦ ν (e i))
    rw [Fintype.sum_equiv e.symm _ (fun i ↦ klDiv (μ (e i)) (ν (e i)))
      (fun i ↦ by rw [Equiv.apply_symm_apply]), ← h, klDiv_eq_fDiv, klDiv_eq_fDiv]
    let e_meas : ((b : ι) → β (e b)) ≃ᵐ ((a : ι') → β a) :=
      MeasurableEquiv.piCongrLeft (fun i ↦ β i) e
    have me := MeasurableEquiv.measurableEmbedding e_meas.symm
    convert (fDiv_map_measurableEmbedding me).symm
      <;> try {rw [← Measure.pi_map_piCongrLeft e, MeasurableEquiv.map_symm_map]}
      <;> infer_instance
  · intro β _ μ ν _ _
    rw [Measure.pi_of_empty, Measure.pi_of_empty, klDiv_self, Finset.univ_eq_empty,
      Finset.sum_empty]
  · intro ι hι ind_h β _ μ ν _ _
    specialize ind_h (β := fun i ↦ β i) (μ := fun i ↦ μ i) (ν := fun i ↦ ν i)
    have h : klDiv (Measure.pi μ) (Measure.pi ν) = klDiv ((Measure.pi (fun (i : ι) ↦ μ i)).prod
        (μ none)) ((Measure.pi (fun (i : ι) ↦ ν i)).prod (ν none)) := by
      rw [klDiv_eq_fDiv, klDiv_eq_fDiv]
      let e_meas : ((i : ι) → β (some i)) × β none ≃ᵐ ((i : Option ι) → β i) :=
        MeasurableEquiv.piOptionEquivProd β |>.symm
      have me := MeasurableEquiv.measurableEmbedding e_meas
      convert fDiv_map_measurableEmbedding me
        <;> try {exact Measure.pi_map_piOptionEquivProd _ |>.symm} <;> infer_instance
    rw [Fintype.sum_option, h, add_comm, ← ind_h]
    convert klDiv_prod_two <;> infer_instance

lemma klDiv_pi_const {ι : Type*} [hι : Fintype ι]
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    klDiv (Measure.pi (fun (_ : ι) ↦ μ)) (Measure.pi (fun (_ : ι) ↦ ν)) = hι.card * klDiv μ ν := by
  rw [klDiv_pi, Finset.sum_const, (Finset.card_eq_iff_eq_univ _).mpr rfl, nsmul_eq_mul]

end Tensorization

end ProbabilityTheory
