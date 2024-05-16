/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

/-!

-/

open Real MeasureTheory Filter

open scoped ENNReal MeasureTheory


lemma MeasureTheory.integrable_of_le_of_le {α : Type*} {mα : MeasurableSpace α} {μ : Measure α}
    {f g₁ g₂ : α → ℝ} (hf : AEStronglyMeasurable f μ)
    (h_le₁ : g₁ ≤ᵐ[μ] f) (h_le₂ : f ≤ᵐ[μ] g₂)
    (h_int₁ : Integrable g₁ μ) (h_int₂ : Integrable g₂ μ) :
    Integrable f μ := by
  have : ∀ᵐ x ∂μ, ‖f x‖ ≤ max ‖g₁ x‖ ‖g₂ x‖ := by
    filter_upwards [h_le₁, h_le₂] with x hx1 hx2
    simp only [norm_eq_abs]
    exact abs_le_max_abs_abs hx1 hx2
  have h_le_add : ∀ᵐ x ∂μ, ‖f x‖ ≤ ‖‖g₁ x‖ + ‖g₂ x‖‖ := by
    filter_upwards [this] with x hx
    refine hx.trans ?_
    conv_rhs => rw [norm_of_nonneg (by positivity)]
    exact max_le_add_of_nonneg (norm_nonneg _) (norm_nonneg _)
  exact Integrable.mono (h_int₁.norm.add h_int₂.norm) hf h_le_add

namespace MeasureTheory.Measure

variable {α β : Type*} {m mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μ ν : Measure α}

lemma rnDeriv_add_self_right (ν μ : Measure α) [SigmaFinite μ] [SigmaFinite ν] :
    ν.rnDeriv (μ + ν) =ᵐ[ν] fun x ↦ (μ.rnDeriv ν x + 1)⁻¹ := by
  have hν_ac : ν ≪ μ + ν := by rw [add_comm]; exact rfl.absolutelyContinuous.add_right _
  filter_upwards [Measure.rnDeriv_add' μ ν ν, Measure.rnDeriv_self ν,
    Measure.inv_rnDeriv hν_ac] with a h1 h2 h3
  rw [Pi.inv_apply, h1, Pi.add_apply, h2, inv_eq_iff_eq_inv] at h3
  rw [h3]

lemma rnDeriv_add_self_left (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν] :
    μ.rnDeriv (μ + ν) =ᵐ[ν] fun x ↦ μ.rnDeriv ν x / (μ.rnDeriv ν x + 1) := by
  have h_add : (μ + ν).rnDeriv (μ + ν) =ᵐ[ν] μ.rnDeriv (μ + ν) + ν.rnDeriv (μ + ν) :=
    (ae_add_measure_iff.mp (Measure.rnDeriv_add' μ ν (μ + ν))).2
  have h_one_add := (ae_add_measure_iff.mp (Measure.rnDeriv_self (μ + ν))).2
  have : (μ.rnDeriv (μ + ν)) =ᵐ[ν] fun x ↦ 1 - (μ.rnDeriv ν x + 1)⁻¹ := by
    filter_upwards [h_add, h_one_add, rnDeriv_add_self_right ν μ] with a h4 h5 h6
    rw [h5, Pi.add_apply] at h4
    nth_rewrite 1 [h4]
    rw [h6]
    simp only [ne_eq, ENNReal.inv_eq_top, add_eq_zero, one_ne_zero, and_false, not_false_eq_true,
      ENNReal.add_sub_cancel_right]
  filter_upwards [this, Measure.rnDeriv_lt_top μ ν] with a ha ha_lt_top
  rw [ha, div_eq_mul_inv]
  refine ENNReal.sub_eq_of_eq_add (by simp) ?_
  nth_rewrite 2 [← one_mul (μ.rnDeriv ν a + 1)⁻¹]
  have h := add_mul (μ.rnDeriv ν a) 1 (μ.rnDeriv ν a + 1)⁻¹
  rw [ENNReal.mul_inv_cancel] at h
  · exact h
  · simp
  · simp [ha_lt_top.ne]

lemma rnDeriv_eq_div (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν] :
    μ.rnDeriv ν =ᵐ[ν] fun x ↦ μ.rnDeriv (μ + ν) x / ν.rnDeriv (μ + ν) x := by
  filter_upwards [rnDeriv_add_self_right ν μ, rnDeriv_add_self_left μ ν, Measure.rnDeriv_lt_top μ ν]
      with a ha1 ha2 ha_lt_top
  rw [ha1, ha2, ENNReal.div_eq_inv_mul, inv_inv, ENNReal.div_eq_inv_mul, ← mul_assoc,
      ENNReal.mul_inv_cancel, one_mul]
  · simp
  · simp [ha_lt_top.ne]

lemma rnDeriv_div_rnDeriv {ξ : Measure α} [SigmaFinite μ] [SigmaFinite ν] [SigmaFinite ξ]
    (hμ : μ ≪ ξ) (hν : ν ≪ ξ) :
    (fun x ↦ μ.rnDeriv ξ x / ν.rnDeriv ξ x)
      =ᵐ[μ + ν] fun x ↦ μ.rnDeriv (μ + ν) x / ν.rnDeriv (μ + ν) x := by
  have h1 : μ.rnDeriv (μ + ν) * (μ + ν).rnDeriv ξ =ᵐ[ξ] μ.rnDeriv ξ :=
    Measure.rnDeriv_mul_rnDeriv (rfl.absolutelyContinuous.add_right _)
  have h2 : ν.rnDeriv (μ + ν) * (μ + ν).rnDeriv ξ =ᵐ[ξ] ν.rnDeriv ξ :=
    Measure.rnDeriv_mul_rnDeriv ?_
  swap; · rw [add_comm]; exact rfl.absolutelyContinuous.add_right _
  have h_ac : μ + ν ≪ ξ := by
    refine (Measure.AbsolutelyContinuous.add hμ hν).trans ?_
    have : ξ + ξ = (2 : ℝ≥0∞) • ξ := by
      ext
      simp only [Measure.coe_add, Pi.add_apply, Measure.coe_smul, Pi.smul_apply, smul_eq_mul]
      rw [two_mul]
    rw [this]
    exact Measure.absolutelyContinuous_of_le_smul le_rfl
  filter_upwards [h_ac h1, h_ac h2, h_ac <| Measure.rnDeriv_lt_top (μ + ν) ξ,
    Measure.rnDeriv_lt_top ν (μ + ν), Measure.rnDeriv_pos h_ac]
    with a h1 h2 h_lt_top1 h_lt_top2 h_pos
  rw [← h1, ← h2, Pi.mul_apply, Pi.mul_apply, div_eq_mul_inv,
    ENNReal.mul_inv (Or.inr h_lt_top1.ne) (Or.inl h_lt_top2.ne), div_eq_mul_inv, mul_assoc,
    mul_comm ((μ + ν).rnDeriv ξ a), mul_assoc, ENNReal.inv_mul_cancel h_pos.ne' h_lt_top1.ne,
    mul_one]

lemma rnDeriv_eq_div' {ξ : Measure α} [SigmaFinite μ] [SigmaFinite ν] [SigmaFinite ξ]
    (hμ : μ ≪ ξ) (hν : ν ≪ ξ) :
    μ.rnDeriv ν =ᵐ[ν] fun x ↦ μ.rnDeriv ξ x / ν.rnDeriv ξ x := by
  have hν_ac : ν ≪ μ + ν := by rw [add_comm]; exact rfl.absolutelyContinuous.add_right _
  filter_upwards [rnDeriv_eq_div μ ν, hν_ac (rnDeriv_div_rnDeriv hμ hν)] with a h1 h2
  exact h1.trans h2.symm

/--Singular part set of μ with respect to ν.-/
def singularPartSet (μ ν : Measure α) := {x | ν.rnDeriv (μ + ν) x = 0}

lemma measurableSet_singularPartSet : MeasurableSet (singularPartSet μ ν) :=
  measurable_rnDeriv _ _ (measurableSet_singleton _)

lemma measure_singularPartSet (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν] :
    ν (singularPartSet μ ν) = 0 := by
  let s := singularPartSet μ ν
  have hs : MeasurableSet s := measurableSet_singularPartSet
  have hν_ac : ν ≪ μ + ν := by rw [add_comm]; exact rfl.absolutelyContinuous.add_right _
  have h1 : ∫⁻ x in s, ν.rnDeriv (μ + ν) x ∂(μ + ν) = 0 := by
    calc ∫⁻ x in s, ν.rnDeriv (μ + ν) x ∂(μ + ν)
      = ∫⁻ _ in s, 0 ∂(μ + ν) := set_lintegral_congr_fun hs (ae_of_all _ (fun _ hx ↦ hx))
    _ = 0 := lintegral_zero
  have h2 : ∫⁻ x in s, ν.rnDeriv (μ + ν) x ∂(μ + ν) = ν s :=
    Measure.set_lintegral_rnDeriv hν_ac _
  exact h2.symm.trans h1

lemma measure_inter_compl_singularPartSet' (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν]
    {t : Set α} (ht : MeasurableSet t) :
    μ (t ∩ (singularPartSet μ ν)ᶜ) = ∫⁻ x in t ∩ (singularPartSet μ ν)ᶜ, μ.rnDeriv ν x ∂ν := by
  let s := singularPartSet μ ν
  have hs : MeasurableSet s := measurableSet_singularPartSet
  have hν_ac : ν ≪ μ + ν := by rw [add_comm]; exact rfl.absolutelyContinuous.add_right _
  have : μ (t ∩ sᶜ) = ∫⁻ x in t ∩ sᶜ,
      ν.rnDeriv (μ + ν) x * (μ.rnDeriv (μ + ν) x / ν.rnDeriv (μ + ν) x) ∂(μ + ν) := by
    have : ∫⁻ x in t ∩ sᶜ,
          ν.rnDeriv (μ + ν) x * (μ.rnDeriv (μ + ν) x / ν.rnDeriv (μ + ν) x) ∂(μ + ν)
        = ∫⁻ x in t ∩ sᶜ, μ.rnDeriv (μ + ν) x ∂(μ + ν) := by
      refine set_lintegral_congr_fun (ht.inter hs.compl) ?_
      filter_upwards [Measure.rnDeriv_lt_top ν (μ + ν)] with x hx_top hx
      rw [div_eq_mul_inv, mul_comm, mul_assoc, ENNReal.inv_mul_cancel, mul_one]
      · simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_setOf_eq, s] at hx
        exact hx.2
      · exact hx_top.ne
    rw [this, Measure.set_lintegral_rnDeriv (rfl.absolutelyContinuous.add_right _)]
  rw [this, set_lintegral_rnDeriv_mul hν_ac _ (ht.inter hs.compl)]
  swap
  · exact ((Measure.measurable_rnDeriv _ _).div (Measure.measurable_rnDeriv _ _)).aemeasurable
  refine set_lintegral_congr_fun (ht.inter hs.compl) ?_
  filter_upwards [Measure.rnDeriv_eq_div μ ν] with x hx
  rw [hx]
  exact fun _ ↦ rfl

lemma measure_inter_compl_singularPartSet (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν]
    {t : Set α} (ht : MeasurableSet t) :
    μ (t ∩ (singularPartSet μ ν)ᶜ) = ∫⁻ x in t, μ.rnDeriv ν x ∂ν := by
  rw [measure_inter_compl_singularPartSet' _ _ ht]
  symm
  calc ∫⁻ x in t, rnDeriv μ ν x ∂ν
    = ∫⁻ x in (singularPartSet μ ν) ∩ t, rnDeriv μ ν x ∂ν
      + ∫⁻ x in (singularPartSet μ ν)ᶜ ∩ t, rnDeriv μ ν x ∂ν := by
        rw [← restrict_restrict measurableSet_singularPartSet,
          ← restrict_restrict measurableSet_singularPartSet.compl,
          lintegral_add_compl _ measurableSet_singularPartSet]
  _ = ∫⁻ x in t ∩ (singularPartSet μ ν)ᶜ, rnDeriv μ ν x ∂ν := by
        rw [set_lintegral_measure_zero _ _ (measure_mono_null (Set.inter_subset_left _ _) ?_),
          Set.inter_comm, zero_add]
        exact measure_singularPartSet _ _

lemma restrict_compl_singularPartSet_eq_withDensity
    (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν] :
    μ.restrict (singularPartSet μ ν)ᶜ = ν.withDensity (μ.rnDeriv ν) := by
  ext t ht
  rw [restrict_apply ht, measure_inter_compl_singularPartSet μ ν ht, withDensity_apply _ ht]

lemma restrict_singularPartSet_eq_singularPart (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν] :
    μ.restrict (singularPartSet μ ν) = μ.singularPart ν := by
  have h_add := haveLebesgueDecomposition_add μ ν
  rw [← restrict_compl_singularPartSet_eq_withDensity μ ν] at h_add
  have : μ = μ.restrict (singularPartSet μ ν) + μ.restrict (singularPartSet μ ν)ᶜ := by
    rw [restrict_add_restrict_compl measurableSet_singularPartSet]
  conv_lhs at h_add => rw [this]
  exact (Measure.add_left_inj _ _ _).mp h_add

lemma absolutelyContinuous_restrict_compl_singularPartSet
    (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν] :
    μ.restrict (singularPartSet μ ν)ᶜ ≪ ν := by
  rw [restrict_compl_singularPartSet_eq_withDensity]
  exact withDensity_absolutelyContinuous _ _

example [SigmaFinite μ] [SigmaFinite ν] :
    μ {x | (ν.rnDeriv (μ + ν)) x = 0} = μ.singularPart ν Set.univ := by
  rw [← restrict_singularPartSet_eq_singularPart]
  simp only [MeasurableSet.univ, restrict_apply, Set.univ_inter]
  rfl

section Trim

lemma toReal_rnDeriv_trim_of_ac (hm : m ≤ mα) [IsFiniteMeasure μ] [SigmaFinite ν]
    [SigmaFinite (ν.trim hm)] (hμν : μ ≪ ν) :
    (fun x ↦ ((μ.trim hm).rnDeriv (ν.trim hm) x).toReal)
      =ᵐ[ν.trim hm] ν[fun x ↦ (μ.rnDeriv ν x).toReal | m] := by
  have h_meas : StronglyMeasurable[m] fun x ↦ (rnDeriv (trim μ hm) (trim ν hm) x).toReal := by
    refine Measurable.stronglyMeasurable ?_
    exact @Measurable.ennreal_toReal _ m _ (Measure.measurable_rnDeriv _ _)
  rw [ae_eq_trim_iff _ h_meas stronglyMeasurable_condexp]
  refine ae_eq_condexp_of_forall_setIntegral_eq ?_ integrable_toReal_rnDeriv ?_ ?_
    h_meas.aeStronglyMeasurable'
  · exact fun s _ _ ↦ (integrable_of_integrable_trim hm integrable_toReal_rnDeriv).integrableOn
  · intro s hs _
    rw [integral_trim hm h_meas, setIntegral_toReal_rnDeriv hμν, ← restrict_trim _ _ hs,
      setIntegral_toReal_rnDeriv (hμν.trim hm), trim_measurableSet_eq hm hs]

lemma rnDeriv_trim_of_ac (hm : m ≤ mα) [IsFiniteMeasure μ] [SigmaFinite ν]
    [SigmaFinite (ν.trim hm)] (hμν : μ ≪ ν) :
    (μ.trim hm).rnDeriv (ν.trim hm)
      =ᵐ[ν.trim hm] fun x ↦ ENNReal.ofReal ((ν[fun x ↦ (μ.rnDeriv ν x).toReal | m]) x) := by
  filter_upwards [toReal_rnDeriv_trim_of_ac hm hμν, rnDeriv_ne_top (μ.trim hm) (ν.trim hm)]
    with x hx hx_ne_top
  rw [← hx, ENNReal.ofReal_toReal hx_ne_top]

end Trim

lemma rnDeriv_toReal_pos [SigmaFinite μ] [SigmaFinite ν] (hμν : μ ≪ ν) :
    ∀ᵐ x ∂μ, 0 < (μ.rnDeriv ν x).toReal := by
  filter_upwards [rnDeriv_pos hμν, hμν.ae_le (rnDeriv_ne_top μ ν)] with x h0 htop
  simp_all only [pos_iff_ne_zero, ne_eq, not_false_eq_true, ENNReal.toReal_pos]

lemma ae_rnDeriv_ne_zero_imp_of_ae_aux [SigmaFinite μ] [SigmaFinite ν] {p : α → Prop}
    (h : ∀ᵐ a ∂μ, p a) (hμν : μ ≪ ν) :
    ∀ᵐ a ∂ν, μ.rnDeriv ν a ≠ 0 → p a := by
  rw [Measure.haveLebesgueDecomposition_add ν μ]
  rw [ae_add_measure_iff]
  constructor
  · rw [← Measure.haveLebesgueDecomposition_add ν μ]
    have : ∀ᵐ x ∂(ν.singularPart μ), μ.rnDeriv ν x = 0 := by
      refine ae_eq_of_forall_set_lintegral_eq_of_sigmaFinite (Measure.measurable_rnDeriv _ _)
        measurable_const (fun s hs _ ↦ ?_)
      simp only [lintegral_const, MeasurableSet.univ, Measure.restrict_apply, Set.univ_inter,
        zero_mul]
      rw [← Measure.restrict_singularPartSet_eq_singularPart, Measure.restrict_restrict hs,
        Measure.set_lintegral_rnDeriv hμν]
      exact measure_mono_null (Set.inter_subset_right _ _) (Measure.measure_singularPartSet _ _)
    filter_upwards [this] with x hx h_absurd using absurd hx h_absurd
  · have h_ac : μ.withDensity (ν.rnDeriv μ) ≪ μ := withDensity_absolutelyContinuous _ _
    rw [← Measure.haveLebesgueDecomposition_add ν μ]
    suffices ∀ᵐx ∂μ, μ.rnDeriv ν x ≠ 0 → p x from h_ac this
    filter_upwards [h] with _ h _ using h

lemma ae_rnDeriv_ne_zero_imp_of_ae [SigmaFinite μ] [SigmaFinite ν] {p : α → Prop}
    (h : ∀ᵐ a ∂μ, p a) :
    ∀ᵐ a ∂ν, μ.rnDeriv ν a ≠ 0 → p a := by
  suffices ∀ᵐ a ∂ν, (ν.withDensity (μ.rnDeriv ν)).rnDeriv ν a ≠ 0 → p a by
    have h := Measure.rnDeriv_withDensity ν (Measure.measurable_rnDeriv μ ν)
    filter_upwards [this, h] with x hx1 hx2
    rwa [hx2] at hx1
  refine ae_rnDeriv_ne_zero_imp_of_ae_aux ?_ (withDensity_absolutelyContinuous _ _)
  exact (Measure.absolutelyContinuous_of_le (μ.withDensity_rnDeriv_le ν)) h

lemma ae_integrable_mul_rnDeriv_of_ae_integrable {κ : α → Measure β} [SigmaFinite μ] [SigmaFinite ν]
    (g : α → β → ℝ) (h : ∀ᵐ a ∂μ, Integrable (fun x => g a x) (κ a)) :
    ∀ᵐ a ∂ν, Integrable (fun x ↦ (μ.rnDeriv ν a).toReal * g a x) (κ a) := by
  apply @Measure.ae_rnDeriv_ne_zero_imp_of_ae _ _ _ ν at h
  filter_upwards [h] with a ha
  by_cases h_zero : μ.rnDeriv ν a = 0
  · rw [h_zero]
    simp only [ENNReal.zero_toReal, zero_mul, integrable_zero]
  · apply Integrable.const_mul
    exact ha h_zero

lemma ae_integrable_of_ae_integrable_mul_rnDeriv {κ : α → Measure β} [SigmaFinite μ] [SigmaFinite ν]
    (hμν : μ ≪ ν) (g : α → β → ℝ)
    (h : ∀ᵐ a ∂ν, Integrable (fun x ↦ (μ.rnDeriv ν a).toReal * g a x) (κ a)) :
    ∀ᵐ a ∂μ, Integrable (fun x => g a x) (κ a) := by
  filter_upwards [hμν.ae_le h, Measure.rnDeriv_toReal_pos hμν] with a ha h_pos
  apply (integrable_const_mul_iff _ (fun x ↦ g a x)).mp ha
  apply isUnit_iff_ne_zero.mpr
  linarith

end MeasureTheory.Measure

namespace MeasurableEmbedding

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μ ν : Measure α}

lemma _root_.MeasurableEmbedding.absolutelyContinuous_map (hμν : μ ≪ ν)
    {g : α → β} (hg : MeasurableEmbedding g) :
    μ.map g ≪ ν.map g := by
  intro t ht
  rw [hg.map_apply] at ht ⊢
  exact hμν ht

lemma _root_.MeasurableEmbedding.mutuallySingular_map (hμν : μ ⟂ₘ ν)
    {g : α → β} (hg : MeasurableEmbedding g) :
    μ.map g ⟂ₘ ν.map g := by
  refine ⟨g '' hμν.nullSet, hg.measurableSet_image' hμν.measurableSet_nullSet, ?_, ?_⟩
  · rw [hg.map_apply, hg.injective.preimage_image, hμν.measure_nullSet]
  · rw [hg.map_apply, Set.preimage_compl, hg.injective.preimage_image, hμν.measure_compl_nullSet]

lemma _root_.MeasurableEmbedding.rnDeriv_map_aux (hμν : μ ≪ ν)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {g : α → β} (hg : MeasurableEmbedding g) :
    (fun x ↦ (μ.map g).rnDeriv (ν.map g) (g x)) =ᵐ[ν] μ.rnDeriv ν := by
  refine ae_eq_of_forall_set_lintegral_eq_of_sigmaFinite ?_ ?_ (fun s _ _ ↦ ?_)
  · exact (Measure.measurable_rnDeriv _ _).comp hg.measurable
  · exact Measure.measurable_rnDeriv _ _
  rw [← hg.lintegral_map, Measure.set_lintegral_rnDeriv hμν]
  have hs_eq : s = g ⁻¹' (g '' s) := by rw [hg.injective.preimage_image]
  rw [hs_eq, ← hg.restrict_map, Measure.set_lintegral_rnDeriv (hg.absolutelyContinuous_map hμν),
    hg.map_apply]

lemma _root_.MeasurableEmbedding.rnDeriv_map (μ ν : Measure α)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {g : α → β} (hg : MeasurableEmbedding g) :
    (fun x ↦ (μ.map g).rnDeriv (ν.map g) (g x)) =ᵐ[ν] μ.rnDeriv ν := by
  rw [μ.haveLebesgueDecomposition_add ν, Measure.map_add _ _ hg.measurable]
  have h_add := Measure.rnDeriv_add ((μ.singularPart ν).map g) ((ν.withDensity (μ.rnDeriv ν)).map g)
    (ν.map g)
  rw [EventuallyEq, hg.ae_map_iff, ← EventuallyEq] at h_add
  refine h_add.trans ((Measure.rnDeriv_add _ _ _).trans ?_).symm
  refine EventuallyEq.add ?_ ?_
  · refine (Measure.rnDeriv_singularPart μ ν).trans ?_
    symm
    suffices (fun x ↦ ((μ.singularPart ν).map g).rnDeriv (ν.map g) x) =ᵐ[ν.map g] 0 by
      rw [EventuallyEq, hg.ae_map_iff] at this
      exact this
    refine Measure.rnDeriv_eq_zero_of_mutuallySingular ?_ Measure.AbsolutelyContinuous.rfl
    exact hg.mutuallySingular_map (μ.mutuallySingular_singularPart ν)
  · exact (hg.rnDeriv_map_aux (withDensity_absolutelyContinuous _ _)).symm

lemma _root_.MeasurableEmbedding.map_withDensity_rnDeriv (μ ν : Measure α)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {g : α → β} (hg : MeasurableEmbedding g) :
    (ν.withDensity (μ.rnDeriv ν)).map g = (ν.map g).withDensity ((μ.map g).rnDeriv (ν.map g)) := by
  ext s hs
  rw [hg.map_apply, withDensity_apply _ (hg.measurable hs), withDensity_apply _ hs,
    set_lintegral_map hs (Measure.measurable_rnDeriv _ _) hg.measurable]
  refine set_lintegral_congr_fun (hg.measurable hs) ?_
  filter_upwards [hg.rnDeriv_map μ ν] with a ha _ using ha.symm

lemma _root_.MeasurableEmbedding.singularPart_map (μ ν : Measure α)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {g : α → β} (hg : MeasurableEmbedding g) :
    (μ.map g).singularPart (ν.map g) = (μ.singularPart ν).map g := by
  have h_add : μ.map g = (μ.singularPart ν).map g
      + (ν.map g).withDensity ((μ.map g).rnDeriv (ν.map g)) := by
    conv_lhs => rw [μ.haveLebesgueDecomposition_add ν]
    rw [Measure.map_add _ _ hg.measurable, ← hg.map_withDensity_rnDeriv μ ν]
  refine (Measure.eq_singularPart (Measure.measurable_rnDeriv _ _) ?_ h_add).symm
  exact hg.mutuallySingular_map (μ.mutuallySingular_singularPart ν)

end MeasurableEmbedding
