/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
import TestingLowerBounds.FDiv.CondFDiv
import TestingLowerBounds.FDiv.Measurable

/-!

# Conditional f-divergence

-/

open MeasureTheory MeasurableSpace Set Filter Real

namespace ProbabilityTheory

variable {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}
  {μ : Measure α} {f : ℝ → ℝ}

lemma condFDiv_snd'_toReal_eq_ae [CountableOrCountablyGenerated β γ] {ξ : Kernel α β}
    [IsFiniteKernel ξ] {κ η : Kernel (α × β) γ} [IsFiniteKernel κ] [IsFiniteKernel η]
    (h_cvx : ConvexOn ℝ (Ici 0) f)
    (h_ac : derivAtTop f = ⊤ → ∀ᵐ a ∂μ, ∀ᵐ b ∂ξ a, κ (a, b) ≪ η (a, b))
    (h_int : ∀ᵐ a ∂μ, ∀ᵐ b ∂ξ a, Integrable (fun x ↦ f ((∂κ (a, b)/∂η (a, b)) x).toReal) (η (a, b)))
    (h_int2 : ∀ᵐ a ∂μ, Integrable
      (fun b ↦ ∫ x, f ((∂κ (a, b)/∂η (a, b)) x).toReal ∂η (a, b)) (ξ a)) :
    ∀ᵐ a ∂μ, (condFDiv f (κ.snd' a) (η.snd' a) (ξ a)).toReal =
      ∫ b, (fDiv f (κ (a, b)) (η (a, b))).toReal ∂ξ a := by
  simp_rw [← Kernel.snd'_apply] at h_int2 h_int h_ac ⊢
  rw [← eventually_all] at h_ac
  filter_upwards [h_ac, h_int, h_int2] with a ha_ac ha_int ha_int2
  rw [condFDiv_eq h_cvx ha_int ha_int2 ha_ac, EReal.toReal_coe]

lemma condFDiv_kernel_snd'_integrable_iff [CountableOrCountablyGenerated (α × β) γ]
    [IsFiniteMeasure μ] {ξ : Kernel α β}  [IsFiniteKernel ξ]
    {κ η : Kernel (α × β) γ} [IsMarkovKernel κ] [IsMarkovKernel η]
    (h_ac : derivAtTop f = ⊤ → ∀ᵐ a ∂μ, ∀ᵐ b ∂ξ a, κ (a, b) ≪ η (a, b))
    (h_int : ∀ᵐ a ∂μ, ∀ᵐ b ∂ξ a, Integrable (fun x ↦ f ((∂κ (a, b)/∂η (a, b)) x).toReal) (η (a, b)))
    (h_int2 : ∀ᵐ a ∂μ, Integrable (fun b ↦ ∫ x, f ((∂κ (a, b)/∂η (a, b)) x).toReal ∂η (a, b)) (ξ a))
    (hf_meas : StronglyMeasurable f) (hf_cvx : ConvexOn ℝ (Ici 0) f)
    (hf_cont : ContinuousOn f (Ici 0)) (hf_one : f 1 = 0) :
    Integrable (fun a ↦ (condFDiv f (κ.snd' a) (η.snd' a) (ξ a)).toReal) μ ↔
      Integrable (fun a ↦ ∫ b, |∫ x, f ((∂κ (a, b)/∂η (a, b)) x).toReal ∂η (a, b)| ∂ξ a) μ := by
  by_cases h_empty : Nonempty α
  swap; simp only [not_nonempty_iff.mp h_empty, Integrable.of_isEmpty]
  have := countableOrCountablyGenerated_right_of_prod_left_of_nonempty (α := α) (β := β) (γ := γ)
  have h_le : ∀ᵐ a ∂μ, ∀ᵐ b ∂ξ a, |∫ x, f ((∂κ (a, b)/∂η (a, b)) x).toReal ∂η (a, b)|
        - (fDiv f (κ (a, b)) (η (a, b))).toReal ≤ |(derivAtTop f).toReal|
      ∧ (fDiv f (κ (a, b)) (η (a, b))).toReal - |∫ x, f ((∂κ (a, b)/∂η (a, b)) x).toReal ∂η (a, b)|
        ≤ |(derivAtTop f).toReal| := by
    filter_upwards [fDiv_toReal_eq_ae hf_cvx h_ac h_int] with a ha_ereal_add
    filter_upwards [ha_ereal_add] with b hb_ereal_add
    apply abs_sub_le_iff.mp
    calc
      _ = |(|∫ (x : γ), f ((∂κ (a, b)/∂η (a, b)) x).toReal ∂η (a, b)|
          - |(fDiv f (κ (a, b)) (η (a, b))).toReal|)| := by
        rw [abs_eq_self.mpr <| EReal.toReal_nonneg (fDiv_nonneg hf_cvx hf_cont hf_one)]
      _ ≤ |∫ (x : γ), f ((∂κ (a, b)/∂η (a, b)) x).toReal ∂η (a, b)
          - (fDiv f (κ (a, b)) (η (a, b))).toReal| := by
        exact abs_abs_sub_abs_le_abs_sub _ _
      _ = |(derivAtTop f).toReal| * ((κ (a, b)).singularPart (η (a, b)) .univ).toReal := by
        rw [hb_ereal_add, sub_add_cancel_left, abs_neg, abs_mul, ENNReal.abs_toReal]
      _ ≤ |(derivAtTop f).toReal| * ((κ (a, b)) .univ).toReal := by
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        gcongr
        · exact measure_ne_top (κ (a, b)) .univ
        · exact (κ (a, b)).singularPart_le (η (a, b)) .univ
      _ = _ := by rw [measure_univ, ENNReal.one_toReal, mul_one]
  have h_int2' : ∀ᵐ a ∂μ, Integrable (fun b ↦ (fDiv f (κ (a, b)) (η (a, b))).toReal) (ξ a) := by
    filter_upwards [eventually_all.mpr h_ac, h_int, h_int2] with a ha_ae ha_int ha_int2
    simp_rw [← Kernel.snd'_apply] at ha_int2 ha_int ha_ae ⊢
    exact (integrable_fDiv_iff hf_cvx ha_int ha_ae).mpr ha_int2
  rw [integrable_congr <| condFDiv_snd'_toReal_eq_ae hf_cvx h_ac h_int h_int2]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · -- using `h_le` we reduce the problem to the integrability of a sum of an integral and
    -- `f'(∞) * (ξ x) (univ)`
    apply Integrable.mono'
      (g := fun a ↦ ∫ b, ((fDiv f (κ (a, b)) (η (a, b))).toReal + |(derivAtTop f).toReal|) ∂ξ a)
    rotate_left
    · refine (StronglyMeasurable.integral_kernel_prod_right ?_).aestronglyMeasurable
      refine Measurable.abs ?_ |>.stronglyMeasurable
      exact measurable_integral_f_rnDeriv κ η hf_meas
    · filter_upwards [h_le, h_int2, h_int2'] with a ha_le ha_int2 ha_int2'
      rw [norm_eq_abs, abs_eq_self.mpr <| integral_nonneg <| fun _ ↦ abs_nonneg _]
      refine integral_mono_ae ha_int2.abs (integrable_add_const_iff.mpr ha_int2') ?_
      filter_upwards [ha_le] with a hb_le using by linarith
    apply Integrable.congr (f := fun a ↦ ∫ b, (fDiv f (κ (a, b)) (η (a, b))).toReal ∂ξ a
      + ((ξ a) .univ).toReal * |(derivAtTop f).toReal|)
    swap
    · filter_upwards [h_int2'] with a ha_int2'
      rw [integral_add ha_int2' (integrable_const _), integral_const, smul_eq_mul]
    -- we already know the integrability of the integral (hp `h`) and the other part is just a
    -- constant times a finite Kernel applied to a fixed set, so it's easy to show that
    -- it's integrable
    exact h.add (Integrable.Kernel _ .univ |>.mul_const _)
  · -- using `h_le'` we reduce the problem to the integrability of a sum of an integral and
    -- `f'(∞) * (ξ x) (univ)`
    apply Integrable.mono' (g := fun a ↦ ∫ b,
      (|∫ (x : γ), f ((∂κ (a, b)/∂η (a, b)) x).toReal ∂η (a, b)| + |(derivAtTop f).toReal|) ∂ξ a)
    rotate_left
    · refine (StronglyMeasurable.integral_kernel_prod_right ?_).aestronglyMeasurable
      exact (measurable_fDiv _ _ hf_meas).ereal_toReal.stronglyMeasurable
    · filter_upwards [h_le, h_int2, h_int2'] with a ha_le ha_int2 ha_int2'
      rw [norm_eq_abs, abs_eq_self.mpr <| integral_nonneg <| fun _ ↦ EReal.toReal_nonneg <|
        fDiv_nonneg hf_cvx hf_cont hf_one]
      refine integral_mono_ae ha_int2' (integrable_add_const_iff.mpr <| ha_int2.abs) ?_
      filter_upwards [ha_le] with a hb_le using by linarith
    apply Integrable.congr (f := fun a ↦ ∫ b, |∫ x, f ((∂κ (a, b)/∂η (a, b)) x).toReal ∂η (a, b)|
      ∂ξ a + ((ξ a) .univ).toReal * |(derivAtTop f).toReal|)
    swap
    · filter_upwards [h_int2] with a ha_int2
      rw [integral_add ha_int2.abs (integrable_const _), integral_const, smul_eq_mul]
    -- same as above
    exact h.add (Integrable.Kernel _ .univ |>.mul_const _)

lemma condFDiv_kernel_fst'_integrable_iff [CountableOrCountablyGenerated (α × β) γ]
    {μ : Measure β} [IsFiniteMeasure μ] {ξ : Kernel β α} [IsFiniteKernel ξ]
    {κ η : Kernel (α × β) γ} [IsMarkovKernel κ] [IsMarkovKernel η]
    (h_ac : derivAtTop f = ⊤ → ∀ᵐ b ∂μ, ∀ᵐ a ∂ξ b, κ (a, b) ≪ η (a, b))
    (h_int : ∀ᵐ b ∂μ, ∀ᵐ a ∂ξ b, Integrable (fun x ↦ f ((∂κ (a, b)/∂η (a, b)) x).toReal) (η (a, b)))
    (h_int2 : ∀ᵐ b ∂μ, Integrable (fun a ↦ ∫ x, f ((∂κ (a, b)/∂η (a, b)) x).toReal ∂η (a, b)) (ξ b))
    (hf_meas : StronglyMeasurable f) (hf_cvx : ConvexOn ℝ (Ici 0) f)
    (hf_cont : ContinuousOn f (Ici 0)) (hf_one : f 1 = 0) :
    Integrable (fun b ↦ (condFDiv f (κ.fst' b) (η.fst' b) (ξ b)).toReal) μ ↔
      Integrable (fun b ↦ ∫ a, |∫ x, f ((∂κ (a, b)/∂η (a, b)) x).toReal ∂η (a, b)| ∂ξ b) μ := by
  simp_rw [← Kernel.snd'_swapRight]
  exact condFDiv_kernel_snd'_integrable_iff h_ac h_int h_int2 hf_meas hf_cvx hf_cont hf_one

lemma condFDiv_compProd_meas_eq_top [CountableOrCountablyGenerated (α × β) γ] [IsFiniteMeasure μ]
    {ξ : Kernel α β} [IsFiniteKernel ξ]
    {κ η : Kernel (α × β) γ} [IsMarkovKernel κ] [IsMarkovKernel η]
    (hf_meas : StronglyMeasurable f) (hf_cvx : ConvexOn ℝ (Ici 0) f)
    (hf_cont : ContinuousOn f (Ici 0)) (hf_one : f 1 = 0) :
    condFDiv f κ η (μ ⊗ₘ ξ) = ⊤
      ↔ ¬ (∀ᵐ a ∂μ, condFDiv f (κ.snd' a) (η.snd' a) (ξ a) ≠ ⊤) ∨
        ¬ Integrable (fun x ↦ (condFDiv f (κ.snd' x) (η.snd' x) (ξ x)).toReal) μ := by
  by_cases h_empty : Nonempty α
  swap; simp only [isEmpty_prod, not_nonempty_iff.mp h_empty, true_or, condFDiv_of_isEmpty_left,
    EReal.zero_ne_top, IsEmpty.forall_iff, Eventually.of_forall, not_true_eq_false,
    Integrable.of_isEmpty, or_self]
  have := countableOrCountablyGenerated_right_of_prod_left_of_nonempty (α := α) (β := β) (γ := γ)
  rw [condFDiv_eq_top_iff hf_cvx]
  constructor
  · by_cases h_ac : derivAtTop f = ⊤ → ∀ᵐ x ∂(μ ⊗ₘ ξ), κ x ≪ η x
    swap
    · rw [Measure.ae_compProd_iff (κ.measurableSet_absolutelyContinuous _)] at h_ac
      simp_rw [condFDiv_ne_top_iff hf_cvx, Kernel.snd'_apply, eventually_and, not_and_or,
        eventually_all]
      intro; left; right; right
      exact h_ac
    have h_ac' := h_ac
    rw [Measure.ae_compProd_iff (κ.measurableSet_absolutelyContinuous _)] at h_ac
    by_cases h_int : ∀ᵐ a ∂μ, ∀ᵐ b ∂ξ a,
      Integrable (fun y ↦ f ((∂κ (a, b)/∂η (a, b)) y).toReal) (η (a, b))
    swap; · simp only [not_eventually, ne_eq, condFDiv_ne_top_iff hf_cvx, Kernel.snd'_apply,
        eventually_and, h_int, eventually_all, false_and, not_false_eq_true, true_or, implies_true]
    have h_int' := h_int
    rw [← Measure.ae_compProd_iff (measurableSet_integrable_f_rnDeriv κ η hf_meas)] at h_int'
    rw [← _root_.not_imp]
    simp_all only [forall_true_left, not_true_eq_false, implies_true, or_false, false_or, ne_eq,
      not_eventually, not_not]
    rw [Measure.integrable_compProd_iff
      (measurable_integral_f_rnDeriv κ η hf_meas).aestronglyMeasurable]
    push_neg
    intro h
    by_cases h_int2 :
      ∀ᵐ a ∂μ, Integrable (fun b ↦ ∫ x, f ((∂κ (a, b)/∂η (a, b)) x).toReal ∂η (a, b)) (ξ a)
    · simp_all only [forall_true_left, norm_eq_abs]
      right
      exact (condFDiv_kernel_snd'_integrable_iff
        h_ac h_int h_int2 hf_meas hf_cvx hf_cont hf_one).mp.mt h
    · left
      contrapose! h_int2
      simp_rw [not_frequently, condFDiv_ne_top_iff hf_cvx] at h_int2
      filter_upwards [h_int2] with a ha_int2
      simp_rw [← Kernel.snd'_apply, ha_int2.2.1]
  · intro h
    contrapose! h
    rcases h with ⟨h_int1, ⟨h_int2, h_ac⟩⟩
    rw [Measure.ae_compProd_iff (measurableSet_integrable_f_rnDeriv κ η hf_meas)] at h_int1
    rw [Measure.ae_compProd_iff (κ.measurableSet_absolutelyContinuous _)] at h_ac
    rw [Measure.integrable_compProd_iff h_int2.aestronglyMeasurable] at h_int2
    simp_all only [implies_true, forall_true_left, norm_eq_abs]
    refine ⟨?_, condFDiv_kernel_snd'_integrable_iff h_ac h_int1 h_int2.1 hf_meas hf_cvx hf_cont
      hf_one |>.mpr h_int2.2⟩
    filter_upwards [eventually_all.mpr h_ac, h_int1, h_int2.1] with a ha_ae ha_int ha_int2
    apply (condFDiv_ne_top_iff hf_cvx).mpr
    exact ⟨ha_int, ⟨ha_int2, ha_ae⟩⟩

-- -- TODO: find a better name
lemma condFDiv_compProd_meas [CountableOrCountablyGenerated (α × β) γ] [IsFiniteMeasure μ]
    {ξ : Kernel α β} [IsFiniteKernel ξ]
    {κ η : Kernel (α × β) γ} [IsMarkovKernel κ] [IsMarkovKernel η]
    (hf_meas : StronglyMeasurable f) (hf_cvx : ConvexOn ℝ (Ici 0) f)
    (hf_cont : ContinuousOn f (Ici 0)) (hf_one : f 1 = 0)
    (h_top : condFDiv f κ η (μ ⊗ₘ ξ) ≠ ⊤) :
    condFDiv f κ η (μ ⊗ₘ ξ)
      = ∫ x, (condFDiv f (κ.snd' x) (η.snd' x) (ξ x)).toReal ∂μ := by
  by_cases h_empty : Nonempty α
  swap; simp only [isEmpty_prod, not_nonempty_iff.mp h_empty, true_or, condFDiv_of_isEmpty_left,
    integral_of_isEmpty, EReal.coe_zero]
  have := countableOrCountablyGenerated_right_of_prod_left_of_nonempty (α := α) (β := β) (γ := γ)
  have h := ((condFDiv_ne_top_iff hf_cvx).mp h_top)
  rw [(condFDiv_ne_top_iff' hf_cvx).mp h_top,
    Measure.integral_compProd <| (integrable_fDiv_iff hf_cvx h.1 h.2.2).mpr h.2.1]
  replace h_top := (condFDiv_compProd_meas_eq_top hf_meas hf_cvx hf_cont hf_one).mpr.mt h_top
  push_neg at h_top
  norm_cast
  apply integral_congr_ae
  filter_upwards [h_top.1] with a ha
  simp_rw [(condFDiv_ne_top_iff' hf_cvx).mp ha, EReal.toReal_coe, Kernel.snd'_apply]

end ProbabilityTheory
