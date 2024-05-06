import TestingLowerBounds.ForMathlib.Measurable

open Real


namespace MeasureTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ ν : Measure α}


--TODO: put this in the right place and PR to mathlib
lemma integrable_left_of_integrable_add_of_nonneg {f g : α → ℝ}
    (h_meas : AEStronglyMeasurable f μ) (hf : 0 ≤ᵐ[μ] f) (hg : 0 ≤ᵐ[μ] g)
    (h_int : Integrable (f + g) μ) : Integrable f μ := by
  simp_rw [Integrable, h_meas, true_and]
  calc
    (∫⁻ a, ‖f a‖₊ ∂μ) ≤ ∫⁻ a, ‖(f + g) a‖₊ ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [hf, hg] with a haf hag
      have hfg : 0 ≤ f a + g a := by
        apply add_nonneg <;> assumption
      simp only [Pi.zero_apply, Pi.add_apply, ENNReal.coe_le_coe] at *
      rw [← toNNReal_eq_nnnorm_of_nonneg haf, ← toNNReal_eq_nnnorm_of_nonneg hfg]
      apply (toNNReal_le_toNNReal_iff hfg).mpr ((le_add_iff_nonneg_right _).mpr hag)
    _ < ⊤ := h_int.2

lemma integrable_right_of_integrable_add_of_nonneg {f g : α → ℝ}
    (h_meas : AEStronglyMeasurable f μ) (hf : 0 ≤ᵐ[μ] f) (hg : 0 ≤ᵐ[μ] g)
    (h_int : Integrable (f + g) μ) : Integrable g μ :=
  integrable_left_of_integrable_add_of_nonneg
    ((AEStronglyMeasurable.add_iff_right h_meas).mp h_int.aestronglyMeasurable)
      hg hf (add_comm f g ▸ h_int)

lemma integrable_add_iff_of_nonneg {f g : α → ℝ} (h_meas : AEStronglyMeasurable f μ)
    (hf : 0 ≤ᵐ[μ] f) (hg : 0 ≤ᵐ[μ] g) :
    Integrable (f + g) μ ↔ Integrable f μ ∧ Integrable g μ :=
  ⟨fun h ↦ ⟨integrable_left_of_integrable_add_of_nonneg h_meas hf hg h,
    integrable_right_of_integrable_add_of_nonneg h_meas hf hg h⟩, fun ⟨hf, hg⟩ ↦ hf.add hg⟩

lemma integrable_add_iff_of_nonpos {f g : α → ℝ} (h_meas : AEStronglyMeasurable f μ)
    (hf : f ≤ᵐ[μ] 0) (hg : g ≤ᵐ[μ] 0) :
    Integrable (f + g) μ ↔ Integrable f μ ∧ Integrable g μ := by
  rw [← integrable_neg_iff, ← integrable_neg_iff (f := f), ← integrable_neg_iff (f := g), neg_add]
  exact integrable_add_iff_of_nonneg h_meas.neg (hf.mono (fun a ↦ neg_nonneg_of_nonpos))
    (hg.mono (fun a ↦ neg_nonneg_of_nonpos))

--should all of the above be calles ...of_ae_non... instead of ...of_non...?

end MeasureTheory


--we could put this in the same section as:
#check MeasureTheory.Integrable.add
--or maybe in some other file, if the file L1space is too general, since in this case we are talking about functions on ℝ
--also, is there some way to generalize this lemma to functions on a more general space?
#minimize_imports
