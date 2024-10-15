/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import TestingLowerBounds.FDiv.Basic
import TestingLowerBounds.Sorry.Jensen

/-!

# f-Divergences on sub-sigma-algebras

## Main statements

* `fDiv_map_le`: data processing inequality for f-divergences and measurable functions
* `fDiv_trim_le`: data processing inequality for f-divergences and sub-sigma-algebras

-/

open Real MeasureTheory Filter Set

open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

variable {α β : Type*} {m mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {μ ν : Measure α} {f g : ℝ → ℝ}

/-- To prove the DPI for an f-divergence, for the map by a function, it suffices to prove it under
an absolute continuity hypothesis. -/
lemma fDiv_map_le_of_map_le_of_ac [IsFiniteMeasure ν]
    (hf : StronglyMeasurable f) (h_cvx : ConvexOn ℝ (Ici 0) f) {g : α → β} (hg : Measurable g)
    (h : ∀ μ : Measure α, IsFiniteMeasure μ → μ ≪ ν → fDiv f (μ.map g) (ν.map g) ≤ fDiv f μ ν)
    (μ : Measure α) [IsFiniteMeasure μ] :
    fDiv f (μ.map g) (ν.map g) ≤ fDiv f μ ν := by
  conv_lhs => rw [← Measure.rnDeriv_add_singularPart μ ν, Measure.map_add _ _ hg]
  refine (fDiv_add_measure_le _ _ _ hf h_cvx).trans ?_
  rw [fDiv_eq_add_withDensity_derivAtTop μ ν h_cvx, Measure.map_apply hg MeasurableSet.univ]
  exact add_le_add (h _ inferInstance (withDensity_absolutelyContinuous _ _)) le_rfl

lemma f_rnDeriv_map_le [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμν : μ ≪ ν) {g : α → β} (hg : Measurable g) (hf : StronglyMeasurable f)
    (hf_cvx : ConvexOn ℝ (Ici 0) f) (hf_cont : ContinuousOn f (Ici 0))
    (h_int : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν) :
    (fun x ↦ f ((∂μ.map g/∂ν.map g) (g x)).toReal)
      ≤ᵐ[ν] ν[fun x ↦ f ((∂μ/∂ν) x).toReal | mβ.comap g] := by
  filter_upwards [Measure.toReal_rnDeriv_map hμν hg,
    ae_of_ae_trim _ <| f_condexp_rnDeriv_le hg.comap_le hf hf_cvx hf_cont h_int] with a ha1 ha2
  calc f ((∂μ.map g/∂ν.map g) (g a)).toReal
      = f ((ν[fun x ↦ ((∂μ/∂ν) x).toReal | mβ.comap g]) a) := by rw [ha1]
    _ ≤ (ν[fun x ↦ f ((∂μ/∂ν) x).toReal | mβ.comap g]) a := ha2

lemma integrable_f_rnDeriv_map [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμν : μ ≪ ν) {g : α → β} (hg : Measurable g) (hf : StronglyMeasurable f)
    (hf_cvx : ConvexOn ℝ (Ici 0) f) (hf_cont : ContinuousOn f (Ici 0))
    (h_int : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν) :
    Integrable (fun x ↦ f ((∂μ.map g/∂ν.map g) x).toReal) (ν.map g) := by
  obtain ⟨c, c', h⟩ : ∃ c c', ∀ x, 0 ≤ x → c * x + c' ≤ f x :=
    hf_cvx.exists_affine_le (convex_Ici 0)
  rw [integrable_map_measure _ hg.aemeasurable]
  swap
  · refine (hf.comp_measurable ?_).aestronglyMeasurable
    exact (Measure.measurable_rnDeriv _ _).ennreal_toReal
  refine integrable_of_le_of_le (f := fun x ↦ f ((∂μ.map g/∂ν.map g) (g x)).toReal)
    (g₁ := fun x ↦ c * ((∂μ.map g/∂ν.map g) (g x)).toReal + c')
    (g₂ := fun x ↦ (ν[fun x ↦ f ((∂μ/∂ν) x).toReal | mβ.comap g]) x)
    ?_ ?_ ?_ ?_ ?_
  · refine (hf.comp_measurable ?_).aestronglyMeasurable
    exact ((Measure.measurable_rnDeriv _ _).comp hg).ennreal_toReal
  · exact ae_of_all _ (fun x ↦ h _ ENNReal.toReal_nonneg)
  · exact f_rnDeriv_map_le hμν hg hf hf_cvx hf_cont h_int
  · refine (Integrable.const_mul ?_ _).add (integrable_const _)
    rw [integrable_congr (Measure.toReal_rnDeriv_map hμν hg)]
    exact integrable_condexp
  · exact integrable_condexp

lemma fDiv_map_of_ac [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμν : μ ≪ ν) {g : α → β} (hg : Measurable g) (hf : StronglyMeasurable f)
    (hf_cvx : ConvexOn ℝ (Ici 0) f) (hf_cont : ContinuousOn f (Ici 0))
    (h_int : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν) :
    fDiv f (μ.map g) (ν.map g) = ∫ x, f ((ν[fun x ↦ ((∂μ/∂ν) x).toReal | mβ.comap g]) x) ∂ν := by
  classical
  rw [fDiv_of_absolutelyContinuous (hμν.map hg),
    if_pos (integrable_f_rnDeriv_map hμν hg hf hf_cvx hf_cont h_int)]
  congr 1
  rw [integral_map hg.aemeasurable]
  swap;
  · refine (hf.comp_measurable ?_).aestronglyMeasurable
    exact (Measure.measurable_rnDeriv _ _).ennreal_toReal
  refine integral_congr_ae ?_
  filter_upwards [Measure.toReal_rnDeriv_map hμν hg] with a ha
  rw [ha]

lemma fDiv_trim_of_ac [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hm : m ≤ mα) (hμν : μ ≪ ν)
    (hf : StronglyMeasurable f)
    (hf_cvx : ConvexOn ℝ (Ici 0) f) (hf_cont : ContinuousOn f (Ici 0))
    (h_int : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν) :
    fDiv f (μ.trim hm) (ν.trim hm) = ∫ x, f ((ν[fun x ↦ ((∂μ/∂ν) x).toReal | m]) x) ∂ν := by
  simp_rw [Measure.trim_eq_map]
  rw [fDiv_map_of_ac hμν (measurable_id'' hm) hf hf_cvx hf_cont h_int]
  congr with x
  congr
  simp

lemma f_rnDeriv_trim_le [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hm : m ≤ mα) (hμν : μ ≪ ν)
    (hf : StronglyMeasurable f)
    (hf_cvx : ConvexOn ℝ (Ici 0) f) (hf_cont : ContinuousOn f (Ici 0))
    (h_int : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν) :
    (fun x ↦ f ((∂μ.trim hm/∂ν.trim hm) x).toReal)
      ≤ᵐ[ν.trim hm] ν[fun x ↦ f ((∂μ/∂ν) x).toReal | m] := by
  filter_upwards [Measure.toReal_rnDeriv_trim_of_ac hm hμν,
    f_condexp_rnDeriv_le hm hf hf_cvx hf_cont h_int] with a ha1 ha2
  calc f ((∂μ.trim hm/∂ν.trim hm) a).toReal
      = f ((ν[fun x ↦ ((∂μ/∂ν) x).toReal | m]) a) := by rw [ha1]
    _ ≤ (ν[fun x ↦ f ((∂μ/∂ν) x).toReal | m]) a := ha2

lemma integrable_f_rnDeriv_trim [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hm : m ≤ mα) (hμν : μ ≪ ν)
    (hf : StronglyMeasurable f)
    (hf_cvx : ConvexOn ℝ (Ici 0) f) (hf_cont : ContinuousOn f (Ici 0))
    (h_int : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν) :
    Integrable (fun x ↦ f ((∂μ.trim hm/∂ν.trim hm) x).toReal) (ν.trim hm) := by
  obtain ⟨c, c', h⟩ : ∃ c c', ∀ x, 0 ≤ x → c * x + c' ≤ f x :=
    hf_cvx.exists_affine_le (convex_Ici 0)
  refine integrable_of_le_of_le (f := fun x ↦ f ((∂μ.trim hm/∂ν.trim hm) x).toReal)
    (g₁ := fun x ↦ c * ((∂μ.trim hm/∂ν.trim hm) x).toReal + c')
    (g₂ := fun x ↦ (ν[fun x ↦ f ((∂μ/∂ν) x).toReal | m]) x)
    ?_ ?_ ?_ ?_ ?_
  · refine (hf.comp_measurable ?_).aestronglyMeasurable
    exact @Measurable.ennreal_toReal _ m _ (Measure.measurable_rnDeriv _ _)
  · exact ae_of_all _ (fun x ↦ h _ ENNReal.toReal_nonneg)
  · exact f_rnDeriv_trim_le hm hμν hf hf_cvx hf_cont h_int
  · refine (Integrable.const_mul ?_ _).add (integrable_const _)
    exact Measure.integrable_toReal_rnDeriv
  · exact integrable_condexp.trim hm stronglyMeasurable_condexp

lemma integrable_f_condexp_rnDeriv [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hm : m ≤ mα) (hμν : μ ≪ ν)
    (hf : StronglyMeasurable f)
    (hf_cvx : ConvexOn ℝ (Ici 0) f) (hf_cont : ContinuousOn f (Ici 0))
    (h_int : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν) :
    Integrable (fun x ↦ f ((ν[fun x ↦ ((∂μ/∂ν) x).toReal | m]) x)) ν := by
  have h := integrable_f_rnDeriv_trim hm hμν hf hf_cvx hf_cont h_int
  refine integrable_of_integrable_trim hm ((integrable_congr ?_).mp h)
  filter_upwards [Measure.toReal_rnDeriv_trim_of_ac hm hμν] with a ha
  rw [ha]

/-- **Data processing inequality** for f-divergences and measurable functions. -/
theorem fDiv_map_le [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {g : α → β} (hg : Measurable g) (hf : StronglyMeasurable f)
    (hf_cvx : ConvexOn ℝ (Ici 0) f) (hf_cont : ContinuousOn f (Ici 0)) :
    fDiv f (μ.map g) (ν.map g) ≤ fDiv f μ ν := by
  refine fDiv_map_le_of_map_le_of_ac hf hf_cvx hg (fun μ _ hμν ↦ ?_) _
  by_cases h_int : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν
  swap; · rw [fDiv_of_not_integrable h_int]; exact le_top
  rw [fDiv_map_of_ac hμν hg hf hf_cvx hf_cont h_int]
  classical
  rw [fDiv_of_absolutelyContinuous hμν, if_pos h_int]
  norm_cast
  conv_rhs => rw [← integral_condexp hg.comap_le]
  refine integral_mono_ae ?_ integrable_condexp ?_
  · exact integrable_f_condexp_rnDeriv hg.comap_le hμν hf hf_cvx hf_cont h_int
  · refine ae_of_ae_trim hg.comap_le ?_
    exact f_condexp_rnDeriv_le hg.comap_le hf hf_cvx hf_cont h_int

/-- **Data processing inequality** for f-divergences and sub-sigma-algebras. -/
theorem fDiv_trim_le [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hm : m ≤ mα)
    (hf : StronglyMeasurable f)
    (hf_cvx : ConvexOn ℝ (Ici 0) f) (hf_cont : ContinuousOn f (Ici 0)) :
    fDiv f (μ.trim hm) (ν.trim hm) ≤ fDiv f μ ν := by
  simp_rw [Measure.trim_eq_map]
  exact fDiv_map_le (measurable_id'' hm) hf hf_cvx hf_cont

-- todo: remove the ac hypothesis?
/-- The f-divergence of two measures restricted to the sigma-algebras generated by their
Radon-Nikodym derivative is the f-divergence of the unrestricted measures.
The restriction to that sigma-algebra is useful because it is countably generated. -/
lemma fDiv_trim_comap_rnDeriv_of_ac [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμν : μ ≪ ν)
    (hf : StronglyMeasurable f) :
    fDiv f (μ.trim (μ.measurable_rnDeriv ν).comap_le) (ν.trim (μ.measurable_rnDeriv ν).comap_le)
      = fDiv f μ ν := by
  classical
  let m := MeasurableSpace.comap (μ.rnDeriv ν) inferInstance
  have hm : m ≤ mα := (μ.measurable_rnDeriv ν).comap_le
  rw [fDiv_of_absolutelyContinuous (hμν.trim hm), fDiv_of_absolutelyContinuous hμν]
  have h_ae_eq : (fun x ↦ f ((∂μ.trim hm/∂ν.trim hm) x).toReal)
      =ᵐ[ν.trim hm] fun x ↦ f (μ.rnDeriv ν x).toReal := by
    filter_upwards [Measure.toReal_rnDeriv_trim_of_ac hm hμν] with x hx
    rw [hx, condexp_of_stronglyMeasurable hm]
    · refine Measurable.stronglyMeasurable ?_
      exact fun s hs ↦ ⟨(fun x ↦ x.toReal) ⁻¹' s, ENNReal.measurable_toReal hs, rfl⟩
    · exact Measure.integrable_toReal_rnDeriv
  rw [integrable_congr h_ae_eq, integral_congr_ae h_ae_eq]
  have h_meas : StronglyMeasurable[m] fun x ↦ f ((∂μ/∂ν) x).toReal := by
    refine hf.comp_measurable ?_
    exact fun s hs ↦ ⟨(fun x ↦ x.toReal) ⁻¹' s, ENNReal.measurable_toReal hs, rfl⟩
  congr 1
  · rw [eq_iff_iff]
    refine ⟨fun h ↦ integrable_of_integrable_trim _ h, fun h ↦ ?_⟩
    refine Integrable.trim hm h h_meas
  · rwa [← integral_trim]

example : MeasurableSpace.CountablyGenerated α
    (m := MeasurableSpace.comap (μ.rnDeriv ν) inferInstance) :=
  MeasurableSpace.CountablyGenerated.comap _

end ProbabilityTheory
