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
  {μ ν : Measure α} {f g : DivFunction}

/-- To prove the DPI for an f-divergence, for the map by a function, it suffices to prove it under
an absolute continuity hypothesis. -/
lemma fDiv_map_le_of_map_le_of_ac [IsFiniteMeasure ν] {g : α → β} (hg : Measurable g)
    (h : ∀ μ : Measure α, IsFiniteMeasure μ → μ ≪ ν → fDiv f (μ.map g) (ν.map g) ≤ fDiv f μ ν)
    (μ : Measure α) [IsFiniteMeasure μ] :
    fDiv f (μ.map g) (ν.map g) ≤ fDiv f μ ν := by
  conv_lhs => rw [← Measure.rnDeriv_add_singularPart μ ν, Measure.map_add _ _ hg]
  refine (fDiv_add_measure_le _ _ _).trans ?_
  rw [fDiv_eq_add_withDensity_derivAtTop μ ν, Measure.map_apply hg MeasurableSet.univ]
  exact add_le_add (h _ inferInstance (withDensity_absolutelyContinuous _ _)) le_rfl

lemma DivFunction.condexp_rnDeriv_le [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hm : m ≤ mα)
    (h_int : ∫⁻ x, f ((∂μ/∂ν) x) ∂ν ≠ ∞) :
    (fun x ↦ f.realFun ((ν[fun x ↦ (μ.rnDeriv ν x).toReal | m]) x))
      ≤ᵐ[ν.trim hm] ν[fun x ↦ f.realFun (μ.rnDeriv ν x).toReal | m] := by
  sorry

lemma f_rnDeriv_map_le [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμν : μ ≪ ν) {g : α → β} (hg : Measurable g)
    (h_int : ∫⁻ x, f ((∂μ/∂ν) x) ∂ν ≠ ∞) :
    (fun x ↦ f.realFun ((∂μ.map g/∂ν.map g) (g x)).toReal)
      ≤ᵐ[ν] ν[fun x ↦ f.realFun ((∂μ/∂ν) x).toReal | mβ.comap g] := by
  filter_upwards [Measure.toReal_rnDeriv_map hμν hg,
    ae_of_ae_trim _ <| f.condexp_rnDeriv_le hg.comap_le h_int] with a ha1 ha2
  calc f.realFun ((∂μ.map g/∂ν.map g) (g a)).toReal
      = f.realFun ((ν[fun x ↦ ((∂μ/∂ν) x).toReal | mβ.comap g]) a) := by rw [ha1]
    _ ≤ (ν[fun x ↦ f.realFun ((∂μ/∂ν) x).toReal | mβ.comap g]) a := ha2

lemma f_rnDeriv_map_le' [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμν : μ ≪ ν) {g : α → β} (hg : Measurable g)
    (h_int : ∫⁻ x, f ((∂μ/∂ν) x) ∂ν ≠ ∞) :
    (fun x ↦ (f ((∂μ.map g/∂ν.map g) (g x))).toReal)
      ≤ᵐ[ν] ν[fun x ↦ f.realFun ((∂μ/∂ν) x).toReal | mβ.comap g] := by
  have h_lt := ae_of_ae_map hg.aemeasurable ((μ.map g).rnDeriv_lt_top (ν.map g))
  filter_upwards [f_rnDeriv_map_le hμν hg h_int, h_lt] with x hx h_lt
  rw [f.realFun_toReal h_lt.ne] at hx
  exact hx

-- todo: remove `hf`
lemma f_rnDeriv_map [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμν : μ ≪ ν) {g : α → β} (hg : Measurable g) (hf : ∀ x ≠ ∞, f x ≠ ∞) :
    (fun a ↦ f ((∂μ.map g/∂ν.map g) (g a)))
      =ᶠ[ae ν] fun a ↦ f (ENNReal.ofReal ((ν[fun x ↦ ((∂μ/∂ν) x).toReal|mβ.comap g]) a)) := by
  have h_lt := ae_of_ae_map hg.aemeasurable ((μ.map g).rnDeriv_lt_top (ν.map g))
  filter_upwards [Measure.toReal_rnDeriv_map hμν hg, h_lt] with a ha h_lt
  rw [← ENNReal.toReal_eq_toReal]
  · rw [← f.realFun_toReal h_lt.ne, ha, DivFunction.realFun]
  · exact hf _ h_lt.ne
  · exact hf _ ENNReal.ofReal_ne_top

-- todo: remove `hf`
lemma integrable_f_rnDeriv_map [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμν : μ ≪ ν) {g : α → β} (hg : Measurable g)
    (h_int : ∫⁻ x, f ((∂μ/∂ν) x) ∂ν ≠ ∞) (hf : ∀ x ≠ ∞, f x ≠ ∞) :
    Integrable (fun x ↦ f.realFun ((∂μ.map g/∂ν.map g) x).toReal) (ν.map g) := by
  have hf_cvx : ConvexOn ℝ (Ici 0) f.realFun := f.convexOn_Ici_realFun hf
  obtain ⟨c, c', h⟩ : ∃ c c', ∀ x, 0 ≤ x → c * x + c' ≤ f.realFun x :=
    hf_cvx.exists_affine_le (convex_Ici 0)
  rw [integrable_map_measure _ hg.aemeasurable]
  swap
  · refine (f.stronglyMeasurable_realFun.comp_measurable ?_).aestronglyMeasurable
    exact (Measure.measurable_rnDeriv _ _).ennreal_toReal
  refine integrable_of_le_of_le (f := fun x ↦ f.realFun ((∂μ.map g/∂ν.map g) (g x)).toReal)
    (g₁ := fun x ↦ c * ((∂μ.map g/∂ν.map g) (g x)).toReal + c')
    (g₂ := fun x ↦ (ν[fun x ↦ f.realFun ((∂μ/∂ν) x).toReal | mβ.comap g]) x)
    ?_ ?_ ?_ ?_ ?_
  · refine (f.stronglyMeasurable_realFun.comp_measurable ?_).aestronglyMeasurable
    exact ((Measure.measurable_rnDeriv _ _).comp hg).ennreal_toReal
  · exact ae_of_all _ (fun x ↦ h _ ENNReal.toReal_nonneg)
  · exact f_rnDeriv_map_le hμν hg h_int
  · refine (Integrable.const_mul ?_ _).add (integrable_const _)
    rw [integrable_congr (Measure.toReal_rnDeriv_map hμν hg)]
    exact integrable_condexp
  · exact integrable_condexp

lemma lintegrable_f_rnDeriv_map_ne_top [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμν : μ ≪ ν) {g : α → β} (hg : Measurable g)
    (h_int : ∫⁻ x, f ((∂μ/∂ν) x) ∂ν ≠ ∞) (hf : ∀ x ≠ ∞, f x ≠ ∞) :
    ∫⁻ x, f ((∂μ.map g/∂ν.map g) x) ∂(ν.map g) ≠ ∞ := by
  have h_lt := (μ.map g).rnDeriv_lt_top (ν.map g)
  rw [← integrable_toReal_iff]
  rotate_left
  · exact measurable_divFunction_rnDeriv.aemeasurable
  · filter_upwards [h_lt] with x hx
    exact hf _ hx.ne
  refine (integrable_congr ?_).mpr (integrable_f_rnDeriv_map hμν hg h_int hf)
  filter_upwards [h_lt] with x hx
  rw [f.realFun_toReal hx.ne]

-- todo: remove `hf`
lemma fDiv_map_of_ac [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμν : μ ≪ ν) {g : α → β} (hg : Measurable g) (hf : ∀ x ≠ ∞, f x ≠ ∞) :
    fDiv f (μ.map g) (ν.map g)
      = ∫⁻ x, f (ENNReal.ofReal ((ν[fun x ↦ ((∂μ/∂ν) x).toReal | mβ.comap g]) x)) ∂ν := by
  rw [fDiv_of_absolutelyContinuous (hμν.map hg), lintegral_map measurable_divFunction_rnDeriv hg,
    lintegral_congr_ae (f_rnDeriv_map hμν hg hf)]

-- todo: remove `hf`
lemma fDiv_trim_of_ac [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hm : m ≤ mα) (hμν : μ ≪ ν)
    (hf : ∀ x ≠ ∞, f x ≠ ∞) :
    fDiv f (μ.trim hm) (ν.trim hm)
      = ∫⁻ x, f (ENNReal.ofReal ((ν[fun x ↦ ((∂μ/∂ν) x).toReal | m]) x)) ∂ν := by
  simp_rw [Measure.trim_eq_map]
  rw [fDiv_map_of_ac hμν (measurable_id'' hm) hf]
  congr with x
  congr
  simp

lemma f_rnDeriv_trim_le [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hm : m ≤ mα) (hμν : μ ≪ ν)
    (h_int : ∫⁻ x, f ((∂μ/∂ν) x) ∂ν ≠ ∞) :
    (fun x ↦ f.realFun ((∂μ.trim hm/∂ν.trim hm) x).toReal)
      ≤ᵐ[ν.trim hm] ν[fun x ↦ f.realFun ((∂μ/∂ν) x).toReal | m] := by
  filter_upwards [Measure.toReal_rnDeriv_trim_of_ac hm hμν,
    f.condexp_rnDeriv_le hm h_int] with a ha1 ha2
  calc f.realFun ((∂μ.trim hm/∂ν.trim hm) a).toReal
      = f.realFun ((ν[fun x ↦ ((∂μ/∂ν) x).toReal | m]) a) := by rw [ha1]
    _ ≤ (ν[fun x ↦ f.realFun ((∂μ/∂ν) x).toReal | m]) a := ha2

lemma integrable_f_rnDeriv_trim [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hm : m ≤ mα) (hμν : μ ≪ ν)
    (h_int : ∫⁻ x, f ((∂μ/∂ν) x) ∂ν ≠ ∞) (hf : ∀ x ≠ ∞, f x ≠ ∞) :
    Integrable (fun x ↦ f.realFun ((∂μ.trim hm/∂ν.trim hm) x).toReal) (ν.trim hm) := by
  have hf_cvx : ConvexOn ℝ (Ici 0) f.realFun := f.convexOn_Ici_realFun hf
  obtain ⟨c, c', h⟩ : ∃ c c', ∀ x, 0 ≤ x → c * x + c' ≤ f.realFun x :=
    hf_cvx.exists_affine_le (convex_Ici 0)
  refine integrable_of_le_of_le (f := fun x ↦ f.realFun ((∂μ.trim hm/∂ν.trim hm) x).toReal)
    (g₁ := fun x ↦ c * ((∂μ.trim hm/∂ν.trim hm) x).toReal + c')
    (g₂ := fun x ↦ (ν[fun x ↦ f.realFun ((∂μ/∂ν) x).toReal | m]) x)
    ?_ ?_ ?_ ?_ ?_
  · refine (f.stronglyMeasurable_realFun.comp_measurable ?_).aestronglyMeasurable
    exact @Measurable.ennreal_toReal _ m _ (Measure.measurable_rnDeriv _ _)
  · exact ae_of_all _ (fun x ↦ h _ ENNReal.toReal_nonneg)
  · exact f_rnDeriv_trim_le hm hμν h_int
  · refine (Integrable.const_mul ?_ _).add (integrable_const _)
    exact Measure.integrable_toReal_rnDeriv
  · exact integrable_condexp.trim hm stronglyMeasurable_condexp

lemma integrable_f_condexp_rnDeriv [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hm : m ≤ mα) (hμν : μ ≪ ν)
    (h_int : ∫⁻ x, f ((∂μ/∂ν) x) ∂ν ≠ ∞) (hf : ∀ x ≠ ∞, f x ≠ ∞) :
    Integrable (fun x ↦ f.realFun ((ν[fun x ↦ ((∂μ/∂ν) x).toReal | m]) x)) ν := by
  have h := integrable_f_rnDeriv_trim hm hμν h_int hf
  refine integrable_of_integrable_trim hm ((integrable_congr ?_).mp h)
  filter_upwards [Measure.toReal_rnDeriv_trim_of_ac hm hμν] with a ha
  rw [ha]

/-- **Data processing inequality** for f-divergences and measurable functions. -/
theorem fDiv_map_le [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {g : α → β} (hg : Measurable g) (hf : ∀ x ≠ ∞, f x ≠ ∞) :
    fDiv f (μ.map g) (ν.map g) ≤ fDiv f μ ν := by
  refine fDiv_map_le_of_map_le_of_ac hg (fun μ _ hμν ↦ ?_) _
  by_cases h_int : ∫⁻ x, f ((∂μ/∂ν) x) ∂ν = ∞
  · rw [fDiv_of_lintegral_eq_top h_int]; exact le_top
  rw [fDiv_map_of_ac hμν hg hf, fDiv_of_absolutelyContinuous hμν]
  rw [← ofReal_integral_realFun_rnDeriv h_int]
  conv_rhs => rw [← integral_condexp hg.comap_le]
  rw [← ofReal_integral_realFun]
  rotate_left
  · refine (StronglyMeasurable.measurable ?_).ennreal_ofReal
    exact stronglyMeasurable_condexp.mono hg.comap_le
  · exact ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top
  · rw [lintegral_congr_ae (f_rnDeriv_map hμν hg hf).symm]
    have h := lintegrable_f_rnDeriv_map_ne_top hμν hg h_int hf
    rwa [lintegral_map measurable_divFunction_rnDeriv hg] at h
  refine ENNReal.ofReal_le_ofReal ?_
  have h_nonneg : 0 ≤ᵐ[ν] fun x ↦ (ν[fun x ↦ ((∂μ/∂ν) x).toReal|mβ.comap g]) x :=
    condexp_nonneg (ae_of_all _ fun _ ↦ ENNReal.toReal_nonneg)
  have h_eq :
      ∫ x, f.realFun (ENNReal.ofReal ((ν[fun x ↦ ((∂μ/∂ν) x).toReal|mβ.comap g]) x)).toReal ∂ν
        = ∫ x, f.realFun ((ν[fun x ↦ ((∂μ/∂ν) x).toReal|mβ.comap g]) x) ∂ν := by
    refine integral_congr_ae ?_
    filter_upwards [h_nonneg] with a ha
    rw [ENNReal.toReal_ofReal ha]
  rw [h_eq]
  refine integral_mono_ae ?_ integrable_condexp ?_
  · exact integrable_f_condexp_rnDeriv hg.comap_le hμν h_int hf
  · exact ae_of_ae_trim _ <| f.condexp_rnDeriv_le hg.comap_le h_int

/-- **Data processing inequality** for f-divergences and sub-sigma-algebras. -/
theorem fDiv_trim_le [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hm : m ≤ mα) (hf : ∀ x ≠ ∞, f x ≠ ∞) :
    fDiv f (μ.trim hm) (ν.trim hm) ≤ fDiv f μ ν := by
  simp_rw [Measure.trim_eq_map]
  exact fDiv_map_le (measurable_id'' hm) hf

-- todo: remove the ac hypothesis?
/-- The f-divergence of two measures restricted to the sigma-algebras generated by their
Radon-Nikodym derivative is the f-divergence of the unrestricted measures.
The restriction to that sigma-algebra is useful because it is countably generated. -/
lemma fDiv_trim_comap_rnDeriv_of_ac [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμν : μ ≪ ν) :
    fDiv f (μ.trim (μ.measurable_rnDeriv ν).comap_le) (ν.trim (μ.measurable_rnDeriv ν).comap_le)
      = fDiv f μ ν := by
  classical
  let m := MeasurableSpace.comap (μ.rnDeriv ν) inferInstance
  have hm : m ≤ mα := (μ.measurable_rnDeriv ν).comap_le
  have h_meas : Measurable[m] (μ.rnDeriv ν) := measurable_iff_comap_le.mpr le_rfl
  rw [fDiv_of_absolutelyContinuous (hμν.trim hm), fDiv_of_absolutelyContinuous hμν]
  have h_ae_eq : (fun x ↦ f ((∂μ.trim hm/∂ν.trim hm) x))
      =ᵐ[ν.trim hm] fun x ↦ f (μ.rnDeriv ν x) := by
    have h_lt : ∀ᵐ x ∂(ν.trim hm), μ.rnDeriv ν x < ∞ := by
      rw [ae_iff, trim_measurableSet_eq hm]
      · exact μ.rnDeriv_lt_top ν
      · refine MeasurableSet.compl ?_
        exact @measurableSet_lt ℝ≥0∞ _ _ _ _ m _ _ _ _ _ h_meas measurable_const
    filter_upwards [Measure.rnDeriv_trim_of_ac hm hμν, h_lt] with x hx h_lt
    rw [hx, condexp_of_stronglyMeasurable hm]
    · rw [ENNReal.ofReal_toReal h_lt.ne]
    · refine Measurable.stronglyMeasurable ?_
      exact fun s hs ↦ ⟨(fun x ↦ x.toReal) ⁻¹' s, ENNReal.measurable_toReal hs, rfl⟩
    · exact Measure.integrable_toReal_rnDeriv
  rw [lintegral_congr_ae h_ae_eq, lintegral_trim]
  exact f.measurable.comp h_meas

example : MeasurableSpace.CountablyGenerated α
    (m := MeasurableSpace.comap (μ.rnDeriv ν) inferInstance) :=
  MeasurableSpace.CountablyGenerated.comap _

end ProbabilityTheory
