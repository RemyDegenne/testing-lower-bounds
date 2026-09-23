/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import TestingLowerBounds.FDiv.Basic
public import Mathlib.InformationTheory.KullbackLeibler.DataProcessing
public import Mathlib.MeasureTheory.Function.ConditionalLExpectation
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.RadonNikodym

/-!

# f-Divergences on sub-sigma-algebras

## Main statements

* `DivFunction.map_condLExp_le`: Jensen's inequality for the conditional Lebesgue expectation
  `ν⁻[X|m]` and a `DivFunction`. It holds for every `DivFunction`, including those taking the
  value `∞` at finite points.
* `fDiv_map_le`: data processing inequality for f-divergences and measurable functions
* `fDiv_trim_le`: data processing inequality for f-divergences and sub-sigma-algebras

-/

@[expose] public section

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

/-- **Jensen's inequality** for the conditional Lebesgue expectation and a `DivFunction`. -/
theorem DivFunction.map_condLExp_le [IsFiniteMeasure ν] (hm : m ≤ mα) {X : α → ℝ≥0∞}
    (hX : Measurable X) (hX_int : ∫⁻ x, X x ∂ν ≠ ∞) :
    (fun x ↦ f (ν⁻[X|m] x)) ≤ᵐ[ν] ν⁻[fun x ↦ f (X x)|m] := by
  have h_tangent : ∀ q : ℚ, ENNReal.ofReal q ∈ Ioo f.xmin f.xmax → ∀ᵐ x ∂ν,
      f (ENNReal.ofReal q)
          + ENNReal.ofReal (max (rightDeriv f.realFun (ENNReal.ofReal q).toReal) 0) * ν⁻[X|m] x
          + ENNReal.ofReal (max (-rightDeriv f.realFun (ENNReal.ofReal q).toReal) 0)
            * ENNReal.ofReal q
        ≤ ν⁻[fun x ↦ f (X x)|m] x
          + ENNReal.ofReal (max (rightDeriv f.realFun (ENNReal.ofReal q).toReal) 0)
            * ENNReal.ofReal q
          + ENNReal.ofReal (max (-rightDeriv f.realFun (ENNReal.ofReal q).toReal) 0)
            * ν⁻[X|m] x := by
    intro q hq
    set A := ENNReal.ofReal (max (rightDeriv f.realFun (ENNReal.ofReal q).toReal) 0) with hA
    set B := ENNReal.ofReal (max (-rightDeriv f.realFun (ENNReal.ofReal q).toReal) 0) with hB
    have h_pt : ((fun _ ↦ f (ENNReal.ofReal q)) + A • X + fun _ ↦ B * ENNReal.ofReal q)
        ≤ᵐ[ν] ((fun x ↦ f (X x)) + (fun _ ↦ A * ENNReal.ofReal q) + B • X) := by
      filter_upwards [ae_lt_top hX hX_int] with x hx
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      exact f.apply_add_le_apply_add hq hx.ne
    have hL : ν⁻[(fun _ ↦ f (ENNReal.ofReal q)) + A • X + fun _ ↦ B * ENNReal.ofReal q | m]
        =ᵐ[ν] (fun _ ↦ f (ENNReal.ofReal q)) + A • ν⁻[X|m] + fun _ ↦ B * ENNReal.ofReal q := by
      calc ν⁻[(fun _ ↦ f (ENNReal.ofReal q)) + A • X + fun _ ↦ B * ENNReal.ofReal q | m]
          =ᵐ[ν] ν⁻[(fun _ ↦ f (ENNReal.ofReal q)) + A • X | m]
            + ν⁻[fun _ ↦ B * ENNReal.ofReal q | m] := condLExp_add_right _ aemeasurable_const
        _ =ᵐ[ν] (ν⁻[fun _ ↦ f (ENNReal.ofReal q) | m] + ν⁻[A • X | m])
            + ν⁻[fun _ ↦ B * ENNReal.ofReal q | m] :=
            (condLExp_add_left _ aemeasurable_const).add EventuallyEq.rfl
        _ =ᵐ[ν] (fun _ ↦ f (ENNReal.ofReal q)) + A • ν⁻[X|m] + fun _ ↦ B * ENNReal.ofReal q := by
            rw [condLExp_const hm, condLExp_const hm]
            exact (EventuallyEq.rfl.add (condLExp_smul X hX.aemeasurable A)).add EventuallyEq.rfl
    have hR : ν⁻[(fun x ↦ f (X x)) + (fun _ ↦ A * ENNReal.ofReal q) + B • X | m]
        =ᵐ[ν] ν⁻[fun x ↦ f (X x)|m] + (fun _ ↦ A * ENNReal.ofReal q) + B • ν⁻[X|m] := by
      calc ν⁻[(fun x ↦ f (X x)) + (fun _ ↦ A * ENNReal.ofReal q) + B • X | m]
          =ᵐ[ν] ν⁻[(fun x ↦ f (X x)) + fun _ ↦ A * ENNReal.ofReal q | m] + ν⁻[B • X | m] :=
            condLExp_add_right _ (hX.const_smul B).aemeasurable
        _ =ᵐ[ν] (ν⁻[fun x ↦ f (X x)|m] + ν⁻[fun _ ↦ A * ENNReal.ofReal q | m]) + ν⁻[B • X | m] :=
            (condLExp_add_right _ aemeasurable_const).add EventuallyEq.rfl
        _ =ᵐ[ν] ν⁻[fun x ↦ f (X x)|m] + (fun _ ↦ A * ENNReal.ofReal q) + B • ν⁻[X|m] := by
            rw [condLExp_const hm]
            exact EventuallyEq.rfl.add (condLExp_smul X hX.aemeasurable B)
    filter_upwards [condLExp_mono (mΩ := m) h_pt, hL, hR] with x hx hLx hRx
    rw [hLx, hRx] at hx
    simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using hx
  have h_all : ∀ᵐ x ∂ν, ∀ q : ℚ, ENNReal.ofReal q ∈ Ioo f.xmin f.xmax →
      f (ENNReal.ofReal q)
          + ENNReal.ofReal (max (rightDeriv f.realFun (ENNReal.ofReal q).toReal) 0) * ν⁻[X|m] x
          + ENNReal.ofReal (max (-rightDeriv f.realFun (ENNReal.ofReal q).toReal) 0)
            * ENNReal.ofReal q
        ≤ ν⁻[fun x ↦ f (X x)|m] x
          + ENNReal.ofReal (max (rightDeriv f.realFun (ENNReal.ofReal q).toReal) 0)
            * ENNReal.ofReal q
          + ENNReal.ofReal (max (-rightDeriv f.realFun (ENNReal.ofReal q).toReal) 0)
            * ν⁻[X|m] x := by
    rw [ae_all_iff]
    intro q
    by_cases hq : ENNReal.ofReal q ∈ Ioo f.xmin f.xmax
    · filter_upwards [h_tangent q hq] with x hx using fun _ ↦ hx
    · exact ae_of_all _ fun x h ↦ absurd h hq
  filter_upwards [h_all, condLExp_ne_top (mΩ := m) hX_int] with x hx hx_top
  exact f.le_of_forall_rat_tangent_le hx_top hx

section Map

variable {g : α → β}

lemma f_rnDeriv_map_le [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμν : μ ≪ ν)
    {g : α → β} (hg : Measurable g) :
    (fun x ↦ f ((∂μ.map g/∂ν.map g) (g x)))
      ≤ᵐ[ν] ν⁻[fun x ↦ f ((∂μ/∂ν) x) | mβ.comap g] := by
  filter_upwards [rnDeriv_map hμν hg, f.map_condLExp_le hg.comap_le (μ.measurable_rnDeriv ν)
    (Measure.lintegral_rnDeriv_lt_top μ ν).ne] with x hx1 hx2
  rw [hx1]
  exact hx2

lemma lintegral_f_rnDeriv_map_le [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμν : μ ≪ ν)
    {g : α → β} (hg : Measurable g) :
    ∫⁻ x, f ((∂μ.map g/∂ν.map g) x) ∂(ν.map g) ≤ ∫⁻ x, f ((∂μ/∂ν) x) ∂ν := by
  rw [lintegral_map measurable_divFunction_rnDeriv hg]
  calc ∫⁻ x, f ((∂μ.map g/∂ν.map g) (g x)) ∂ν
    ≤ ∫⁻ x, ν⁻[fun x ↦ f ((∂μ/∂ν) x) | mβ.comap g] x ∂ν :=
        lintegral_mono_ae (f_rnDeriv_map_le hμν hg)
  _ = ∫⁻ x, f ((∂μ/∂ν) x) ∂ν := lintegral_condLExp hg.comap_le ν _

lemma f_rnDeriv_map [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμν : μ ≪ ν) (hg : Measurable g) :
    (fun a ↦ f ((∂μ.map g/∂ν.map g) (g a)))
      =ᵐ[ν] fun a ↦ f (ν⁻[∂μ/∂ν | mβ.comap g] a) := by
  filter_upwards [rnDeriv_map hμν hg] with a ha
  rw [ha]

lemma fDiv_map_of_ac [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμν : μ ≪ ν) (hg : Measurable g) :
    fDiv f (μ.map g) (ν.map g) = ∫⁻ x, f (ν⁻[∂μ/∂ν | mβ.comap g] x) ∂ν := by
  rw [fDiv_of_absolutelyContinuous (hμν.map hg), lintegral_map measurable_divFunction_rnDeriv hg,
    lintegral_congr_ae (f_rnDeriv_map hμν hg)]

lemma lintegral_f_rnDeriv_map_ne_top [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμν : μ ≪ ν)
    (hg : Measurable g) (h_int : ∫⁻ x, f ((∂μ/∂ν) x) ∂ν ≠ ∞) :
    ∫⁻ x, f ((∂μ.map g/∂ν.map g) x) ∂(ν.map g) ≠ ∞ :=
  ((lintegral_f_rnDeriv_map_le hμν hg).trans_lt h_int.lt_top).ne

lemma integrable_f_rnDeriv_map [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμν : μ ≪ ν)
    (hg : Measurable g) (h_int : ∫⁻ x, f ((∂μ/∂ν) x) ∂ν ≠ ∞) :
    Integrable (fun x ↦ f.realFun ((∂μ.map g/∂ν.map g) x).toReal) (ν.map g) := by
  refine (integrable_congr ?_).mp (integrable_toReal_of_lintegral_ne_top
    measurable_divFunction_rnDeriv.aemeasurable (lintegral_f_rnDeriv_map_ne_top hμν hg h_int))
  filter_upwards [(μ.map g).rnDeriv_lt_top (ν.map g)] with x hx
  rw [f.realFun_toReal hx.ne]

/-- **Data processing inequality** for f-divergences and measurable functions. -/
theorem fDiv_map_le [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hg : Measurable g) :
    fDiv f (μ.map g) (ν.map g) ≤ fDiv f μ ν := by
  refine fDiv_map_le_of_map_le_of_ac hg (fun μ _ hμν ↦ ?_) _
  rw [fDiv_of_absolutelyContinuous (hμν.map hg), fDiv_of_absolutelyContinuous hμν]
  exact lintegral_f_rnDeriv_map_le hμν hg

end Map

section Trim

lemma f_rnDeriv_trim_le [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hm : m ≤ mα) (hμν : μ ≪ ν) :
    (fun x ↦ f ((∂μ.trim hm/∂ν.trim hm) x)) ≤ᵐ[ν] ν⁻[fun x ↦ f ((∂μ/∂ν) x) | m] := by
  have h := f_rnDeriv_map_le (f := f) hμν (measurable_id'' hm)
  rwa [← trim_eq_map hm, ← trim_eq_map hm, MeasurableSpace.comap_id] at h

lemma fDiv_trim_of_ac [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hm : m ≤ mα) (hμν : μ ≪ ν) :
    fDiv f (μ.trim hm) (ν.trim hm) = ∫⁻ x, f (ν⁻[∂μ/∂ν | m] x) ∂ν := by
  simp_rw [trim_eq_map]
  rw [fDiv_map_of_ac hμν (measurable_id'' hm), MeasurableSpace.comap_id]

lemma lintegral_f_rnDeriv_trim_le [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hm : m ≤ mα)
    (hμν : μ ≪ ν) :
    ∫⁻ x, f ((∂μ.trim hm/∂ν.trim hm) x) ∂(ν.trim hm) ≤ ∫⁻ x, f ((∂μ/∂ν) x) ∂ν := by
  simp_rw [trim_eq_map]
  exact lintegral_f_rnDeriv_map_le hμν (measurable_id'' hm)

lemma integrable_f_rnDeriv_trim [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hm : m ≤ mα)
    (hμν : μ ≪ ν) (h_int : ∫⁻ x, f ((∂μ/∂ν) x) ∂ν ≠ ∞) :
    Integrable (fun x ↦ f.realFun ((∂μ.trim hm/∂ν.trim hm) x).toReal) (ν.trim hm) := by
  refine (integrable_congr ?_).mp (integrable_toReal_of_lintegral_ne_top
    measurable_divFunction_rnDeriv.aemeasurable
    ((lintegral_f_rnDeriv_trim_le hm hμν).trans_lt h_int.lt_top).ne)
  filter_upwards [(μ.trim hm).rnDeriv_lt_top (ν.trim hm)] with x hx
  rw [f.realFun_toReal hx.ne]

/-- **Data processing inequality** for f-divergences and sub-sigma-algebras. -/
theorem fDiv_trim_le [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hm : m ≤ mα) :
    fDiv f (μ.trim hm) (ν.trim hm) ≤ fDiv f μ ν := by
  simp_rw [trim_eq_map]
  exact fDiv_map_le (measurable_id'' hm)

/-- The f-divergence between the images of two measures by a measurable function `g` is equal to
the f-divergence between the two measures restricted to the sigma-algebra `mβ.comap g`. -/
lemma fDiv_map_eq_fDiv_trim_of_ac [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμν : μ ≪ ν)
    {g : α → β} (hg : Measurable g) :
    fDiv f (μ.map g) (ν.map g) = fDiv f (μ.trim hg.comap_le) (ν.trim hg.comap_le) := by
  rw [fDiv_map_of_ac hμν hg, fDiv_trim_of_ac hg.comap_le hμν]

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
    filter_upwards [rnDeriv_trim hm hμν, h_lt] with x hx h_lt
    rw [hx, condExp_of_stronglyMeasurable hm]
    · rw [ENNReal.ofReal_toReal h_lt.ne]
    · refine Measurable.stronglyMeasurable ?_
      exact fun s hs ↦ ⟨(fun x ↦ x.toReal) ⁻¹' s, ENNReal.measurable_toReal hs, rfl⟩
    · exact Measure.integrable_toReal_rnDeriv
  rw [lintegral_congr_ae h_ae_eq, lintegral_trim]
  exact f.measurable.comp h_meas

example : MeasurableSpace.CountablyGenerated α
    (m := MeasurableSpace.comap (μ.rnDeriv ν) inferInstance) :=
  MeasurableSpace.CountablyGenerated.comap _

end Trim

end ProbabilityTheory
