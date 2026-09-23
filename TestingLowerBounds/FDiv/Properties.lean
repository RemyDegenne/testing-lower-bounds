/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import TestingLowerBounds.Divergences.KullbackLeibler.KullbackLeibler
public import TestingLowerBounds.Divergences.StatInfo.DPI
public import TestingLowerBounds.Divergences.TotalVariation
public import TestingLowerBounds.FDiv.Conj
public import TestingLowerBounds.FDiv.Trim
public import TestingLowerBounds.Testing.BoolMeasure

/-! # Further properties of f-divergences

## Main statements

* `fDiv_eq_fDiv_restrict_add_fDiv_restrict_compl`: an f-divergence splits along any measurable set.
* `fDiv_prod_right`: `fDiv f (μ.prod ξ) (ν.prod ξ) = fDiv f μ ν` for a probability measure `ξ`.
* `fDiv_comp_eq_of_fst`: a Markov kernel `κ : α → α × β` whose first marginal is `δ_x` at every
  `x` preserves f-divergences.
* `fDiv_boolMeasure_le`: data-processing inequality for the indicator of an event.
* `fDiv_add_add_le`, `fDiv_smul_smul`, `fDiv_convex`: joint convexity of f-divergences.
* `statInfo_eq_fDiv`, `tv_eq_fDiv`: on probability measures, the statistical information and the
  total variation distance are f-divergences.
* `apply_one_add_tv_add_apply_one_sub_tv_le_fDiv`, `conj_one_add_tv_add_conj_one_sub_tv_le_fDiv`:
  Bretagnolle-Huber type lower bounds on f-divergences in terms of the total variation distance.
* `neg_log_one_sub_sq_tv_le_klDiv`: the **Bretagnolle-Huber inequality**
  `-log (1 - tv μ ν ^ 2) ≤ klDiv μ ν`.

-/

@[expose] public section

open MeasureTheory Set InformationTheory

open Filter

open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {μ ν : Measure α} {f : DivFunction}

section Restrict

lemma _root_.MeasureTheory.Measure.rnDeriv_restrict_restrict (μ ν : Measure α) [SigmaFinite μ]
    [SigmaFinite ν] {s : Set α} (hs : MeasurableSet s) :
    (μ.restrict s).rnDeriv (ν.restrict s) =ᵐ[ν.restrict s] μ.rnDeriv ν := by
  refine (Measure.eq_rnDeriv (μ := μ.restrict s) (ν := ν.restrict s)
    (s := (μ.singularPart ν).restrict s) (Measure.measurable_rnDeriv μ ν)
    (((Measure.mutuallySingular_singularPart μ ν).restrict s).symm.restrict s).symm ?_).symm
  conv_lhs => rw [μ.haveLebesgueDecomposition_add ν]
  rw [Measure.restrict_add, restrict_withDensity hs]

lemma _root_.MeasureTheory.Measure.singularPart_restrict_restrict (μ ν : Measure α)
    [SigmaFinite μ] [SigmaFinite ν] {s : Set α} (hs : MeasurableSet s) :
    (μ.restrict s).singularPart (ν.restrict s) = (μ.singularPart ν).restrict s := by
  refine (Measure.eq_singularPart (μ := μ.restrict s) (ν := ν.restrict s)
    (Measure.measurable_rnDeriv μ ν)
    (((Measure.mutuallySingular_singularPart μ ν).restrict s).symm.restrict s).symm ?_).symm
  conv_lhs => rw [μ.haveLebesgueDecomposition_add ν]
  rw [Measure.restrict_add, restrict_withDensity hs]

lemma fDiv_restrict_restrict (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν]
    {s : Set α} (hs : MeasurableSet s) :
    fDiv f (μ.restrict s) (ν.restrict s)
      = ∫⁻ x in s, f ((∂μ/∂ν) x) ∂ν + f.derivAtTop * μ.singularPart ν s := by
  rw [fDiv, Measure.singularPart_restrict_restrict μ ν hs, Measure.restrict_apply_univ,
    lintegral_congr_ae ?_]
  filter_upwards [Measure.rnDeriv_restrict_restrict μ ν hs] with x hx
  rw [hx]

/-- An f-divergence splits as the sum of the divergences of the restrictions to a measurable set
and to its complement. -/
lemma fDiv_eq_fDiv_restrict_add_fDiv_restrict_compl (μ ν : Measure α) [SigmaFinite μ]
    [SigmaFinite ν] {s : Set α} (hs : MeasurableSet s) :
    fDiv f μ ν = fDiv f (μ.restrict s) (ν.restrict s) + fDiv f (μ.restrict sᶜ) (ν.restrict sᶜ) := by
  rw [fDiv_restrict_restrict μ ν hs, fDiv_restrict_restrict μ ν hs.compl, add_add_add_comm,
    lintegral_add_compl _ hs, ← mul_add, measure_add_measure_compl hs, fDiv]

end Restrict

section DataProcessing

/-- The f-divergence is invariant under taking the product with a probability measure. -/
lemma fDiv_prod_right (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (ξ : Measure β) [IsProbabilityMeasure ξ] :
    fDiv f (μ.prod ξ) (ν.prod ξ) = fDiv f μ ν := by
  simpa [Measure.compProd_const] using fDiv_compProd_right' (f := f) (μ := μ) (ν := ν)
    (Kernel.const α ξ)

/-- A Markov kernel `κ : α → α × β` such that the first marginal of `κ x` is `δ_x` for all `x`
preserves f-divergences. -/
lemma fDiv_comp_eq_of_fst (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ : Kernel α (α × β)) [IsMarkovKernel κ] (hκ : ∀ x, (κ x).fst = Measure.dirac x) :
    fDiv f (κ ∘ₘ μ) (κ ∘ₘ ν) = fDiv f μ ν := by
  refine le_antisymm (fDiv_comp_right_le' κ) ?_
  have h_fst (ξ : Measure α) [IsFiniteMeasure ξ] : (κ ∘ₘ ξ).fst = ξ := by
    have : κ.map Prod.fst = Kernel.id := by
      ext x : 1
      rw [Kernel.map_apply _ measurable_fst, ← Measure.fst, hκ, Kernel.id_apply]
    rw [Measure.fst, Measure.map_comp _ _ measurable_fst, this, Measure.id_comp]
  calc fDiv f μ ν = fDiv f (κ ∘ₘ μ).fst (κ ∘ₘ ν).fst := by rw [h_fst, h_fst]
  _ ≤ fDiv f (κ ∘ₘ μ) (κ ∘ₘ ν) := fDiv_fst_le' _ _

/-- **Data processing inequality** for the indicator of an event: the f-divergence between the
laws of `𝕀{x ∈ s}` under `μ` and `ν` is at most `fDiv f μ ν`. -/
lemma fDiv_boolMeasure_le (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {s : Set α} (hs : MeasurableSet s) :
    fDiv f (Bool.boolMeasure (μ sᶜ) (μ s)) (Bool.boolMeasure (ν sᶜ) (ν s)) ≤ fDiv f μ ν := by
  classical
  have hg : Measurable (fun x ↦ decide (x ∈ s)) := measurable_to_countable' fun b ↦ by
    cases b
    · convert hs.compl using 1
      ext x
      simp
    · convert hs using 1
      ext x
      simp
  have h_map (ξ : Measure α) : ξ.map (fun x ↦ decide (x ∈ s))
      = Bool.boolMeasure (ξ sᶜ) (ξ s) := by
    refine Measure.ext_of_singleton fun b ↦ ?_
    rw [Measure.map_apply hg (measurableSet_singleton b)]
    cases b
    · simp [Bool.boolMeasure_apply_false, preimage, compl_def]
    · simp [Bool.boolMeasure_apply_true, preimage]
  rw [← h_map, ← h_map]
  exact fDiv_map_le hg

end DataProcessing

section Convexity

/-- The f-divergence of the sum of two pairs of measures is at most the sum of the
f-divergences. -/
theorem fDiv_add_add_le (μ₀ μ₁ ν₀ ν₁ : Measure α) [IsFiniteMeasure μ₀] [IsFiniteMeasure μ₁]
    [IsFiniteMeasure ν₀] [IsFiniteMeasure ν₁] :
    fDiv f (μ₀ + μ₁) (ν₀ + ν₁) ≤ fDiv f μ₀ ν₀ + fDiv f μ₁ ν₁ := by
  -- we embed the measures in `Bool × α` and use the data-processing inequality for `Prod.snd`
  let P : Measure (Bool × α) := μ₀.map (Prod.mk false) + μ₁.map (Prod.mk true)
  let Q : Measure (Bool × α) := ν₀.map (Prod.mk false) + ν₁.map (Prod.mk true)
  have h_snd (ξ₀ ξ₁ : Measure α) :
      (ξ₀.map (Prod.mk false) + ξ₁.map (Prod.mk true)).snd = ξ₀ + ξ₁ := by
    rw [Measure.snd_add, Measure.snd, Measure.snd,
      Measure.map_map measurable_snd measurable_prodMk_left,
      Measure.map_map measurable_snd measurable_prodMk_left]
    simp [Function.comp_def]
  set s : Set (Bool × α) := {p | p.1 = false} with hs_def
  have hs : MeasurableSet s := measurable_fst (measurableSet_singleton false)
  have h_restrict (ξ₀ ξ₁ : Measure α) :
      (ξ₀.map (Prod.mk false) + ξ₁.map (Prod.mk true)).restrict s = ξ₀.map (Prod.mk false) := by
    rw [Measure.restrict_add, Measure.restrict_map measurable_prodMk_left hs,
      Measure.restrict_map measurable_prodMk_left hs]
    simp [s, preimage]
  have h_restrict_compl (ξ₀ ξ₁ : Measure α) :
      (ξ₀.map (Prod.mk false) + ξ₁.map (Prod.mk true)).restrict sᶜ = ξ₁.map (Prod.mk true) := by
    rw [Measure.restrict_add, Measure.restrict_map measurable_prodMk_left hs.compl,
      Measure.restrict_map measurable_prodMk_left hs.compl]
    simp [s, preimage]
  calc fDiv f (μ₀ + μ₁) (ν₀ + ν₁) = fDiv f P.snd Q.snd := by rw [h_snd, h_snd]
  _ ≤ fDiv f P Q := fDiv_snd_le' P Q
  _ = fDiv f μ₀ ν₀ + fDiv f μ₁ ν₁ := by
    rw [fDiv_eq_fDiv_restrict_add_fDiv_restrict_compl P Q hs, h_restrict, h_restrict,
      h_restrict_compl, h_restrict_compl,
      fDiv_map_measurableEmbedding (measurableEmbedding_prodMk_left false),
      fDiv_map_measurableEmbedding (measurableEmbedding_prodMk_left true)]

/-- Scaling both measures by the same constant scales the f-divergence. -/
lemma fDiv_smul_smul (c : ℝ≥0) (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν] :
    fDiv f (c • μ) (c • ν) = c * fDiv f μ ν := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  rw [fDiv_smul_right _ hc, smul_smul, inv_mul_cancel₀ hc, one_smul]

/-- **Joint convexity** of f-divergences. -/
theorem fDiv_convex (μ₀ μ₁ ν₀ ν₁ : Measure α) [IsFiniteMeasure μ₀] [IsFiniteMeasure μ₁]
    [IsFiniteMeasure ν₀] [IsFiniteMeasure ν₁] (a b : ℝ≥0) :
    fDiv f (a • μ₀ + b • μ₁) (a • ν₀ + b • ν₁) ≤ a * fDiv f μ₀ ν₀ + b * fDiv f μ₁ ν₁ := by
  rw [← fDiv_smul_smul, ← fDiv_smul_smul]
  exact fDiv_add_add_le _ _ _ _

end Convexity

section StatisticalDivergences

/-- On probability measures, the statistical information with prior `π` is the f-divergence for the
function `statInfoFun (π {false}) (π {true})`. -/
lemma statInfo_eq_fDiv (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (π : Measure Bool) [IsFiniteMeasure π] :
    statInfo μ ν π = fDiv (statInfoDivFun (π {false}).toReal (π {true}).toReal) μ ν := by
  set β := (π {false}).toReal
  set γ := (π {true}).toReal
  have h := fDiv_statInfoFun_eq_StatInfo_of_nonneg (μ := μ) (ν := ν) (β := β) (γ := γ)
    ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  have h_corr : |β - γ| + (if γ ≤ β then -1 else 1) * (β - γ) = 0 := by
    split_ifs with hβγ
    · rw [abs_of_nonneg (sub_nonneg.mpr hβγ)]
      ring
    · rw [abs_of_neg (sub_neg.mpr (not_le.mp hβγ))]
      ring
  simp only [measure_univ, ENNReal.toReal_one, mul_one, β, γ,
    ENNReal.ofReal_toReal (measure_ne_top π _), ← Bool.measure_eq_boolMeasure] at h
  rw [h_corr, mul_zero, add_zero] at h
  exact ((ENNReal.toReal_eq_toReal_iff' fDiv_statInfoDivFun_ne_top statInfo_ne_top).mp h).symm

/-- On probability measures, the total variation distance is the f-divergence for the function
`x ↦ max 0 (1 - x)`. -/
lemma tv_eq_fDiv (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    tv μ ν = (fDiv (statInfoDivFun 1 1) μ ν).toReal := by
  rw [tv, statInfo_eq_fDiv]
  simp

end StatisticalDivergences

section BretagnolleHuber

lemma tv_symm (μ ν : Measure α) : tv μ ν = tv ν μ := by
  rw [tv, tv, statInfo_symm]
  congr 2
  refine Measure.ext_of_singleton fun b ↦ ?_
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton b)]
  cases b <;> simp [preimage]

lemma lintegral_one_sub_rnDeriv_eq_tv (μ ν : Measure α) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] :
    ∫⁻ x, 1 - (∂μ/∂ν) x ∂ν = ENNReal.ofReal (tv μ ν) := by
  have h := toReal_statInfo_eq_integral_max_of_ge (μ := μ) (ν := ν) (π := Bool.boolMeasure 1 1)
    (by simp)
  simp only [Bool.boolMeasure_apply_true, Bool.boolMeasure_apply_false, ENNReal.toReal_one,
    one_mul] at h
  rw [tv, h, ofReal_integral_eq_lintegral_ofReal]
  · refine lintegral_congr_ae ?_
    filter_upwards [μ.rnDeriv_ne_top ν] with x hx
    rw [ENNReal.ofReal_max, ENNReal.ofReal_zero, zero_max,
      ENNReal.ofReal_sub _ ENNReal.toReal_nonneg, ENNReal.ofReal_one, ENNReal.ofReal_toReal hx]
  · exact (integrable_zero _ _ _).sup ((integrable_const _).sub Measure.integrable_toReal_rnDeriv)
  · exact ae_of_all _ fun _ ↦ le_max_left _ _

/-- **Bretagnolle-Huber** type lower bound on an f-divergence in terms of the total variation
distance. -/
theorem apply_one_add_tv_add_apply_one_sub_tv_le_fDiv (μ ν : Measure α) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] :
    f (1 + ENNReal.ofReal (tv μ ν)) + f (1 - ENNReal.ofReal (tv μ ν)) ≤ fDiv f μ ν := by
  set T := ENNReal.ofReal (tv μ ν)
  have hT := lintegral_one_sub_rnDeriv_eq_tv μ ν
  have hr : Measurable (∂μ/∂ν) := Measure.measurable_rnDeriv μ ν
  have h_min : ∫⁻ x, min ((∂μ/∂ν) x) 1 ∂ν = 1 - T := by
    have h_eq x : min ((∂μ/∂ν) x) 1 = 1 - (1 - (∂μ/∂ν) x) := by
      rcases le_total ((∂μ/∂ν) x) 1 with h | h
      · rw [min_eq_left h, ENNReal.sub_sub_cancel ENNReal.one_ne_top h]
      · rw [min_eq_right h, tsub_eq_zero_of_le h, tsub_zero]
    simp_rw [h_eq]
    rw [lintegral_sub (g := fun x ↦ 1 - (∂μ/∂ν) x) (measurable_const.sub hr)
      (hT ▸ ENNReal.ofReal_ne_top)
      (ae_of_all _ fun _ ↦ tsub_le_self), lintegral_const, measure_univ, one_mul, hT]
  have h_max : ∫⁻ x, max ((∂μ/∂ν) x) 1 ∂ν + μ.singularPart ν univ = 1 + T := by
    have h_eq x : max ((∂μ/∂ν) x) 1 = (∂μ/∂ν) x + (1 - (∂μ/∂ν) x) := by
      rcases le_total ((∂μ/∂ν) x) 1 with h | h
      · rw [max_eq_right h, add_tsub_cancel_of_le h]
      · rw [max_eq_left h, tsub_eq_zero_of_le h, add_zero]
    simp_rw [h_eq]
    have h_univ : μ univ = μ.singularPart ν univ + ∫⁻ x, (∂μ/∂ν) x ∂ν := by
      conv_lhs => rw [μ.haveLebesgueDecomposition_add ν]
      rw [Measure.add_apply, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    rw [lintegral_add_left hr, hT, add_right_comm, add_comm (∫⁻ x, (∂μ/∂ν) x ∂ν), ← h_univ,
      measure_univ]
  have h_split x : f ((∂μ/∂ν) x) = f (max ((∂μ/∂ν) x) 1) + f (min ((∂μ/∂ν) x) 1) := by
    rcases le_total ((∂μ/∂ν) x) 1 with h | h
    · simp [max_eq_right h, min_eq_left h]
    · simp [max_eq_left h, min_eq_right h]
  have h_max_ne_top : ∫⁻ x, max ((∂μ/∂ν) x) 1 ∂ν ≠ ∞ :=
    ne_top_of_le_ne_top (by simp [T]) (le_self_add.trans h_max.le)
  have h_min_ne_top : ∫⁻ x, min ((∂μ/∂ν) x) 1 ∂ν ≠ ∞ := by
    rw [h_min]
    exact ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self
  have h_jensen_max := f.map_lintegral_le (hr.max measurable_const).aemeasurable h_max_ne_top
  have h_jensen_min := f.map_lintegral_le (hr.min measurable_const).aemeasurable h_min_ne_top
  rw [h_min] at h_jensen_min
  calc f (1 + T) + f (1 - T)
      = f (∫⁻ x, max ((∂μ/∂ν) x) 1 ∂ν + μ.singularPart ν univ) + f (1 - T) := by rw [h_max]
    _ ≤ f (∫⁻ x, max ((∂μ/∂ν) x) 1 ∂ν) + f.derivAtTop * μ.singularPart ν univ
        + ∫⁻ x, f (min ((∂μ/∂ν) x) 1) ∂ν := by
      gcongr
      exact f.le_add_derivAtTop'' _ _
    _ ≤ ∫⁻ x, f (max ((∂μ/∂ν) x) 1) ∂ν + f.derivAtTop * μ.singularPart ν univ
        + ∫⁻ x, f (min ((∂μ/∂ν) x) 1) ∂ν := by gcongr
    _ = fDiv f μ ν := by
      have h_meas : Measurable fun x ↦ f (max ((∂μ/∂ν) x) 1) :=
        f.measurable.comp (hr.max measurable_const)
      rw [fDiv, lintegral_congr (fun x ↦ h_split x), lintegral_add_left h_meas]
      ring

/-- **Bretagnolle-Huber** type lower bound on an f-divergence in terms of the total variation
distance, obtained by applying `apply_one_add_tv_add_apply_one_sub_tv_le_fDiv` to `f.conj`. For
`t ≠ 0`, `f.conj t = t * f t⁻¹`. -/
theorem conj_one_add_tv_add_conj_one_sub_tv_le_fDiv (μ ν : Measure α) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] :
    f.conj (1 + ENNReal.ofReal (tv μ ν)) + f.conj (1 - ENNReal.ofReal (tv μ ν)) ≤ fDiv f μ ν := by
  rw [← fDiv_conj, tv_symm]
  exact apply_one_add_tv_add_apply_one_sub_tv_le_fDiv ν μ

lemma conj_klDivFun_ofReal {s : ℝ} (hs : 0 < s) :
    klDivFun.conj (ENNReal.ofReal s) = ENNReal.ofReal (s - 1 - Real.log s) := by
  rw [DivFunction.conj_of_ne_zero (ENNReal.ofReal_pos.2 hs).ne', ← ENNReal.ofReal_inv_of_pos hs,
    klDivFun_apply ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal (inv_nonneg.2 hs.le),
    ← ENNReal.ofReal_mul hs.le, Real.log_inv]
  congr 1
  field_simp
  ring

/-- **Bretagnolle-Huber inequality**: `-log (1 - tv μ ν ^ 2) ≤ klDiv μ ν`. -/
theorem neg_log_one_sub_sq_tv_le_klDiv (μ ν : Measure α) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] :
    ENNReal.ofReal (-Real.log (1 - tv μ ν ^ 2)) ≤ klDiv μ ν := by
  have h := conj_one_add_tv_add_conj_one_sub_tv_le_fDiv (f := klDivFun) μ ν
  rw [← klDiv_eq_fDiv] at h
  refine le_trans ?_ h
  have htv0 : 0 ≤ tv μ ν := tv_nonneg
  have htv1 : tv μ ν ≤ 1 := tv_le.trans (by simp)
  rcases htv1.lt_or_eq with htv1 | htv1
  swap
  · simp [htv1]
  rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one htv0,
    ← ENNReal.ofReal_sub _ htv0, conj_klDivFun_ofReal (by linarith),
    conj_klDivFun_ofReal (by linarith),
    ← ENNReal.ofReal_add (sub_nonneg.2 (Real.log_le_sub_one_of_pos (by linarith)))
      (sub_nonneg.2 (Real.log_le_sub_one_of_pos (by linarith)))]
  refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
  rw [show 1 - tv μ ν ^ 2 = (1 + tv μ ν) * (1 - tv μ ν) by ring,
    Real.log_mul (by linarith) (by linarith)]
  ring

/-- The divergence function `x ↦ |x - 1| / 2`, which defines the total variation distance on
probability measures (see `fDiv_tvDivFun`). -/
noncomputable
def tvDivFun : DivFunction :=
  DivFunction.ofReal (fun x ↦ 2⁻¹ * |x - 1|)
    (by
      have h1 : ConvexOn ℝ univ (fun x : ℝ ↦ x - 1) :=
        (convexOn_id convex_univ).sub (concaveOn_const 1 convex_univ)
      have h2 : ConvexOn ℝ univ (fun x : ℝ ↦ 1 - x) :=
        (convexOn_const 1 convex_univ).sub (concaveOn_id convex_univ)
      have h := (h1.sup h2).smul (by norm_num : (0 : ℝ) ≤ 2⁻¹)
      refine (h.subset (subset_univ _) (convex_Ioi 0)).congr fun x _ ↦ ?_
      simp [abs_eq_max_neg])
    (by simp)

lemma tvDivFun_apply {x : ℝ≥0∞} (hx : x ≠ ∞) : tvDivFun x = 2⁻¹ * ((x - 1) + (1 - x)) := by
  rw [tvDivFun, DivFunction.ofReal_apply_of_continuousWithinAt (by fun_prop) hx,
    ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_inv_of_pos (by norm_num), ENNReal.ofReal_ofNat]
  congr 1
  rcases le_total x 1 with h | h
  · have h' : x.toReal ≤ 1 := ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using h)
    rw [abs_of_nonpos (sub_nonpos.2 h'), tsub_eq_zero_of_le h, zero_add, neg_sub,
      ENNReal.ofReal_sub _ ENNReal.toReal_nonneg, ENNReal.ofReal_one, ENNReal.ofReal_toReal hx]
  · have h' : 1 ≤ x.toReal := by
      rw [← ENNReal.toReal_one]
      exact ENNReal.toReal_mono hx h
    rw [abs_of_nonneg (sub_nonneg.2 h'), tsub_eq_zero_of_le h, add_zero,
      ENNReal.ofReal_sub _ zero_le_one, ENNReal.ofReal_one, ENNReal.ofReal_toReal hx]

@[simp] lemma derivAtTop_tvDivFun : tvDivFun.derivAtTop = 2⁻¹ := by
  have : (𝓝[<] (∞ : ℝ≥0∞)).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, ENNReal.zero_lt_top⟩
  refine tendsto_nhds_unique tvDivFun.tendsto_div_nhdsLT_top ?_
  have h_inv : Tendsto (fun y : ℝ≥0∞ ↦ y⁻¹) (𝓝[<] ∞) (𝓝 0) := by
    simpa using (continuous_inv.tendsto (∞ : ℝ≥0∞)).mono_left nhdsWithin_le_nhds
  have h := ENNReal.Tendsto.const_mul
    (ENNReal.Tendsto.sub tendsto_const_nhds h_inv (Or.inl ENNReal.one_ne_top))
    (a := 2⁻¹) (Or.inr (by simp))
  rw [tsub_zero, mul_one] at h
  refine h.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT ENNReal.one_lt_top] with y hy
  have hy0 : y ≠ 0 := (zero_lt_one.trans hy.1).ne'
  rw [tvDivFun_apply hy.2.ne, tsub_eq_zero_of_le hy.1.le, add_zero, mul_div_assoc,
    ENNReal.sub_div (fun _ _ ↦ hy0), ENNReal.div_self hy0 hy.2.ne, one_div]

/-- On probability measures, the total variation distance is the f-divergence for the function
`x ↦ |x - 1| / 2`. -/
lemma fDiv_tvDivFun (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    fDiv tvDivFun μ ν = ENNReal.ofReal (tv μ ν) := by
  set T := ENNReal.ofReal (tv μ ν)
  have hT := lintegral_one_sub_rnDeriv_eq_tv μ ν
  have hr : Measurable (∂μ/∂ν) := Measure.measurable_rnDeriv μ ν
  -- `∫⁻ (r - 1) ∂ν + μ⊥(X) = T`
  have h_sub : ∫⁻ x, (∂μ/∂ν) x - 1 ∂ν + μ.singularPart ν univ = T := by
    have h_univ : μ univ = μ.singularPart ν univ + ∫⁻ x, (∂μ/∂ν) x ∂ν := by
      conv_lhs => rw [μ.haveLebesgueDecomposition_add ν]
      rw [Measure.add_apply, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    have h_eq x : (∂μ/∂ν) x + (1 - (∂μ/∂ν) x) = 1 + ((∂μ/∂ν) x - 1) := by
      rcases le_total ((∂μ/∂ν) x) 1 with h | h
      · rw [add_tsub_cancel_of_le h, tsub_eq_zero_of_le h, add_zero]
      · rw [tsub_eq_zero_of_le h, add_zero, add_tsub_cancel_of_le h]
    have h_int := lintegral_congr (μ := ν) h_eq
    rw [lintegral_add_left hr, lintegral_add_left measurable_const, lintegral_const,
      measure_univ, one_mul, hT] at h_int
    have h_total : 1 + (∫⁻ x, (∂μ/∂ν) x - 1 ∂ν + μ.singularPart ν univ) = 1 + T := by
      rw [← add_assoc, ← h_int, add_right_comm, add_comm (∫⁻ x, (∂μ/∂ν) x ∂ν), ← h_univ,
        measure_univ]
    exact (ENNReal.add_right_inj ENNReal.one_ne_top).mp h_total
  have h_ae : (fun x ↦ tvDivFun ((∂μ/∂ν) x))
      =ᵐ[ν] fun x ↦ 2⁻¹ * (((∂μ/∂ν) x - 1) + (1 - (∂μ/∂ν) x)) := by
    filter_upwards [μ.rnDeriv_ne_top ν] with x hx
    rw [tvDivFun_apply hx]
  have h_meas₁ : Measurable fun x ↦ (∂μ/∂ν) x - 1 := hr.sub measurable_const
  have h_meas₂ : Measurable fun x ↦ ((∂μ/∂ν) x - 1) + (1 - (∂μ/∂ν) x) :=
    h_meas₁.add (measurable_const.sub hr)
  rw [fDiv, lintegral_congr_ae h_ae, lintegral_const_mul _ h_meas₂, lintegral_add_left h_meas₁, hT,
    derivAtTop_tvDivFun, ← mul_add, add_right_comm, h_sub, ← two_mul, ← mul_assoc,
    ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]

/-- On probability measures, the total variation distance is the f-divergence for the function
`x ↦ |x - 1| / 2`. -/
lemma tv_eq_fDiv_tvDivFun (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    tv μ ν = (fDiv tvDivFun μ ν).toReal := by
  rw [fDiv_tvDivFun, ENNReal.toReal_ofReal tv_nonneg]

end BretagnolleHuber

end ProbabilityTheory
