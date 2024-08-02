/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
import TestingLowerBounds.DerivAtTop
import TestingLowerBounds.ForMathlib.RadonNikodym
import TestingLowerBounds.ForMathlib.RnDeriv

/-!

# f-Divergences

## Main definitions

* `FooBar`

## Main statements

* `fooBar_unique`

## Notation

## Implementation details

The most natural type for `f` is `ℝ≥0∞ → EReal` since we apply it to an `ℝ≥0∞`-valued RN derivative,
and its value can be in general both positive or negative, and potentially +∞.
However, we use `ℝ → ℝ` instead, for the following reasons:
* domain: convexity results like `ConvexOn.map_average_le` don't work for `ℝ≥0∞` because they
  require a normed space with scalars in `ℝ`, but `ℝ≥0∞` is a module over `ℝ≥0`.
  Also, the RN derivative is almost everywhere finite for σ-finite measures, so losing ∞ in the
  domain is not an issue.
* codomain: `EReal` is underdeveloped, and all functions we will actually use are finite anyway.

Most results will require these conditions on `f`:
`(hf_cvx : ConvexOn ℝ (Ici 0) f) (hf_cont : ContinuousOn f (Ici 0)) (hf_one : f 1 = 0)`

## References

* [F. Bar, *Quuxes*][bibkey]

## Tags

Foobars, barfoos
-/

open Real MeasureTheory Filter Set

open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

variable {α β : Type*} {m mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {μ ν : Measure α} {κ η : Kernel α β} {f g : ℝ → ℝ}

lemma integrable_toReal_iff {f : α → ℝ≥0∞} (hf : AEMeasurable f μ) (hf_ne_top : ∀ᵐ x ∂μ, f x ≠ ∞) :
    Integrable (fun x ↦ (f x).toReal) μ ↔ ∫⁻ x, f x ∂μ ≠ ∞ := by
  refine ⟨fun h ↦ ?_, fun h ↦ integrable_toReal_of_lintegral_ne_top hf h⟩
  rw [Integrable, HasFiniteIntegral] at h
  have : ∀ᵐ x ∂μ, f x = ↑‖(f x).toReal‖₊ := by
    filter_upwards [hf_ne_top] with x hx
    rw [← ofReal_norm_eq_coe_nnnorm, norm_of_nonneg ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hx]
  rw [lintegral_congr_ae this]
  exact h.2.ne

lemma integrable_f_rnDeriv_of_derivAtTop_ne_top (μ ν : Measure α) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (hf : StronglyMeasurable f)
    (hf_cvx : ConvexOn ℝ (Ici 0) f) (hf_deriv : derivAtTop f ≠ ⊤) :
    Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν := by
  obtain ⟨c, c', h⟩ : ∃ c c', ∀ x, _ → c * x + c' ≤ f x :=
    hf_cvx.exists_affine_le (convex_Ici 0)
  refine integrable_of_le_of_le (f := fun x ↦ f ((∂μ/∂ν) x).toReal)
    (g₁ := fun x ↦ c * ((∂μ/∂ν) x).toReal + c')
    (g₂ := fun x ↦ (derivAtTop f).toReal * ((∂μ/∂ν) x).toReal + f 0)
    ?_ ?_ ?_ ?_ ?_
  · exact (hf.comp_measurable (μ.measurable_rnDeriv ν).ennreal_toReal).aestronglyMeasurable
  · exact ae_of_all _ (fun x ↦ h _ ENNReal.toReal_nonneg)
  · refine ae_of_all _ (fun x ↦ ?_)
    have h := le_add_derivAtTop'' hf_cvx hf_deriv le_rfl
      (ENNReal.toReal_nonneg : 0 ≤ ((∂μ/∂ν) x).toReal)
    rwa [zero_add, add_comm] at h
  · refine (Integrable.const_mul ?_ _).add (integrable_const _)
    exact Measure.integrable_toReal_rnDeriv
  · refine (Integrable.const_mul ?_ _).add (integrable_const _)
    exact Measure.integrable_toReal_rnDeriv

open Classical in
/-- f-Divergence of two measures. -/
noncomputable
def fDiv (f : ℝ → ℝ) (μ ν : Measure α) : EReal :=
  if ¬ Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν then ⊤
  else ∫ x, f ((∂μ/∂ν) x).toReal ∂ν + derivAtTop f * μ.singularPart ν Set.univ

lemma fDiv_of_not_integrable (hf : ¬ Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν) :
    fDiv f μ ν = ⊤ := if_pos hf

lemma fDiv_of_integrable (hf : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν) :
    fDiv f μ ν = ∫ x, f ((∂μ/∂ν) x).toReal ∂ν + derivAtTop f * μ.singularPart ν Set.univ :=
  if_neg (not_not.mpr hf)

lemma fDiv_of_mul_eq_top (h : derivAtTop f * μ.singularPart ν Set.univ = ⊤) :
    fDiv f μ ν = ⊤ := by
  by_cases hf : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν
  · rw [fDiv, if_neg (not_not.mpr hf), h, EReal.coe_add_top]
  · exact fDiv_of_not_integrable hf

lemma fDiv_ne_bot [IsFiniteMeasure μ] (hf_cvx : ConvexOn ℝ (Ici 0) f) : fDiv f μ ν ≠ ⊥ := by
  rw [fDiv]
  split_ifs with h
  · simp only [ne_eq, EReal.add_eq_bot_iff, EReal.coe_ne_bot, false_or]
    rw [EReal.mul_eq_bot]
    simp [hf_cvx.derivAtTop_ne_bot, not_lt.mpr (EReal.coe_ennreal_nonneg _), measure_ne_top]
  · simp

lemma fDiv_ne_bot_of_derivAtTop_nonneg (hf : 0 ≤ derivAtTop f) : fDiv f μ ν ≠ ⊥ := by
  rw [fDiv]
  split_ifs with h
  · simp only [ne_eq, EReal.add_eq_bot_iff, EReal.coe_ne_bot, false_or]
    rw [EReal.mul_eq_bot]
    have h_ne_bot : derivAtTop f ≠ ⊥ := fun h_eq ↦ by
      rw [h_eq] at hf
      simp at hf
    simp [h_ne_bot, not_lt.mpr (EReal.coe_ennreal_nonneg _), not_lt.mpr hf]
  · simp

@[simp]
lemma fDiv_zero (μ ν : Measure α) : fDiv (fun _ ↦ 0) μ ν = 0 := by simp [fDiv]

lemma fDiv_congr' (μ ν : Measure α) (hfg : ∀ᵐ x ∂ν.map (fun x ↦ ((∂μ/∂ν) x).toReal), f x = g x)
    (hfg' : f =ᶠ[atTop] g) :
    fDiv f μ ν = fDiv g μ ν := by
  have h : (fun a ↦ f ((∂μ/∂ν) a).toReal) =ᶠ[ae ν] fun a ↦ g ((∂μ/∂ν) a).toReal :=
    ae_of_ae_map (Measure.measurable_rnDeriv μ ν).ennreal_toReal.aemeasurable hfg
  rw [fDiv, derivAtTop_congr hfg']
  congr 2
  · exact eq_iff_iff.mpr ⟨fun hf ↦ hf.congr h, fun hf ↦ hf.congr h.symm⟩
  · exact EReal.coe_eq_coe_iff.mpr (integral_congr_ae h)

lemma fDiv_congr (μ ν : Measure α) (h : ∀ x ≥ 0, f x = g x) :
    fDiv f μ ν = fDiv g μ ν := by
  have (x : α) : f ((∂μ/∂ν) x).toReal = g ((∂μ/∂ν) x).toReal := h _ ENNReal.toReal_nonneg
  simp_rw [fDiv, this, derivAtTop_congr_nonneg h]
  congr
  simp_rw [this]

-- TODO: finish the proof of `fDiv_of_eq_on_nonneg` and use it to shorten the proof of `fDiv_of_zero_on_nonneg`.
--the name feels a bit wrong, what could I write instead of `on_nonneg`?
lemma fDiv_of_zero_on_nonneg (μ ν : Measure α) (hf : ∀ x ≥ 0, f x = 0) :
    fDiv f μ ν = 0 := by
  have (x : α) : f ((∂μ/∂ν) x).toReal = 0 := hf _ ENNReal.toReal_nonneg
  rw [fDiv_of_integrable (by simp [this])]
  simp_rw [this, integral_zero, EReal.coe_zero, zero_add]
  convert zero_mul _
  rw [derivAtTop_congr_nonneg, derivAtTop_zero]
  exact fun x hx ↦ hf x hx

@[simp]
lemma fDiv_zero_measure (ν : Measure α) [IsFiniteMeasure ν] : fDiv f 0 ν = f 0 * ν Set.univ := by
  have : (fun x ↦ f ((∂0/∂ν) x).toReal) =ᵐ[ν] fun _ ↦ f 0 := by
    filter_upwards [Measure.rnDeriv_zero ν] with x hx
    rw [hx]
    simp
  rw [fDiv_of_integrable]
  · simp only [Measure.singularPart_zero, Measure.coe_zero, Pi.zero_apply, EReal.coe_ennreal_zero,
      mul_zero, add_zero]
    rw [integral_congr_ae this, mul_comm (f 0 : EReal), integral_const, smul_eq_mul, EReal.coe_mul,
      ← EReal.coe_ennreal_toReal (measure_ne_top _ _)]
  · rw [integrable_congr this]
    exact integrable_const _

@[simp]
lemma fDiv_zero_measure_right (μ : Measure α) : fDiv f μ 0 = derivAtTop f * μ Set.univ := by
  rw [fDiv_of_integrable] <;> simp

@[simp]
lemma fDiv_const (c : ℝ) (μ ν : Measure α) [IsFiniteMeasure ν] :
    fDiv (fun _ ↦ c) μ ν = ν Set.univ * c := by
  rw [fDiv_of_integrable (integrable_const c), integral_const]
  simp only [smul_eq_mul, EReal.coe_mul, derivAtTop_const, zero_mul, add_zero]
  congr
  rw [EReal.coe_ennreal_toReal]
  exact measure_ne_top _ _

lemma fDiv_const' {c : ℝ} (hc : 0 ≤ c) (μ ν : Measure α) :
    fDiv (fun _ ↦ c) μ ν = ν Set.univ * c := by
  by_cases hν : IsFiniteMeasure ν
  · exact fDiv_const c μ ν
  · have : ν Set.univ = ∞ := by
      by_contra h_univ
      exact absurd ⟨Ne.lt_top h_univ⟩ hν
    rw [this]
    by_cases hc0 : c = 0
    · simp [hc0]
    rw [fDiv_of_not_integrable]
    · simp only [EReal.coe_ennreal_top]
      rw [EReal.top_mul_of_pos]
      refine lt_of_le_of_ne ?_ (Ne.symm ?_)
      · exact mod_cast hc
      · exact mod_cast hc0
    · rw [integrable_const_iff]
      simp [hc0, this]

lemma fDiv_self (hf_one : f 1 = 0) (μ : Measure α) [SigmaFinite μ] : fDiv f μ μ = 0 := by
  have h : (fun x ↦ f (μ.rnDeriv μ x).toReal) =ᵐ[μ] 0 := by
    filter_upwards [Measure.rnDeriv_self μ] with x hx
    rw [hx, ENNReal.one_toReal, hf_one]
    rfl
  rw [fDiv_of_integrable]
  swap; · rw [integrable_congr h]; exact integrable_zero _ _ _
  rw [integral_congr_ae h]
  simp only [Pi.zero_apply, integral_zero, EReal.coe_zero, zero_add]
  rw [Measure.singularPart_self]
  simp

@[simp]
lemma fDiv_id (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν] :
    fDiv id μ ν = μ Set.univ := by
  by_cases h_int : Integrable (fun x ↦ ((∂μ/∂ν) x).toReal) ν
  · rw [fDiv_of_integrable h_int]
    simp only [id_eq, derivAtTop_id, one_mul]
    rw [← integral_univ, Measure.setIntegral_toReal_rnDeriv_eq_withDensity]
    have h_ne_top : (Measure.withDensity ν (∂μ/∂ν)) Set.univ ≠ ∞ := by
      rw [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ]
      rwa [integrable_toReal_iff] at h_int
      · exact (μ.measurable_rnDeriv ν).aemeasurable
      · exact μ.rnDeriv_ne_top ν
    rw [EReal.coe_ennreal_toReal h_ne_top]
    norm_cast
    conv_rhs => rw [μ.haveLebesgueDecomposition_add ν, add_comm]
    simp
  · rw [fDiv_of_not_integrable h_int]
    symm
    by_contra h_ne_top
    have : IsFiniteMeasure μ := ⟨Ne.lt_top ?_⟩
    swap; · rw [← EReal.coe_ennreal_top] at h_ne_top; exact mod_cast h_ne_top
    refine h_int ?_
    refine integrable_toReal_of_lintegral_ne_top (μ.measurable_rnDeriv ν).aemeasurable ?_
    exact (Measure.lintegral_rnDeriv_lt_top _ _).ne

@[simp]
lemma fDiv_id' (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν] :
    fDiv (fun x ↦ x) μ ν = μ Set.univ := fDiv_id μ ν

lemma fDiv_mul {c : ℝ} (hc : 0 ≤ c) (hf_cvx : ConvexOn ℝ (Ici 0) f)
    (μ ν : Measure α) :
    fDiv (fun x ↦ c * f x) μ ν = c * fDiv f μ ν := by
  by_cases hc0 : c = 0
  · simp [hc0]
  by_cases h_int : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν
  · rw [fDiv_of_integrable h_int, fDiv_of_integrable]
    swap; · exact h_int.const_mul _
    rw [integral_mul_left, derivAtTop_const_mul hf_cvx hc0,
      EReal.coe_mul, EReal.coe_mul_add_of_nonneg hc, mul_assoc]
  · rw [fDiv_of_not_integrable h_int, fDiv_of_not_integrable]
    · rw [EReal.mul_top_of_pos]
      norm_cast
      exact lt_of_le_of_ne hc (Ne.symm hc0)
    · refine fun h ↦ h_int ?_
      have : (fun x ↦ f ((∂μ/∂ν) x).toReal) = (fun x ↦ c⁻¹ * (c * f ((∂μ/∂ν) x).toReal)) := by
        ext; rw [← mul_assoc, inv_mul_cancel hc0, one_mul]
      rw [this]
      exact h.const_mul _

lemma fDiv_mul_of_ne_top (c : ℝ) (hf_cvx : ConvexOn ℝ (Ici 0) f) (h_top : derivAtTop f ≠ ⊤)
    (μ ν : Measure α) [IsFiniteMeasure μ] (h_int : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν) :
    fDiv (fun x ↦ c * f x) μ ν = c * fDiv f μ ν := by
  by_cases hc0 : c = 0
  · simp [hc0]
  rw [fDiv_of_integrable h_int, fDiv_of_integrable]
  swap; · exact h_int.const_mul _
  rw [integral_mul_left, derivAtTop_const_mul hf_cvx hc0]
  lift derivAtTop f to ℝ using ⟨h_top, hf_cvx.derivAtTop_ne_bot⟩ with df
  rw [← EReal.coe_ennreal_toReal (measure_ne_top _ _)]
  norm_cast
  ring

-- TODO: in the case where both functions are convex, integrability of the sum is equivalent to
-- integrability of both, and we don't need hf and hg.
-- In general it's not true that if the sum is integrable then both are, even if the functions are
-- convex, take for example f(x) = -x and g(x) = x with the Lebesgue measure. But maybe with some
-- additional hypothesis it's true.
lemma fDiv_add [IsFiniteMeasure μ] (hf : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν)
    (hg : Integrable (fun x ↦ g ((∂μ/∂ν) x).toReal) ν)
    (hf_cvx : ConvexOn ℝ (Ici 0) f) (hg_cvx : ConvexOn ℝ (Ici 0) g) :
    fDiv (fun x ↦ f x + g x) μ ν = fDiv f μ ν + fDiv g μ ν := by
  rw [fDiv_of_integrable (hf.add hg), integral_add hf hg, fDiv_of_integrable hf,
    fDiv_of_integrable hg, derivAtTop_add hf_cvx hg_cvx]
  simp only [EReal.coe_add]
  rw [add_assoc, add_assoc]
  congr 1
  conv_rhs => rw [← add_assoc, add_comm, ← add_assoc, add_comm]
  congr 1
  rw [← EReal.coe_ennreal_toReal]
  · rw [add_comm, EReal.add_mul_coe_of_nonneg ENNReal.toReal_nonneg]
  · exact measure_ne_top _ _

lemma fDiv_add_const (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hf_cvx : ConvexOn ℝ (Set.Ici 0) f) (c : ℝ) :
    fDiv (fun x ↦ f x + c) μ ν = fDiv f μ ν + c * ν Set.univ := by
  by_cases hf_int : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν
  · rw [fDiv_add hf_int (integrable_const _) hf_cvx, fDiv_const, mul_comm]
    exact convexOn_const _ (convex_Ici 0)
  · rw [fDiv_of_not_integrable hf_int, fDiv_of_not_integrable]
    · rw [← EReal.coe_ennreal_toReal, ← EReal.coe_mul, EReal.top_add_coe]
      exact measure_ne_top _ _
    · have : (fun x ↦ f ((∂μ/∂ν) x).toReal) = (fun x ↦ (f ((∂μ/∂ν) x).toReal + c) - c) := by
        ext; simp
      rw [this] at hf_int
      exact fun h_int ↦ hf_int (h_int.sub (integrable_const _))

lemma fDiv_sub_const (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hf_cvx : ConvexOn ℝ (Set.Ici 0) f) (c : ℝ) :
    fDiv (fun x ↦ f x - c) μ ν = fDiv f μ ν - c * ν Set.univ := by
  have : f = fun x ↦ (f x - c) + c := by ext; simp
  conv_rhs => rw [this]
  rw [fDiv_add_const]
  · rw [← EReal.coe_ennreal_toReal (measure_ne_top ν _), ← EReal.coe_mul, EReal.add_sub_cancel]
  · exact hf_cvx.sub (concaveOn_const _ (convex_Ici 0))

lemma fDiv_linear {c : ℝ} [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    fDiv (fun x ↦ c * (x - 1)) μ ν
      = c * ((μ Set.univ).toReal - (ν Set.univ).toReal) := by
  rw [fDiv_mul_of_ne_top]
  rotate_left
  · exact (convexOn_id (convex_Ici 0)).add (convexOn_const _ (convex_Ici 0))
  · rw [derivAtTop_sub_const, derivAtTop_id']
    swap; · exact convexOn_id (convex_Ici 0)
    exact ne_of_beq_false rfl
  · exact integrable_add_const_iff.mpr Measure.integrable_toReal_rnDeriv
  rw [fDiv_sub_const, fDiv_id']
  swap; · exact convexOn_id (convex_Ici 0)
  simp [EReal.coe_ennreal_toReal, measure_ne_top]

lemma fDiv_add_linear' {c : ℝ} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hf_cvx : ConvexOn ℝ (Set.Ici 0) f) :
    fDiv (fun x ↦ f x + c * (x - 1)) μ ν
      = fDiv f μ ν + c * ((μ Set.univ).toReal - (ν Set.univ).toReal) := by
  by_cases hf : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν
  · rw [fDiv_add hf _ hf_cvx _, fDiv_linear]
    · exact (Measure.integrable_toReal_rnDeriv.sub (integrable_const _)).const_mul c
    · rcases le_total 0 c with (hc | hc)
      · exact ((convexOn_id (convex_Ici 0)).sub (concaveOn_const _ (convex_Ici 0))).smul hc
      · rw [← neg_neg c]
        simp_rw [neg_mul (-c)]
        exact (concaveOn_id (convex_Ici 0)).sub (convexOn_const _ (convex_Ici 0)) |>.smul
          (neg_nonneg.mpr hc) |>.neg
  · rw [fDiv_of_not_integrable hf, fDiv_of_not_integrable, EReal.top_add_of_ne_bot]
    · refine (EReal.mul_ne_bot _ _).mpr ⟨?_, ?_, ?_, ?_⟩
      · simp
      · exact Or.inr <| EReal.add_top_iff_ne_bot.mp rfl
      · simp
      · exact Or.inr <| Ne.symm (ne_of_beq_false rfl)
    · refine fun h_int ↦ hf ?_
      have : (fun x ↦ f ((∂μ/∂ν) x).toReal)
          = fun x ↦ (f ((∂μ/∂ν) x).toReal + c * (((∂μ/∂ν) x).toReal - 1))
            - c * (((∂μ/∂ν) x).toReal - 1) := by ext x; simp
      rw [this]
      exact h_int.add ((Measure.integrable_toReal_rnDeriv.sub (integrable_const _)).const_mul c).neg

lemma fDiv_add_linear {c : ℝ} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hf_cvx : ConvexOn ℝ (Set.Ici 0) f) (h_eq : μ Set.univ = ν Set.univ) :
    fDiv (fun x ↦ f x + c * (x - 1)) μ ν = fDiv f μ ν := by
  rw [fDiv_add_linear' hf_cvx, h_eq, ← EReal.coe_sub, sub_self]
  simp

lemma fDiv_of_mutuallySingular [SigmaFinite μ] [IsFiniteMeasure ν] (h : μ ⟂ₘ ν) :
    fDiv f μ ν = (f 0 : EReal) * ν Set.univ + derivAtTop f * μ Set.univ := by
  have : μ.singularPart ν = μ := (μ.singularPart_eq_self).mpr h
  have hf_rnDeriv : (fun x ↦ f ((∂μ/∂ν) x).toReal) =ᵐ[ν] fun _ ↦ f 0 := by
    filter_upwards [Measure.rnDeriv_eq_zero_of_mutuallySingular h Measure.AbsolutelyContinuous.rfl]
      with x hx using by simp [hx]
  have h_int : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν := by
      rw [integrable_congr hf_rnDeriv]
      exact integrable_const _
  rw [fDiv_of_integrable h_int, integral_congr_ae hf_rnDeriv]
  simp only [integral_const, smul_eq_mul, EReal.coe_mul, this]
  rw [mul_comm]
  congr
  rw [EReal.coe_ennreal_toReal]
  exact measure_ne_top _ _

lemma fDiv_of_absolutelyContinuous
    [Decidable (Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν)] (h : μ ≪ ν) :
    fDiv f μ ν = if Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν
      then (↑(∫ x, f ((∂μ/∂ν) x).toReal ∂ν) : EReal) else ⊤ := by
  split_ifs with h_int
  · rw [fDiv_of_integrable h_int, Measure.singularPart_eq_zero_of_ac h]
    simp only [Measure.coe_zero, Pi.zero_apply, mul_zero, ENNReal.zero_toReal, add_zero]
    simp [Measure.singularPart_eq_zero_of_ac h]
  · rw [fDiv_of_not_integrable h_int]

lemma fDiv_eq_add_withDensity_singularPart
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hf_cvx : ConvexOn ℝ (Ici 0) f) :
    fDiv f μ ν = fDiv f (ν.withDensity (∂μ/∂ν)) ν + fDiv f (μ.singularPart ν) ν
      - f 0 * ν Set.univ := by
  have h_int_iff : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν
      ↔ Integrable (fun x ↦ f ((∂(ν.withDensity (∂μ/∂ν))/∂ν) x).toReal) ν := by
    refine integrable_congr ?_
    filter_upwards [Measure.rnDeriv_withDensity ν (μ.measurable_rnDeriv ν)] with x hx
    rw [hx]
  classical
  rw [fDiv_of_mutuallySingular (Measure.mutuallySingular_singularPart _ _)]
  by_cases hf : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν
  · rw [fDiv_of_absolutelyContinuous (withDensity_absolutelyContinuous _ _), if_pos,
      fDiv_of_integrable hf]
    swap
    · exact h_int_iff.mp hf
    rw [add_sub_assoc]
    congr 2
    · refine integral_congr_ae ?_
      filter_upwards [Measure.rnDeriv_withDensity ν (μ.measurable_rnDeriv ν)] with x hx
      rw [hx]
    rw [← EReal.coe_ennreal_toReal (measure_ne_top ν _), ← EReal.coe_mul, EReal.add_sub_cancel']
  · rw [fDiv_of_not_integrable hf, fDiv_of_not_integrable]
    · rw [add_sub_assoc, ← EReal.coe_ennreal_toReal (measure_ne_top ν _), ← EReal.coe_mul,
        EReal.add_sub_cancel']
      by_cases h0 : μ.singularPart ν Set.univ = 0
      · simp [h0]
      · by_cases h_top : derivAtTop f = ⊤
        · rw [h_top, EReal.top_mul_ennreal_coe h0, EReal.top_add_top]
        · lift derivAtTop f to ℝ using ⟨h_top, hf_cvx.derivAtTop_ne_bot⟩ with x
          rw [← EReal.coe_ennreal_toReal (measure_ne_top _ _), ← EReal.coe_mul, EReal.top_add_coe]
    · rwa [← h_int_iff]

lemma fDiv_eq_add_withDensity_singularPart'
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hf_cvx : ConvexOn ℝ (Ici 0) f) :
    fDiv f μ ν = fDiv (fun x ↦ f x - f 0) (ν.withDensity (∂μ/∂ν)) ν
      + fDiv f (μ.singularPart ν) ν := by
  rw [fDiv_eq_add_withDensity_singularPart _ _ hf_cvx, fDiv_sub_const, add_sub_assoc,
    sub_eq_add_neg, sub_eq_add_neg, add_assoc]
  · congr 1
    rw [add_comm]
  · exact hf_cvx

lemma fDiv_eq_add_withDensity_singularPart''
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hf_cvx : ConvexOn ℝ (Ici 0) f) :
    fDiv f μ ν = fDiv f (ν.withDensity (∂μ/∂ν)) ν
      + fDiv (fun x ↦ f x - f 0) (μ.singularPart ν) ν := by
  rw [fDiv_eq_add_withDensity_singularPart _ _ hf_cvx, fDiv_sub_const, add_sub_assoc,
    sub_eq_add_neg]
  exact hf_cvx

lemma fDiv_eq_add_withDensity_derivAtTop
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hf_cvx : ConvexOn ℝ (Ici 0) f) :
    fDiv f μ ν = fDiv f (ν.withDensity (∂μ/∂ν)) ν + derivAtTop f * μ.singularPart ν Set.univ := by
  rw [fDiv_eq_add_withDensity_singularPart'' μ ν hf_cvx,
    fDiv_of_mutuallySingular (Measure.mutuallySingular_singularPart _ _),
    derivAtTop_sub_const hf_cvx]
  simp

lemma fDiv_lt_top_of_ac (h : μ ≪ ν) (h_int : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν) :
    fDiv f μ ν < ⊤ := by
  classical
  rw [fDiv_of_absolutelyContinuous h, if_pos h_int]
  simp

lemma fDiv_add_measure_le_of_ac {μ₁ μ₂ ν : Measure α} [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂]
    [IsFiniteMeasure ν] (h₁ : μ₁ ≪ ν) (h₂ : μ₂ ≪ ν)
    (hf : StronglyMeasurable f) (hf_cvx : ConvexOn ℝ (Ici 0) f) :
    fDiv f (μ₁ + μ₂) ν ≤ fDiv f μ₁ ν + derivAtTop f * μ₂ Set.univ := by
  classical
  by_cases hμ₂0 : μ₂ = 0
  · simp [hμ₂0]
  by_cases h_top : derivAtTop f = ⊤
  · rw [h_top, EReal.top_mul_of_pos, EReal.add_top_of_ne_bot]
    · exact le_top
    · refine fDiv_ne_bot_of_derivAtTop_nonneg ?_
      simp [h_top]
    · simp [hμ₂0]
  have h_int : Integrable (fun x ↦ f ((∂μ₁/∂ν) x).toReal) ν :=
    integrable_f_rnDeriv_of_derivAtTop_ne_top _ _ hf hf_cvx h_top
  have h_int_add : Integrable (fun x ↦ f ((∂μ₁ + μ₂/∂ν) x).toReal) ν :=
    integrable_f_rnDeriv_of_derivAtTop_ne_top _ _ hf hf_cvx h_top
  have h_le : ∀ᵐ x ∂ν, f ((∂μ₁ + μ₂/∂ν) x).toReal
      ≤ f ((∂μ₁/∂ν) x).toReal + (derivAtTop f).toReal * ((∂μ₂/∂ν) x).toReal := by
    have h_add := Measure.rnDeriv_add' μ₁ μ₂ ν
    filter_upwards [h_add, μ₁.rnDeriv_lt_top ν, μ₂.rnDeriv_lt_top ν] with x hx hx₁ hx₂
    rw [hx, Pi.add_apply, ENNReal.toReal_add hx₁.ne hx₂.ne]
    exact le_add_derivAtTop'' hf_cvx h_top ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  rw [fDiv_of_absolutelyContinuous (Measure.AbsolutelyContinuous.add_left_iff.mpr ⟨h₁, h₂⟩),
    if_pos h_int_add, fDiv_of_absolutelyContinuous h₁, if_pos h_int]
  lift derivAtTop f to ℝ using ⟨h_top, hf_cvx.derivAtTop_ne_bot⟩ with df
  rw [← EReal.coe_ennreal_toReal (measure_ne_top _ _)]
  norm_cast
  calc ∫ x, f ((∂μ₁ + μ₂/∂ν) x).toReal ∂ν
    ≤ ∫ x, f ((∂μ₁/∂ν) x).toReal + df * ((∂μ₂/∂ν) x).toReal ∂ν := by
        refine integral_mono_ae h_int_add ?_ h_le
        exact h_int.add (Measure.integrable_toReal_rnDeriv.const_mul _)
  _ ≤ ∫ x, f ((∂μ₁/∂ν) x).toReal ∂ν + df * (μ₂ Set.univ).toReal := by
        rw [integral_add h_int (Measure.integrable_toReal_rnDeriv.const_mul _),
          integral_mul_left, Measure.integral_toReal_rnDeriv h₂]

lemma fDiv_absolutelyContinuous_add_mutuallySingular {μ₁ μ₂ ν : Measure α}
    [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂] [IsFiniteMeasure ν] (h₁ : μ₁ ≪ ν) (h₂ : μ₂ ⟂ₘ ν)
    (hf_cvx : ConvexOn ℝ (Ici 0) f) :
    fDiv f (μ₁ + μ₂) ν = fDiv f μ₁ ν + derivAtTop f * μ₂ Set.univ := by
  rw [fDiv_eq_add_withDensity_derivAtTop  _ _ hf_cvx, Measure.singularPart_add,
    Measure.singularPart_eq_zero_of_ac h₁, Measure.singularPart_eq_self.mpr h₂, zero_add]
  congr
  conv_rhs => rw [← Measure.withDensity_rnDeriv_eq μ₁ ν h₁]
  refine withDensity_congr_ae ?_
  refine (Measure.rnDeriv_add' _ _ _).trans ?_
  filter_upwards [Measure.rnDeriv_eq_zero_of_mutuallySingular h₂ Measure.AbsolutelyContinuous.rfl]
    with x hx
  simp [hx]

lemma fDiv_add_measure_le (μ₁ μ₂ ν : Measure α) [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂]
    [IsFiniteMeasure ν] (hf : StronglyMeasurable f) (hf_cvx : ConvexOn ℝ (Ici 0) f) :
    fDiv f (μ₁ + μ₂) ν ≤ fDiv f μ₁ ν + derivAtTop f * μ₂ Set.univ := by
  rw [μ₂.haveLebesgueDecomposition_add ν, μ₁.haveLebesgueDecomposition_add ν]
  have : μ₁.singularPart ν + ν.withDensity (∂μ₁/∂ν) + (μ₂.singularPart ν + ν.withDensity (∂μ₂/∂ν))
      = (ν.withDensity (∂μ₁/∂ν) + ν.withDensity (∂μ₂/∂ν))
        + (μ₁.singularPart ν + μ₂.singularPart ν) := by
    abel
  rw [this, fDiv_absolutelyContinuous_add_mutuallySingular
      ((withDensity_absolutelyContinuous _ _).add_left (withDensity_absolutelyContinuous _ _))
      ((Measure.mutuallySingular_singularPart _ _).add_left
        (Measure.mutuallySingular_singularPart _ _)) hf_cvx]
  simp only [Measure.coe_add, Pi.add_apply, EReal.coe_ennreal_add]
  conv_rhs => rw [add_comm (μ₁.singularPart ν)]
  rw [fDiv_absolutelyContinuous_add_mutuallySingular (withDensity_absolutelyContinuous _ _)
    (Measure.mutuallySingular_singularPart _ _) hf_cvx]
  calc fDiv f (ν.withDensity (∂μ₁/∂ν) + ν.withDensity (∂μ₂/∂ν)) ν +
      derivAtTop f * (↑(μ₁.singularPart ν Set.univ) + ↑(μ₂.singularPart ν Set.univ))
    = fDiv f (ν.withDensity (∂μ₁/∂ν) + ν.withDensity (∂μ₂/∂ν)) ν
      + derivAtTop f * μ₁.singularPart ν Set.univ
      + derivAtTop f * μ₂.singularPart ν Set.univ := by
        simp_rw [← EReal.coe_ennreal_toReal (measure_ne_top _ _)]
        rw [add_assoc, EReal.mul_add_coe_of_nonneg _ ENNReal.toReal_nonneg ENNReal.toReal_nonneg]
  _ ≤ fDiv f (ν.withDensity (∂μ₁/∂ν)) ν + derivAtTop f * ν.withDensity (∂μ₂/∂ν) Set.univ
      + derivAtTop f * μ₁.singularPart ν Set.univ
      + derivAtTop f * μ₂.singularPart ν Set.univ := by
        gcongr
        exact fDiv_add_measure_le_of_ac (withDensity_absolutelyContinuous _ _)
          (withDensity_absolutelyContinuous _ _) hf hf_cvx
  _ = fDiv f (ν.withDensity (∂μ₁/∂ν)) ν
      + derivAtTop f * μ₁.singularPart ν Set.univ
      + derivAtTop f * μ₂.singularPart ν Set.univ
      + derivAtTop f * ν.withDensity (∂μ₂/∂ν) Set.univ := by
        abel
  _ = fDiv f (ν.withDensity (∂μ₁/∂ν)) ν
      + derivAtTop f * μ₁.singularPart ν Set.univ
      + derivAtTop f * (↑(μ₂.singularPart ν Set.univ) + ↑(ν.withDensity (∂μ₂/∂ν) Set.univ)) := by
        simp_rw [← EReal.coe_ennreal_toReal (measure_ne_top _ _)]
        rw [add_assoc, EReal.mul_add_coe_of_nonneg _ ENNReal.toReal_nonneg ENNReal.toReal_nonneg]

lemma fDiv_le_zero_add_top_of_ac [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμν : μ ≪ ν)
    (hf : StronglyMeasurable f) (hf_cvx : ConvexOn ℝ (Ici 0) f) :
    fDiv f μ ν ≤ f 0 * ν Set.univ + derivAtTop f * μ Set.univ := by
  classical
  by_cases hμ : μ = 0
  · simp [hμ]
  by_cases h_top : derivAtTop f = ⊤
  · rw [h_top, ← EReal.coe_ennreal_toReal (measure_ne_top _ _),
      ← EReal.coe_ennreal_toReal (measure_ne_top _ _), EReal.top_mul_of_pos, ← EReal.coe_mul,
      EReal.coe_add_top]
    · exact le_top
    · norm_cast
      refine ENNReal.toReal_pos (by simp [hμ]) (measure_ne_top _ _)
  · have h_int := integrable_f_rnDeriv_of_derivAtTop_ne_top μ ν hf hf_cvx h_top
    rw [fDiv_of_absolutelyContinuous hμν, if_pos h_int]
    have h := fun x ↦ le_add_derivAtTop'' hf_cvx h_top le_rfl
      (ENNReal.toReal_nonneg : 0 ≤ ((∂μ/∂ν) x).toReal)
    simp only [zero_add] at h
    rw [← EReal.coe_ennreal_toReal (measure_ne_top _ _),
      ← EReal.coe_ennreal_toReal (measure_ne_top _ _)]
    lift derivAtTop f to ℝ using ⟨h_top, hf_cvx.derivAtTop_ne_bot⟩ with df
    norm_cast
    refine (integral_mono h_int ?_ h).trans_eq ?_
    · exact (integrable_const _).add (Measure.integrable_toReal_rnDeriv.const_mul _)
    rw [integral_add (integrable_const _), integral_const, integral_mul_left, smul_eq_mul, mul_comm,
      Measure.integral_toReal_rnDeriv hμν]
    · simp
    · exact Measure.integrable_toReal_rnDeriv.const_mul _

lemma fDiv_le_zero_add_top [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hf : StronglyMeasurable f) (hf_cvx : ConvexOn ℝ (Ici 0) f) :
    fDiv f μ ν ≤ f 0 * ν Set.univ + derivAtTop f * μ Set.univ := by
  rw [fDiv_eq_add_withDensity_derivAtTop _ _ hf_cvx]
  calc fDiv f (ν.withDensity (∂μ/∂ν)) ν + derivAtTop f * μ.singularPart ν Set.univ
    ≤ f 0 * ν Set.univ + derivAtTop f * ν.withDensity (∂μ/∂ν) Set.univ
      + derivAtTop f * μ.singularPart ν Set.univ := by
        gcongr
        exact fDiv_le_zero_add_top_of_ac (withDensity_absolutelyContinuous _ _) hf hf_cvx
  _ ≤ f 0 * ν Set.univ + derivAtTop f * μ Set.univ := by
        rw [add_assoc]
        gcongr
        conv_rhs => rw [μ.haveLebesgueDecomposition_add ν, add_comm]
        simp only [Measure.coe_add, Pi.add_apply, EReal.coe_ennreal_add]
        simp_rw [← EReal.coe_ennreal_toReal (measure_ne_top _ _)]
        rw [EReal.mul_add_coe_of_nonneg _ ENNReal.toReal_nonneg ENNReal.toReal_nonneg]

section derivAtTopTop

lemma fDiv_of_not_ac [SigmaFinite μ] [SigmaFinite ν] (hf : derivAtTop f = ⊤) (hμν : ¬ μ ≪ ν) :
    fDiv f μ ν = ⊤ := by
  rw [fDiv]
  split_ifs with h_int
  · rw [hf]
    suffices Measure.singularPart μ ν Set.univ ≠ 0 by
      rw [EReal.top_mul_of_pos, EReal.coe_add_top]
      refine lt_of_le_of_ne (EReal.coe_ennreal_nonneg _) ?_
      exact mod_cast this.symm
    simp only [ne_eq, Measure.measure_univ_eq_zero]
    rw [Measure.singularPart_eq_zero]
    exact hμν
  · rfl

lemma fDiv_lt_top_iff_ac [SigmaFinite μ] [SigmaFinite ν] (hf : derivAtTop f = ⊤)
    (h_int : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν) :
    fDiv f μ ν < ⊤ ↔ μ ≪ ν := by
  refine ⟨fun h ↦ ?_, fun h ↦ fDiv_lt_top_of_ac h h_int⟩
  by_contra h_not_ac
  refine h.ne (fDiv_of_not_ac hf h_not_ac)

lemma fDiv_ne_top_iff_ac [SigmaFinite μ] [SigmaFinite ν] (hf : derivAtTop f = ⊤)
    (h_int : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν) :
    fDiv f μ ν ≠ ⊤ ↔ μ ≪ ν := by
  rw [← fDiv_lt_top_iff_ac hf h_int, lt_top_iff_ne_top]

lemma fDiv_eq_top_iff_not_ac [SigmaFinite μ] [SigmaFinite ν] (hf : derivAtTop f = ⊤)
    (h_int : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν) :
    fDiv f μ ν = ⊤ ↔ ¬ μ ≪ ν := by
  rw [← fDiv_ne_top_iff_ac hf h_int, not_not]

lemma fDiv_of_derivAtTop_eq_top [SigmaFinite μ] [SigmaFinite ν] (hf : derivAtTop f = ⊤)
    [Decidable (Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν ∧ μ ≪ ν)] :
    fDiv f μ ν = if (Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν ∧ μ ≪ ν)
      then ((∫ x, f ((∂μ/∂ν) x).toReal ∂ν : ℝ) : EReal)
      else ⊤ := by
  split_ifs with h
  · rw [fDiv_of_integrable h.1, Measure.singularPart_eq_zero_of_ac h.2]
    simp
  · push_neg at h
    by_cases hf_int : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν
    · exact fDiv_of_not_ac hf (h hf_int)
    · exact fDiv_of_not_integrable hf_int

end derivAtTopTop

lemma fDiv_lt_top_of_derivAtTop_ne_top [IsFiniteMeasure μ] (hf : derivAtTop f ≠ ⊤)
    (h_int : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν) :
    fDiv f μ ν < ⊤ := by
  rw [fDiv_of_integrable h_int]
  refine EReal.add_lt_top ?_ ?_
  · simp
  · rw [ne_eq, EReal.mul_eq_top]
    simp only [EReal.coe_ennreal_ne_bot, and_false, EReal.coe_ennreal_pos, Measure.measure_univ_pos,
      ne_eq, EReal.coe_ennreal_eq_top_iff, false_or, not_or, not_and, not_lt, not_not]
    refine ⟨fun _ ↦ ?_, ?_, ?_⟩
    · norm_cast
      exact zero_le'
    · simp [hf]
    · exact fun _ ↦ measure_ne_top _ _

lemma fDiv_lt_top_iff_of_derivAtTop_ne_top [IsFiniteMeasure μ] (hf : derivAtTop f ≠ ⊤) :
    fDiv f μ ν < ⊤ ↔ Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν := by
  refine ⟨fun h ↦ ?_, fDiv_lt_top_of_derivAtTop_ne_top hf⟩
  by_contra h_not_int
  rw [fDiv_of_not_integrable h_not_int] at h
  simp at h

lemma fDiv_ne_top_iff_of_derivAtTop_ne_top [IsFiniteMeasure μ] (hf : derivAtTop f ≠ ⊤) :
    fDiv f μ ν ≠ ⊤ ↔ Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν := by
  rw [← fDiv_lt_top_iff_of_derivAtTop_ne_top hf, lt_top_iff_ne_top]

lemma fDiv_eq_top_iff_of_derivAtTop_ne_top [IsFiniteMeasure μ] (hf : derivAtTop f ≠ ⊤) :
    fDiv f μ ν = ⊤ ↔ ¬ Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν := by
  rw [← fDiv_ne_top_iff_of_derivAtTop_ne_top hf, not_not]

lemma fDiv_eq_top_iff [IsFiniteMeasure μ] [SigmaFinite ν] :
    fDiv f μ ν = ⊤
      ↔ (¬ Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν) ∨ (derivAtTop f = ⊤ ∧ ¬ μ ≪ ν) := by
  by_cases h : derivAtTop f = ⊤
  · simp only [h, true_and]
    by_cases hf : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν
    · simp only [hf, not_true_eq_false, false_or]
      exact fDiv_eq_top_iff_not_ac h hf
    · simp [hf, fDiv_of_not_integrable hf]
  · simp only [h, false_and, or_false]
    exact fDiv_eq_top_iff_of_derivAtTop_ne_top h

lemma fDiv_ne_top_iff [IsFiniteMeasure μ] [SigmaFinite ν] :
    fDiv f μ ν ≠ ⊤
      ↔ (Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν) ∧ (derivAtTop f = ⊤ → μ ≪ ν) := by
  rw [ne_eq, fDiv_eq_top_iff]
  push_neg
  rfl

lemma integrable_of_fDiv_ne_top (h : fDiv f μ ν ≠ ⊤) :
    Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν := by
  by_contra h_not
  exact h (fDiv_of_not_integrable h_not)

lemma fDiv_of_ne_top (h : fDiv f μ ν ≠ ⊤) :
    fDiv f μ ν = ∫ x, f ((∂μ/∂ν) x).toReal ∂ν + derivAtTop f * μ.singularPart ν Set.univ := by
  rw [fDiv_of_integrable]
  exact integrable_of_fDiv_ne_top h

lemma toReal_fDiv_of_integrable [IsFiniteMeasure μ] (hf_cvx : ConvexOn ℝ (Ici 0) f)
    (hf_int : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν)
    (h_deriv : derivAtTop f = ⊤ → μ ≪ ν) :
    (fDiv f μ ν).toReal = ∫ y, f ((∂μ/∂ν) y).toReal ∂ν
        + (derivAtTop f * μ.singularPart ν Set.univ).toReal := by
  rw [fDiv_of_integrable hf_int, EReal.toReal_add]
  rotate_left
  · simp
  · simp
  · simp only [ne_eq, EReal.mul_eq_top, hf_cvx.derivAtTop_ne_bot, false_and, EReal.coe_ennreal_ne_bot,
      and_false, EReal.coe_ennreal_pos, Measure.measure_univ_pos, EReal.coe_ennreal_eq_top_iff,
      measure_ne_top, or_false, false_or, not_and, not_not]
    intro h_top
    simp [h_top, Measure.singularPart_eq_zero_of_ac (h_deriv h_top)]
  · simp only [ne_eq, EReal.mul_eq_bot, hf_cvx.derivAtTop_ne_bot, EReal.coe_ennreal_pos,
      Measure.measure_univ_pos, false_and, EReal.coe_ennreal_ne_bot, and_false,
      EReal.coe_ennreal_eq_top_iff, measure_ne_top, or_false, false_or, not_and, not_lt]
    exact fun _ ↦ EReal.coe_ennreal_nonneg _
  rfl

lemma le_fDiv_of_ac [IsFiniteMeasure μ] [IsProbabilityMeasure ν]
    (hf_cvx : ConvexOn ℝ (Ici 0) f) (hf_cont : ContinuousOn f (Ici 0))
    (hμν : μ ≪ ν) :
    f (μ Set.univ).toReal ≤ fDiv f μ ν := by
  by_cases hf_int : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν
  swap; · rw [fDiv_of_not_integrable hf_int]; exact le_top
  rw [fDiv_of_integrable hf_int, Measure.singularPart_eq_zero_of_ac hμν]
  simp only [Measure.coe_zero, Pi.zero_apply,
    EReal.coe_ennreal_zero, mul_zero, add_zero, EReal.coe_le_coe_iff]
  calc f (μ Set.univ).toReal
    = f (∫ x, (μ.rnDeriv ν x).toReal ∂ν) := by rw [Measure.integral_toReal_rnDeriv hμν]
  _ ≤ ∫ x, f (μ.rnDeriv ν x).toReal ∂ν := by
    rw [← average_eq_integral, ← average_eq_integral]
    exact ConvexOn.map_average_le hf_cvx hf_cont isClosed_Ici (by simp)
      Measure.integrable_toReal_rnDeriv hf_int

lemma f_measure_univ_le_add (μ ν : Measure α) [IsFiniteMeasure μ] [IsProbabilityMeasure ν]
    (hf_cvx : ConvexOn ℝ (Ici 0) f) :
    f (μ Set.univ).toReal
      ≤ f (ν.withDensity (∂μ/∂ν) Set.univ).toReal + derivAtTop f * μ.singularPart ν Set.univ := by
  have : μ Set.univ = ν.withDensity (∂μ/∂ν) Set.univ + μ.singularPart ν Set.univ := by
    conv_lhs => rw [μ.haveLebesgueDecomposition_add ν, add_comm]
    simp
  rw [this]
  exact toReal_le_add_derivAtTop hf_cvx (measure_ne_top _ _) (measure_ne_top _ _)

lemma le_fDiv [IsFiniteMeasure μ] [IsProbabilityMeasure ν]
    (hf_cvx : ConvexOn ℝ (Ici 0) f) (hf_cont : ContinuousOn f (Ici 0)) :
    f (μ Set.univ).toReal ≤ fDiv f μ ν := by
  refine (f_measure_univ_le_add μ ν hf_cvx).trans ?_
  rw [fDiv_eq_add_withDensity_singularPart'' μ _ hf_cvx,
    fDiv_of_mutuallySingular  (Measure.mutuallySingular_singularPart μ ν),
    derivAtTop_sub_const hf_cvx]
  simp only [MeasurableSet.univ, withDensity_apply, Measure.restrict_univ, sub_self, EReal.coe_zero,
    measure_univ, EReal.coe_ennreal_one, mul_one, zero_add]
  gcongr
  rw [← setLIntegral_univ, ← withDensity_apply _ MeasurableSet.univ]
  exact le_fDiv_of_ac hf_cvx hf_cont (withDensity_absolutelyContinuous _ _)

lemma fDiv_nonneg [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hf_cvx : ConvexOn ℝ (Ici 0) f) (hf_cont : ContinuousOn f (Ici 0)) (hf_one : f 1 = 0) :
    0 ≤ fDiv f μ ν := by
  calc (0 : EReal) = f (μ Set.univ).toReal := by simp [hf_one]
  _ ≤ fDiv f μ ν := le_fDiv hf_cvx hf_cont

/- The hypothesis `hfg'` can maybe become something like `f ≤ᵐ[atTop] g`, but then we would need
some lemma like `derivAtTop_mono`, and I'm not sure this is true in gneral, without any assumption on `f`.
We could prove it if we had some lemma saying that the new derivAtTop is equal to the old definition,
this is probably false in general, but under some assumptions it should be true. -/
lemma fDiv_mono' (hf_int : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν)
    (hfg : f ≤ᵐ[ν.map (fun x ↦ ((∂μ/∂ν) x).toReal)] g) (hfg' : derivAtTop f ≤ derivAtTop g) :
    fDiv f μ ν ≤ fDiv g μ ν := by
  rw [fDiv_of_integrable hf_int, fDiv]
  split_ifs with hg_int
  swap; · simp
  gcongr
  · exact EReal.coe_le_coe_iff.mpr <| integral_mono_ae hf_int hg_int <|
      ae_of_ae_map (Measure.measurable_rnDeriv μ ν).ennreal_toReal.aemeasurable hfg
  · exact EReal.coe_ennreal_nonneg _

lemma fDiv_mono (hf_int : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν)
    (hfg : f ≤ g) (hfg' : derivAtTop f ≤ derivAtTop g) : fDiv f μ ν ≤ fDiv g μ ν :=
  fDiv_mono' hf_int (eventually_of_forall hfg) hfg'

lemma fDiv_nonneg_of_nonneg (hf : 0 ≤ f) (hf' : 0 ≤ derivAtTop f) :
    0 ≤ fDiv f μ ν :=
  fDiv_zero μ ν ▸ fDiv_mono (integrable_zero α ℝ ν) hf (derivAtTop_zero ▸ hf')

lemma fDiv_eq_zero_iff [IsFiniteMeasure μ] [IsFiniteMeasure ν] (h_mass : μ Set.univ = ν Set.univ)
    (hf_deriv : derivAtTop f = ⊤) (hf_cvx : StrictConvexOn ℝ (Ici 0) f)
    (hf_cont : ContinuousOn f (Ici 0)) (hf_one : f 1 = 0) :
    fDiv f μ ν = 0 ↔ μ = ν := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ fDiv_self hf_one _⟩
  by_cases hμν : μ ≪ ν
  swap; · rw [fDiv_of_not_ac hf_deriv hμν] at h; exact (EReal.top_ne_zero h).elim
  by_cases h_int : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν
  swap; · rw [fDiv_of_not_integrable h_int] at h; exact (EReal.top_ne_zero h).elim
  by_cases hμ_zero : μ = 0
  · rw [hμ_zero] at h_mass ⊢
    rw [Measure.measure_univ_eq_zero.mp h_mass.symm]
  classical
  rw [fDiv_of_derivAtTop_eq_top hf_deriv, if_pos ⟨h_int, hμν⟩, EReal.coe_eq_zero] at h
  have h_eq := StrictConvexOn.ae_eq_const_or_map_average_lt hf_cvx hf_cont isClosed_Ici (by simp)
    Measure.integrable_toReal_rnDeriv h_int
  simp only [average, integral_smul_measure, smul_eq_mul, h, mul_zero, ← h_mass] at h_eq
  rw [Measure.integral_toReal_rnDeriv hμν, ← ENNReal.toReal_mul,
    ENNReal.inv_mul_cancel (Measure.measure_univ_ne_zero.mpr hμ_zero) (measure_ne_top μ _)] at h_eq
  simp only [ENNReal.one_toReal, Function.const_one, log_one, mul_zero, lt_self_iff_false,
    or_false, hf_one] at h_eq
  exact (Measure.rnDeriv_eq_one_iff_eq hμν).mp <| ENNReal.eventuallyEq_of_toReal_eventuallyEq
    (Measure.rnDeriv_ne_top _ _) (eventually_of_forall fun _ ↦ ENNReal.one_ne_top) h_eq

lemma fDiv_eq_zero_iff' [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hf_deriv : derivAtTop f = ⊤) (hf_cvx : StrictConvexOn ℝ (Ici 0) f)
    (hf_cont : ContinuousOn f (Ici 0)) (hf_one : f 1 = 0) :
    fDiv f μ ν = 0 ↔ μ = ν := by
  exact fDiv_eq_zero_iff (by simp) hf_deriv hf_cvx hf_cont hf_one

lemma fDiv_map_measurableEmbedding [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {g : α → β} (hg : MeasurableEmbedding g) :
    fDiv f (μ.map g) (ν.map g) = fDiv f μ ν := by
  by_cases h_int : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν
  · rw [fDiv_of_integrable h_int, fDiv_of_integrable]
    swap
    · rw [hg.integrable_map_iff]
      refine (integrable_congr ?_).mpr h_int
      filter_upwards [hg.rnDeriv_map μ ν] with a ha
      simp [ha]
    rw [hg.integral_map]
    congr 2
    · refine integral_congr_ae ?_
      filter_upwards [hg.rnDeriv_map μ ν] with a ha
      simp [ha]
    · rw [hg.singularPart_map μ ν, hg.map_apply]
      simp
  · rw [fDiv_of_not_integrable h_int, fDiv_of_not_integrable]
    rw [hg.integrable_map_iff]
    rwa [(integrable_congr ?_)]
    filter_upwards [hg.rnDeriv_map μ ν] with a ha
    simp [ha]

lemma fDiv_restrict_of_integrable (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {s : Set α} (hs : MeasurableSet s) (h_int : IntegrableOn (fun x ↦ f ((∂μ/∂ν) x).toReal) s ν) :
    fDiv f (μ.restrict s) ν = ∫ x in s, f ((∂μ/∂ν) x).toReal ∂ν
        + f 0 * ν sᶜ + derivAtTop f * (μ.singularPart ν s) := by
  classical
  have h : (fun x ↦ f ((∂μ.restrict s/∂ν) x).toReal)
      =ᵐ[ν] s.piecewise (fun x ↦ f ((∂μ/∂ν) x).toReal) (fun _ ↦ f 0) := by
    filter_upwards [Measure.rnDeriv_restrict μ ν hs] with a ha
    rw [ha]
    by_cases has : a ∈ s <;> simp [has]
  rw [fDiv_of_integrable, μ.singularPart_restrict ν hs, Measure.restrict_apply_univ]
  swap;
  · rw [integrable_congr h]
    exact Integrable.piecewise hs h_int (integrable_const _)
  congr 1
  rw [integral_congr_ae h, integral_piecewise hs h_int (integrable_const _), integral_const]
  simp only [MeasurableSet.univ, Measure.restrict_apply, Set.univ_inter, smul_eq_mul, EReal.coe_add,
    EReal.coe_mul]
  rw [EReal.coe_ennreal_toReal, mul_comm]
  exact measure_ne_top _ _

section Measurability

lemma measurableSet_integrable_f_kernel_rnDeriv [MeasurableSpace.CountableOrCountablyGenerated α β]
    (κ η ξ : Kernel α β) [IsFiniteKernel ξ] (hf : StronglyMeasurable f) :
    MeasurableSet {a | Integrable (fun x ↦ f (Kernel.rnDeriv κ η a x).toReal) (ξ a)} :=
  measurableSet_kernel_integrable
    (hf.comp_measurable (Kernel.measurable_rnDeriv κ η).ennreal_toReal)

lemma measurableSet_integrable_f_rnDeriv [MeasurableSpace.CountableOrCountablyGenerated α β]
    (κ η : Kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η] (hf : StronglyMeasurable f) :
    MeasurableSet {a | Integrable (fun x ↦ f ((∂κ a/∂η a) x).toReal) (η a)} := by
  convert measurableSet_integrable_f_kernel_rnDeriv κ η η hf using 3 with a
  refine integrable_congr ?_
  filter_upwards [Kernel.rnDeriv_eq_rnDeriv_measure κ η a] with b hb
  rw [hb]

lemma measurable_integral_f_rnDeriv [MeasurableSpace.CountableOrCountablyGenerated α β]
    (κ η : Kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η] (hf : StronglyMeasurable f) :
    Measurable fun a ↦ ∫ x, f ((∂κ a/∂η a) x).toReal ∂(η a) := by
  have : ∀ a, ∫ x, f ((∂κ a/∂η a) x).toReal ∂η a
      = ∫ x, f (Kernel.rnDeriv κ η a x).toReal ∂η a := by
    refine fun a ↦ integral_congr_ae ?_
    filter_upwards [Kernel.rnDeriv_eq_rnDeriv_measure κ η a] with x hx
    rw [hx]
  simp_rw [this]
  refine (StronglyMeasurable.integral_kernel_prod_left ?_).measurable
  refine hf.comp_measurable ?_
  exact ((Kernel.measurable_rnDeriv κ η).comp measurable_swap).ennreal_toReal

lemma measurable_fDiv [MeasurableSpace.CountableOrCountablyGenerated α β]
    (κ η : Kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η]
    (hf : StronglyMeasurable f) :
    Measurable (fun a ↦ fDiv f (κ a) (η a)) := by
  let s := {a | Integrable (fun x ↦ f ((∂κ a/∂η a) x).toReal) (η a)}
  have hs : MeasurableSet s := measurableSet_integrable_f_rnDeriv κ η hf
  classical
  have h_eq : (fun a ↦ fDiv f (κ a) (η a))
      = fun a ↦ if a ∈ s then ∫ x, f ((∂κ a/∂η a) x).toReal ∂(η a)
          + derivAtTop f * (κ a).singularPart (η a) Set.univ
        else ⊤ := by
    ext a
    split_ifs with ha
    · rw [fDiv_of_integrable ha]
    · rw [fDiv_of_not_integrable ha]
  rw [h_eq]
  refine Measurable.ite hs ?_ measurable_const
  refine Measurable.add ?_ ?_
  · exact (measurable_integral_f_rnDeriv _ _ hf).coe_real_ereal
  · refine Measurable.const_mul ?_ _
    exact ((Measure.measurable_coe MeasurableSet.univ).comp
      (Kernel.measurable_singularPart κ η)).coe_ereal_ennreal

end Measurability

end ProbabilityTheory
