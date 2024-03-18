/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import TestingLowerBounds.ForMathlib.EReal
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Calculus.MeanValue
import TestingLowerBounds.SoonInMathlib.RadonNikodym

/-!

# f-Divergences

## Main definitions

* `FooBar`

## Main statements

* `fooBar_unique`

## Notation

## Implementation details

The most natural type for `f` is `ℝ≥0∞ → EReal` since we apply it to an `ℝ≥0∞`-values RN derivative,
and its value can be in general both positive or negative, and potentially +∞.
However, we use `ℝ → ℝ` instead, for the following reasons:
* domain: convexity results like `ConvexOn.map_average_le` don't work for `ℝ≥0∞` because they
  require a normed space with scalars in `ℝ`, but `ℝ≥0∞` is a module over `ℝ≥0`.
  Also, the RN derivative is almost everywhere finite for σ-finite measures, so losing ∞ in the
  domain is not an issue.
* codomain: `EReal` is underdeveloped, and all functions we will actually use are finite anyway.

Most results will require these conditions on `f`:
`(hf_cvx : ConvexOn ℝ (Set.Ici 0) f) (hf_cont : ContinuousOn f (Set.Ici 0)) (hf_one : f 1 = 0)`

## References

* [F. Bar, *Quuxes*][bibkey]

## Tags

Foobars, barfoos
-/

open Real MeasureTheory Filter

open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {μ ν : Measure α} {κ η : kernel α β} {f g : ℝ → ℝ}

lemma integrable_toReal_iff {f : α → ℝ≥0∞} (hf : AEMeasurable f μ) (hf_ne_top : ∀ᵐ x ∂μ, f x ≠ ∞) :
    Integrable (fun x ↦ (f x).toReal) μ ↔ ∫⁻ x, f x ∂μ ≠ ∞ := by
  refine ⟨fun h ↦ ?_, fun h ↦ integrable_toReal_of_lintegral_ne_top hf h⟩
  rw [Integrable, HasFiniteIntegral] at h
  have : ∀ᵐ x ∂μ, f x = ↑‖(f x).toReal‖₊ := by
    filter_upwards [hf_ne_top] with x hx
    rw [← ofReal_norm_eq_coe_nnnorm, norm_of_nonneg ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hx]
  rw [lintegral_congr_ae this]
  exact h.2.ne

-- we put the coe outside the limsup to ensure it's not ⊥
open Classical in
noncomputable
def derivAtTop (f : ℝ → ℝ) : EReal :=
  if Tendsto (fun x ↦ f x / x) atTop atTop then ⊤ else ↑(limsup (fun x ↦ f x / x) atTop)

lemma bot_lt_derivAtTop : ⊥ < derivAtTop f := by
  rw [derivAtTop]
  split_ifs with h <;> simp

lemma derivAtTop_ne_bot : derivAtTop f ≠ ⊥ := bot_lt_derivAtTop.ne'

@[simp]
lemma derivAtTop_const (c : ℝ) : derivAtTop (fun _ ↦ c) = 0 := by
  sorry

@[simp]
lemma derivAtTop_id : derivAtTop id = 1 := by
  rw [derivAtTop, if_neg]
  · norm_cast
    sorry
  · sorry

@[simp]
lemma derivAtTop_id' : derivAtTop (fun x ↦ x) = 1 := derivAtTop_id

lemma derivAtTop_add : derivAtTop (fun x ↦ f x + g x) = derivAtTop f + derivAtTop g := by
  sorry

lemma derivAtTop_add' : derivAtTop (f + g) = derivAtTop f + derivAtTop g := by
  sorry

lemma derivAtTop_const_mul (c : ℝ) :
    derivAtTop (fun x ↦ c * f x) = c * derivAtTop f := by
  sorry

lemma le_add_derivAtTop (h_cvx : ConvexOn ℝ (Set.Ici 0) f)
    (h : ¬ Tendsto (fun x ↦ f x / x) atTop atTop) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    f x ≤ f y + (derivAtTop f).toReal * (x - y) := by
  sorry

lemma le_add_derivAtTop' (h_cvx : ConvexOn ℝ (Set.Ici 0) f)
    (h : ¬ Tendsto (fun x ↦ f x / x) atTop atTop) {x u : ℝ} (hx : 0 ≤ x) (hu : 0 ≤ u) :
    f x ≤ f (u * x) + (derivAtTop f).toReal * x * (1 - u) := by
  sorry

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

lemma fDiv_of_eq_top (h : derivAtTop f * μ.singularPart ν Set.univ = ⊤) :
    fDiv f μ ν = ⊤ := by
  by_cases hf : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν
  · rw [fDiv, if_neg (not_not.mpr hf), h, EReal.coe_add_top]
  · exact fDiv_of_not_integrable hf

@[simp]
lemma fDiv_zero (μ ν : Measure α) : fDiv (fun _ ↦ 0) μ ν = 0 := by
  rw [fDiv]
  simp

@[simp]
lemma fDiv_const (c : ℝ) (μ ν : Measure α) [IsFiniteMeasure ν] :
    fDiv (fun _ ↦ c) μ ν = ν Set.univ * c := by
  rw [fDiv_of_integrable (integrable_const c), integral_const]
  simp only [smul_eq_mul, EReal.coe_mul, derivAtTop_const, zero_mul, add_zero]
  congr
  rw [EReal.coe_ennreal_toReal]
  exact measure_ne_top _ _

@[simp]
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

lemma fDiv_of_mutuallySingular [SigmaFinite μ] [IsFiniteMeasure ν] (h : μ ⟂ₘ ν) :
    fDiv f μ ν = (f 0 : EReal) * ν Set.univ + derivAtTop f * μ Set.univ := by
  have : μ.singularPart ν = μ := (μ.singularPart_eq_self ν).mpr h
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

lemma fDiv_of_absolutelyContinuous [SigmaFinite μ] [SigmaFinite ν]
    [Decidable (Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν)] (h : μ ≪ ν) :
    fDiv f μ ν = if Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν
      then (↑(∫ x, f ((∂μ/∂ν) x).toReal ∂ν) : EReal) else ⊤ := by
  split_ifs with h_int
  · rw [fDiv_of_integrable h_int, Measure.singularPart_eq_zero_of_ac h]
    simp only [Measure.zero_toOuterMeasure, OuterMeasure.coe_zero, Pi.zero_apply, mul_zero,
      ENNReal.zero_toReal, add_zero]
    simp [Measure.singularPart_eq_zero_of_ac h]
  · rw [fDiv_of_not_integrable h_int]

lemma fDiv_add_const
    (μ ν : Measure α) [SigmaFinite μ] [IsFiniteMeasure ν] (c : ℝ) :
    fDiv (fun x ↦ f x + c) μ ν = fDiv f μ ν + c * ν Set.univ := by
  by_cases hf_int : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν
  · rw [fDiv_of_integrable hf_int, fDiv_of_integrable]
    swap; · exact hf_int.add (integrable_const _)
    rw [integral_add hf_int (integrable_const _)]
    simp only [integral_const, smul_eq_mul, EReal.coe_add, EReal.coe_mul]
    rw [add_assoc, add_assoc]
    congr 1
    rw [add_comm, derivAtTop_add, derivAtTop_const, add_zero]
    congr 1
    rw [mul_comm]
    congr
    rw [EReal.coe_ennreal_toReal]
    exact measure_ne_top _ _
  · rw [fDiv_of_not_integrable hf_int, fDiv_of_not_integrable]
    · sorry
    · have : (fun x ↦ f ((∂μ/∂ν) x).toReal) = (fun x ↦ (f ((∂μ/∂ν) x).toReal + c) - c) := by
        ext; simp
      rw [this] at hf_int
      exact fun h_int ↦ hf_int (h_int.sub (integrable_const _))

lemma fDiv_sub_const
    (μ ν : Measure α) [SigmaFinite μ] [IsFiniteMeasure ν] (c : ℝ) :
    fDiv (fun x ↦ f x - c) μ ν = fDiv f μ ν - c * ν Set.univ := by
  have : f = fun x ↦ (f x - c) + c := by ext; simp
  conv_rhs => rw [this, fDiv_add_const]
  sorry

lemma fDiv_eq_add_withDensity_singularPart
    (μ ν : Measure α) [SigmaFinite μ] [IsFiniteMeasure ν]
    (hf : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν) :
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
    sorry
  · rw [fDiv_of_not_integrable hf, fDiv_of_not_integrable]
    · sorry
    · rwa [← h_int_iff]

lemma fDiv_eq_add_withDensity_singularPart'
    (μ ν : Measure α) [SigmaFinite μ] [IsFiniteMeasure ν]
    (hf : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν) :
    fDiv f μ ν = fDiv (fun x ↦ f x - f 0) (ν.withDensity (∂μ/∂ν)) ν
      + fDiv f (μ.singularPart ν) ν := by
  rw [fDiv_eq_add_withDensity_singularPart _ _ hf, fDiv_sub_const, add_sub_assoc,
    sub_eq_add_neg, sub_eq_add_neg, add_assoc]
  congr 1
  rw [add_comm]

lemma fDiv_eq_add_withDensity_singularPart''
    (μ ν : Measure α) [SigmaFinite μ] [IsFiniteMeasure ν]
    (hf : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν) :
    fDiv f μ ν = fDiv f (ν.withDensity (∂μ/∂ν)) ν
      + fDiv (fun x ↦ f x - f 0) (μ.singularPart ν) ν := by
  rw [fDiv_eq_add_withDensity_singularPart _ _ hf, fDiv_sub_const, add_sub_assoc,
    sub_eq_add_neg]

lemma fDiv_id (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν] :
    fDiv id μ ν = μ Set.univ := by
  by_cases h_int : Integrable (fun x ↦ ((∂μ/∂ν) x).toReal) ν
  · rw [fDiv_of_integrable h_int]
    simp only [id_eq, derivAtTop_id, one_mul]
    rw [← integral_univ, Measure.set_integral_toReal_rnDeriv_eq_withDensity]
    have h_lt_top : (Measure.withDensity ν (∂μ/∂ν)) Set.univ < ∞ := by
      sorry -- use h_int
    sorry
  · rw [fDiv_of_not_integrable h_int]
    norm_cast
    symm
    by_contra h_ne_top
    have : IsFiniteMeasure μ := ⟨Ne.lt_top ?_⟩
    swap; · rw [← EReal.coe_ennreal_top] at h_ne_top; exact mod_cast h_ne_top
    refine h_int ?_
    refine integrable_toReal_of_lintegral_ne_top (μ.measurable_rnDeriv ν).aemeasurable ?_
    exact (Measure.lintegral_rnDeriv_lt_top _ _).ne

lemma fDiv_id' (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν] :
    fDiv (fun x ↦ x) μ ν = μ Set.univ := fDiv_id μ ν

lemma fDiv_mul {c : ℝ} (hc : 0 ≤ c) (f : ℝ → ℝ) (μ ν : Measure α) :
    fDiv (fun x ↦ c * f x) μ ν = c * fDiv f μ ν := by
  by_cases hc0 : c = 0
  · simp [hc0]
  by_cases h_int : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν
  · rw [fDiv_of_integrable h_int, fDiv_of_integrable]
    swap; · exact h_int.const_mul _
    rw [integral_mul_left, derivAtTop_const_mul]
    simp only [EReal.coe_mul]
    sorry
  · rw [fDiv_of_not_integrable h_int, fDiv_of_not_integrable]
    · rw [EReal.mul_top_of_pos]
      norm_cast
      exact lt_of_le_of_ne hc (Ne.symm hc0)
    · refine fun h ↦ h_int ?_
      have : (fun x ↦ f ((∂μ/∂ν) x).toReal) = (fun x ↦ c⁻¹ * (c * f ((∂μ/∂ν) x).toReal)) := by
        ext; rw [← mul_assoc, inv_mul_cancel hc0, one_mul]
      rw [this]
      exact h.const_mul _

-- TODO: in the case where both functions are convex, integrability of the sum is equivalent to
-- integrability of both, and we don't need hf and hg.
lemma fDiv_add (hf : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν)
    (hg : Integrable (fun x ↦ g ((∂μ/∂ν) x).toReal) ν) :
    fDiv (fun x ↦ f x + g x) μ ν = fDiv f μ ν + fDiv g μ ν := by
  rw [fDiv_of_integrable (hf.add hg), integral_add hf hg, fDiv_of_integrable hf,
    fDiv_of_integrable hg, derivAtTop_add]
  simp only [EReal.coe_add]
  rw [add_assoc, add_assoc]
  congr 1
  conv_rhs => rw [← add_assoc, add_comm, ← add_assoc, add_comm]
  congr 1
  sorry

lemma fDiv_add_linear' {c : ℝ} (hc : 0 ≤ c) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hf : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν) :
    fDiv (fun x ↦ f x + c * (x - 1)) μ ν
      = fDiv f μ ν + c * ((μ Set.univ).toReal - (ν Set.univ).toReal) := by
  rw [fDiv_add hf]
  · simp_rw [sub_eq_add_neg]
    rw [fDiv_mul hc, fDiv_add Measure.integrable_toReal_rnDeriv (integrable_const _),
      fDiv_const, fDiv_id']
    simp only [EReal.coe_neg, EReal.coe_one, mul_neg, mul_one]
    congr
    · sorry
    · sorry
  · exact (Measure.integrable_toReal_rnDeriv.sub (integrable_const _)).const_mul c

lemma fDiv_add_linear {c : ℝ} (hc : 0 ≤ c) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h_eq : μ Set.univ = ν Set.univ) :
    fDiv (fun x ↦ f x + c * (x - 1)) μ ν = fDiv f μ ν := by
  by_cases hf : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν
  · rw [fDiv_add_linear' hc hf, h_eq, ← EReal.coe_sub, sub_self]
    simp
  · rw [fDiv_of_not_integrable hf,fDiv_of_not_integrable]
    refine fun h_int ↦ hf ?_
    have : (fun x ↦ f ((∂μ/∂ν) x).toReal)
        = fun x ↦ (f ((∂μ/∂ν) x).toReal + c * (((∂μ/∂ν) x).toReal - 1))
          - c * (((∂μ/∂ν) x).toReal - 1) := by
      ext x
      simp
    rw [this]
    exact h_int.add ((Measure.integrable_toReal_rnDeriv.sub (integrable_const _)).const_mul c).neg

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

lemma fDiv_lt_top_of_ac [SigmaFinite μ] [SigmaFinite ν] (h : μ ≪ ν)
    (h_int : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν) :
    fDiv f μ ν < ⊤ := by
  classical
  rw [fDiv_of_absolutelyContinuous h, if_pos h_int]
  simp

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

lemma fDiv_lt_top_of_derivAtTop_ne_top [IsFiniteMeasure μ] [SigmaFinite ν]
    (hf : derivAtTop f ≠ ⊤) (h_int : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν) :
    fDiv f μ ν < ⊤ := by
  rw [fDiv_of_integrable h_int]
  refine EReal.add_lt_top ?_ ?_
  · simp
  · have : μ.singularPart ν Set.univ < (⊤ : EReal) := by
      rw [← EReal.coe_ennreal_top]
      norm_cast
      exact measure_lt_top _ _
    rw [ne_eq, EReal.mul_eq_top]
    simp only [derivAtTop_ne_bot, false_and, EReal.coe_ennreal_ne_bot, and_false, hf,
      EReal.coe_ennreal_pos, Measure.measure_univ_pos, ne_eq, EReal.coe_ennreal_eq_top_iff,
      false_or, not_and]
    exact fun _ ↦ measure_ne_top _ _

lemma fDiv_lt_top_iff_of_derivAtTop_ne_top [IsFiniteMeasure μ] [SigmaFinite ν]
    (hf : derivAtTop f ≠ ⊤) :
    fDiv f μ ν < ⊤ ↔ Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν := by
  refine ⟨fun h ↦ ?_, fDiv_lt_top_of_derivAtTop_ne_top hf⟩
  by_contra h_not_int
  rw [fDiv_of_not_integrable h_not_int] at h
  simp at h

lemma fDiv_ne_top_iff_of_derivAtTop_ne_top [IsFiniteMeasure μ] [SigmaFinite ν]
    (hf : derivAtTop f ≠ ⊤) :
    fDiv f μ ν ≠ ⊤ ↔ Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν := by
  rw [← fDiv_lt_top_iff_of_derivAtTop_ne_top hf, lt_top_iff_ne_top]

lemma fDiv_eq_top_iff_of_derivAtTop_ne_top [IsFiniteMeasure μ] [SigmaFinite ν]
    (hf : derivAtTop f ≠ ⊤) :
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

/-
-- todo: extend beyond μ ≪ ν
lemma le_fDiv [IsFiniteMeasure μ] [IsProbabilityMeasure ν]
    (hf_cvx : ConvexOn ℝ (Set.Ici 0) f) (hf_cont : ContinuousOn f (Set.Ici 0))
    (hf_int : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν) (hμν : μ ≪ ν) :
    f (μ Set.univ).toReal ≤ fDiv f μ ν := by
  classical
  rw [fDiv_of_absolutelyContinuous hμν, if_pos hf_int]
  calc f (μ Set.univ).toReal
    = f (∫ x, ((∂μ/∂ν) x).toReal ∂ν) := by rw [Measure.integral_toReal_rnDeriv hμν]
  _ ≤ ∫ x, f ((∂μ/∂ν) x).toReal ∂ν := by
    rw [← average_eq_integral, ← average_eq_integral]
    exact ConvexOn.map_average_le hf_cvx hf_cont isClosed_Ici (by simp)
      Measure.integrable_toReal_rnDeriv hf_int
  _ = ∫ x, f ((∂μ/∂ν) x).toReal ∂ν := rfl

lemma fDiv_nonneg [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hf_cvx : ConvexOn ℝ (Set.Ici 0) f) (hf_cont : ContinuousOn f (Set.Ici 0)) (hf_one : f 1 = 0)
    (hf_int : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν) (hμν : μ ≪ ν) :
    0 ≤ fDiv f μ ν :=
  calc 0 = f (μ Set.univ).toReal := by simp [hf_one]
  _ ≤ ∫ x, f ((∂μ/∂ν) x).toReal ∂ν := le_fDiv hf_cvx hf_cont hf_int hμν
-/

section Conditional

open Classical in
/- Conditinal f-divergence. -/
noncomputable
def condFDivReal (f : ℝ → ℝ) (κ η : kernel α β) (μ : Measure α) : EReal :=
  if (∀ᵐ a ∂μ, fDiv f (κ a) (η a) ≠ ⊤)
    ∧ (Integrable (fun x ↦ (fDiv f (κ x) (η x)).toReal) μ)
  then ((μ[fun x ↦ (fDiv f (κ x) (η x)).toReal] : ℝ) : EReal)
  else ⊤

lemma condFDivReal_of_not_ae_finite (hf : ¬ ∀ᵐ a ∂μ, fDiv f (κ a) (η a) ≠ ⊤) :
    condFDivReal f κ η μ = ⊤ := by
  rw [condFDivReal, if_neg]
  push_neg
  exact fun h ↦ absurd h hf

lemma condFDivReal_of_not_integrable
    (hf : ¬ Integrable (fun x ↦ (fDiv f (κ x) (η x)).toReal) μ) :
    condFDivReal f κ η μ = ⊤ := by
  rw [condFDivReal, if_neg]
  push_neg
  exact fun _ ↦ hf

lemma condFDivReal_eq (hf_ae : ∀ᵐ a ∂μ, fDiv f (κ a) (η a) ≠ ⊤)
    (hf : Integrable (fun x ↦ (fDiv f (κ x) (η x)).toReal) μ) :
    condFDivReal f κ η μ = ((μ[fun x ↦ (fDiv f (κ x) (η x)).toReal] : ℝ) : EReal) :=
  if_pos ⟨hf_ae, hf⟩

variable [MeasurableSpace.CountablyGenerated β]

section Integrable

/-! We show that the integrability of the functions used in `fDiv f (μ ⊗ₘ κ) (μ ⊗ₘ η)`
and in `condFDivReal f κ η μ` are equivalent. -/

-- todo find better name
theorem _root_.MeasureTheory.Integrable.compProd_mk_left_ae' [NormedAddCommGroup E]
    [IsFiniteMeasure μ] [IsSFiniteKernel κ] ⦃f : α × β → E⦄
    (hf : Integrable f (μ ⊗ₘ κ)) :
    ∀ᵐ x ∂μ, Integrable (fun y ↦ f (x, y)) (κ x) :=
  hf.compProd_mk_left_ae

theorem _root_.MeasureTheory.Integrable.integral_norm_compProd' [NormedAddCommGroup E]
    [IsFiniteMeasure μ] [IsSFiniteKernel κ] ⦃f : α × β → E⦄
    (hf : Integrable f (μ ⊗ₘ κ)) :
    Integrable (fun x ↦ ∫ y, ‖f (x, y)‖ ∂(κ x)) μ :=
  hf.integral_norm_compProd

theorem _root_.MeasureTheory.Integrable.integral_compProd' [NormedAddCommGroup E]
    [IsFiniteMeasure μ] [IsSFiniteKernel κ] ⦃f : α × β → E⦄ [NormedSpace ℝ E] [CompleteSpace E]
    (hf : Integrable f (μ ⊗ₘ κ)) :
    Integrable (fun x ↦ ∫ y, f (x, y) ∂(κ x)) μ :=
  hf.integral_compProd

lemma f_compProd_congr (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ η : kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η] :
    ∀ᵐ a ∂ν, (fun b ↦ f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) (a, b)).toReal)
      =ᵐ[η a] fun b ↦ f ((∂μ/∂ν) a * (∂κ a/∂η a) b).toReal := by
  have h_eq_compProd := kernel.rnDeriv_measure_compProd' μ ν κ η
  filter_upwards [h_eq_compProd] with a ha
  filter_upwards [ha] with b hb
  rw [hb]

lemma integral_f_compProd_congr (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ η : kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η] :
    (fun a ↦ ∫ b, f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) (a, b)).toReal ∂(η a))
      =ᵐ[ν] fun a ↦ ∫ b, f ((∂μ/∂ν) a * (∂κ a/∂η a) b).toReal ∂(η a) := by
  filter_upwards [f_compProd_congr μ ν κ η] with a ha using integral_congr_ae ha

lemma integral_f_compProd_right_congr (μ : Measure α) [IsFiniteMeasure μ]
    (κ η : kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η] :
    (fun a ↦ ∫ b, f ((∂μ ⊗ₘ κ/∂μ ⊗ₘ η) (a, b)).toReal ∂(η a))
      =ᵐ[μ] fun a ↦ ∫ b, f ((∂κ a/∂η a) b).toReal ∂(η a) := by
  filter_upwards [integral_f_compProd_congr μ μ κ η, Measure.rnDeriv_self μ] with a ha h_eq_one
  rw [ha]
  simp_rw [h_eq_one, one_mul]

lemma integral_f_compProd_left_congr (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ : kernel α β) [IsFiniteKernel κ]  :
    (fun a ↦ ∫ b, f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ κ) (a, b)).toReal ∂(κ a))
      =ᵐ[ν] fun a ↦ (κ a Set.univ).toReal * f ((∂μ/∂ν) a).toReal := by
  filter_upwards [integral_f_compProd_congr (f := f) μ ν κ κ] with a ha
  have h_one := (κ a).rnDeriv_self
  rw [ha, ← smul_eq_mul,  ← integral_const]
  refine integral_congr_ae ?_
  filter_upwards [h_one] with b hb
  simp [hb]

lemma integrable_f_rnDeriv_of_integrable_compProd [IsFiniteMeasure μ] [IsFiniteKernel κ]
    [IsFiniteKernel η] (hf : StronglyMeasurable f)
    (hf_int : Integrable (fun x ↦ f ((μ ⊗ₘ κ).rnDeriv (μ ⊗ₘ η) x).toReal) (μ ⊗ₘ η)) :
    ∀ᵐ a ∂μ, Integrable (fun x ↦ f ((κ a).rnDeriv (η a) x).toReal) (η a) := by
  have h := hf_int.integral_compProd'
  rw [Measure.integrable_compProd_iff] at hf_int
  swap
  · exact (hf.comp_measurable (Measure.measurable_rnDeriv _ _).ennreal_toReal).aestronglyMeasurable
  have h := kernel.rnDeriv_measure_compProd_right' μ κ η
  filter_upwards [h, hf_int.1] with a ha1 ha2
  refine (integrable_congr ?_).mp ha2
  filter_upwards [ha1] with b hb
  rw [hb]

lemma integrable_f_rnDeriv_compProd_iff [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [IsFiniteKernel κ] [IsFiniteKernel η] (hf : StronglyMeasurable f)
    (h_cvx : ConvexOn ℝ (Set.Ici 0) f) :
    Integrable (fun x ↦ f ((μ ⊗ₘ κ).rnDeriv (ν ⊗ₘ η) x).toReal) (ν ⊗ₘ η)
      ↔ (∀ᵐ a ∂ν, Integrable (fun x ↦ f ((∂μ/∂ν) a * (∂κ a/∂η a) x).toReal) (η a))
        ∧ Integrable (fun a ↦ ∫ b, f ((∂μ/∂ν) a * (∂κ a/∂η a) b).toReal ∂(η a)) ν := by
  have h_ae_eq : ∀ᵐ a ∂ν, (fun y ↦ f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) (a, y)).toReal)
      =ᵐ[η a] fun x ↦ f ((∂μ/∂ν) a * (∂κ a/∂η a) x).toReal := f_compProd_congr μ ν κ η
  refine ⟨fun h ↦ ?_, fun ⟨h1, h2⟩ ↦ ?_⟩
  · have h_int := h.integral_compProd'
    rw [Measure.integrable_compProd_iff] at h
    swap
    · exact (hf.comp_measurable
        (Measure.measurable_rnDeriv _ _).ennreal_toReal).aestronglyMeasurable
    constructor
    · filter_upwards [h.1, h_ae_eq] with a ha1 ha2
      exact (integrable_congr ha2).mp ha1
    · refine (integrable_congr ?_).mp h_int
      filter_upwards [h_ae_eq] with a ha
      exact integral_congr_ae ha
  · rw [Measure.integrable_compProd_iff]
    swap
    · exact (hf.comp_measurable
        (Measure.measurable_rnDeriv _ _).ennreal_toReal).aestronglyMeasurable
    constructor
    · filter_upwards [h1, h_ae_eq] with a ha1 ha2
      exact (integrable_congr ha2).mpr ha1
    · rw [← integrable_congr (integral_f_compProd_congr μ ν κ η)] at h2
      -- todo: cut into two parts, depending on sign of f.
      -- on the positive part, use h2.
      -- on the negative part, use `f x ≥ a * x + b` by convexity, then since both measures are
      -- finite the integral is finite.
      sorry

lemma fDiv_compProd_ne_top_iff [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [IsMarkovKernel κ] [IsFiniteKernel η] (hf : StronglyMeasurable f)
    (h_cvx : ConvexOn ℝ (Set.Ici 0) f) :
  fDiv f (μ ⊗ₘ κ) (ν ⊗ₘ η) ≠ ⊤ ↔
    (∀ᵐ a ∂ν, Integrable (fun x ↦ f ((∂μ/∂ν) a * (∂κ a/∂η a) x).toReal) (η a))
      ∧ Integrable (fun a ↦ ∫ b, f ((∂μ/∂ν) a * (∂κ a/∂η a) b).toReal ∂(η a)) ν
      ∧ (derivAtTop f = ⊤ → μ ≪ ν ∧ ∀ᵐ a ∂μ, κ a ≪ η a) := by
  rw [fDiv_ne_top_iff, integrable_f_rnDeriv_compProd_iff hf h_cvx,
    kernel.Measure.absolutelyContinuous_compProd_iff, and_assoc]

lemma fDiv_compProd_eq_top_iff [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [IsMarkovKernel κ] [IsFiniteKernel η] (hf : StronglyMeasurable f)
    (h_cvx : ConvexOn ℝ (Set.Ici 0) f) :
    fDiv f (μ ⊗ₘ κ) (ν ⊗ₘ η) = ⊤ ↔
    (∀ᵐ a ∂ν, Integrable (fun x ↦ f ((∂μ/∂ν) a * (∂κ a/∂η a) x).toReal) (η a)) →
      Integrable (fun a ↦ ∫ b, f ((∂μ/∂ν) a * (∂κ a/∂η a) b).toReal ∂η a) ν →
      derivAtTop f = ⊤ ∧ (μ ≪ ν → ¬∀ᵐ a ∂μ, κ a ≪ η a) := by
  rw [← not_iff_not, ← ne_eq, fDiv_compProd_ne_top_iff hf h_cvx]
  push_neg
  rfl

lemma fDiv_compProd_right_ne_top_iff [IsFiniteMeasure μ]
    [IsMarkovKernel κ] [IsFiniteKernel η] (hf : StronglyMeasurable f)
    (h_cvx : ConvexOn ℝ (Set.Ici 0) f) :
  fDiv f (μ ⊗ₘ κ) (μ ⊗ₘ η) ≠ ⊤ ↔
    (∀ᵐ a ∂μ, Integrable (fun x ↦ f ((∂κ a/∂η a) x).toReal) (η a))
      ∧ Integrable (fun a ↦ ∫ b, f ((∂κ a/∂η a) b).toReal ∂(η a)) μ
      ∧ (derivAtTop f = ⊤ → ∀ᵐ a ∂μ, κ a ≪ η a) := by
  rw [fDiv_compProd_ne_top_iff hf h_cvx]
  have h_self := μ.rnDeriv_self
  refine ⟨fun h ↦ ⟨?_, ?_, ?_⟩, fun h ↦ ⟨?_, ?_, ?_⟩⟩
  · filter_upwards [h_self, h.1] with a ha1 ha2
    simp_rw [ha1, one_mul] at ha2
    exact ha2
  · refine (integrable_congr ?_).mp h.2.1
    filter_upwards [h_self] with a ha1
    simp_rw [ha1, one_mul]
  · simp only [Measure.AbsolutelyContinuous.rfl, true_and] at h
    exact h.2.2
  · filter_upwards [h_self, h.1] with a ha1 ha2
    simp_rw [ha1, one_mul]
    exact ha2
  · refine (integrable_congr ?_).mp h.2.1
    filter_upwards [h_self] with a ha1
    simp_rw [ha1, one_mul]
  · simp only [Measure.AbsolutelyContinuous.rfl, true_and]
    exact h.2.2

lemma fDiv_compProd_right_eq_top_iff [IsFiniteMeasure μ]
    [IsMarkovKernel κ] [IsFiniteKernel η] (hf : StronglyMeasurable f)
    (h_cvx : ConvexOn ℝ (Set.Ici 0) f) :
    fDiv f (μ ⊗ₘ κ) (μ ⊗ₘ η) = ⊤ ↔
    (∀ᵐ a ∂μ, Integrable (fun x ↦ f ((∂κ a/∂η a) x).toReal) (η a)) →
      Integrable (fun a ↦ ∫ b, f ((∂κ a/∂η a) b).toReal ∂η a) μ →
      derivAtTop f = ⊤ ∧ ¬∀ᵐ a ∂μ, κ a ≪ η a := by
  rw [← not_iff_not, ← ne_eq, fDiv_compProd_right_ne_top_iff hf h_cvx]
  push_neg
  rfl

lemma fDiv_compProd_left_ne_top_iff [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [IsMarkovKernel κ] (hf : StronglyMeasurable f) (h_cvx : ConvexOn ℝ (Set.Ici 0) f) :
  fDiv f (μ ⊗ₘ κ) (ν ⊗ₘ κ) ≠ ⊤ ↔
    Integrable (fun a ↦ f ((∂μ/∂ν) a).toReal) ν ∧ (derivAtTop f = ⊤ → μ ≪ ν) := by
  rw [fDiv_compProd_ne_top_iff hf h_cvx]
  have h_one : ∀ a, ∂(κ a)/∂(κ a) =ᵐ[κ a] 1 := fun a ↦ Measure.rnDeriv_self (κ a)
  simp only [ENNReal.toReal_mul, Measure.AbsolutelyContinuous.rfl, eventually_true, and_true]
  have : ∀ a, ∫ b, f (((∂μ/∂ν) a).toReal * ((∂κ a/∂κ a) b).toReal) ∂κ a
        = ∫ _, f (((∂μ/∂ν) a).toReal) ∂κ a := by
      refine fun a ↦ integral_congr_ae ?_
      filter_upwards [h_one a] with b hb
      simp [hb]
  refine ⟨fun ⟨_, h2, h3⟩ ↦ ⟨?_, h3⟩, fun ⟨h1, h2⟩ ↦ ⟨?_, ?_, h2⟩⟩
  · refine (integrable_congr ?_).mpr h2
    refine ae_of_all _ (fun a ↦ ?_)
    simp only
    simp [this]
  · refine ae_of_all _ (fun a ↦ ?_)
    have : (fun x ↦ f (((∂μ/∂ν) a).toReal * ((∂κ a/∂κ a) x).toReal))
        =ᵐ[κ a] (fun _ ↦ f ((∂μ/∂ν) a).toReal) := by
      filter_upwards [h_one a] with b hb
      simp [hb]
    rw [integrable_congr this]
    simp
  · simp only [this, integral_const, measure_univ, ENNReal.one_toReal, smul_eq_mul, one_mul]
    exact h1

lemma fDiv_compProd_left_eq_top_iff [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [IsMarkovKernel κ] (hf : StronglyMeasurable f) (h_cvx : ConvexOn ℝ (Set.Ici 0) f) :
  fDiv f (μ ⊗ₘ κ) (ν ⊗ₘ κ) = ⊤ ↔
    Integrable (fun a ↦ f ((∂μ/∂ν) a).toReal) ν → (derivAtTop f = ⊤ ∧ ¬ μ ≪ ν) := by
  rw [← not_iff_not, ← ne_eq, fDiv_compProd_left_ne_top_iff hf h_cvx]
  push_neg
  rfl

lemma integrable_singularPart [IsFiniteMeasure μ]
    [IsFiniteKernel κ] [IsFiniteKernel η] :
    Integrable (fun x ↦ ((κ x).singularPart (η x) Set.univ).toReal) μ := by
  refine integrable_toReal_of_lintegral_ne_top ?_ (ne_of_lt ?_)
  · simp_rw [← kernel.singularPart_eq_singularPart_measure]
    exact (kernel.measurable_coe _ MeasurableSet.univ).aemeasurable
  calc ∫⁻ x, (κ x).singularPart (η x) Set.univ ∂μ
  _ ≤ ∫⁻ x, κ x Set.univ ∂μ := by
        refine lintegral_mono (fun x ↦ ?_)
        exact Measure.singularPart_le _ _ _
  _ = (μ ⊗ₘ κ) Set.univ := by
        rw [← Set.univ_prod_univ, Measure.compProd_apply_prod MeasurableSet.univ MeasurableSet.univ,
          set_lintegral_univ]
  _ < ⊤ := measure_lt_top _ _

lemma integrable_fDiv_iff [IsFiniteMeasure μ] [IsFiniteKernel κ] [IsFiniteKernel η]
    (h_fin : ∀ᵐ a ∂μ, fDiv f (κ a) (η a) ≠ ⊤) :
    Integrable (fun x ↦ EReal.toReal (fDiv f (κ x) (η x))) μ
      ↔ Integrable (fun a ↦ ∫ b, f ((∂κ a/∂η a) b).toReal ∂η a) μ := by
  by_cases h_top : derivAtTop f = ⊤
  · classical
    simp_rw [fDiv_of_derivAtTop_eq_top h_top]
    simp only [fDiv_ne_top_iff, h_top, forall_true_left] at h_fin
    refine integrable_congr ?_
    filter_upwards [h_fin] with a ha
    rw [if_pos ha, EReal.toReal_coe]
  · have h_fin' := h_fin
    simp_rw [fDiv_ne_top_iff_of_derivAtTop_ne_top h_top] at h_fin
    have : (fun x ↦ (fDiv f (κ x) (η x)).toReal)
        =ᵐ[μ] (fun x ↦ ∫ y, f ((∂κ x/∂η x) y).toReal ∂(η x)
          + (derivAtTop f).toReal * ((κ x).singularPart (η x) Set.univ).toReal) := by
      filter_upwards [h_fin'] with x hx1
      rw [fDiv_of_ne_top hx1, EReal.toReal_add]
      · simp only [EReal.toReal_coe, add_right_inj]
        rw [EReal.toReal_mul]
        simp
      · simp
      · simp
      · simp [h_top, EReal.mul_eq_top, derivAtTop_ne_bot, measure_ne_top]
      · simp [EReal.mul_eq_bot, derivAtTop_ne_bot, h_top, measure_ne_top]
    rw [integrable_congr this]
    have h_int : Integrable (fun x ↦ (derivAtTop f).toReal
        * ((κ x).singularPart (η x) Set.univ).toReal) μ := by
      refine Integrable.const_mul ?_ (derivAtTop f).toReal
      exact integrable_singularPart
    refine ⟨fun h ↦ ?_, fun h ↦ h.add h_int⟩
    have : (fun x ↦ ∫ y, f ((∂κ x/∂η x) y).toReal ∂η x)
        = (fun x ↦ (∫ y, f ((∂κ x/∂η x) y).toReal ∂η x +
          (derivAtTop f).toReal * ((κ x).singularPart (η x) Set.univ).toReal)
          - (derivAtTop f).toReal * ((κ x).singularPart (η x) Set.univ).toReal) := by
      ext; simp
    rw [this]
    exact h.sub h_int

lemma condFDivReal_ne_top_iff [IsFiniteMeasure μ] [IsMarkovKernel κ] [IsFiniteKernel η] :
  condFDivReal f κ η μ ≠ ⊤ ↔
    (∀ᵐ a ∂μ, Integrable (fun x ↦ f ((∂κ a/∂η a) x).toReal) (η a))
      ∧ Integrable (fun a ↦ ∫ b, f ((∂κ a/∂η a) b).toReal ∂(η a)) μ
      ∧ (derivAtTop f = ⊤ → ∀ᵐ a ∂μ, κ a ≪ η a) := by
  rw [condFDivReal]
  split_ifs with h
  · have h' := h
    simp_rw [fDiv_ne_top_iff] at h
    simp only [ne_eq, EReal.coe_ne_top, not_false_eq_true, true_iff]
    refine ⟨?_, ?_, ?_⟩
    · filter_upwards [h.1] with a ha
      exact ha.1
    · have h_int := h.2
      rwa [integrable_fDiv_iff h'.1] at h_int
    · intro h_top
      filter_upwards [h.1] with a ha
      exact ha.2 h_top
  · simp only [ne_eq, not_true_eq_false, false_iff, not_and, not_forall, not_eventually,
      exists_prop]
    push_neg at h
    intro hf_int h_int
    simp_rw [fDiv_ne_top_iff] at h
    by_contra h_contra
    simp only [not_and, not_frequently, not_not] at h_contra
    rw [eventually_and] at h
    simp only [hf_int, eventually_all, true_and] at h
    specialize h h_contra
    have h_top : ∀ᵐ a ∂μ, fDiv f (κ a) (η a) ≠ ⊤ := by
      simp only [ne_eq, fDiv_ne_top_iff, eventually_and, eventually_all]
      exact ⟨hf_int, h_contra⟩
    rw [integrable_fDiv_iff h_top] at h
    exact h h_int

lemma condFDivReal_ne_top_iff_fDiv_compProd_ne_top [IsFiniteMeasure μ]
    [IsMarkovKernel κ] [IsFiniteKernel η] (hf : StronglyMeasurable f)
    (h_cvx : ConvexOn ℝ (Set.Ici 0) f) :
    condFDivReal f κ η μ ≠ ⊤ ↔ fDiv f (μ ⊗ₘ κ) (μ ⊗ₘ η) ≠ ⊤ := by
  rw [condFDivReal_ne_top_iff, fDiv_compProd_right_ne_top_iff hf h_cvx]

lemma condFDivReal_eq_top_iff_fDiv_compProd_eq_top [IsFiniteMeasure μ]
    [IsMarkovKernel κ] [IsFiniteKernel η] (hf : StronglyMeasurable f)
    (h_cvx : ConvexOn ℝ (Set.Ici 0) f) :
    condFDivReal f κ η μ = ⊤ ↔ fDiv f (μ ⊗ₘ κ) (μ ⊗ₘ η) = ⊤ := by
  rw [← not_iff_not]
  exact condFDivReal_ne_top_iff_fDiv_compProd_ne_top hf h_cvx

lemma condFDivReal_eq_add [IsFiniteMeasure μ]
    [IsFiniteKernel κ] [IsFiniteKernel η] (hf_ae : ∀ᵐ a ∂μ, fDiv f (κ a) (η a) ≠ ⊤)
    (hf : Integrable (fun x ↦ (fDiv f (κ x) (η x)).toReal) μ) :
    condFDivReal f κ η μ = (μ[fun a ↦ ∫ y, f ((∂κ a/∂η a) y).toReal ∂η a] : ℝ)
      + (derivAtTop f).toReal * (μ[fun a ↦ ((κ a).singularPart (η a) Set.univ).toReal] : ℝ) := by
  rw [condFDivReal_eq hf_ae hf]
  have : (fun x ↦ EReal.toReal (fDiv f (κ x) (η x)))
      =ᵐ[μ] fun x ↦ ∫ y, f ((∂(κ x)/∂(η x)) y).toReal ∂(η x)
        + (derivAtTop f * (κ x).singularPart (η x) Set.univ).toReal := by
    filter_upwards [hf_ae] with x hx
    rw [fDiv_of_ne_top hx, EReal.toReal_add]
    rotate_left
    · simp
    · simp
    · simp only [ne_eq, EReal.mul_eq_top, derivAtTop_ne_bot, false_and, EReal.coe_ennreal_ne_bot,
        and_false, EReal.coe_ennreal_pos, Measure.measure_univ_pos, EReal.coe_ennreal_eq_top_iff,
        measure_ne_top, or_false, false_or, not_and, not_not]
      intro h_top
      rw [fDiv_ne_top_iff] at hx
      simp [h_top, Measure.singularPart_eq_zero_of_ac (hx.2 h_top)]
    · simp only [ne_eq, EReal.mul_eq_bot, derivAtTop_ne_bot, EReal.coe_ennreal_pos,
        Measure.measure_univ_pos, false_and, EReal.coe_ennreal_ne_bot, and_false,
        EReal.coe_ennreal_eq_top_iff, measure_ne_top, or_false, false_or, not_and, not_lt]
      exact fun _ ↦ EReal.coe_ennreal_nonneg _
    rfl
  rw [integral_congr_ae this]
  rw [integral_add]
  rotate_left
  · rwa [integrable_fDiv_iff hf_ae] at hf
  · simp_rw [EReal.toReal_mul]
    convert (integrable_singularPart (κ := κ) (η := η) (μ := μ)).const_mul (derivAtTop f).toReal
    rw [← EReal.coe_ennreal_toReal, EReal.toReal_coe]
    exact measure_ne_top _ _
  simp only [EReal.coe_add, EReal.toReal_mul]
  rw [integral_mul_left]
  simp only [_root_.EReal.toReal_coe_ennreal, EReal.coe_mul]

lemma condFDivReal_of_derivAtTop_eq_top [IsFiniteMeasure μ]
    [IsFiniteKernel κ] [IsFiniteKernel η] (hf_ae : ∀ᵐ a ∂μ, fDiv f (κ a) (η a) ≠ ⊤)
    (hf : Integrable (fun x ↦ (fDiv f (κ x) (η x)).toReal) μ) (h_top : derivAtTop f = ⊤):
    condFDivReal f κ η μ = (μ[fun a ↦ ∫ y, f ((∂κ a/∂η a) y).toReal ∂η a] : ℝ) := by
  rw [condFDivReal_eq_add hf_ae hf]
  simp [h_top]

end Integrable

lemma fDiv_compProd_left (μ : Measure α) [IsFiniteMeasure μ]
    (κ η : kernel α β) [IsMarkovKernel κ] [IsFiniteKernel η] (hf : StronglyMeasurable f)
    (h_cvx : ConvexOn ℝ (Set.Ici 0) f) :
    fDiv f (μ ⊗ₘ κ) (μ ⊗ₘ η) = condFDivReal f κ η μ := by
  by_cases hf_top : condFDivReal f κ η μ = ⊤
  · rwa [hf_top, ← condFDivReal_eq_top_iff_fDiv_compProd_eq_top hf h_cvx]
  have hf_top' := hf_top
  have hf_top'' := hf_top
  have hf_top''' := hf_top
  rw [← ne_eq, condFDivReal_ne_top_iff] at hf_top'
  rw [condFDivReal_eq_top_iff_fDiv_compProd_eq_top hf h_cvx, ← ne_eq, fDiv_ne_top_iff]
    at hf_top''
  rw [condFDivReal_eq_top_iff_fDiv_compProd_eq_top hf h_cvx] at hf_top'''
  rcases hf_top' with ⟨h1, h2, h3⟩
  rcases hf_top'' with ⟨h4, h5⟩
  classical
  by_cases h_deriv : derivAtTop f = ⊤
  · rw [fDiv_of_derivAtTop_eq_top h_deriv, if_pos ⟨h4, h5 h_deriv⟩,
      condFDivReal_of_derivAtTop_eq_top _ _ h_deriv]
    sorry
    sorry
    sorry
  · rw [fDiv_of_ne_top, condFDivReal_eq_add]
    rotate_left
    · sorry
    · sorry
    · exact hf_top'''
    congr
    · sorry
    · rw [EReal.coe_toReal h_deriv derivAtTop_ne_bot]
    · -- extract lemma
      sorry

end Conditional

lemma fDiv_compProd_right [MeasurableSpace.CountablyGenerated β]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ : kernel α β) [IsMarkovKernel κ] (hf : StronglyMeasurable f)
    (h_cvx : ConvexOn ℝ (Set.Ici 0) f) :
    fDiv f (μ ⊗ₘ κ) (ν ⊗ₘ κ) = fDiv f μ ν := by
  by_cases h_top : fDiv f (μ ⊗ₘ κ) (ν ⊗ₘ κ) = ⊤
  · symm
    rw [h_top, fDiv_eq_top_iff]
    have h_top' := (fDiv_compProd_left_eq_top_iff hf h_cvx).mp h_top
    by_cases h : Integrable (fun a ↦ f ((∂μ/∂ν) a).toReal) ν
    · exact Or.inr (h_top' h)
    · exact Or.inl h
  · have h_top' := (fDiv_compProd_left_ne_top_iff hf h_cvx).mp h_top
    have h_top'' : fDiv f μ ν ≠ ⊤ := by rwa [fDiv_ne_top_iff]
    rw [fDiv_of_ne_top h_top, fDiv_of_ne_top h_top'']
    have h := integral_f_compProd_left_congr μ ν κ (f := f)
    simp only [measure_univ, ENNReal.one_toReal, one_mul] at h
    rw [integral_congr_ae h.symm, Measure.integral_compProd]
    · congr
      sorry  -- extract lemma
    · sorry

lemma f_rnDeriv_ae_le_integral [MeasurableSpace.CountablyGenerated β]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ η : kernel α β) [IsFiniteKernel κ] [IsMarkovKernel η]
    (hf_cvx : ConvexOn ℝ (Set.Ici 0) f) (hf_cont : ContinuousOn f (Set.Ici 0))
    (h_int : Integrable (fun p ↦ f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) p).toReal) (ν ⊗ₘ η))
    (hκη : ∀ᵐ a ∂ν, κ a ≪ η a) :
    (fun a ↦ f ((∂μ/∂ν) a * κ a Set.univ).toReal)
      ≤ᵐ[ν] fun a ↦ ∫ b, f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) (a, b)).toReal ∂(η a) := by
  have h_compProd := kernel.rnDeriv_measure_compProd' μ ν κ η
  have h_lt_top := Measure.ae_ae_of_ae_compProd <| Measure.rnDeriv_lt_top (μ ⊗ₘ κ) (ν ⊗ₘ η)
  have := Measure.integrable_toReal_rnDeriv (μ := μ ⊗ₘ κ) (ν := ν ⊗ₘ η)
  rw [Measure.integrable_compProd_iff] at this
  swap
  · refine (Measurable.stronglyMeasurable ?_).aestronglyMeasurable
    exact (Measure.measurable_rnDeriv _ _).ennreal_toReal
  filter_upwards [hκη, h_compProd, h_lt_top, h_int.compProd_mk_left_ae', this.1]
    with a h_ac h_eq h_lt_top h_int' h_rnDeriv_int
  calc f ((∂μ/∂ν) a * κ a Set.univ).toReal
    = f ((∂μ/∂ν) a * ∫⁻ b, (∂κ a/∂η a) b ∂η a).toReal := by rw [Measure.lintegral_rnDeriv h_ac]
  _ = f (∫⁻ b,(∂μ/∂ν) a * (∂κ a/∂η a) b ∂η a).toReal := by
        rw [lintegral_const_mul _ (Measure.measurable_rnDeriv _ _)]
  _ = f (∫⁻ b, (∂μ ⊗ₘ κ/∂ν ⊗ₘ η) (a, b) ∂η a).toReal := by rw [lintegral_congr_ae h_eq]
  _ = f (∫ b, ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) (a, b)).toReal ∂η a) := by
        rw [integral_toReal _ h_lt_top]
        exact ((Measure.measurable_rnDeriv _ _).comp measurable_prod_mk_left).aemeasurable
  _ ≤ ∫ b, f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) (a, b)).toReal ∂η a := by
        rw [← average_eq_integral, ← average_eq_integral]
        exact ConvexOn.map_average_le hf_cvx hf_cont isClosed_Ici (by simp) h_rnDeriv_int h_int'

lemma le_fDiv_compProd [MeasurableSpace.CountablyGenerated β]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ η : kernel α β) [IsMarkovKernel κ] [IsMarkovKernel η]
    (hf_cvx : ConvexOn ℝ (Set.Ici 0) f) (hf_cont : ContinuousOn f (Set.Ici 0))
    (h_int : Integrable (fun p ↦ f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) p).toReal) (ν ⊗ₘ η))
    (h_int_meas : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν) :
    fDiv f μ ν ≤ fDiv f (μ ⊗ₘ κ) (ν ⊗ₘ η) := by
  let κ' := kernel.withDensity η (kernel.rnDeriv κ η)
  have h : ∀ a, f ((∂μ/∂ν) a).toReal
      ≤ f ((∂μ/∂ν) a * κ' a Set.univ).toReal
        + (derivAtTop f).toReal * ((∂μ/∂ν) a).toReal
          * (kernel.singularPart κ η a Set.univ).toReal := by
    sorry
  sorry

end ProbabilityTheory
