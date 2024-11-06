/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
import Mathlib.Analysis.Convex.Integral
import Mathlib.Probability.Notation
import TestingLowerBounds.FDiv.DivFunction.OfReal
import TestingLowerBounds.ForMathlib.RadonNikodym

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

open Real MeasureTheory Filter Set MeasurableSpace

open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

variable {α β : Type*} {m mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {μ ν : Measure α} {f g : DivFunction}

open Classical in
/-- f-Divergence of two measures. -/
noncomputable
def fDiv (f : DivFunction) (μ ν : Measure α) : ℝ≥0∞ :=
  ∫⁻ x, f ((∂μ/∂ν) x) ∂ν + f.derivAtTop * μ.singularPart ν .univ

-- todo: useless lemma?
lemma fDiv_of_lintegral_eq_top (hf : ∫⁻ x, f ((∂μ/∂ν) x) ∂ν = ∞) :
     fDiv f μ ν = ∞ := by simp [fDiv, hf]

-- lemma fDiv_of_integrable (hf : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν) :
--     fDiv f μ ν = ∫ x, f ((∂μ/∂ν) x).toReal ∂ν + derivAtTop f * μ.singularPart ν .univ :=
--   if_neg (not_not.mpr hf)

-- lemma fDiv_ne_bot [IsFiniteMeasure μ] (hf_cvx : ConvexOn ℝ (Ici 0) f) : fDiv f μ ν ≠ ⊥ := by
--   rw [fDiv]
--   split_ifs with h
--   · simp only [ne_eq, EReal.add_eq_bot_iff, EReal.coe_ne_bot, false_or]
--     rw [EReal.mul_eq_bot]
--     simp [hf_cvx.derivAtTop_ne_bot, not_lt.mpr (EReal.coe_ennreal_nonneg _), measure_ne_top]
--   · simp

-- lemma fDiv_ne_bot_of_derivAtTop_nonneg (hf : 0 ≤ derivAtTop f) : fDiv f μ ν ≠ ⊥ := by
--   rw [fDiv]
--   split_ifs with h
--   · simp only [ne_eq, EReal.add_eq_bot_iff, EReal.coe_ne_bot, false_or]
--     rw [EReal.mul_eq_bot]
--     have h_ne_bot : derivAtTop f ≠ ⊥ := fun h_eq ↦ by
--       rw [h_eq] at hf
--       simp at hf
--     simp [h_ne_bot, not_lt.mpr (EReal.coe_ennreal_nonneg _), not_lt.mpr hf]
--   · simp

section SimpleValues

@[simp] lemma fDiv_zero (μ ν : Measure α) : fDiv 0 μ ν = 0 := by simp [fDiv]

@[simp]
lemma fDiv_zero_measure_left (ν : Measure α) : fDiv f 0 ν = f 0 * ν .univ := by
  have : (fun x ↦ f ((∂0/∂ν) x)) =ᵐ[ν] fun _ ↦ f 0 := by
    filter_upwards [ν.rnDeriv_zero] with x hx
    rw [hx]
    simp
  simp [fDiv, lintegral_congr_ae this]

@[simp]
lemma fDiv_zero_measure_right (μ : Measure α) : fDiv f μ 0 = f.derivAtTop * μ .univ := by
  rw [fDiv]; simp

-- @[simp]
-- lemma fDiv_const (c : ℝ) (μ ν : Measure α) [IsFiniteMeasure ν] :
--     fDiv (fun _ ↦ c) μ ν = ν .univ * c := by
--   rw [fDiv_of_integrable (integrable_const c), integral_const]
--   simp only [smul_eq_mul, EReal.coe_mul, derivAtTop_const, zero_mul, add_zero]
--   congr
--   rw [EReal.coe_ennreal_toReal]
--   exact measure_ne_top _ _

-- lemma fDiv_const' {c : ℝ} (hc : 0 ≤ c) (μ ν : Measure α) :
--     fDiv (fun _ ↦ c) μ ν = ν .univ * c := by
--   by_cases hν : IsFiniteMeasure ν
--   · exact fDiv_const c μ ν
--   · have : ν .univ = ∞ := by
--       by_contra h_univ
--       exact absurd ⟨Ne.lt_top h_univ⟩ hν
--     rw [this]
--     by_cases hc0 : c = 0
--     · simp [hc0]
--     rw [fDiv_of_not_integrable]
--     · simp only [EReal.coe_ennreal_top]
--       rw [EReal.top_mul_of_pos]
--       refine lt_of_le_of_ne ?_ (Ne.symm ?_)
--       · exact mod_cast hc
--       · exact mod_cast hc0
--     · rw [integrable_const_iff]
--       simp [hc0, this]

lemma fDiv_self (μ : Measure α) [SigmaFinite μ] : fDiv f μ μ = 0 := by
  have h : (fun x ↦ f (μ.rnDeriv μ x)) =ᵐ[μ] 0 := by
    filter_upwards [μ.rnDeriv_self] with x hx
    rw [hx, f.one]
    rfl
  simp [fDiv, lintegral_congr_ae h]

-- @[simp]
-- lemma fDiv_id (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν] :
--     fDiv id μ ν = μ .univ := by
--   by_cases h_int : Integrable (fun x ↦ ((∂μ/∂ν) x).toReal) ν
--   · rw [fDiv_of_integrable h_int]
--     simp only [id_eq, derivAtTop_id, one_mul]
--     rw [← setIntegral_univ, Measure.setIntegral_toReal_rnDeriv_eq_withDensity]
--     have h_ne_top : (ν.withDensity (∂μ/∂ν)) .univ ≠ ∞ := by
--       rw [withDensity_apply _ .univ, setLIntegral_univ]
--       rwa [integrable_toReal_iff] at h_int
--       · exact (μ.measurable_rnDeriv ν).aemeasurable
--       · exact μ.rnDeriv_ne_top ν
--     rw [EReal.coe_ennreal_toReal h_ne_top]
--     norm_cast
--     conv_rhs => rw [μ.haveLebesgueDecomposition_add ν, add_comm]
--     simp
--   · rw [fDiv_of_not_integrable h_int]
--     symm
--     by_contra h_ne_top
--     have : IsFiniteMeasure μ := ⟨Ne.lt_top ?_⟩
--     swap; · rw [← EReal.coe_ennreal_top] at h_ne_top; exact mod_cast h_ne_top
--     refine h_int <| integrable_toReal_of_lintegral_ne_top (μ.measurable_rnDeriv ν).aemeasurable ?_
--     exact (μ.lintegral_rnDeriv_lt_top _).ne

-- @[simp]
-- lemma fDiv_id' (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν] :
--     fDiv (fun x ↦ x) μ ν = μ .univ := fDiv_id μ ν

end SimpleValues

section Congr

lemma fDiv_congr' (μ ν : Measure α) (hfg : ∀ᵐ x ∂ν.map (fun x ↦ ((∂μ/∂ν) x)), f x = g x)
    (hfg' : f =ᶠ[atTop] g) :
    fDiv f μ ν = fDiv g μ ν := by
  have h : (fun a ↦ f ((∂μ/∂ν) a)) =ᶠ[ae ν] fun a ↦ g ((∂μ/∂ν) a) :=
    ae_of_ae_map (μ.measurable_rnDeriv ν).aemeasurable hfg
  rw [fDiv, DivFunction.derivAtTop_congr hfg', lintegral_congr_ae h]
  rfl

-- lemma fDiv_congr (μ ν : Measure α) (h : ∀ x ≥ 0, f x = g x) :
--     fDiv f μ ν = fDiv g μ ν := by
--   have (x : α) : f ((∂μ/∂ν) x) = g ((∂μ/∂ν) x) := h _ ENNReal.toReal_nonneg
--   simp_rw [fDiv, this, DivFunction.derivAtTop_congr_nonneg h]

lemma fDiv_congr_measure {μ ν : Measure α} {μ' ν' : Measure β}
    (h_eq : ∫⁻ x, f ((∂μ/∂ν) x) ∂ν = ∫⁻ x, f ((∂μ'/∂ν') x) ∂ν')
    (h_sing : μ.singularPart ν univ = μ'.singularPart ν' univ) :
    fDiv f μ ν = fDiv f μ' ν' := by
  rw [fDiv, fDiv, h_sing, h_eq]

-- lemma fDiv_eq_zero_of_forall_nonneg (μ ν : Measure α) (hf : ∀ x ≥ 0, f x = 0) :
--     fDiv f μ ν = 0 := by
--   rw [← fDiv_zero (μ := μ) (ν := ν)]
--   exact fDiv_congr μ ν hf

end Congr

section MulAdd

lemma fDiv_smul (c : ℝ≥0) (μ ν : Measure α) : fDiv (c • f) μ ν = c * fDiv f μ ν := by
  rw [fDiv]
  simp only [DivFunction.smul_apply, DivFunction.derivAtTop_smul]
  rw [lintegral_const_mul _ measurable_divFunction_rnDeriv, fDiv, mul_add, ← mul_assoc]

-- lemma fDiv_mul_of_ne_top (c : ℝ) (hf_cvx : ConvexOn ℝ (Ici 0) f) (h_top : derivAtTop f ≠ ⊤)
--     (μ ν : Measure α) [IsFiniteMeasure μ] (h_int : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν) :
--     fDiv (fun x ↦ c * f x) μ ν = c * fDiv f μ ν := by
--   by_cases hc0 : c = 0
--   · simp [hc0]
--   rw [fDiv_of_integrable h_int, fDiv_of_integrable]
--   swap; · exact h_int.const_mul _
--   rw [integral_mul_left, derivAtTop_const_mul hf_cvx hc0]
--   lift derivAtTop f to ℝ using ⟨h_top, hf_cvx.derivAtTop_ne_bot⟩ with df
--   rw [← EReal.coe_ennreal_toReal (measure_ne_top _ _)]
--   norm_cast
--   ring

-- TODO: in the case where both functions are convex, integrability of the sum is equivalent to
-- integrability of both, and we don't need hf and hg.
-- In general it's not true that if the sum is integrable then both are, even if the functions are
-- convex, take for example f(x) = -x and g(x) = x with the Lebesgue measure. But maybe with some
-- additional hypothesis it's true.
lemma fDiv_add : fDiv (f + g) μ ν = fDiv f μ ν + fDiv g μ ν := by
  simp only [fDiv, DivFunction.add_apply, DivFunction.derivAtTop_add]
  rw [lintegral_add_left measurable_divFunction_rnDeriv]
  ring

-- lemma fDiv_add_const (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
--     (hf_cvx : ConvexOn ℝ (Set.Ici 0) f) (c : ℝ) :
--     fDiv (fun x ↦ f x + c) μ ν = fDiv f μ ν + c * ν .univ := by
--   by_cases hf_int : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν
--   · rw [fDiv_add hf_int (integrable_const _) hf_cvx, fDiv_const, mul_comm]
--     exact convexOn_const _ (convex_Ici 0)
--   · rw [fDiv_of_not_integrable hf_int, fDiv_of_not_integrable]
--     · rw [← EReal.coe_ennreal_toReal, ← EReal.coe_mul, EReal.top_add_coe]
--       exact measure_ne_top _ _
--     · have : (fun x ↦ f ((∂μ/∂ν) x).toReal) = (fun x ↦ (f ((∂μ/∂ν) x).toReal + c) - c) := by
--         ext; simp
--       rw [this] at hf_int
--       exact fun h_int ↦ hf_int (h_int.sub (integrable_const _))

-- lemma fDiv_sub_const (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
--     (hf_cvx : ConvexOn ℝ (Set.Ici 0) f) (c : ℝ) :
--     fDiv (fun x ↦ f x - c) μ ν = fDiv f μ ν - c * ν .univ := by
--   have : f = fun x ↦ (f x - c) + c := by ext; simp
--   conv_rhs => rw [this]
--   rw [fDiv_add_const]
--   · rw [← EReal.coe_ennreal_toReal (measure_ne_top ν _), ← EReal.coe_mul, EReal.add_sub_cancel]
--   · exact hf_cvx.sub (concaveOn_const _ (convex_Ici 0))

-- lemma fDiv_linear {c : ℝ} [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
--     fDiv (fun x ↦ c * (x - 1)) μ ν
--       = c * ((μ .univ).toReal - (ν .univ).toReal) := by
--   rw [fDiv_mul_of_ne_top]
--   rotate_left
--   · exact (convexOn_id (convex_Ici 0)).add (convexOn_const _ (convex_Ici 0))
--   · rw [derivAtTop_sub_const, derivAtTop_id']
--     swap; · exact convexOn_id (convex_Ici 0)
--     exact ne_of_beq_false rfl
--   · exact integrable_add_const_iff.mpr Measure.integrable_toReal_rnDeriv
--   rw [fDiv_sub_const, fDiv_id']
--   swap; · exact convexOn_id (convex_Ici 0)
--   simp [EReal.coe_ennreal_toReal, measure_ne_top]

-- lemma fDiv_add_linear' {c : ℝ} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
--     (hf_cvx : ConvexOn ℝ (Set.Ici 0) f) :
--     fDiv (fun x ↦ f x + c * (x - 1)) μ ν
--       = fDiv f μ ν + c * ((μ .univ).toReal - (ν .univ).toReal) := by
--   by_cases hf : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν
--   · rw [fDiv_add hf _ hf_cvx _, fDiv_linear]
--     · exact (Measure.integrable_toReal_rnDeriv.sub (integrable_const _)).const_mul c
--     · rcases le_total 0 c with (hc | hc)
--       · exact ((convexOn_id (convex_Ici 0)).sub (concaveOn_const _ (convex_Ici 0))).smul hc
--       · rw [← neg_neg c]
--         simp_rw [neg_mul (-c)]
--         exact (concaveOn_id (convex_Ici 0)).sub (convexOn_const _ (convex_Ici 0)) |>.smul
--           (neg_nonneg.mpr hc) |>.neg
--   · rw [fDiv_of_not_integrable hf, fDiv_of_not_integrable, EReal.top_add_of_ne_bot]
--     · refine (EReal.mul_ne_bot _ _).mpr ⟨?_, ?_, ?_, ?_⟩
--       · simp
--       · exact Or.inr <| EReal.add_top_iff_ne_bot.mp rfl
--       · simp
--       · exact Or.inr <| Ne.symm (ne_of_beq_false rfl)
--     · refine fun h_int ↦ hf ?_
--       have : (fun x ↦ f ((∂μ/∂ν) x).toReal)
--           = fun x ↦ (f ((∂μ/∂ν) x).toReal + c * (((∂μ/∂ν) x).toReal - 1))
--             - c * (((∂μ/∂ν) x).toReal - 1) := by ext x; simp
--       rw [this]
--       exact h_int.add ((Measure.integrable_toReal_rnDeriv.sub (integrable_const _)).const_mul c).neg

-- lemma fDiv_add_linear {c : ℝ} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
--     (hf_cvx : ConvexOn ℝ (Set.Ici 0) f) (h_eq : μ .univ = ν .univ) :
--     fDiv (fun x ↦ f x + c * (x - 1)) μ ν = fDiv f μ ν := by
--   rw [fDiv_add_linear' hf_cvx, h_eq, ← EReal.coe_sub, sub_self]
--   simp

-- lemma fDiv_eq_fDiv_centeredFunction [IsFiniteMeasure μ] [IsFiniteMeasure ν]
--     (hf_cvx : ConvexOn ℝ (Ici 0) f) :
--     fDiv f μ ν = fDiv (fun x ↦ f x - f 1 - rightDeriv f 1 * (x - 1)) μ ν
--       + f 1 * ν univ + rightDeriv f 1 * ((μ univ).toReal - (ν univ).toReal) := by
--   simp_rw [sub_eq_add_neg (f _), sub_eq_add_neg (_ + _), ← neg_mul]
--   rw [fDiv_add_linear' ?_, fDiv_add_const _ _ hf_cvx]
--   swap; · exact hf_cvx.add_const _
--   simp_rw [EReal.coe_neg, neg_mul]
--   rw [add_assoc, add_comm (_ * _), ← add_assoc, add_assoc _ (-(_ * _)), add_comm (-(_ * _)),
--     ← sub_eq_add_neg (_ * _), EReal.sub_self, add_zero]
--   rotate_left
--   · refine (EReal.mul_ne_top _ _).mpr ⟨?_, Or.inr <| EReal.add_top_iff_ne_bot.mp rfl,
--       ?_, Or.inr <| Ne.symm (ne_of_beq_false rfl)⟩ <;> simp
--   · refine (EReal.mul_ne_bot _ _).mpr ⟨?_, Or.inr <| EReal.add_top_iff_ne_bot.mp rfl,
--       ?_, Or.inr <| Ne.symm (ne_of_beq_false rfl)⟩ <;> simp
--   rw [add_assoc, add_comm (-(_ * _)), ← sub_eq_add_neg, EReal.sub_self, add_zero]
--     <;> simp [EReal.mul_ne_top, EReal.mul_ne_bot, measure_ne_top]

end MulAdd

section AbsolutelyContinuousMutuallySingular

lemma fDiv_of_mutuallySingular [SigmaFinite μ] [SigmaFinite ν] (h : μ ⟂ₘ ν) :
    fDiv f μ ν = f 0 * ν .univ + f.derivAtTop * μ .univ := by
  have : μ.singularPart ν = μ := (μ.singularPart_eq_self).mpr h
  have hf_rnDeriv : (fun x ↦ f ((∂μ/∂ν) x)) =ᵐ[ν] fun _ ↦ f 0 := by
    filter_upwards [Measure.rnDeriv_eq_zero_of_mutuallySingular h Measure.AbsolutelyContinuous.rfl]
      with x hx using by simp [hx]
  simp [fDiv, lintegral_congr_ae hf_rnDeriv, this]

lemma fDiv_of_absolutelyContinuous (h : μ ≪ ν) : fDiv f μ ν = ∫⁻ x, f ((∂μ/∂ν) x) ∂ν := by
  simp [fDiv, Measure.singularPart_eq_zero_of_ac h]

lemma fDiv_absolutelyContinuous_add_mutuallySingular {μ₁ μ₂ ν : Measure α}
    [SigmaFinite μ₁] [SigmaFinite μ₂] [SigmaFinite ν] (h₁ : μ₁ ≪ ν) (h₂ : μ₂ ⟂ₘ ν) :
    fDiv f (μ₁ + μ₂) ν = fDiv f μ₁ ν + f.derivAtTop * μ₂ .univ := by
  have h1 : μ₁.singularPart ν = 0 := (Measure.singularPart_eq_zero _ _).mpr h₁
  have h2 : (μ₁ + μ₂).singularPart ν = μ₂ := by
    rw [Measure.singularPart_add, h1, zero_add, Measure.singularPart_eq_self.mpr h₂]
  have h_ae : (fun x ↦ f ((∂μ₁ + μ₂/∂ν) x)) =ᵐ[ν] (fun x ↦ f ((∂μ₁/∂ν) x)) := by
    have h_zero : (∂μ₂/∂ν) =ᵐ[ν] 0 := (Measure.rnDeriv_eq_zero _ _).mpr h₂
    filter_upwards [h_zero, Measure.rnDeriv_add' μ₁ μ₂ ν] with x hx_zero hx_add
    rw [hx_add, Pi.add_apply, hx_zero]
    simp only [Pi.zero_apply, add_zero, implies_true]
  simp [fDiv, lintegral_congr_ae h_ae, h1, h2]

-- lemma fDiv_eq_add_withDensity_singularPart
--     (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν] :
--     fDiv f μ ν = fDiv f (ν.withDensity (∂μ/∂ν)) ν + fDiv f (μ.singularPart ν) ν
--       - f 0 * ν .univ := by
--   conv_lhs => rw [μ.haveLebesgueDecomposition_add ν, add_comm,
--     fDiv_absolutelyContinuous_add_mutuallySingular (withDensity_absolutelyContinuous _ _)
--       (Measure.mutuallySingular_singularPart _ _)]
--   rw [fDiv_of_mutuallySingular (Measure.mutuallySingular_singularPart _ _)]
--   classical
--   rw [fDiv_of_mutuallySingular (μ.mutuallySingular_singularPart _),
--     fDiv_of_absolutelyContinuous (withDensity_absolutelyContinuous _ _),
--     add_comm _ (f.derivAtTop * _), ← add_assoc]
--   by_cases h0 : f 0 = ∞
--   · simp only [h0]
--     sorry
--   rw [ENNReal.add_sub_cancel_right]
--   · rw [fDiv]
--     congr 1
--     refine lintegral_congr_ae ?_
--     filter_upwards [ν.rnDeriv_withDensity (μ.measurable_rnDeriv ν)] with x hx
--     rw [hx]
--   · refine ENNReal.mul_ne_top ENNReal.coe_ne_top ?_
--   by_cases hf : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν
--   · rw [fDiv_of_absolutelyContinuous (withDensity_absolutelyContinuous _ _), if_pos,
--       fDiv_of_integrable hf]
--     swap
--     · exact h_int_iff.mp hf
--     rw [add_sub_assoc]
--     congr 2
--     · refine integral_congr_ae ?_
--       filter_upwards [ν.rnDeriv_withDensity (μ.measurable_rnDeriv ν)] with x hx
--       rw [hx]
--     rw [← EReal.coe_ennreal_toReal (measure_ne_top ν _), ← EReal.coe_mul, EReal.add_sub_cancel']
--   · rw [fDiv_of_not_integrable hf, fDiv_of_not_integrable]
--     · rw [add_sub_assoc, ← EReal.coe_ennreal_toReal (measure_ne_top ν _), ← EReal.coe_mul,
--         EReal.add_sub_cancel']
--       by_cases h0 : μ.singularPart ν .univ = 0
--       · simp [h0]
--       · by_cases h_top : derivAtTop f = ⊤
--         · rw [h_top, EReal.top_mul_ennreal_coe h0, EReal.top_add_top]
--         · lift derivAtTop f to ℝ using ⟨h_top, hf_cvx.derivAtTop_ne_bot⟩ with x
--           rw [← EReal.coe_ennreal_toReal (measure_ne_top _ _), ← EReal.coe_mul, EReal.top_add_coe]
--     · rwa [← h_int_iff]

-- lemma fDiv_eq_add_withDensity_singularPart'
--     (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
--     (hf_cvx : ConvexOn ℝ (Ici 0) f) :
--     fDiv f μ ν = fDiv (fun x ↦ f x - f 0) (ν.withDensity (∂μ/∂ν)) ν
--       + fDiv f (μ.singularPart ν) ν := by
--   rw [fDiv_eq_add_withDensity_singularPart _ _ hf_cvx, fDiv_sub_const, add_sub_assoc,
--     sub_eq_add_neg, sub_eq_add_neg, add_assoc]
--   · congr 1
--     rw [add_comm]
--   · exact hf_cvx

-- lemma fDiv_eq_add_withDensity_singularPart''
--     (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
--     (hf_cvx : ConvexOn ℝ (Ici 0) f) :
--     fDiv f μ ν = fDiv f (ν.withDensity (∂μ/∂ν)) ν
--       + fDiv (fun x ↦ f x - f 0) (μ.singularPart ν) ν := by
--   rw [fDiv_eq_add_withDensity_singularPart _ _ hf_cvx, fDiv_sub_const, add_sub_assoc,
--     sub_eq_add_neg]
--   exact hf_cvx

lemma fDiv_eq_add_withDensity_derivAtTop
    (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν] :
    fDiv f μ ν = fDiv f (ν.withDensity (∂μ/∂ν)) ν + f.derivAtTop * μ.singularPart ν .univ := by
  conv_lhs => rw [μ.haveLebesgueDecomposition_add ν, add_comm,
     fDiv_absolutelyContinuous_add_mutuallySingular (withDensity_absolutelyContinuous _ _)
       (Measure.mutuallySingular_singularPart _ _)]

end AbsolutelyContinuousMutuallySingular

section AddMeasure

/-- Auxiliary lemma for `fDiv_add_measure_le`. -/
lemma fDiv_add_measure_le_of_ac {μ₁ μ₂ ν : Measure α} [SigmaFinite μ₁] [SigmaFinite μ₂]
    [SigmaFinite ν] (h₁ : μ₁ ≪ ν) (h₂ : μ₂ ≪ ν) :
    fDiv f (μ₁ + μ₂) ν ≤ fDiv f μ₁ ν + f.derivAtTop * μ₂ univ := by
  have h_le : ∀ᵐ x ∂ν, f ((∂μ₁ + μ₂/∂ν) x)
      ≤ f ((∂μ₁/∂ν) x) + f.derivAtTop * ((∂μ₂/∂ν) x) := by
    filter_upwards [μ₁.rnDeriv_add' μ₂ ν] with x hx
    rw [hx, Pi.add_apply]
    exact f.le_add_derivAtTop'' _ _
  rw [fDiv_of_absolutelyContinuous (Measure.AbsolutelyContinuous.add_left_iff.mpr ⟨h₁, h₂⟩),
    fDiv_of_absolutelyContinuous h₁]
  calc ∫⁻ x, f ((∂μ₁ + μ₂/∂ν) x) ∂ν
    ≤ ∫⁻ x, f ((∂μ₁/∂ν) x) + f.derivAtTop * (∂μ₂/∂ν) x ∂ν := lintegral_mono_ae h_le
  _ ≤ ∫⁻ x, f ((∂μ₁/∂ν) x) ∂ν + f.derivAtTop * μ₂ .univ := by
        rw [lintegral_add_left measurable_divFunction_rnDeriv,
          lintegral_const_mul _ (Measure.measurable_rnDeriv _ _), Measure.lintegral_rnDeriv h₂]

lemma fDiv_add_measure_le (μ₁ μ₂ ν : Measure α) [SigmaFinite μ₁] [SigmaFinite μ₂]
    [SigmaFinite ν] :
    fDiv f (μ₁ + μ₂) ν ≤ fDiv f μ₁ ν + f.derivAtTop * μ₂ .univ := by
  rw [μ₂.haveLebesgueDecomposition_add ν, μ₁.haveLebesgueDecomposition_add ν]
  have : μ₁.singularPart ν + ν.withDensity (∂μ₁/∂ν) + (μ₂.singularPart ν + ν.withDensity (∂μ₂/∂ν))
      = (ν.withDensity (∂μ₁/∂ν) + ν.withDensity (∂μ₂/∂ν))
        + (μ₁.singularPart ν + μ₂.singularPart ν) := by
    abel
  rw [this, fDiv_absolutelyContinuous_add_mutuallySingular
      ((withDensity_absolutelyContinuous _ _).add_left (withDensity_absolutelyContinuous _ _))
      ((μ₁.mutuallySingular_singularPart _).add_left (μ₂.mutuallySingular_singularPart _))]
  simp only [Measure.coe_add, Pi.add_apply, EReal.coe_ennreal_add]
  conv_rhs => rw [add_comm (μ₁.singularPart ν)]
  rw [fDiv_absolutelyContinuous_add_mutuallySingular (withDensity_absolutelyContinuous _ _)
    (μ₁.mutuallySingular_singularPart _)]
  calc fDiv f (ν.withDensity (∂μ₁/∂ν) + ν.withDensity (∂μ₂/∂ν)) ν
      + f.derivAtTop * (μ₁.singularPart ν univ + μ₂.singularPart ν univ)
  _ ≤ fDiv f (ν.withDensity (∂μ₁/∂ν)) ν + f.derivAtTop * ν.withDensity (∂μ₂/∂ν) univ
      + f.derivAtTop * μ₁.singularPart ν univ + f.derivAtTop * μ₂.singularPart ν univ := by
        rw [mul_add, add_assoc]
        gcongr
        exact fDiv_add_measure_le_of_ac (withDensity_absolutelyContinuous _ _)
          (withDensity_absolutelyContinuous _ _)
  _ = fDiv f (ν.withDensity (∂μ₁/∂ν)) ν + f.derivAtTop * μ₁.singularPart ν univ
      + f.derivAtTop * (μ₂.singularPart ν univ + ν.withDensity (∂μ₂/∂ν) univ) := by
        ring

end AddMeasure

/-- Auxiliary lemma for `fDiv_le_zero_add_top`. -/
lemma fDiv_le_zero_add_top_of_ac [SigmaFinite μ] [SigmaFinite ν] (hμν : μ ≪ ν) :
    fDiv f μ ν ≤ f 0 * ν .univ + f.derivAtTop * μ .univ := by
  rw [fDiv_of_absolutelyContinuous hμν]
  have h x : f ((∂μ/∂ν) x) ≤ f 0 + f.derivAtTop * (∂μ/∂ν) x := by
    conv_lhs => rw [← zero_add ((∂μ/∂ν) x)]
    exact f.le_add_derivAtTop'' _ _
  refine (lintegral_mono h).trans_eq ?_
  rw [lintegral_add_left measurable_const, lintegral_const,
    lintegral_const_mul _ (Measure.measurable_rnDeriv _ _), Measure.lintegral_rnDeriv hμν]

lemma fDiv_le_zero_add_top [SigmaFinite μ] [SigmaFinite ν] :
    fDiv f μ ν ≤ f 0 * ν .univ + f.derivAtTop * μ .univ := by
  rw [fDiv_eq_add_withDensity_derivAtTop]
  calc fDiv f (ν.withDensity (∂μ/∂ν)) ν + f.derivAtTop * μ.singularPart ν .univ
    ≤ f 0 * ν .univ + f.derivAtTop * ν.withDensity (∂μ/∂ν) .univ
      + f.derivAtTop * μ.singularPart ν .univ := by
        gcongr
        exact fDiv_le_zero_add_top_of_ac (withDensity_absolutelyContinuous _ _)
    _ ≤ f 0 * ν .univ + f.derivAtTop * μ .univ := by
      rw [add_assoc, ← mul_add]
      conv_rhs => rw [μ.haveLebesgueDecomposition_add ν, add_comm (μ.singularPart ν)]
      rfl

lemma fDiv_lt_top_of_ac (h : μ ≪ ν) (h_int : ∫⁻ x, f ((∂μ/∂ν) x) ∂ν ≠ ∞) :
    fDiv f μ ν < ∞ := by
  rw [fDiv_of_absolutelyContinuous h]
  exact h_int.lt_top

section derivAtTopTop

lemma fDiv_of_not_ac [SigmaFinite μ] [SigmaFinite ν] (hf : f.derivAtTop = ∞) (hμν : ¬ μ ≪ ν) :
    fDiv f μ ν = ∞ := by
  rw [fDiv, hf]
  suffices μ.singularPart ν .univ ≠ 0 by
    rw [ENNReal.add_eq_top, ENNReal.top_mul this]
    exact Or.inr rfl
  simp only [ne_eq, Measure.measure_univ_eq_zero]
  rw [Measure.singularPart_eq_zero]
  exact hμν

lemma fDiv_lt_top_iff_ac [SigmaFinite μ] [SigmaFinite ν] (hf : f.derivAtTop = ∞)
    (h_int : ∫⁻ x, f ((∂μ/∂ν) x) ∂ν ≠ ∞) :
    fDiv f μ ν < ∞ ↔ μ ≪ ν := by
  refine ⟨fun h ↦ ?_, fun h ↦ fDiv_lt_top_of_ac h h_int⟩
  by_contra h_not_ac
  refine h.ne (fDiv_of_not_ac hf h_not_ac)

lemma fDiv_ne_top_iff_ac [SigmaFinite μ] [SigmaFinite ν] (hf : f.derivAtTop = ∞)
    (h_int : ∫⁻ x, f ((∂μ/∂ν) x) ∂ν ≠ ∞) :
    fDiv f μ ν ≠ ∞ ↔ μ ≪ ν := by
  rw [← fDiv_lt_top_iff_ac hf h_int, lt_top_iff_ne_top]

lemma fDiv_eq_top_iff_not_ac [SigmaFinite μ] [SigmaFinite ν] (hf : f.derivAtTop = ∞)
    (h_int : ∫⁻ x, f ((∂μ/∂ν) x) ∂ν ≠ ∞) :
    fDiv f μ ν = ∞ ↔ ¬ μ ≪ ν := by
  rw [← fDiv_ne_top_iff_ac hf h_int, not_not]

lemma fDiv_of_derivAtTop_eq_top [SigmaFinite μ] [SigmaFinite ν] (hf : f.derivAtTop = ∞)
    [Decidable (μ ≪ ν)] :
    fDiv f μ ν = if μ ≪ ν then ∫⁻ x, f ((∂μ/∂ν) x) ∂ν else ∞ := by
  split_ifs with h
  · rw [fDiv_of_absolutelyContinuous h]
  · rw [fDiv_of_not_ac _ h]
    exact hf

end derivAtTopTop

lemma fDiv_lt_top_of_derivAtTop_ne_top [IsFiniteMeasure μ] (hf : f.derivAtTop ≠ ∞)
    (h_int : ∫⁻ x, f ((∂μ/∂ν) x) ∂ν ≠ ∞) :
    fDiv f μ ν < ∞ := by
  rw [fDiv, ENNReal.add_lt_top, ENNReal.mul_lt_top_iff]
  refine ⟨h_int.lt_top, ?_⟩
  simp [hf.lt_top]

lemma fDiv_lt_top_of_derivAtTop_ne_top' [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h_zero : f 0 ≠ ∞) (h_top : f.derivAtTop ≠ ∞) :
    fDiv f μ ν < ∞ := by
  have h_int : ∫⁻ x, f ((∂μ/∂ν) x) ∂ν ≠ ∞ := f.lintegral_comp_rnDeriv_ne_top μ ν h_zero h_top
  exact fDiv_lt_top_of_derivAtTop_ne_top h_top h_int

lemma fDiv_lt_top_iff_of_derivAtTop_ne_top [IsFiniteMeasure μ] (hf : f.derivAtTop ≠ ∞) :
    fDiv f μ ν < ∞ ↔ ∫⁻ x, f ((∂μ/∂ν) x) ∂ν ≠ ∞ := by
  refine ⟨fun h ↦ ?_, fDiv_lt_top_of_derivAtTop_ne_top hf⟩
  rw [fDiv, ENNReal.add_lt_top] at h
  exact h.1.ne

lemma fDiv_ne_top_of_derivAtTop_ne_top [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h_zero : f 0 ≠ ∞) (h_top : f.derivAtTop ≠ ∞) :
    fDiv f μ ν ≠ ∞ := by
  rw [← lt_top_iff_ne_top]
  exact fDiv_lt_top_of_derivAtTop_ne_top' h_zero h_top

lemma fDiv_ne_top_iff_of_derivAtTop_ne_top [IsFiniteMeasure μ] (hf : f.derivAtTop ≠ ∞) :
    fDiv f μ ν ≠ ∞ ↔ ∫⁻ x, f ((∂μ/∂ν) x) ∂ν ≠ ∞ := by
  rw [← fDiv_lt_top_iff_of_derivAtTop_ne_top hf, lt_top_iff_ne_top]

lemma fDiv_eq_top_iff_of_derivAtTop_ne_top [IsFiniteMeasure μ] (hf : f.derivAtTop ≠ ∞) :
    fDiv f μ ν = ∞ ↔ ∫⁻ x, f ((∂μ/∂ν) x) ∂ν = ∞ := by
  rw [← not_not (a := fDiv f μ ν = ∞), ← ne_eq, fDiv_ne_top_iff_of_derivAtTop_ne_top hf, not_not]

lemma fDiv_eq_top_iff [IsFiniteMeasure μ] [SigmaFinite ν] :
    fDiv f μ ν = ∞
      ↔ (∫⁻ x, f ((∂μ/∂ν) x) ∂ν = ∞) ∨ (f.derivAtTop = ∞ ∧ ¬ μ ≪ ν) := by
  by_cases h : f.derivAtTop = ∞
  · simp only [h, true_and]
    by_cases hf : ∫⁻ x, f ((∂μ/∂ν) x) ∂ν = ∞
    · simp [fDiv, hf]
    · simp only [hf, not_true_eq_false, false_or]
      exact fDiv_eq_top_iff_not_ac h hf
  · simp only [h, false_and, or_false]
    exact fDiv_eq_top_iff_of_derivAtTop_ne_top h

lemma fDiv_eq_top_iff' [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    fDiv f μ ν = ∞
      ↔ (f.derivAtTop = ∞ ∧ ¬ μ ≪ ν)
        ∨ ((f 0 = ∞ ∨ f.derivAtTop = ∞) ∧ ∫⁻ x, f ((∂μ/∂ν) x) ∂ν = ∞) := by
  by_cases h_top : f.derivAtTop = ∞
  · rw [fDiv_eq_top_iff]
    simp only [h_top, true_and, iff_or_self, and_imp]
    tauto
  by_cases h_zero : f 0 = ∞
  · rw [fDiv_eq_top_iff]
    simp [h_top, h_zero]
  simp only [h_top, false_and, or_false, h_zero, or_self, iff_false]
  exact fDiv_ne_top_of_derivAtTop_ne_top h_zero h_top

lemma fDiv_ne_top_iff [IsFiniteMeasure μ] [SigmaFinite ν] :
    fDiv f μ ν ≠ ∞
      ↔ (∫⁻ x, f ((∂μ/∂ν) x) ∂ν ≠ ∞) ∧ (f.derivAtTop = ∞ → μ ≪ ν) := by
  rw [ne_eq, fDiv_eq_top_iff]
  push_neg
  rfl

lemma fDiv_ne_top_iff' [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    fDiv f μ ν ≠ ∞
      ↔ ((f.derivAtTop = ⊤ → μ ≪ ν)
        ∧ ((f 0 = ∞ ∨ f.derivAtTop = ∞) → ∫⁻ x, f ((∂μ/∂ν) x) ∂ν ≠ ∞)) := by
  rw [ne_eq, fDiv_eq_top_iff']
  push_neg
  rfl

lemma lintegral_ne_top_of_fDiv_ne_top (h : fDiv f μ ν ≠ ⊤) :
    ∫⁻ x, f ((∂μ/∂ν) x) ∂ν ≠ ∞ := by
  by_contra h_not
  simp [fDiv, h_not] at h

-- lemma fDiv_of_ne_top (h : fDiv f μ ν ≠ ⊤) :
--     fDiv f μ ν = ∫ x, f ((∂μ/∂ν) x).toReal ∂ν + derivAtTop f * μ.singularPart ν .univ := by
--   rw [fDiv_of_integrable]
--   exact integrable_of_fDiv_ne_top h

-- lemma toReal_fDiv_of_integrable [IsFiniteMeasure μ] (hf_cvx : ConvexOn ℝ (Ici 0) f)
--     (hf_int : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν)
--     (h_deriv : derivAtTop f = ⊤ → μ ≪ ν) :
--     (fDiv f μ ν).toReal = ∫ y, f ((∂μ/∂ν) y).toReal ∂ν
--         + (derivAtTop f * μ.singularPart ν .univ).toReal := by
--   rw [fDiv_of_integrable hf_int, EReal.toReal_add]
--   rotate_left
--   · simp
--   · simp
--   · simp only [ne_eq, EReal.mul_eq_top, hf_cvx.derivAtTop_ne_bot, false_and,
--       EReal.coe_ennreal_ne_bot, and_false, EReal.coe_ennreal_pos, Measure.measure_univ_pos,
--       EReal.coe_ennreal_eq_top_iff, measure_ne_top, or_false, false_or, not_and, not_not]
--     intro h_top
--     simp [h_top, Measure.singularPart_eq_zero_of_ac (h_deriv h_top)]
--   · simp only [ne_eq, EReal.mul_eq_bot, hf_cvx.derivAtTop_ne_bot, EReal.coe_ennreal_pos,
--       Measure.measure_univ_pos, false_and, EReal.coe_ennreal_ne_bot, and_false,
--       EReal.coe_ennreal_eq_top_iff, measure_ne_top, or_false, false_or, not_and, not_lt]
--     exact fun _ ↦ EReal.coe_ennreal_nonneg _
--   rfl

lemma _root_.MeasureTheory.laverage_eq_average [IsFiniteMeasure μ] {f : α → ℝ≥0∞}
    (hf : AEMeasurable f μ) (hf_top : ∫⁻ a, f a ∂μ ≠ ⊤) :
    ⨍⁻ x, f x ∂μ = ENNReal.ofReal (⨍ x, (f x).toReal ∂μ) := by
  rw [laverage_eq, average_eq]
  by_cases hμ0 : μ = 0
  · simp [hμ0]
  simp only [smul_eq_mul]
  rw [ENNReal.ofReal_mul (by simp),
    ENNReal.ofReal_inv_of_pos (by simp [ENNReal.toReal_pos_iff, hμ0]),
    ENNReal.ofReal_toReal (by simp), integral_toReal hf (ae_lt_top' hf hf_top),
    ENNReal.ofReal_toReal hf_top, div_eq_mul_inv, mul_comm]

lemma _root_.ConvexOn.map_laverage_le [IsFiniteMeasure μ] [NeZero μ]
    {f : α → ℝ≥0∞} {g : ℝ≥0∞ → ℝ≥0∞} {s : Set ℝ≥0∞}
    (hf : AEMeasurable f μ)
    (hg : ConvexOn ℝ≥0 s g) (hgc : ContinuousOn g s) (hsc : IsClosed s)
    (hfs : ∀ᵐ x ∂μ, f x ∈ s) (hfi : ∫⁻ x, f x ∂μ ≠ ∞) :
    g (⨍⁻ x, f x ∂μ) ≤ ⨍⁻ x, g (f x) ∂μ := by
  by_cases hgi : ∫⁻ x, g (f x) ∂μ = ∞
  · conv_rhs => rw [laverage_eq, hgi]
    rw [ENNReal.top_div_of_ne_top (measure_ne_top _ _)]
    simp
  have hf_lt_top : ∀ᵐ x ∂μ, f x < ∞ := ae_lt_top' hf hfi
  have hg_lt_top : ∀ᵐ x ∂μ, g (f x) < ∞ := ae_lt_top' ?_ hgi
  swap; · sorry
  have hf_ofReal_toReal : ∀ᵐ x ∂μ, ENNReal.ofReal (f x).toReal = f x := by
    filter_upwards [hf_lt_top] with x hx
    rw [ENNReal.ofReal_toReal hx.ne]
  rw [laverage_eq_average hf hfi]
  rw [← ENNReal.toReal_le_toReal]
  rotate_left
  · sorry
  · sorry
  have hf_int : Integrable (fun x ↦ (f x).toReal) μ := integrable_toReal_of_lintegral_ne_top hf hfi
  have hg_int : Integrable ((fun x ↦ (g (ENNReal.ofReal x)).toReal)
      ∘ (fun x ↦ (f x).toReal)) μ := by
    have : ((fun x ↦ (g (ENNReal.ofReal x)).toReal) ∘ fun x ↦ (f x).toReal)
        =ᵐ[μ] fun x ↦ (g (f x)).toReal := by
      filter_upwards [hf_ofReal_toReal] with x hx
      simp [hx]
    rw [integrable_congr this]
    refine integrable_toReal_of_lintegral_ne_top ?_ hgi
    sorry
  refine (ConvexOn.map_average_le ?_ ?_ ?_ ?_ hf_int hg_int (s := ENNReal.toReal '' s)).trans ?_
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry

lemma le_fDiv_of_ac' [IsFiniteMeasure μ] [IsProbabilityMeasure ν] (hμν : μ ≪ ν)
    (hf : ∀ x, f x ≠ ∞) :
    f (μ .univ) ≤ fDiv f μ ν := by
  rw [fDiv_of_absolutelyContinuous hμν]
  by_cases hf_int : ∫⁻ x, f ((∂μ/∂ν) x) ∂ν = ∞
  · simp [hf_int]
  have h_eq : μ univ = ∫⁻ x, μ.rnDeriv ν x ∂ν := by rw [Measure.lintegral_rnDeriv hμν]
  calc f (μ .univ)
  _ = f (∫⁻ x, μ.rnDeriv ν x ∂ν) := by rw [Measure.lintegral_rnDeriv hμν]
  _ = f (⨍⁻ x, μ.rnDeriv ν x ∂ν) := by rw [laverage_eq_lintegral]
  _ ≤ ⨍⁻ x, f (μ.rnDeriv ν x) ∂ν := by sorry
  _ = ∫⁻ x, f (μ.rnDeriv ν x) ∂ν := by rw [laverage_eq_lintegral]

-- todo: remove `hf`
lemma le_fDiv_of_ac [IsFiniteMeasure μ] [IsProbabilityMeasure ν] (hμν : μ ≪ ν)
    (hf : ∀ x ≠ ∞, f x ≠ ∞) :
    f (μ .univ) ≤ fDiv f μ ν := by
  rw [fDiv_of_absolutelyContinuous hμν]
  by_cases hf_int : ∫⁻ x, f ((∂μ/∂ν) x) ∂ν = ∞
  · simp [hf_int]
  have h_eq : μ univ = ENNReal.ofReal (∫ x, (μ.rnDeriv ν x).toReal ∂ν) := by
    rw [Measure.integral_toReal_rnDeriv hμν, ENNReal.ofReal_toReal]
    simp
  calc f (μ .univ)
  _ = f (ENNReal.ofReal (∫ x, (μ.rnDeriv ν x).toReal ∂ν)) := by rw [h_eq]
  _ = ENNReal.ofReal (f.realFun (∫ x, (μ.rnDeriv ν x).toReal ∂ν)) := by
      rw [DivFunction.realFun, ENNReal.ofReal_toReal]
      rw [← h_eq]
      exact hf _ (measure_ne_top _ _)
  _ ≤ ENNReal.ofReal (∫ x, f.realFun (μ.rnDeriv ν x).toReal ∂ν) := by
    rw [← average_eq_integral, ← average_eq_integral]
    gcongr
    refine ConvexOn.map_average_le ?_ ?_ (isClosed_Ici (a := 0)) ?_
      Measure.integrable_toReal_rnDeriv (integrable_realFun_rnDeriv hf_int)
    · exact f.convexOn_Ici_realFun hf
    · exact f.continuousOn_realFun_Ici hf
    · exact ae_of_all _ fun _ ↦ ENNReal.toReal_nonneg
  _ = ∫⁻ x, f ((∂μ/∂ν) x) ∂ν := by
    rw [integral_realFun_rnDeriv hf_int, ENNReal.ofReal_toReal hf_int]

lemma f_measure_univ_le_add (μ ν : Measure α) [IsFiniteMeasure μ] [IsProbabilityMeasure ν] :
    f (μ .univ)
      ≤ f (ν.withDensity (∂μ/∂ν) .univ) + f.derivAtTop * μ.singularPart ν .univ := by
  have : μ .univ = ν.withDensity (∂μ/∂ν) .univ + μ.singularPart ν .univ := by
    conv_lhs => rw [μ.haveLebesgueDecomposition_add ν, add_comm]
    simp
  rw [this]
  exact f.le_add_derivAtTop'' _ _

-- todo: remove `hf`
lemma le_fDiv [IsFiniteMeasure μ] [IsProbabilityMeasure ν] (hf : ∀ x ≠ ∞, f x ≠ ∞) :
    f (μ .univ) ≤ fDiv f μ ν := by
  refine (f_measure_univ_le_add μ ν).trans ?_
  rw [fDiv_eq_add_withDensity_derivAtTop]
  gcongr
  exact le_fDiv_of_ac (withDensity_absolutelyContinuous _ _) hf

-- lemma fDiv_nonneg [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
--     0 ≤ fDiv f μ ν := by
--   calc (0 : ℝ≥0∞) = f (μ .univ).toReal := by simp
--   _ ≤ fDiv f μ ν := le_fDiv

/- The hypothesis `hfg'` can maybe become something like `f ≤ᵐ[atTop] g`, but then we would need
some lemma like `derivAtTop_mono`. -/
lemma fDiv_mono'' (hfg : f ≤ᵐ[ν.map (∂μ/∂ν)] g)
    (hfg' : f.derivAtTop ≤ g.derivAtTop) :
    fDiv f μ ν ≤ fDiv g μ ν := by
  rw [fDiv, fDiv]
  refine add_le_add ?_ ?_
  · refine lintegral_mono_ae ?_
    exact ae_of_ae_map (μ.measurable_rnDeriv ν).aemeasurable hfg
  · gcongr

/- The hypothesis `hfg'` can probably be removed if we ask for the functions to be convex,
since then it is true that `derivAtTop` is monotone. -/
lemma fDiv_mono' (hfg : ∀ x, f x ≤ g x) (hfg' : f.derivAtTop ≤ g.derivAtTop) :
    fDiv f μ ν ≤ fDiv g μ ν :=
  fDiv_mono'' (.of_forall hfg) hfg'

-- lemma fDiv_nonneg_of_nonneg (hf : ∀ x, 0 ≤ f x) : 0 ≤ fDiv f μ ν :=
--   fDiv_zero μ ν ▸ fDiv_mono' hf (DivFunction.derivAtTop_zero ▸ zero_le')

lemma fDiv_eq_zero_iff [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hf_deriv : f.derivAtTop = ∞) (hf_cvx : StrictConvexOn ℝ (Ioi 0) f.realFun) :
    fDiv f μ ν = 0 ↔ μ = ν := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ fDiv_self _⟩
  by_cases hμν : μ ≪ ν
  swap; · rw [fDiv_of_not_ac hf_deriv hμν] at h; exact (ENNReal.top_ne_zero h).elim
  classical
  rw [fDiv_of_derivAtTop_eq_top hf_deriv] at h
  simp only [hμν, ↓reduceIte] at h
  rw [lintegral_eq_zero_iff measurable_divFunction_rnDeriv] at h
  have h_eq_zero_iff x : f x = 0 ↔ x = 1 := by
    rw [f.eq_zero_iff zero_lt_one one_lt_two]
    exact hf_cvx.subset (fun x hx ↦ hx.1) (convex_Ioo _ _)
  refine (Measure.rnDeriv_eq_one_iff_eq hμν).mp ?_
  filter_upwards [h] with x hx
  simp only [Pi.zero_apply, h_eq_zero_iff] at hx
  exact hx

-- lemma fDiv_eq_zero_iff' [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
--     (hf_deriv : f.derivAtTop = ∞) (hf_cvx : StrictConvexOn ℝ (Ici 0) f.realFun) :
--     fDiv f μ ν = 0 ↔ μ = ν :=
--   fDiv_eq_zero_iff hf_deriv hf_cvx

lemma fDiv_map_measurableEmbedding [SigmaFinite μ] [SigmaFinite ν]
    {g : α → β} (hg : MeasurableEmbedding g) :
    fDiv f (μ.map g) (ν.map g) = fDiv f μ ν := by
  rw [fDiv, fDiv]
  rw [hg.lintegral_map]
  congr 1
  · refine lintegral_congr_ae ?_
    filter_upwards [hg.rnDeriv_map μ ν] with a ha using ha ▸ rfl
  · rw [hg.singularPart_map μ ν, hg.map_apply, preimage_univ]

theorem lintegral_piecewise {s : Set α} {f g : α → ℝ≥0∞} [DecidablePred (· ∈ s)]
    (hf : AEMeasurable f μ)
    (hs : MeasurableSet s) :
    ∫⁻ x, s.piecewise f g x ∂μ = ∫⁻ x in s, f x ∂μ + ∫⁻ x in sᶜ, g x ∂μ := by
  rw [← Set.indicator_add_compl_eq_piecewise]
  simp only [Pi.add_apply]
  rw [lintegral_add_left', lintegral_indicator _ hs, lintegral_indicator _ hs.compl]
  exact hf.indicator hs

lemma fDiv_restrict (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν]
    {s : Set α} (hs : MeasurableSet s) :
    fDiv f (μ.restrict s) ν = ∫⁻ x in s, f ((∂μ/∂ν) x) ∂ν
        + f 0 * ν sᶜ + f.derivAtTop * (μ.singularPart ν s) := by
  classical
  have h : (fun x ↦ f ((∂μ.restrict s/∂ν) x))
      =ᵐ[ν] s.piecewise (fun x ↦ f ((∂μ/∂ν) x)) (fun _ ↦ f 0) := by
    filter_upwards [μ.rnDeriv_restrict ν hs] with a ha
    rw [ha]
    by_cases has : a ∈ s <;> simp [has]
  rw [fDiv, μ.singularPart_restrict ν hs, Measure.restrict_apply_univ]
  congr 1
  rw [lintegral_congr_ae h]
  rw [lintegral_piecewise measurable_divFunction_rnDeriv.aemeasurable hs, lintegral_const]
  simp only [MeasurableSet.univ, Measure.restrict_apply, univ_inter]

end ProbabilityTheory
