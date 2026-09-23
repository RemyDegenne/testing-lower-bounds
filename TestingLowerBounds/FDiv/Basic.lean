/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
import Mathlib.Analysis.Convex.Integral
import Mathlib.Probability.Notation
import TestingLowerBounds.FDiv.DivFunction.OfReal
import TestingLowerBounds.ForMathlib.RadonNikodym
import Mathlib.MeasureTheory.Measure.Decomposition.IntegralRNDeriv

/-!
# f-Divergences

## Main definitions

* `fDiv f μ ν`: the f-divergence between the measures `μ` and `ν` for the divergence function
  `f : DivFunction`, defined as `∫⁻ x, f (∂μ/∂ν x) ∂ν + f.derivAtTop * μ.singularPart ν univ`.

## Main statements

* `fDiv_of_absolutelyContinuous`, `fDiv_of_mutuallySingular`: values of `fDiv` in the two extreme
  cases of the Lebesgue decomposition.
* `fDiv_eq_add_withDensity_derivAtTop`, `fDiv_add_eq_add_withDensity_singularPart`:
  decompositions of `fDiv` according to the Lebesgue decomposition of `μ` with respect to `ν`.
* `fDiv_eq_top_iff`, `fDiv_ne_top_iff`: finiteness of `fDiv`.
* `le_fDiv_of_ac`: Jensen-type lower bound, `f (μ univ / ν univ) * ν univ ≤ fDiv f μ ν`.
* `fDiv_eq_zero_iff`: for a strictly convex divergence function with infinite derivative at
  infinity, `fDiv f μ ν = 0 ↔ μ = ν`.
* `fDiv_map_measurableEmbedding`: invariance under measurable embeddings.

## Implementation details

The divergence function `f` is a `DivFunction`: a function `ℝ≥0∞ → ℝ≥0∞` which is convex,
continuous and vanishes at `1`. We use `ℝ≥0∞ → ℝ≥0∞` so that `fDiv` can be defined with a
Lebesgue integral, without integrability conditions, and takes values in `ℝ≥0∞`.
The results that need derivatives or the convexity lemmas of Mathlib use the real function
`f.realFun : ℝ → ℝ` instead.

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

lemma fDiv_self (μ : Measure α) [SigmaFinite μ] : fDiv f μ μ = 0 := by
  have h : (fun x ↦ f (μ.rnDeriv μ x)) =ᵐ[μ] 0 := by
    filter_upwards [μ.rnDeriv_self] with x hx
    rw [hx, f.one]
    rfl
  simp [fDiv, lintegral_congr_ae h]

end SimpleValues

section Congr

lemma fDiv_congr' (μ ν : Measure α) (hfg : ∀ᵐ x ∂ν.map (fun x ↦ ((∂μ/∂ν) x)), f x = g x)
    (hfg' : (f : ℝ≥0∞ → ℝ≥0∞) =ᶠ[𝓝[<] ∞] g) :
    fDiv f μ ν = fDiv g μ ν := by
  have h : (fun a ↦ f ((∂μ/∂ν) a)) =ᶠ[ae ν] fun a ↦ g ((∂μ/∂ν) a) :=
    ae_of_ae_map (μ.measurable_rnDeriv ν).aemeasurable hfg
  rw [fDiv, DivFunction.derivAtTop_congr hfg', lintegral_congr_ae h]
  rfl

lemma fDiv_congr_measure {μ ν : Measure α} {μ' ν' : Measure β}
    (h_eq : ∫⁻ x, f ((∂μ/∂ν) x) ∂ν = ∫⁻ x, f ((∂μ'/∂ν') x) ∂ν')
    (h_sing : μ.singularPart ν univ = μ'.singularPart ν' univ) :
    fDiv f μ ν = fDiv f μ' ν' := by
  rw [fDiv, fDiv, h_sing, h_eq]

end Congr

section MulAdd

lemma fDiv_smul (c : ℝ≥0) (μ ν : Measure α) : fDiv (c • f) μ ν = c * fDiv f μ ν := by
  rw [fDiv]
  simp only [DivFunction.smul_apply, DivFunction.derivAtTop_smul]
  rw [lintegral_const_mul _ measurable_divFunction_rnDeriv, fDiv, mul_add, ← mul_assoc]

/-- Scaling the second measure by `c ≠ 0` is the same as scaling the first by `c⁻¹` and
multiplying the divergence by `c`. -/
lemma fDiv_smul_right [SigmaFinite μ] [SigmaFinite ν] (c : ℝ≥0) (hc : c ≠ 0) :
    fDiv f μ (c • ν) = c * fDiv f (c⁻¹ • μ) ν := by
  have h : (fun x ↦ f ((∂μ/∂(c • ν)) x)) =ᵐ[ν] fun x ↦ f ((∂(c⁻¹ • μ)/∂ν) x) := by
    filter_upwards [Measure.rnDeriv_smul_right' μ ν hc, Measure.rnDeriv_smul_left' μ ν c⁻¹]
      with x hx hy
    rw [hx, hy]
  rw [fDiv, fDiv, lintegral_smul_measure, lintegral_congr_ae h,
    Measure.singularPart_smul_right _ _ _ hc, Measure.singularPart_smul,
    Measure.coe_nnreal_smul_apply, mul_add, ENNReal.smul_def, smul_eq_mul, ENNReal.coe_inv hc]
  congr 1
  rw [mul_left_comm (c : ℝ≥0∞), ← mul_assoc (c : ℝ≥0∞),
    ENNReal.mul_inv_cancel (by exact_mod_cast hc) ENNReal.coe_ne_top, one_mul]

lemma fDiv_add : fDiv (f + g) μ ν = fDiv f μ ν + fDiv g μ ν := by
  simp only [fDiv, DivFunction.add_apply, DivFunction.derivAtTop_add]
  rw [lintegral_add_left measurable_divFunction_rnDeriv]
  ring

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
    simp only [Pi.zero_apply, add_zero]
  simp [fDiv, lintegral_congr_ae h_ae, h1, h2]

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

/-- Decomposition of `fDiv f μ ν` according to the Lebesgue decomposition of `μ` with respect to
`ν`, in additive form: the term `f 0 * ν univ` accounts for the value of `f` at `0` on the singular
part. -/
lemma fDiv_add_eq_add_withDensity_singularPart
    (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν] :
    fDiv f μ ν + f 0 * ν .univ
      = fDiv f (ν.withDensity (∂μ/∂ν)) ν + fDiv f (μ.singularPart ν) ν := by
  rw [fDiv_of_mutuallySingular (μ.mutuallySingular_singularPart ν),
    fDiv_eq_add_withDensity_derivAtTop μ ν]
  ring

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
  simp only [Measure.coe_add, Pi.add_apply]
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
    · simp only [hf, false_or]
      exact fDiv_eq_top_iff_not_ac h hf
  · simp only [h, false_and, or_false]
    exact fDiv_eq_top_iff_of_derivAtTop_ne_top h

lemma fDiv_eq_top_iff' [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    fDiv f μ ν = ∞
      ↔ (f.derivAtTop = ∞ ∧ ¬ μ ≪ ν)
        ∨ ((f 0 = ∞ ∨ f.derivAtTop = ∞) ∧ ∫⁻ x, f ((∂μ/∂ν) x) ∂ν = ∞) := by
  by_cases h_top : f.derivAtTop = ∞
  · rw [fDiv_eq_top_iff]
    simp only [h_top, true_and]
    tauto
  by_cases h_zero : f 0 = ∞
  · rw [fDiv_eq_top_iff]
    simp [h_top, h_zero]
  simp only [h_top, false_and, h_zero, or_self, iff_false]
  exact fDiv_ne_top_of_derivAtTop_ne_top h_zero h_top

lemma fDiv_ne_top_iff [IsFiniteMeasure μ] [SigmaFinite ν] :
    fDiv f μ ν ≠ ∞
      ↔ (∫⁻ x, f ((∂μ/∂ν) x) ∂ν ≠ ∞) ∧ (f.derivAtTop = ∞ → μ ≪ ν) := by
  rw [ne_eq, fDiv_eq_top_iff]
  push Not
  rfl

lemma fDiv_ne_top_iff' [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    fDiv f μ ν ≠ ∞
      ↔ ((f.derivAtTop = ⊤ → μ ≪ ν)
        ∧ ((f 0 = ∞ ∨ f.derivAtTop = ∞) → ∫⁻ x, f ((∂μ/∂ν) x) ∂ν ≠ ∞)) := by
  rw [ne_eq, fDiv_eq_top_iff']
  push Not
  rfl

lemma lintegral_ne_top_of_fDiv_ne_top (h : fDiv f μ ν ≠ ⊤) :
    ∫⁻ x, f ((∂μ/∂ν) x) ∂ν ≠ ∞ := by
  by_contra h_not
  simp [fDiv, h_not] at h

lemma _root_.MeasureTheory.laverage_eq_average [IsFiniteMeasure μ] {f : α → ℝ≥0∞}
    (hf : AEMeasurable f μ) (hf_top : ∫⁻ a, f a ∂μ ≠ ⊤) :
    ⨍⁻ x, f x ∂μ = ENNReal.ofReal (⨍ x, (f x).toReal ∂μ) := by
  rw [laverage_eq, average_eq]
  by_cases hμ0 : μ = 0
  · simp [hμ0]
  simp only [smul_eq_mul, measureReal_def]
  rw [ENNReal.ofReal_mul (by simp),
    ENNReal.ofReal_inv_of_pos (by simp [ENNReal.toReal_pos_iff, hμ0]),
    ENNReal.ofReal_toReal (by simp), integral_toReal hf (ae_lt_top' hf hf_top),
    ENNReal.ofReal_toReal hf_top, div_eq_mul_inv, mul_comm]

lemma _root_.ConvexOn.map_laverage_le [IsFiniteMeasure μ] [NeZero μ]
    {f : α → ℝ≥0∞} {g : ℝ≥0∞ → ℝ≥0∞} {s : Set ℝ≥0∞}
    (hf : AEMeasurable f μ) (hfg : AEMeasurable (g ∘ f) μ)
    (hg : ConvexOn ℝ≥0 s g) (hgc : ContinuousOn g s) (hsc : IsClosed s)
    (hfs : ∀ᵐ x ∂μ, f x ∈ s) (hfi : ∫⁻ x, f x ∂μ ≠ ∞) :
    g (⨍⁻ x, f x ∂μ) ≤ ⨍⁻ x, g (f x) ∂μ := by
  by_cases hgi : ∫⁻ x, g (f x) ∂μ = ∞
  · conv_rhs => rw [laverage_eq, hgi]
    rw [ENNReal.top_div_of_ne_top (measure_ne_top _ _)]
    simp
  have hf_lt_top : ∀ᵐ x ∂μ, f x < ∞ := ae_lt_top' hf hfi
  have hg_lt_top : ∀ᵐ x ∂μ, g (f x) < ∞ := ae_lt_top' hfg hgi
  have hf_ofReal_toReal : ∀ᵐ x ∂μ, ENNReal.ofReal (f x).toReal = f x := by
    filter_upwards [hf_lt_top] with x hx
    rw [ENNReal.ofReal_toReal hx.ne]
  have h_avg_real : ⨍⁻ x, f x ∂μ = ENNReal.ofReal (⨍ x, (f x).toReal ∂μ) := by
    sorry
  rw [laverage_eq_average hf hfi]
  rw [← ENNReal.toReal_le_toReal]
  rotate_left
  · rw [← h_avg_real]
    sorry
  · simp only [laverage, lintegral_smul_measure, smul_eq_mul, ne_eq, ENNReal.mul_eq_top,
      ENNReal.inv_eq_zero, measure_ne_top, not_false_eq_true, hgi, and_false, ENNReal.inv_eq_top,
      Measure.measure_univ_eq_zero, false_or, not_and, Decidable.not_not]
    intro hμ
    simp [hμ]
  have hf_int : Integrable (fun x ↦ (f x).toReal) μ := integrable_toReal_of_lintegral_ne_top hf hfi
  have hg_int : Integrable ((fun x ↦ (g (ENNReal.ofReal x)).toReal)
      ∘ (fun x ↦ (f x).toReal)) μ := by
    have : ((fun x ↦ (g (ENNReal.ofReal x)).toReal) ∘ fun x ↦ (f x).toReal)
        =ᵐ[μ] fun x ↦ (g (f x)).toReal := by
      filter_upwards [hf_ofReal_toReal] with x hx
      simp [hx]
    rw [integrable_congr this]
    exact integrable_toReal_of_lintegral_ne_top hfg hgi
  refine (ConvexOn.map_average_le ?_ ?_ ?_ ?_ hf_int hg_int (s := ENNReal.toReal '' s)).trans ?_
  · sorry
  · sorry
  · sorry
  · filter_upwards [hfs] with a has using mem_image_of_mem _ has
  · sorry

lemma le_fDiv_of_ac' [IsFiniteMeasure μ] [IsProbabilityMeasure ν] (hμν : μ ≪ ν) :
    f (μ .univ) ≤ fDiv f μ ν := by
  rw [fDiv_of_absolutelyContinuous hμν]
  by_cases hf_int : ∫⁻ x, f ((∂μ/∂ν) x) ∂ν = ∞
  · simp [hf_int]
  calc f (μ .univ)
  _ = f (∫⁻ x, μ.rnDeriv ν x ∂ν) := by rw [Measure.lintegral_rnDeriv hμν]
  _ = f (⨍⁻ x, μ.rnDeriv ν x ∂ν) := by rw [laverage_eq_lintegral]
  _ ≤ ⨍⁻ x, f (μ.rnDeriv ν x) ∂ν := f.convexOn.map_laverage_le (μ.measurable_rnDeriv ν).aemeasurable
    (f.measurable.comp (μ.measurable_rnDeriv ν)).aemeasurable f.continuous.continuousOn
    isClosed_univ (ae_of_all _ fun _ ↦ by simp) (Measure.lintegral_rnDeriv_lt_top _ _).ne
  _ = ∫⁻ x, f (μ.rnDeriv ν x) ∂ν := by rw [laverage_eq_lintegral]

-- todo: remove `hf`
lemma le_fDiv_of_ac [IsFiniteMeasure μ] [IsProbabilityMeasure ν] (hμν : μ ≪ ν)
    (hf : ∀ x ≠ ∞, f x ≠ ∞) :
    f (μ .univ) ≤ fDiv f μ ν := by
  rw [fDiv_of_absolutelyContinuous hμν]
  by_cases hf_int : ∫⁻ x, f ((∂μ/∂ν) x) ∂ν = ∞
  · simp [hf_int]
  have h_eq : μ univ = ENNReal.ofReal (∫ x, (μ.rnDeriv ν x).toReal ∂ν) := by
    rw [Measure.integral_toReal_rnDeriv hμν, measureReal_def, ENNReal.ofReal_toReal]
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
  rw [lintegral_add_left', lintegral_indicator hs _, lintegral_indicator hs.compl _]
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

section OfReal

/-! ### f-divergences for a `DivFunction` given by `DivFunction.ofReal` -/

variable {f : ℝ → ℝ} {hf : ConvexOn ℝ (Ioi 0) f} {hf_one : f 1 = 0}

lemma fDiv_ofReal_of_not_integrable [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hf_nonneg : ∀ x, 0 ≤ x → 0 ≤ f x)
    (h : ¬ Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν) :
    fDiv (.ofReal f hf hf_one) μ ν = ∞ :=
  fDiv_of_lintegral_eq_top <|
    DivFunction.lintegral_ofReal_eq_top_of_not_integrable hf_nonneg h

lemma fDiv_ofReal_eq_integral_add [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hf_nonneg : ∀ x, 0 ≤ x → 0 ≤ f x) (h_cont : ContinuousWithinAt f (Ioi 0) 0)
    (h_int : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν) :
    fDiv (.ofReal f hf hf_one) μ ν
      = ENNReal.ofReal (∫ x, f ((∂μ/∂ν) x).toReal ∂ν)
        + (DivFunction.ofReal f hf hf_one).derivAtTop * μ.singularPart ν univ := by
  rw [fDiv, DivFunction.lintegral_ofReal_eq_integral_of_continuous hf_nonneg h_cont h_int]

lemma fDiv_ofReal_eq_top_iff_of_derivAtTop_eq_top [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hf_nonneg : ∀ x, 0 ≤ x → 0 ≤ f x) (h_cont : ContinuousWithinAt f (Ioi 0) 0)
    (h_top : (DivFunction.ofReal f hf hf_one).derivAtTop = ∞) :
    fDiv (.ofReal f hf hf_one) μ ν = ∞
      ↔ ¬ Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν ∨ ¬ μ ≪ ν := by
  by_cases h_int : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν
  · simp only [fDiv_ofReal_eq_integral_add hf_nonneg h_cont h_int, h_top, ENNReal.add_eq_top,
      ENNReal.ofReal_ne_top, ENNReal.mul_eq_top, ne_eq, ENNReal.top_ne_zero, not_false_eq_true,
      measure_ne_top, and_false, Measure.measure_univ_eq_zero, true_and, false_or, h_int,
      not_true_eq_false, Measure.singularPart_eq_zero]
  · simp [h_int, fDiv_ofReal_of_not_integrable hf_nonneg h_int]

lemma fDiv_ofReal_ne_top' [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h_zero : Function.rightLim (fun x ↦ ENNReal.ofReal (f x)) 0 ≠ ∞)
    (h_top : (DivFunction.ofReal f hf hf_one).derivAtTop ≠ ∞) :
    fDiv (.ofReal f hf hf_one) μ ν ≠ ∞ := by
  refine fDiv_ne_top_of_derivAtTop_ne_top ?_ h_top
  simp [h_zero]

lemma fDiv_ofReal_ne_top [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hf_nonneg : ∀ x, 0 ≤ x → 0 ≤ f x)
    (h_zero : Function.rightLim (fun x ↦ ENNReal.ofReal (f x)) 0 ≠ ∞)
    (h_top : limsup (fun x ↦ ENNReal.ofReal (rightDeriv f x)) atTop ≠ ∞) :
    fDiv (.ofReal f hf hf_one) μ ν ≠ ∞ :=
  fDiv_ofReal_ne_top' h_zero
    (DivFunction.derivAtTop_ofReal_ne_top (fun x hx ↦ hf_nonneg x hx.le) h_top)

lemma fDiv_ofReal_eq_integral_of_ac [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hf_nonneg : ∀ x, 0 ≤ x → 0 ≤ f x) (h_cont : ContinuousWithinAt f (Ioi 0) 0)
    (h_int : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν) (hμν : μ ≪ ν) :
    fDiv (.ofReal f hf hf_one) μ ν = ENNReal.ofReal (∫ x, f ((∂μ/∂ν) x).toReal ∂ν) := by
  rw [fDiv_ofReal_eq_integral_add hf_nonneg h_cont h_int, Measure.singularPart_eq_zero_of_ac hμν]
  simp

lemma fDiv_ofReal_eq_lintegral_of_ac [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hf_nonneg : ∀ x, 0 ≤ x → 0 ≤ f x) (h_cont : ContinuousWithinAt f (Ioi 0) 0)
    (h_int : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν) (hμν : μ ≪ ν) :
    fDiv (.ofReal f hf hf_one) μ ν
      = ∫⁻ x, ENNReal.ofReal (f ((∂μ/∂ν) x).toReal) ∂ν := by
  rw [fDiv_ofReal_eq_integral_of_ac hf_nonneg h_cont h_int hμν,
    ofReal_integral_eq_lintegral_ofReal h_int]
  exact ae_of_all _ fun x ↦ hf_nonneg _ ENNReal.toReal_nonneg

lemma toReal_fDiv_ofReal_eq_integral_add' [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hf_nonneg : ∀ x, 0 ≤ x → 0 ≤ f x) (h_cont : ContinuousWithinAt f (Ioi 0) 0)
    (h_int : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν)
    (h_ne : (DivFunction.ofReal f hf hf_one).derivAtTop ≠ ∞) :
    (fDiv (.ofReal f hf hf_one) μ ν).toReal
      = ∫ x, f ((∂μ/∂ν) x).toReal ∂ν
        + (DivFunction.ofReal f hf hf_one).derivAtTop.toReal * (μ.singularPart ν univ).toReal := by
  rw [fDiv_ofReal_eq_integral_add hf_nonneg h_cont h_int, ENNReal.toReal_add, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal]
  · exact integral_nonneg (fun _ ↦ hf_nonneg _ ENNReal.toReal_nonneg)
  · exact ENNReal.ofReal_ne_top
  · exact ENNReal.mul_ne_top h_ne (measure_ne_top _ _)

lemma toReal_fDiv_ofReal_eq_integral_add_of_ac [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hf_nonneg : ∀ x, 0 ≤ x → 0 ≤ f x) (h_cont : ContinuousWithinAt f (Ioi 0) 0)
    (h_int : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν)
    (h_ac : μ ≪ ν) :
    (fDiv (.ofReal f hf hf_one) μ ν).toReal = ∫ x, f ((∂μ/∂ν) x).toReal ∂ν := by
  rw [fDiv_ofReal_eq_integral_add hf_nonneg h_cont h_int]
  simp only [Measure.singularPart_eq_zero_of_ac h_ac, Measure.coe_zero, Pi.zero_apply, mul_zero,
    add_zero, ENNReal.toReal_ofReal_eq_iff]
  exact integral_nonneg fun x ↦ hf_nonneg _ ENNReal.toReal_nonneg

lemma toReal_fDiv_ofReal_eq_integral_add [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hf_nonneg : ∀ x, 0 ≤ x → 0 ≤ f x) (h_cont : ContinuousWithinAt f (Ioi 0) 0)
    (h_int : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν)
    (h_ne : limsup (fun x ↦ ENNReal.ofReal (rightDeriv f x)) atTop ≠ ∞) :
    (fDiv (.ofReal f hf hf_one) μ ν).toReal
      = ∫ x, f ((∂μ/∂ν) x).toReal ∂ν
        + (DivFunction.ofReal f hf hf_one).derivAtTop.toReal * (μ.singularPart ν univ).toReal := by
  rw [toReal_fDiv_ofReal_eq_integral_add' hf_nonneg h_cont h_int]
  exact DivFunction.derivAtTop_ofReal_ne_top (fun x hx ↦ hf_nonneg x hx.le) h_ne

end OfReal

end ProbabilityTheory
