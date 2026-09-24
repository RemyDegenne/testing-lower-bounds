/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
module

public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Probability.Notation
public import TestingLowerBounds.FDiv.DivFunction.OfReal
public import TestingLowerBounds.ForMathlib.RadonNikodym
public import Mathlib.MeasureTheory.Measure.Decomposition.IntegralRNDeriv

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

@[expose] public section

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

lemma fDiv_of_lintegral_eq_top (hf : ∫⁻ x, f ((∂μ/∂ν) x) ∂ν = ∞) : fDiv f μ ν = ∞ := by
  simp [fDiv, hf]

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
  simp [fDiv]

lemma fDiv_self (μ : Measure α) [SigmaFinite μ] : fDiv f μ μ = 0 := by
  have h : (fun x ↦ f (μ.rnDeriv μ x)) =ᵐ[μ] 0 := by
    filter_upwards [μ.rnDeriv_self] with x hx
    rw [hx, f.one]
    rfl
  simp [fDiv, lintegral_congr_ae h]

end SimpleValues

section Congr

/-- `fDiv f μ ν` depends on `f` only through its values on the range of `∂μ/∂ν` and through
`f.derivAtTop`. -/
lemma fDiv_congr (hfg : f =ᵐ[ν.map (∂μ/∂ν)] g) (hfg' : f.derivAtTop = g.derivAtTop) :
    fDiv f μ ν = fDiv g μ ν := by
  have h : (fun x ↦ f ((∂μ/∂ν) x)) =ᵐ[ν] fun x ↦ g ((∂μ/∂ν) x) :=
    ae_of_ae_map (μ.measurable_rnDeriv ν).aemeasurable hfg
  rw [fDiv, fDiv, hfg', lintegral_congr_ae h]

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

/-- Scaling both measures by the same constant scales the f-divergence. -/
lemma fDiv_smul_smul (c : ℝ≥0) (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν] :
    fDiv f (c • μ) (c • ν) = c * fDiv f μ ν := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  rw [fDiv_smul_right _ hc, smul_smul, inv_mul_cancel₀ hc, one_smul]

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

lemma fDiv_le_zero_add_top [SigmaFinite μ] [SigmaFinite ν] :
    fDiv f μ ν ≤ f 0 * ν .univ + f.derivAtTop * μ .univ := by
  simpa using fDiv_add_measure_le (f := f) 0 μ ν

end AddMeasure

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

lemma fDiv_ne_top_iff_ac [SigmaFinite μ] [SigmaFinite ν] (hf : f.derivAtTop = ∞)
    (h_int : ∫⁻ x, f ((∂μ/∂ν) x) ∂ν ≠ ∞) :
    fDiv f μ ν ≠ ∞ ↔ μ ≪ ν := by
  refine ⟨fun h ↦ ?_, fun h ↦ by rwa [fDiv_of_absolutelyContinuous h]⟩
  by_contra h_not_ac
  exact h (fDiv_of_not_ac hf h_not_ac)

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

lemma fDiv_eq_top_iff_of_derivAtTop_ne_top [IsFiniteMeasure μ] (hf : f.derivAtTop ≠ ∞) :
    fDiv f μ ν = ∞ ↔ ∫⁻ x, f ((∂μ/∂ν) x) ∂ν = ∞ := by
  simp [fDiv, ENNReal.mul_eq_top, hf]

lemma fDiv_ne_top_iff_of_derivAtTop_ne_top [IsFiniteMeasure μ] (hf : f.derivAtTop ≠ ∞) :
    fDiv f μ ν ≠ ∞ ↔ ∫⁻ x, f ((∂μ/∂ν) x) ∂ν ≠ ∞ :=
  (fDiv_eq_top_iff_of_derivAtTop_ne_top hf).not

lemma fDiv_ne_top_of_derivAtTop_ne_top [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h_zero : f 0 ≠ ∞) (h_top : f.derivAtTop ≠ ∞) :
    fDiv f μ ν ≠ ∞ :=
  (fDiv_ne_top_iff_of_derivAtTop_ne_top h_top).mpr
    (f.lintegral_comp_rnDeriv_ne_top μ ν h_zero h_top)

lemma fDiv_eq_top_iff [IsFiniteMeasure μ] [SigmaFinite ν] :
    fDiv f μ ν = ∞
      ↔ (∫⁻ x, f ((∂μ/∂ν) x) ∂ν = ∞) ∨ (f.derivAtTop = ∞ ∧ ¬ μ ≪ ν) := by
  simp [fDiv, ENNReal.mul_eq_top, Measure.singularPart_eq_zero]

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
      ↔ ((f.derivAtTop = ∞ → μ ≪ ν)
        ∧ ((f 0 = ∞ ∨ f.derivAtTop = ∞) → ∫⁻ x, f ((∂μ/∂ν) x) ∂ν ≠ ∞)) := by
  rw [ne_eq, fDiv_eq_top_iff']
  push Not
  rfl

lemma lintegral_ne_top_of_fDiv_ne_top (h : fDiv f μ ν ≠ ∞) :
    ∫⁻ x, f ((∂μ/∂ν) x) ∂ν ≠ ∞ :=
  fun h_eq ↦ h (fDiv_of_lintegral_eq_top h_eq)

/-- Jensen's inequality for a `DivFunction` and a probability measure. -/
theorem DivFunction.map_lintegral_le [IsProbabilityMeasure μ] {h : α → ℝ≥0∞} (hh : AEMeasurable h μ)
    (hhi : ∫⁻ x, h x ∂μ ≠ ∞) :
    f (∫⁻ x, h x ∂μ) ≤ ∫⁻ x, f (h x) ∂μ := by
  by_cases hJ : ∫⁻ x, f (h x) ∂μ = ∞
  · rw [hJ]
    exact le_top
  have hfh : AEMeasurable (fun x ↦ f (h x)) μ := f.measurable.comp_aemeasurable hh
  have h_lt_top : ∀ᵐ x ∂μ, h x < ∞ := ae_lt_top' hh hhi
  have hf_lt_top : ∀ᵐ x ∂μ, f (h x) < ∞ := ae_lt_top' hfh hJ
  have h_le_xmax : ∀ᵐ x ∂μ, h x ≤ f.xmax := by
    filter_upwards [hf_lt_top] with x hx
    by_contra h_gt
    exact hx.ne (f.eq_top_of_xmax_lt (not_le.mp h_gt))
  have h_xmin_le : ∀ᵐ x ∂μ, f.xmin ≤ h x := by
    filter_upwards [hf_lt_top] with x hx
    by_contra h_gt
    exact hx.ne (f.eq_top_of_lt_xmin (not_le.mp h_gt))
  set m := ∫⁻ x, h x ∂μ with hm
  -- integrated supporting-line inequality at any interior point
  have h_key : ∀ x ∈ Ioo f.xmin f.xmax,
      f x + ENNReal.ofReal (max (rightDeriv f.realFun x.toReal) 0) * m
          + ENNReal.ofReal (max (-rightDeriv f.realFun x.toReal) 0) * x
        ≤ (∫⁻ y, f (h y) ∂μ) + ENNReal.ofReal (max (rightDeriv f.realFun x.toReal) 0) * x
          + ENNReal.ofReal (max (-rightDeriv f.realFun x.toReal) 0) * m := by
    intro x hx
    have h_ae : ∀ᵐ y ∂μ, f x + ENNReal.ofReal (max (rightDeriv f.realFun x.toReal) 0) * h y
          + ENNReal.ofReal (max (-rightDeriv f.realFun x.toReal) 0) * x
        ≤ f (h y) + ENNReal.ofReal (max (rightDeriv f.realFun x.toReal) 0) * x
          + ENNReal.ofReal (max (-rightDeriv f.realFun x.toReal) 0) * h y := by
      filter_upwards [h_lt_top] with y hy
      exact f.apply_add_le_apply_add hx hy.ne
    have h_int := lintegral_mono_ae h_ae
    rwa [lintegral_add_right' _ aemeasurable_const, lintegral_add_left' aemeasurable_const,
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_const, lintegral_const,
      measure_univ, mul_one, mul_one, lintegral_add_right' _ (hh.const_mul _),
      lintegral_add_right' _ aemeasurable_const, lintegral_const, measure_univ, mul_one,
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at h_int
  have hm_le : m ≤ f.xmax := by
    calc m ≤ ∫⁻ _, f.xmax ∂μ := lintegral_mono_ae h_le_xmax
      _ = f.xmax := by simp
  have hm_ge : f.xmin ≤ m := by
    calc f.xmin = ∫⁻ _, f.xmin ∂μ := by simp
      _ ≤ m := lintegral_mono_ae h_xmin_le
  rcases lt_or_eq_of_le hm_le with hm_lt | hm_eq
  swap
  · -- `m = xmax`: impossible, since `h < xmax` a.e. and the measure is a probability measure
    exfalso
    have h_top : f.xmax ≠ ∞ := hm_eq ▸ hhi
    have h_lt : ∀ᵐ x ∂μ, h x < f.xmax := by
      filter_upwards [h_le_xmax, hf_lt_top] with x hx hx'
      refine lt_of_le_of_ne hx fun h_eq ↦ hx'.ne ?_
      rw [h_eq]
      exact f.apply_xmax_eq_top h_top
    have := lintegral_strict_mono (NeZero.ne μ) aemeasurable_const hhi h_lt
    simp only [lintegral_const, measure_univ, mul_one] at this
    exact this.ne hm_eq
  rcases lt_or_eq_of_le hm_ge with hm_gt | hm_eq
  swap
  · -- `m = xmin`: either `xmin = 0` and `h = 0` a.e., or `h > xmin` a.e., which is impossible
    by_cases h0 : f.xmin = 0
    · have hm0 : m = 0 := by rw [← hm_eq, h0]
      have h_zero : h =ᵐ[μ] 0 := (lintegral_eq_zero_iff' hh).mp hm0
      rw [hm0]
      refine le_of_eq ?_
      calc f 0 = ∫⁻ _, f 0 ∂μ := by simp
        _ = ∫⁻ y, f (h y) ∂μ := by
          refine lintegral_congr_ae ?_
          filter_upwards [h_zero] with y hy
          rw [hy, Pi.zero_apply]
    · exfalso
      have h_lt : ∀ᵐ x ∂μ, f.xmin < h x := by
        filter_upwards [h_xmin_le, hf_lt_top] with x hx hx'
        refine lt_of_le_of_ne hx fun h_eq ↦ hx'.ne ?_
        rw [← h_eq]
        exact f.apply_xmin_eq_top (pos_iff_ne_zero.mpr h0)
      have := lintegral_strict_mono (NeZero.ne μ) hh (by simp [xmin_ne_top]) h_lt
      simp only [lintegral_const, measure_univ, mul_one] at this
      exact this.ne hm_eq
  -- interior case: cancel the finite terms
  have h := h_key m ⟨hm_gt, hm_lt⟩
  rw [add_assoc, add_assoc] at h
  exact ENNReal.le_of_add_le_add_right (by finiteness) h

/-- Jensen's inequality for a `DivFunction` and a finite measure. -/
theorem DivFunction.map_laverage_le [IsFiniteMeasure μ] [NeZero μ] {h : α → ℝ≥0∞}
    (hh : AEMeasurable h μ) (hhi : ∫⁻ x, h x ∂μ ≠ ∞) :
    f (⨍⁻ x, h x ∂μ) ≤ ⨍⁻ x, f (h x) ∂μ := by
  rw [laverage_eq', laverage_eq']
  refine f.map_lintegral_le (hh.smul_measure _) ?_
  rw [lintegral_smul_measure, smul_eq_mul]
  exact ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr (NeZero.ne _)) hhi

/-- Jensen-type lower bound on `fDiv` for absolutely continuous measures. -/
lemma le_fDiv_of_ac [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμν : μ ≪ ν) :
    ν .univ * f (μ .univ / ν .univ) ≤ fDiv f μ ν := by
  rcases eq_zero_or_neZero ν with rfl | hν
  · simp
  rw [fDiv_of_absolutelyContinuous hμν, ← Measure.lintegral_rnDeriv hμν, ← laverage_eq]
  calc ν .univ * f (⨍⁻ x, (∂μ/∂ν) x ∂ν)
  _ ≤ ν .univ * ⨍⁻ x, f ((∂μ/∂ν) x) ∂ν := by
    gcongr
    exact f.map_laverage_le (μ.measurable_rnDeriv ν).aemeasurable
      (Measure.lintegral_rnDeriv_lt_top _ _).ne
  _ = ∫⁻ x, f ((∂μ/∂ν) x) ∂ν := by
    rw [laverage_eq, ENNReal.mul_div_cancel (by simp [NeZero.ne ν]) (measure_ne_top _ _)]

/-- Jensen-type lower bound on `fDiv`. For probability measures, it reads
`f (μ univ) ≤ fDiv f μ ν`. -/
lemma le_fDiv [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    ν .univ * f (μ .univ / ν .univ) ≤ fDiv f μ ν := by
  rcases eq_zero_or_neZero ν with rfl | hν
  · simp
  have hμ : μ .univ = ν.withDensity (∂μ/∂ν) .univ + μ.singularPart ν .univ := by
    conv_lhs => rw [μ.haveLebesgueDecomposition_add ν, add_comm]
    simp
  calc ν .univ * f (μ .univ / ν .univ)
  _ ≤ ν .univ * (f (ν.withDensity (∂μ/∂ν) .univ / ν .univ)
      + f.derivAtTop * (μ.singularPart ν .univ / ν .univ)) := by
    rw [hμ, ENNReal.add_div]
    gcongr
    exact f.le_add_derivAtTop'' _ _
  _ = ν .univ * f (ν.withDensity (∂μ/∂ν) .univ / ν .univ)
      + f.derivAtTop * μ.singularPart ν .univ := by
    rw [mul_add, mul_left_comm (ν .univ),
      ENNReal.mul_div_cancel (by simp [NeZero.ne ν]) (measure_ne_top _ _)]
  _ ≤ fDiv f (ν.withDensity (∂μ/∂ν)) ν + f.derivAtTop * μ.singularPart ν .univ := by
    gcongr
    exact le_fDiv_of_ac (withDensity_absolutelyContinuous _ _)
  _ = fDiv f μ ν := (fDiv_eq_add_withDensity_derivAtTop μ ν).symm

lemma fDiv_mono'' (hfg : f ≤ᵐ[ν.map (∂μ/∂ν)] g) (hfg' : f.derivAtTop ≤ g.derivAtTop) :
    fDiv f μ ν ≤ fDiv g μ ν := by
  rw [fDiv, fDiv]
  refine add_le_add (lintegral_mono_ae ?_) (by gcongr)
  exact ae_of_ae_map (μ.measurable_rnDeriv ν).aemeasurable hfg

lemma fDiv_mono' (hfg : ∀ x, f x ≤ g x) (hfg' : f.derivAtTop ≤ g.derivAtTop) :
    fDiv f μ ν ≤ fDiv g μ ν :=
  fDiv_mono'' (.of_forall hfg) hfg'

/-- If `f ≤ g` then `fDiv f μ ν ≤ fDiv g μ ν`. -/
lemma fDiv_mono (hfg : ∀ x, f x ≤ g x) : fDiv f μ ν ≤ fDiv g μ ν :=
  fDiv_mono' hfg (DivFunction.derivAtTop_mono hfg)

/-- For a strictly convex divergence function, `fDiv f μ ν = 0 ↔ μ = ν`. -/
lemma fDiv_eq_zero_iff [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hf_cvx : StrictConvexOn ℝ (Ioi 0) f.realFun) :
    fDiv f μ ν = 0 ↔ μ = ν := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ fDiv_self _⟩
  have h_eq_zero_iff x : f x = 0 ↔ x = 1 := by
    rw [f.eq_zero_iff zero_lt_one one_lt_two]
    exact hf_cvx.subset (fun x hx ↦ hx.1) (convex_Ioo _ _)
  -- by strict convexity, `f 2 ≠ 0`, hence `f.derivAtTop ≠ 0`
  have h_deriv : f.derivAtTop ≠ 0 := by
    intro h0
    have h2 := f.apply_le_derivAtTop_mul (y := 2) one_le_two
    rw [h0, zero_mul, nonpos_iff_eq_zero, h_eq_zero_iff] at h2
    norm_num at h2
  rw [fDiv, add_eq_zero, mul_eq_zero, lintegral_eq_zero_iff measurable_divFunction_rnDeriv] at h
  have hμν : μ ≪ ν := by
    rw [← Measure.singularPart_eq_zero]
    simpa [h_deriv] using h.2
  refine (Measure.rnDeriv_eq_one_iff_eq hμν).mp ?_
  filter_upwards [h.1] with x hx
  simpa [h_eq_zero_iff] using hx

lemma fDiv_map_measurableEmbedding [SigmaFinite μ] [SigmaFinite ν]
    {g : α → β} (hg : MeasurableEmbedding g) :
    fDiv f (μ.map g) (ν.map g) = fDiv f μ ν := by
  rw [fDiv, fDiv, hg.lintegral_map]
  congr 1
  · refine lintegral_congr_ae ?_
    filter_upwards [hg.rnDeriv_map μ ν] with a ha using ha ▸ rfl
  · rw [hg.singularPart_map μ ν, hg.map_apply, preimage_univ]

section Restrict

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
  rw [fDiv, μ.singularPart_restrict ν hs, Measure.restrict_apply_univ, lintegral_congr_ae h,
    lintegral_piecewise hs, setLIntegral_const]

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

section OfReal

/-! ### f-divergences for a `DivFunction` given by `DivFunction.ofReal` -/

variable {f : ℝ → ℝ} {hf : ConvexOn ℝ (Ioi 0) f} {hf_one : f 1 = 0}

lemma fDiv_ofReal_of_not_integrable [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hf_nonneg : ∀ x, 0 ≤ x → 0 ≤ f x)
    (h : ¬ Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν) :
    fDiv (.ofReal f hf hf_one) μ ν = ∞ :=
  fDiv_of_lintegral_eq_top <|
    DivFunction.lintegral_ofReal_eq_top_of_not_integrable hf_nonneg h

lemma fDiv_ofReal_eq_integral_add [IsFiniteMeasure μ]
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

lemma fDiv_ofReal_eq_integral_of_ac [IsFiniteMeasure μ]
    (hf_nonneg : ∀ x, 0 ≤ x → 0 ≤ f x) (h_cont : ContinuousWithinAt f (Ioi 0) 0)
    (h_int : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν) (hμν : μ ≪ ν) :
    fDiv (.ofReal f hf hf_one) μ ν = ENNReal.ofReal (∫ x, f ((∂μ/∂ν) x).toReal ∂ν) := by
  rw [fDiv_ofReal_eq_integral_add hf_nonneg h_cont h_int, Measure.singularPart_eq_zero_of_ac hμν]
  simp

lemma fDiv_ofReal_eq_lintegral_of_ac [IsFiniteMeasure μ]
    (hf_nonneg : ∀ x, 0 ≤ x → 0 ≤ f x) (h_cont : ContinuousWithinAt f (Ioi 0) 0)
    (h_int : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν) (hμν : μ ≪ ν) :
    fDiv (.ofReal f hf hf_one) μ ν
      = ∫⁻ x, ENNReal.ofReal (f ((∂μ/∂ν) x).toReal) ∂ν := by
  rw [fDiv_ofReal_eq_integral_of_ac hf_nonneg h_cont h_int hμν,
    ofReal_integral_eq_lintegral_ofReal h_int]
  exact ae_of_all _ fun x ↦ hf_nonneg _ ENNReal.toReal_nonneg

lemma toReal_fDiv_ofReal_eq_integral_add [IsFiniteMeasure μ]
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

lemma toReal_fDiv_ofReal_eq_integral_add_of_ac [IsFiniteMeasure μ]
    (hf_nonneg : ∀ x, 0 ≤ x → 0 ≤ f x) (h_cont : ContinuousWithinAt f (Ioi 0) 0)
    (h_int : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν)
    (h_ac : μ ≪ ν) :
    (fDiv (.ofReal f hf hf_one) μ ν).toReal = ∫ x, f ((∂μ/∂ν) x).toReal ∂ν := by
  rw [fDiv_ofReal_eq_integral_of_ac hf_nonneg h_cont h_int h_ac,
    ENNReal.toReal_ofReal (integral_nonneg fun _ ↦ hf_nonneg _ ENNReal.toReal_nonneg)]

end OfReal

end ProbabilityTheory
