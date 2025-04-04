/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import TestingLowerBounds.FDiv.Basic
import TestingLowerBounds.FDiv.IntegralRnDerivSingularPart
import TestingLowerBounds.MeasureCompProd
/-!

# f-Divergences of composition products: infinite values

We determine when `fDiv f (μ ⊗ₘ κ) (ν ⊗ₘ κ)` is infinite, with special attention given to the
case `ν = μ`, which is linked to the conditional divergence.
Every measure and kernel are supposed finite.

Recall `fDiv_ne_top_iff'`:
`fDiv f μ ν ≠ ⊤ ↔ f.derivAtTop = ⊤ → (Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν ∧ μ ≪ ν)`

If `f.derivAtTop ≠ ⊤` then `fDiv f μ ν ≠ ⊤`.

If `f.derivAtTop = ⊤`, then `fDiv f (μ ⊗ₘ κ) (ν ⊗ₘ κ) = ⊤` unless
* `μ ⊗ₘ κ ≪ ν ⊗ₘ κ`. That's equivalent to `μ ≪ ν` and `μ ⊗ₘ κ ≪ μ ⊗ₘ κ`.
* `Integrable (fun x ↦ f ((∂(μ ⊗ₘ κ)/∂(ν ⊗ₘ κ)) x).toReal) (ν ⊗ₘ κ)`.
  TODO

-/

open Real MeasureTheory Filter MeasurableSpace Set

open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {μ ν : Measure α} {κ η : Kernel α β} {f g : DivFunction}

section CompProd

-- todo: right vs left is inconsistent in the fDiv_compProd names
@[simp]
lemma fDiv_compProd_right (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ : Kernel α β) [IsMarkovKernel κ] :
    fDiv f (μ ⊗ₘ κ) (ν ⊗ₘ κ) = fDiv f μ ν := by
  refine fDiv_congr_measure ?_ ?_
  · have h_eq : (fun x ↦ f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ κ) x))
        =ᵐ[ν ⊗ₘ κ] fun x ↦ f ((∂μ/∂ν) x.1) := by
      filter_upwards [Kernel.rnDeriv_measure_compProd_left μ ν κ] with x hx
      rw [hx]
    rw [lintegral_congr_ae h_eq, Measure.lintegral_compProd]
    · simp
    · exact measurable_divFunction_rnDeriv.comp measurable_fst
  · rw [singularPart_compProd_left, Measure.compProd_apply_univ]

lemma fDiv_compProd_ne_top_iff''' [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [IsFiniteKernel κ] [∀ a, NeZero (κ a)] [IsFiniteKernel η] :
    fDiv f (μ ⊗ₘ κ) (ν ⊗ₘ η) ≠ ∞
      ↔ (f.derivAtTop = ∞ → μ ⊗ₘ κ ≪ ν ⊗ₘ η)
        ∧ (f 0 = ∞ ∨ f.derivAtTop = ∞ → ∫⁻ a, ∫⁻ b, f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) (a, b)) ∂η a ∂ν ≠ ∞) := by
  rw [fDiv_ne_top_iff', Measure.lintegral_compProd measurable_divFunction_rnDeriv]

lemma fDiv_compProd_ne_top_iff'' [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [IsFiniteKernel κ] [∀ a, NeZero (κ a)] [IsFiniteKernel η] (h_zero : f 0 ≠ ∞) :
    fDiv f (μ ⊗ₘ κ) (ν ⊗ₘ η) ≠ ∞
      ↔ f.derivAtTop = ∞
        → (∫⁻ a, ∫⁻ b, f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) (a, b)) ∂η a ∂ν ≠ ∞ ∧ μ ⊗ₘ κ ≪ ν ⊗ₘ η) := by
  rw [fDiv_compProd_ne_top_iff''']
  simp only [h_zero, false_or, ne_eq]
  tauto

lemma fDiv_compProd_ne_top_iff'_of_ac [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [IsFiniteKernel κ] [∀ a, NeZero (κ a)] [IsFiniteKernel η] (h_ac : μ ⊗ₘ κ ≪ μ ⊗ₘ η) :
    fDiv f (μ ⊗ₘ κ) (ν ⊗ₘ η) ≠ ∞
      ↔ (f.derivAtTop = ∞ → μ ⊗ₘ κ ≪ ν ⊗ₘ η)
        ∧ (f 0 = ∞ ∨ f.derivAtTop = ∞
          → ∫⁻ a, ∫⁻ b, f ((∂μ/∂ν) a * (∂(μ ⊗ₘ κ)/∂(μ ⊗ₘ η)) (a, b)) ∂(η a) ∂ν ≠ ∞) := by
  rw [fDiv_compProd_ne_top_iff''']
  suffices ∫⁻ a, ∫⁻ b, f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) (a, b)) ∂η a ∂ν
      = ∫⁻ a, ∫⁻ b, f ((∂μ/∂ν) a * (∂(μ ⊗ₘ κ)/∂(μ ⊗ₘ η)) (a, b)) ∂η a ∂ν by
    rw [this]
  have h_eq := Kernel.rnDeriv_compProd' h_ac ν
  refine lintegral_congr_ae ?_
  filter_upwards [h_eq] with a ha
  refine lintegral_congr_ae ?_
  filter_upwards [ha] with b hb
  rw [hb]

-- todo : h_zero
lemma fDiv_compProd_ne_top_iff' [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [IsFiniteKernel κ] [∀ a, NeZero (κ a)] [IsFiniteKernel η] (h_zero : f 0 ≠ ∞) :
    fDiv f (μ ⊗ₘ κ) (ν ⊗ₘ η) ≠ ∞ ↔
      f.derivAtTop = ∞ →
      (∫⁻ a, ∫⁻ b, f ((∂μ/∂ν) a * (∂(μ ⊗ₘ κ)/∂(μ ⊗ₘ η)) (a, b)) ∂(η a) ∂ν ≠ ∞
        ∧ μ ⊗ₘ κ ≪ ν ⊗ₘ η) := by
  rw [fDiv_compProd_ne_top_iff'' h_zero]
  by_cases h_top : f.derivAtTop = ∞
  swap; · simp [h_top]
  simp only [h_top, true_implies, and_congr_left_iff]
  intro h_ac'
  have h_ac : μ ⊗ₘ κ ≪ μ ⊗ₘ η := Measure.absolutelyContinuous_compProd_of_compProd' h_ac'
  suffices ∫⁻ a, ∫⁻ b, f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) (a, b)) ∂η a ∂ν
      = ∫⁻ a, ∫⁻ b, f ((∂μ/∂ν) a * (∂(μ ⊗ₘ κ)/∂(μ ⊗ₘ η)) (a, b)) ∂η a ∂ν by
    rw [this]
  have h_eq := Kernel.rnDeriv_compProd' h_ac ν
  refine lintegral_congr_ae ?_
  filter_upwards [h_eq] with a ha
  refine lintegral_congr_ae ?_
  filter_upwards [ha] with b hb
  rw [hb]

lemma fDiv_compProd_eq_top_iff'' [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [IsFiniteKernel κ] [∀ a, NeZero (κ a)] [IsFiniteKernel η] (h_zero : f 0 ≠ ∞) :
    fDiv f (μ ⊗ₘ κ) (ν ⊗ₘ η) = ∞ ↔
      f.derivAtTop = ∞
      ∧ (∫⁻ a, ∫⁻ b, f ((∂(μ ⊗ₘ κ)/∂(ν ⊗ₘ η)) (a, b)) ∂η a ∂ν ≠ ∞ → μ ≪ ν →
          ¬ μ ⊗ₘ κ ≪ μ ⊗ₘ η) := by
  rw [← not_iff_not, ← ne_eq, fDiv_compProd_ne_top_iff'' h_zero,
    Measure.absolutelyContinuous_compProd_iff']
  push_neg
  rfl

lemma fDiv_compProd_eq_top_iff' [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [IsFiniteKernel κ] [∀ a, NeZero (κ a)] [IsFiniteKernel η] (h_zero : f 0 ≠ ∞) :
    fDiv f (μ ⊗ₘ κ) (ν ⊗ₘ η) = ∞ ↔
      f.derivAtTop = ∞
      ∧ (∫⁻ a, ∫⁻ b, f ((∂μ/∂ν) a * (∂(μ ⊗ₘ κ)/∂(μ ⊗ₘ η)) (a, b)) ∂η a ∂ν ≠ ∞ → μ ≪ ν →
          ¬ μ ⊗ₘ κ ≪ μ ⊗ₘ η) := by
  rw [← not_iff_not, ← ne_eq, fDiv_compProd_ne_top_iff' h_zero,
    Measure.absolutelyContinuous_compProd_iff']
  push_neg
  rfl

lemma fDiv_compProd_right_ne_top_iff' [IsFiniteMeasure μ]
    [IsFiniteKernel κ] [∀ a, NeZero (κ a)] [IsFiniteKernel η] (h_zero : f 0 ≠ ∞) :
    fDiv f (μ ⊗ₘ κ) (μ ⊗ₘ η) ≠ ∞ ↔
      f.derivAtTop = ∞ →
      (∫⁻ a, ∫⁻ b, f ((∂(μ ⊗ₘ κ)/∂(μ ⊗ₘ η)) (a, b)) ∂(η a) ∂μ ≠ ∞ ∧ μ ⊗ₘ κ ≪ μ ⊗ₘ η) := by
  rw [fDiv_compProd_ne_top_iff'' h_zero]

lemma fDiv_compProd_right_eq_top_iff' [IsFiniteMeasure μ]
    [IsFiniteKernel κ] [∀ a, NeZero (κ a)] [IsFiniteKernel η] (h_zero : f 0 ≠ ∞) :
    fDiv f (μ ⊗ₘ κ) (μ ⊗ₘ η) = ∞ ↔
      f.derivAtTop = ∞
      ∧ (∫⁻ a, ∫⁻ b, f ((∂(μ ⊗ₘ κ)/∂(μ ⊗ₘ η)) (a, b)) ∂η a ∂μ ≠ ∞ → ¬ μ ⊗ₘ κ ≪ μ ⊗ₘ η) := by
  rw [← not_iff_not, ← ne_eq, fDiv_compProd_right_ne_top_iff' h_zero]
  push_neg
  rfl

variable [CountableOrCountablyGenerated α β]

lemma fDiv_compProd_ne_top_iff [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [IsFiniteKernel κ] [∀ a, NeZero (κ a)] [IsFiniteKernel η] :
    fDiv f (μ ⊗ₘ κ) (ν ⊗ₘ η) ≠ ∞ ↔
      ∫⁻ a, ∫⁻ b, f ((∂μ/∂ν) a * (∂κ a/∂η a) b) ∂(η a) ∂ν ≠ ∞
        ∧ (f.derivAtTop = ∞ → μ ≪ ν ∧ ∀ᵐ a ∂μ, κ a ≪ η a) := by
  rw [fDiv_ne_top_iff, Measure.absolutelyContinuous_compProd_iff,
    Measure.lintegral_compProd measurable_divFunction_rnDeriv]
  suffices ∫⁻ a, ∫⁻ b, f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) (a, b)) ∂η a ∂ν
      = ∫⁻ a, ∫⁻ b, f ((∂μ/∂ν) a * (∂κ a/∂η a) b) ∂(η a) ∂ν by
    rw [this]
  have h_eq := Kernel.rnDeriv_measure_compProd' μ ν κ η
  refine lintegral_congr_ae ?_
  filter_upwards [h_eq] with a ha
  refine lintegral_congr_ae ?_
  filter_upwards [ha] with b hb
  rw [hb]

lemma fDiv_compProd_eq_top_iff [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [IsFiniteKernel κ] [∀ a, NeZero (κ a)] [IsFiniteKernel η] :
    fDiv f (μ ⊗ₘ κ) (ν ⊗ₘ η) = ∞ ↔
      ∫⁻ a, ∫⁻ b, f ((∂μ/∂ν) a * (∂κ a/∂η a) b) ∂η a ∂ν ≠ ∞ →
        f.derivAtTop = ∞ ∧ (μ ≪ ν → ¬∀ᵐ a ∂μ, κ a ≪ η a) := by
  rw [← not_iff_not, ← ne_eq, fDiv_compProd_ne_top_iff]
  push_neg
  rfl

lemma fDiv_compProd_right_ne_top_iff [IsFiniteMeasure μ]
    [IsFiniteKernel κ] [∀ a, NeZero (κ a)] [IsFiniteKernel η] :
    fDiv f (μ ⊗ₘ κ) (μ ⊗ₘ η) ≠ ∞ ↔
      ∫⁻ a, ∫⁻ b, f ((∂κ a/∂η a) b) ∂(η a) ∂μ ≠ ∞ ∧ (f.derivAtTop = ∞ → ∀ᵐ a ∂μ, κ a ≪ η a) := by
  rw [fDiv_compProd_ne_top_iff]
  have h_self := μ.rnDeriv_self
  have h_eq : ∫⁻ a, ∫⁻ b, f ((∂μ/∂μ) a * (∂κ a/∂η a) b) ∂η a ∂μ
      = ∫⁻ a, ∫⁻ b, f ((∂κ a/∂η a) b) ∂η a ∂μ := by
    refine lintegral_congr_ae ?_
    filter_upwards [h_self] with a h_one
    simp_rw [h_one, one_mul]
  refine ⟨fun h ↦ ⟨?_, ?_⟩, fun h ↦ ⟨?_, ?_⟩⟩
  · rw [← h_eq]
    exact h.1
  · exact fun h_top ↦ (h.2 h_top).2
  · rw [h_eq]
    exact h.1
  · exact fun h_top ↦ ⟨Measure.AbsolutelyContinuous.rfl, h.2 h_top⟩

lemma fDiv_compProd_right_eq_top_iff [IsFiniteMeasure μ]
    [IsFiniteKernel κ] [∀ a, NeZero (κ a)] [IsFiniteKernel η] :
    fDiv f (μ ⊗ₘ κ) (μ ⊗ₘ η) = ∞ ↔
      ∫⁻ a, ∫⁻ b, f ((∂κ a/∂η a) b) ∂η a ∂μ ≠ ∞ → f.derivAtTop = ∞ ∧ ¬∀ᵐ a ∂μ, κ a ≪ η a := by
  rw [← not_iff_not, ← ne_eq, fDiv_compProd_right_ne_top_iff]
  push_neg
  rfl

end CompProd

lemma f_rnDeriv_le_add [CountableOrCountablyGenerated α β]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ η : Kernel α β) [IsMarkovKernel κ] [IsFiniteKernel η]
    (h_deriv : f.derivAtTop = ∞ → ∀ᵐ a ∂μ, κ a ≪ η a) :
    ∀ᵐ a ∂ ν, f ((∂μ/∂ν) a)
      ≤ f ((∂μ/∂ν) a * η.withDensity (κ.rnDeriv η) a .univ)
        + f.derivAtTop * ((∂μ/∂ν) a) * (κ.singularPart η a .univ) := by
  by_cases h_deriv_top : f.derivAtTop = ∞
  · simp only [ENNReal.toReal_mul, h_deriv_top, EReal.toReal_top, zero_mul, add_zero]
    have h_ae : ∀ᵐ a ∂ν, (∂μ/∂ν) a ≠ 0 → η.withDensity (κ.rnDeriv η) a = κ a := by
      refine Measure.ae_rnDeriv_ne_zero_imp_of_ae ?_
      filter_upwards [h_deriv h_deriv_top] with a ha_ac
      rw [Kernel.withDensity_rnDeriv_eq ha_ac]
    filter_upwards [h_ae] with a ha
    by_cases h0 : (∂μ/∂ν) a = 0
    · simp [h0]
    · rw [ha h0]
      simp
  refine ae_of_all _ fun a ↦ ?_
  let κ' := η.withDensity (κ.rnDeriv η)
  calc f ((∂μ/∂ν) a)
  _ ≤ f ((∂μ/∂ν) a * κ' a .univ)
        + f.derivAtTop * (∂μ/∂ν) a * (1 - κ' a .univ) := by
      refine f.le_add_derivAtTop' _ ?_
      calc κ' a .univ
      _ ≤ κ a .univ := by
          exact κ.withDensity_rnDeriv_le η a .univ
      _ = 1 := by simp
  _ = f ((∂μ/∂ν) a * κ' a .univ)
        + f.derivAtTop * (∂μ/∂ν) a * κ.singularPart η a .univ := by
      congr
      norm_cast
      unfold_let κ'
      refine ENNReal.sub_eq_of_eq_add (measure_ne_top _ _) ?_
      rw [← measure_univ (μ := κ a)]
      conv_lhs => rw [← κ.rnDeriv_add_singularPart η, add_comm]
      simp only [Kernel.coe_add, Pi.add_apply, Measure.coe_add]

lemma f_rnDeriv_ae_le_lintegral [CountableOrCountablyGenerated α β]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ η : Kernel α β) [IsFiniteKernel κ] [IsMarkovKernel η]
    (h_int : ∫⁻ p, f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) p) ∂(ν ⊗ₘ η) ≠ ∞)
    (hκη : ∀ᵐ a ∂μ, κ a ≪ η a) :
    (fun a ↦ f ((∂μ/∂ν) a * κ a .univ))
      ≤ᵐ[ν] fun a ↦ ∫⁻ b, f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) (a, b)) ∂(η a) := by
  have h_compProd := Kernel.rnDeriv_measure_compProd' μ ν κ η
  have h_lt_top := Measure.ae_ae_of_ae_compProd <| (μ ⊗ₘ κ).rnDeriv_lt_top (ν ⊗ₘ η)
  have h_int' := integrable_realFun_rnDeriv h_int
  have := Measure.integrable_toReal_rnDeriv (μ := μ ⊗ₘ κ) (ν := ν ⊗ₘ η)
  rw [Measure.integrable_compProd_iff] at this
  swap
  · refine (Measurable.stronglyMeasurable ?_).aestronglyMeasurable
    exact (Measure.measurable_rnDeriv _ _).ennreal_toReal
  have hκη' : ∀ᵐ a ∂ν, (∂μ/∂ν) a ≠ 0 → κ a ≪ η a := Measure.ae_rnDeriv_ne_zero_imp_of_ae hκη
  filter_upwards [hκη', h_compProd, h_lt_top, this.1, h_int'.compProd_mk_left_ae']
    with a h_ac h_eq h_lt_top h_rnDeriv_int h_int'
  calc f ((∂μ/∂ν) a * κ a .univ)
    = f ((∂μ/∂ν) a * ∫⁻ b, (∂κ a/∂η a) b ∂η a) := by
        by_cases h0 : (∂μ/∂ν) a = 0
        · simp [h0]
        · rw [Measure.lintegral_rnDeriv (h_ac h0)]
  _ = f (∫⁻ b,(∂μ/∂ν) a * (∂κ a/∂η a) b ∂η a) := by
        rw [lintegral_const_mul _ ((κ a).measurable_rnDeriv _)]
  _ = f (∫⁻ b, (∂μ ⊗ₘ κ/∂ν ⊗ₘ η) (a, b) ∂η a) := by rw [lintegral_congr_ae h_eq]
  _ = f (ENNReal.ofReal (∫ b, ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) (a, b)).toReal ∂η a)) := by
        rw [integral_toReal _ h_lt_top]
        · sorry
        · exact ((Measure.measurable_rnDeriv _ _).comp measurable_prod_mk_left).aemeasurable
  _ = ENNReal.ofReal (f.realFun (∫ b, ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) (a, b)).toReal ∂η a)) := by
        rw [DivFunction.realFun, ENNReal.ofReal_toReal]
        sorry
  _ ≤ ENNReal.ofReal (∫ b, f.realFun ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) (a, b)).toReal ∂η a) := by
        rw [← average_eq_integral, ← average_eq_integral]
        refine ENNReal.ofReal_le_ofReal ?_
        refine ConvexOn.map_average_le ?_ ?_ (isClosed_Ici (a := 0)) ?_ h_rnDeriv_int h_int'
        · sorry
        · sorry
        · exact ae_of_all _ fun _ ↦ ENNReal.toReal_nonneg
  _ = ∫⁻ b, f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) (a, b)) ∂η a := sorry

lemma integrable_f_rnDeriv_mul_kernel [CountableOrCountablyGenerated α β]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ η : Kernel α β) [IsFiniteKernel κ] [IsMarkovKernel η]
    (h_int : ∫⁻ p, f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) p) ∂(ν ⊗ₘ η) ≠ ∞)
    (hκη : ∀ᵐ a ∂μ, κ a ≪ η a) :
    ∫⁻ a, f ((∂μ/∂ν) a * κ a .univ) ∂ν ≠ ∞ := by
  have h_int_le := lintegral_mono_ae (f_rnDeriv_ae_le_lintegral μ ν κ η h_int hκη)
  refine (h_int_le.trans_lt (lt_top_iff_ne_top.mpr ?_)).ne
  rwa [Measure.lintegral_compProd measurable_divFunction_rnDeriv] at h_int

lemma integrable_f_rnDeriv_mul_withDensity [CountableOrCountablyGenerated α β]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ η : Kernel α β) [IsFiniteKernel κ] [IsMarkovKernel η]
    (h_int : ∫⁻ p, f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) p) ∂(ν ⊗ₘ η) ≠ ∞) :
    ∫⁻ a, f ((∂μ/∂ν) a * η.withDensity (κ.rnDeriv η) a .univ) ∂ν ≠ ∞ := by
  refine integrable_f_rnDeriv_mul_kernel μ ν _ η ?_ ?_
  · have h_eq := Measure.rnDeriv_measure_compProd_Kernel_withDensity μ ν κ η
    suffices ∫⁻ p, f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) p) ∂ν ⊗ₘ η
        = ∫⁻ p, f ((∂μ ⊗ₘ η.withDensity (κ.rnDeriv η)/∂ν ⊗ₘ η) p) ∂ν ⊗ₘ η by
      rwa [← this]
    refine lintegral_congr_ae ?_
    filter_upwards [h_eq] with x hx
    rw [hx]
  · exact ae_of_all _ (fun _ ↦ Kernel.withDensity_absolutelyContinuous _ _)

lemma integrable_f_rnDeriv_of_integrable_compProd' [CountableOrCountablyGenerated α β]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ η : Kernel α β) [IsMarkovKernel κ] [IsMarkovKernel η]
    (hf_int : ∫⁻ p, f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) p) ∂(ν ⊗ₘ η) ≠ ∞)
    (h_deriv : f.derivAtTop = ∞ → ∀ᵐ a ∂μ, κ a ≪ η a) :
    ∫⁻ x, f ((∂μ/∂ν) x) ∂ν ≠ ∞ := by
  have h_int_le := lintegral_mono_ae (f_rnDeriv_le_add μ ν κ η h_deriv)
  refine (h_int_le.trans_lt ?_).ne
  have h_meas : Measurable fun a ↦ f.derivAtTop * (∂μ/∂ν) a * ((κ.singularPart η) a) univ := by
    simp_rw [mul_assoc]
    refine Measurable.const_mul ?_ f.derivAtTop
    exact (μ.measurable_rnDeriv ν).mul (Kernel.measurable_coe _ .univ)
  rw [lintegral_add_right _ h_meas]
  simp only [ENNReal.add_lt_top]
  simp_rw [lt_top_iff_ne_top]
  constructor
  · exact integrable_f_rnDeriv_mul_withDensity _ _ _ _ hf_int
  · by_cases h_top : f.derivAtTop = ∞
    · have : ∀ᵐ a ∂μ, κ.singularPart η a = 0 := by
        simp_rw [Kernel.singularPart_eq_zero_iff_absolutelyContinuous]
        exact h_deriv h_top
      suffices ∫⁻ a, f.derivAtTop * (∂μ/∂ν) a * ((κ.singularPart η) a) univ ∂ν = 0 by
        simp [this]
      rw [lintegral_eq_zero_iff h_meas]
      suffices (fun a ↦ (∂μ/∂ν) a * ((κ.singularPart η) a) univ) =ᵐ[ν] 0 by
        filter_upwards [this] with x hx
        rw [mul_assoc, hx]
        simp
      have h := Measure.ae_rnDeriv_ne_zero_imp_of_ae (ν := ν) this
      filter_upwards [h] with x hx
      by_cases h0 : μ.rnDeriv ν x = 0
      · simp [h0]
      · simp [hx h0]
    · simp_rw [mul_assoc]
      rw [lintegral_const_mul]
      swap; · exact (μ.measurable_rnDeriv ν).mul (Kernel.measurable_coe _ .univ)
      refine ENNReal.mul_ne_top h_top ?_
      simp_rw [Kernel.singularPart_eq_singularPart_measure]
      rw [lintegral_rnDeriv_mul_singularPart μ ν κ η .univ]
      simp

lemma fDiv_ne_top_of_fDiv_compProd_ne_top [CountableOrCountablyGenerated α β]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ η : Kernel α β) [IsMarkovKernel κ] [IsMarkovKernel η]
    (h_ne_top : fDiv f (μ ⊗ₘ κ) (ν ⊗ₘ η) ≠ ∞) :
    fDiv f μ ν ≠ ∞ := by
  rw [fDiv_ne_top_iff]
  have h_ne_top' := (fDiv_compProd_ne_top_iff).mp h_ne_top
  obtain ⟨h1, h2⟩ := h_ne_top'
  refine ⟨?_, fun h_top ↦ (h2 h_top).1⟩
  rw [fDiv_ne_top_iff] at h_ne_top
  exact integrable_f_rnDeriv_of_integrable_compProd' μ ν κ η h_ne_top.1 (fun h ↦ (h2 h).2)

end ProbabilityTheory
