/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
import TestingLowerBounds.Divergences.KullbackLeibler.CondKL
import TestingLowerBounds.Divergences.Hellinger.Hellinger

/-!
# Conditional Hellinger divergence

## Main definitions

* `FooBar`

## Main statements

* `fooBar_unique`

## Notation



## Implementation details

-/

open Real MeasureTheory Filter MeasurableSpace

open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {μ ν : Measure α} {κ η : Kernel α β}
  {a : ℝ}

lemma hellingerDiv_ae_ne_top_iff'' (κ η : Kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η] :
    (∀ᵐ x ∂μ, hellingerDiv a (κ x) (η x) ≠ ∞)
      ↔ (∀ᵐ x ∂μ, ∫⁻ b, hellingerDivFun a ((∂κ x/∂η x) b) ∂(η x) ≠ ∞)
        ∧ (1 ≤ a → ∀ᵐ x ∂μ, (κ x) ≪ (η x)) := by
  simp_rw [hellingerDiv_ne_top_iff, eventually_and, eventually_all]

-- lemma hellingerDiv_ae_ne_top_iff' (κ η : Kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η] :
--     (∀ᵐ x ∂μ, hellingerDiv a (κ x) (η x) ≠ ∞)
--       ↔ (∀ᵐ x ∂μ, Integrable (fun b ↦ hellingerFun a ((∂κ x/∂η x) b).toReal) (η x))
--         ∧ (1 ≤ a → ∀ᵐ x ∂μ, (κ x) ≪ (η x)) := by
--   simp_rw [hellingerDiv_ne_top_iff, eventually_and, eventually_all]

-- lemma hellingerDiv_ae_ne_top_iff (ha_ne_one : a ≠ 1)
--     (κ η : Kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η] :
--     (∀ᵐ x ∂μ, hellingerDiv a (κ x) (η x) ≠ ∞)
--       ↔ (∀ᵐ x ∂μ, Integrable (fun b ↦ ((∂κ x/∂η x) b).toReal ^ a) (η x))
--         ∧ (1 ≤ a → ∀ᵐ x ∂μ, (κ x) ≪ (η x)) := by
--   convert hellingerDiv_ae_ne_top_iff' κ η using 4 with x
--   exact (integrable_hellingerFun_iff_integrable_rpow ha_ne_one).symm

-- lemma hellingerDiv_ae_ne_top_iff_of_lt_one' (ha : a < 1) (κ η : Kernel α β) :
--     (∀ᵐ x ∂μ, hellingerDiv a (κ x) (η x) ≠ ∞)
--       ↔ (∀ᵐ x ∂μ, Integrable (fun b ↦ hellingerFun a ((∂κ x/∂η x) b).toReal) (η x)) := by
--   simp_rw [hellingerDiv_ne_top_iff_of_lt_one ha]

-- lemma hellingerDiv_ae_ne_top_iff_of_lt_one (ha : a < 1) (κ η : Kernel α β) [IsFiniteKernel η] :
--     (∀ᵐ x ∂μ, hellingerDiv a (κ x) (η x) ≠ ∞)
--       ↔ (∀ᵐ x ∂μ, Integrable (fun b ↦ ((∂κ x/∂η x) b).toReal ^ a) (η x)) := by
--   convert hellingerDiv_ae_ne_top_iff_of_lt_one' ha κ η using 3 with x
--   exact (integrable_hellingerFun_iff_integrable_rpow ha.ne).symm

-- /--Use this version only for the case `1 < a` or when one of the kernels is not finite, otherwise
-- use `integrable_hellingerDiv_iff_of_lt_one`, as it is strictly more general.-/
-- lemma integrable_hellingerDiv_iff
--     (h_int : ∀ᵐ x ∂μ, Integrable (fun b ↦ hellingerFun a ((∂κ x/∂η x) b).toReal) (η x))
--     (h_ac : 1 ≤ a → ∀ᵐ x ∂μ, κ x ≪ η x) :
--     Integrable (fun x ↦ (hellingerDiv a (κ x) (η x)).toReal) μ
--       ↔ Integrable (fun x ↦ ∫ b, hellingerFun a ((∂κ x/∂η x) b).toReal ∂η x) μ := by
--   apply integrable_congr
--   filter_upwards [h_int, eventually_all.mpr h_ac] with x hx_int hx_ac
--   rw [hellingerDiv_eq_integral_of_integrable_of_ac hx_int hx_ac, EReal.toReal_coe]

-- lemma integrable_hellingerDiv_iff_of_lt_one (ha_nonneg : 0 ≤ a) (ha : a < 1)
--     [IsFiniteKernel κ] [IsFiniteKernel η] :
--     Integrable (fun x ↦ (hellingerDiv a (κ x) (η x)).toReal) μ
--       ↔ Integrable (fun x ↦ ∫ b, hellingerFun a ((∂κ x/∂η x) b).toReal ∂η x) μ := by
--   refine integrable_congr (.of_forall fun x ↦ ?_)
--   simp_rw [hellingerDiv_eq_integral_of_lt_one ha_nonneg ha, EReal.toReal_coe]

-- lemma integrable_hellingerDiv_iff' (ha_pos : 0 < a) (ha_ne_one : a ≠ 1)
--     [IsFiniteMeasure μ] [IsFiniteKernel κ] [IsFiniteKernel η]
--     (h_int : ∀ᵐ x ∂μ, Integrable (fun b ↦ ((∂κ x/∂η x) b).toReal ^ a) (η x))
--     (h_ac : 1 ≤ a → ∀ᵐ x ∂μ, κ x ≪ η x) :
--     Integrable (fun x ↦ (hellingerDiv a (κ x) (η x)).toReal) μ
--       ↔ Integrable (fun x ↦ ∫ b, ((∂κ x/∂η x) b).toReal ^ a ∂η x) μ := by
--   have h_fin : ∀ᵐ x ∂μ, hellingerDiv a (κ x) (η x) ≠ ∞ := by
--     filter_upwards [h_int, eventually_all.mpr h_ac] with x hx_int hx_ac
--     rcases lt_or_gt_of_ne ha_ne_one with ha_lt | ha_gt
--     · exact hellingerDiv_ne_top_of_lt_one ha_pos.le ha_lt _ _
--     · exact hellingerDiv_ne_top_iff_of_one_lt ha_gt _ _ |>.mpr ⟨hx_int, hx_ac ha_gt.le⟩
--   have h_eq_eq : ∀ᵐ x ∂μ, (hellingerDiv a (κ x) (η x)).toReal =
--       (a - 1)⁻¹ * ((∫ b, ((∂κ x/∂η x) b).toReal ^ a ∂η x) - ((η x) .univ).toReal) := by
--     filter_upwards [h_fin] with x hx
--     rw [hellingerDiv_eq_integral_of_ne_top' ha_pos.ne.symm ha_ne_one hx, ← EReal.coe_mul,
--       EReal.toReal_sub (EReal.coe_ne_top _) (EReal.coe_ne_bot _), EReal.toReal_coe,
--       EReal.toReal_mul, EReal.toReal_coe, EReal.toReal_coe_ennreal, mul_sub]
--     · refine (EReal.mul_eq_top _ _).mp.mt ?_
--       push_neg
--       exact ⟨fun _ ↦ EReal.coe_ennreal_nonneg _, ⟨fun _ ↦ EReal.coe_ennreal_ne_bot _,
--         ⟨by simp only [EReal.coe_ne_top, IsEmpty.forall_iff],
--         fun _ ↦ EReal.coe_ennreal_eq_top_iff.mp.mt (measure_ne_top _ _)⟩⟩⟩
--     · refine (EReal.mul_eq_bot _ _).mp.mt ?_
--       push_neg
--       exact ⟨by simp only [EReal.coe_ne_bot, IsEmpty.forall_iff],
--         ⟨fun _ ↦ EReal.coe_ennreal_ne_bot _, ⟨fun _ ↦ EReal.coe_ennreal_nonneg _,
--         fun _ ↦ EReal.coe_ennreal_eq_top_iff.mp.mt (measure_ne_top _ _)⟩⟩⟩
--   rw [integrable_congr h_eq_eq, integrable_const_mul_iff (isUnit_iff_ne_zero.mpr <| (ne_eq _ _).mpr
--     <| inv_eq_zero.mp.mt <| sub_ne_zero_of_ne ha_ne_one)]
--   obtain ⟨C, ⟨hC_finite, hC⟩⟩ := IsFiniteKernel.exists_univ_le (κ := η)
--   refine integrable_add_iff_integrable_left <| (integrable_const C.toReal).mono' ?_ ?_
--   · exact η.measurable_coe .univ |>.ennreal_toReal.neg.aestronglyMeasurable
--   refine .of_forall (fun x ↦ ?_)
--   rw [norm_eq_abs, abs_neg, abs_eq_self.mpr ENNReal.toReal_nonneg, ENNReal.toReal_le_toReal
--     (measure_ne_top _ _) (lt_top_iff_ne_top.mp hC_finite)]
--   exact hC x

-- --TODO: shouldn't Set.setOf_app_iff be a simp lemma?

-- lemma integrable_hellingerDiv_zero [CountableOrCountablyGenerated α β]
--     [IsFiniteMeasure μ] [IsFiniteKernel κ] [IsFiniteKernel η] :
--     Integrable (fun x ↦ (hellingerDiv 0 (κ x) (η x)).toReal) μ := by
--   simp_rw [hellingerDiv_zero]
--   obtain ⟨C, ⟨hC_finite, hC⟩⟩ := IsFiniteKernel.exists_univ_le (κ := η)
--   simp only [EReal.toReal_coe_ennreal]
--   have h_eq : (fun x ↦ ((η x) {y | ((κ x).rnDeriv (η x) y).toReal = 0}).toReal) =
--       fun x ↦ ((η x) {y | (κ.rnDeriv η x y).toReal = 0}).toReal := by
--     ext x
--     congr 1
--     apply measure_congr
--     filter_upwards [κ.rnDeriv_eq_rnDeriv_measure] with y hy
--     simp only [Set.setOf_app_iff, eq_iff_iff, hy]
--   simp_rw [h_eq]
--   apply (integrable_const C.toReal).mono'
--   · apply Measurable.aestronglyMeasurable
--     apply Measurable.ennreal_toReal
--     exact Kernel.measurable_kernel_prod_mk_left
--       (measurableSet_eq_fun (κ.measurable_rnDeriv η).ennreal_toReal measurable_const)
--   · refine .of_forall fun x ↦ ?_
--     simp only [norm_eq_abs, ENNReal.abs_toReal, ENNReal.toReal_le_toReal
--     (measure_ne_top _ _) (lt_top_iff_ne_top.mp hC_finite)]
--     exact measure_mono (Set.subset_univ _) |>.trans (hC x)

-- lemma integrable_hellingerDiv_iff'_of_lt_one (ha_pos : 0 < a) (ha : a < 1)
--     [IsFiniteMeasure μ] [IsFiniteKernel κ] [IsFiniteKernel η] :
--     Integrable (fun x ↦ (hellingerDiv a (κ x) (η x)).toReal) μ
--       ↔ Integrable (fun x ↦ ∫ b, ((∂κ x/∂η x) b).toReal ^ a ∂η x) μ :=
--   integrable_hellingerDiv_iff' ha_pos ha.ne (.of_forall
--     (fun _ ↦ integrable_rpow_rnDeriv_of_lt_one ha_pos.le ha)) (not_le_of_gt ha).elim

/-- Conditional Hellinger divergence of order `a`. -/
noncomputable def condHellingerDiv (a : ℝ) (κ η : Kernel α β) (μ : Measure α) : ℝ≥0∞ :=
  condFDiv (hellingerDivFun a) κ η μ

lemma hellingerDiv_compProd_left [CountableOrCountablyGenerated α β]
    (μ : Measure α) [IsFiniteMeasure μ]
    (κ η : Kernel α β) [IsFiniteKernel κ] [∀ x, NeZero (κ x)] [IsFiniteKernel η] :
    hellingerDiv a (μ ⊗ₘ κ) (μ ⊗ₘ η) = condHellingerDiv a κ η μ := by
  rw [hellingerDiv, condHellingerDiv, fDiv_compProd_left _ _ _]

lemma hellingerDiv_comp_left_le [Nonempty α] [StandardBorelSpace α]
    [CountableOrCountablyGenerated α β] (μ : Measure α) [IsFiniteMeasure μ]
    (κ η : Kernel α β) [IsFiniteKernel κ] [∀ a, NeZero (κ a)] [IsFiniteKernel η] :
    hellingerDiv a (κ ∘ₘ μ) (η ∘ₘ μ) ≤ condHellingerDiv a κ η μ :=
  fDiv_comp_left_le μ κ η

/-! There are multiple combinations of hypotheses that give rise to slightly different versions of
the following lemmas. The ones we will consider as a normal form are when we assume that `μ`, `κ`
and `η` are all finite and `a ∈ (0, 1) ∪ (1, +∞)`.

Consider the following conditions:
1. `condHellingerDiv a κ η μ ≠ ∞`
2. `condHellingerDiv a κ η μ = ∫ x, (hellingerDiv a (κ x) (η x)).toReal ∂μ`
3.a `∀ᵐ x ∂μ, Integrable (fun b ↦ ((∂κ x/∂η x) b).toReal ^ a) (η x)` (`h_int`)
3.b `∀ᵐ x ∂μ, (κ x) ≪ (η x)` (`h_ac`)
3.c `Integrable (fun x ↦ ∫ b, ((∂κ x/∂η x) b).toReal ^ a ∂η x) μ` (`h_int'`)
4. `condHellingerDiv a κ η μ = (a - 1)⁻¹ * ∫ x, ∫ b, ((∂κ x/∂η x) b).toReal ^ a ∂η x ∂μ - (a - 1)⁻¹ * ((μ ⊗ₘ η) .univ).toReal`

Then the following hold:
- 1. ↔ 2. (`condHellingerDiv_eq_integral_iff_ne_top`)
- if `1 < a`:
  - 1. ↔ 3.a ∧ 3.b ∧ 3.c (`condHellingerDiv_ne_top_iff_of_one_lt`)
  - 2. ↔ 3.a ∧ 3.b ∧ 3.c (`condHellingerDiv_eq_integral_iff_of_one_lt`)
  - 3.a ∧ 3.b ∧ 3.c → 4. (`condHellingerDiv_eq_integral'_of_one_lt`)
- if `a < 1`:
  - 1. ↔ 3.c (`condHellingerDiv_ne_top_iff_of_lt_one'`)
  - 2. ↔ 3.c (`condHellingerDiv_eq_integral_iff_of_lt_one`)
  - 3.c → 4. (`condHellingerDiv_eq_integral'_of_lt_one`)

The implications 4. → 1./2./3. are not explicitely stated but, if needed, it should be immediate to
prove 4. → 1. and then have all the other implications for free.
-/
section CondHellingerEq

lemma condHellingerDiv_one [IsFiniteKernel κ] [IsFiniteKernel η] :
    condHellingerDiv 1 κ η μ = condKL κ η μ := by
  rw [condHellingerDiv, hellingerDivFun_one, condKL_eq_condFDiv]

lemma condHellingerDiv_of_not_ae_finite [CountableOrCountablyGenerated α β]
    [IsFiniteKernel κ] [IsFiniteKernel η]
    (h_ae : ¬ ∀ᵐ x ∂μ, hellingerDiv a (κ x) (η x) ≠ ∞) :
    condHellingerDiv a κ η μ = ∞ := by
  rw [condHellingerDiv]
  exact condFDiv_of_not_ae_finite h_ae

-- lemma condHellingerDiv_of_not_ae_integrable' [IsFiniteKernel κ] [IsFiniteKernel η]
--     (h_int : ¬ ∀ᵐ x ∂μ, Integrable (fun b ↦ hellingerFun a ((∂κ x/∂η x) b).toReal) (η x)) :
--     condHellingerDiv a κ η μ = ∞ := condFDiv_of_not_ae_integrable h_int

-- lemma condHellingerDiv_of_not_ae_integrable (ha_ne_one : a ≠ 1)
--     [IsFiniteKernel κ] [IsFiniteKernel η]
--     (h_int : ¬ ∀ᵐ x ∂μ, Integrable (fun b ↦ ((∂κ x/∂η x) b).toReal ^ a) (η x)) :
--     condHellingerDiv a κ η μ = ∞ := by
--   simp_rw [← integrable_hellingerFun_iff_integrable_rpow ha_ne_one] at h_int
--   exact condFDiv_of_not_ae_integrable h_int

-- lemma condHellingerDiv_of_not_ae_integrable_of_lt_one (ha : a < 1)
--     (h_int : ¬ ∀ᵐ x ∂μ, Integrable (fun b ↦ hellingerFun a ((∂κ x/∂η x) b).toReal) (η x)) :
--     condHellingerDiv a κ η μ = ∞ := by
--   apply condHellingerDiv_of_not_ae_finite
--   rw [hellingerDiv_ae_ne_top_iff_of_lt_one' ha]
--   exact h_int

-- lemma condHellingerDiv_of_not_ae_ac_of_one_le (ha : 1 ≤ a) [IsFiniteKernel κ] [IsFiniteKernel η]
--     (h_ac : ¬ ∀ᵐ x ∂μ, κ x ≪ η x) :
--     condHellingerDiv a κ η μ = ∞ := by
--   apply condHellingerDiv_of_not_ae_finite
--   rw [hellingerDiv_ae_ne_top_iff']
--   tauto

-- lemma condHellingerDiv_of_not_integrable
--     (h_int : ¬ Integrable (fun x ↦ (hellingerDiv a (κ x) (η x)).toReal) μ) :
--     condHellingerDiv a κ η μ = ∞ := condFDiv_of_not_integrable h_int

-- lemma condHellingerDiv_of_not_integrable' (ha_nonneg : 0 ≤ a) (ha_ne_one : a ≠ 1)
--     [IsFiniteMeasure μ] [IsFiniteKernel κ] [IsFiniteKernel η]
--     (h_int' : ¬ Integrable (fun x ↦ ∫ b, ((∂κ x/∂η x) b).toReal ^ a ∂η x) μ) :
--     condHellingerDiv a κ η μ = ∞ := by
--   by_cases ha_zero : a = 0
--   · simp [ha_zero, Integrable.Kernel] at h_int'
--   have ha_pos := ha_nonneg.lt_of_ne fun h ↦ ha_zero h.symm
--   by_cases h_int2 : ∀ᵐ x ∂μ, Integrable (fun b ↦ ((∂κ x/∂η x) b).toReal ^ a) (η x)
--   swap; exact condHellingerDiv_of_not_ae_integrable ha_ne_one h_int2
--   by_cases h_ac : 1 ≤ a → ∀ᵐ x ∂μ, κ x ≪ η x
--   swap
--   · push_neg at h_ac
--     exact condHellingerDiv_of_not_ae_ac_of_one_le h_ac.1 h_ac.2
--   apply condHellingerDiv_of_not_integrable
--   rwa [integrable_hellingerDiv_iff' ha_pos ha_ne_one h_int2 h_ac]

-- lemma condHellingerDiv_of_ae_finite_of_integrable (h_ae : ∀ᵐ x ∂μ, hellingerDiv a (κ x) (η x) ≠ ∞)
--     (h_int2 : Integrable (fun x ↦ (hellingerDiv a (κ x) (η x)).toReal) μ) :
--     condHellingerDiv a κ η μ = ∫ x, (hellingerDiv a (κ x) (η x)).toReal ∂μ :=
--   condFDiv_eq' h_ae h_int2

-- lemma condHellingerDiv_of_ae_integrable_of_ae_ac_of_integrable [IsFiniteKernel κ] [IsFiniteKernel η]
--     (h_int : ∀ᵐ x ∂μ, Integrable (fun b ↦ hellingerFun a ((∂κ x/∂η x) b).toReal) (η x))
--     (h_ac : 1 ≤ a → ∀ᵐ x ∂μ, (κ x) ≪ (η x))
--     (h_int2 : Integrable (fun x ↦ (hellingerDiv a (κ x) (η x)).toReal) μ) :
--     condHellingerDiv a κ η μ = ∫ x, (hellingerDiv a (κ x) (η x)).toReal ∂μ :=
--   condHellingerDiv_of_ae_finite_of_integrable
--     ((hellingerDiv_ae_ne_top_iff' _ _).mpr ⟨h_int, h_ac⟩) h_int2

-- lemma condHellingerDiv_zero_eq [CountableOrCountablyGenerated α β]
--     [IsFiniteMeasure μ] [IsFiniteKernel κ] [IsFiniteKernel η] :
--     condHellingerDiv 0 κ η μ = ∫ x, (hellingerDiv 0 (κ x) (η x)).toReal ∂μ :=
--   condHellingerDiv_of_ae_finite_of_integrable
--     ((hellingerDiv_ae_ne_top_iff' _ _).mpr
--       ⟨.of_forall fun _ ↦ integrable_hellingerFun_zero, by simp⟩)
--     integrable_hellingerDiv_zero

-- lemma condHellingerDiv_zero_of_ae_integrable_of_integrable [IsFiniteKernel κ] [IsFiniteKernel η]
--     (h_int2 : Integrable (fun x ↦ (hellingerDiv 0 (κ x) (η x)).toReal) μ) :
--     condHellingerDiv 0 κ η μ = ∫ x, (hellingerDiv 0 (κ x) (η x)).toReal ∂μ :=
--   condHellingerDiv_of_ae_finite_of_integrable
--     ((hellingerDiv_ae_ne_top_iff' _ _).mpr
--       ⟨.of_forall fun _ ↦ integrable_hellingerFun_zero, by simp⟩) h_int2

-- --TODO: try to generalize this to the case `a = 0`
-- lemma condHellingerDiv_of_ae_integrable_of_ae_ac_of_integrable' (ha_pos : 0 < a) (ha_ne_one : a ≠ 1)
--     [IsFiniteMeasure μ] [IsFiniteKernel κ] [IsFiniteKernel η]
--     (h_int : ∀ᵐ x ∂μ, Integrable (fun b ↦ ((∂κ x/∂η x) b).toReal ^ a) (η x))
--     (h_ac : 1 ≤ a → ∀ᵐ x ∂μ, (κ x) ≪ (η x))
--     (h_int' : Integrable (fun x ↦ ∫ b, ((∂κ x/∂η x) b).toReal ^ a ∂η x) μ) :
--     condHellingerDiv a κ η μ = ∫ x, (hellingerDiv a (κ x) (η x)).toReal ∂μ :=
--   condHellingerDiv_of_ae_finite_of_integrable
--     ((hellingerDiv_ae_ne_top_iff ha_ne_one _ _).mpr ⟨h_int, h_ac⟩)
--     (integrable_hellingerDiv_iff' ha_pos ha_ne_one h_int h_ac |>.mpr h_int')

-- lemma condHellingerDiv_of_ae_integrable_of_integrable_of_lt_one (ha : a < 1) [IsFiniteKernel η]
--     (h_int : ∀ᵐ x ∂μ, Integrable (fun b ↦ ((∂κ x/∂η x) b).toReal ^ a) (η x))
--     (h_int2 : Integrable (fun x ↦ (hellingerDiv a (κ x) (η x)).toReal) μ) :
--     condHellingerDiv a κ η μ = ∫ x, (hellingerDiv a (κ x) (η x)).toReal ∂μ :=
--   condHellingerDiv_of_ae_finite_of_integrable
--     ((hellingerDiv_ae_ne_top_iff_of_lt_one ha _ _).mpr h_int) h_int2

-- lemma condHellingerDiv_of_integrable'_of_lt_one (ha_pos : 0 < a) (ha : a < 1)
--     [IsFiniteMeasure μ] [IsFiniteKernel κ] [IsFiniteKernel η]
--     (h_int' : Integrable (fun x ↦ ∫ b, ((∂κ x/∂η x) b).toReal ^ a ∂η x) μ) :
--     condHellingerDiv a κ η μ = ∫ x, (hellingerDiv a (κ x) (η x)).toReal ∂μ :=
--   condHellingerDiv_of_ae_finite_of_integrable
--     ((hellingerDiv_ae_ne_top_iff_of_lt_one ha _ _).mpr
--       (.of_forall <| fun _ ↦ integrable_rpow_rnDeriv_of_lt_one ha_pos.le ha))
--     (integrable_hellingerDiv_iff'_of_lt_one ha_pos ha |>.mpr h_int')

-- lemma condHellingerDiv_eq_top_iff [IsFiniteKernel κ] [IsFiniteKernel η] :
--     condHellingerDiv a κ η μ = ∞
--       ↔ ¬ (∀ᵐ x ∂μ, Integrable (fun b ↦ hellingerFun a ((∂κ x/∂η x) b).toReal) (η x))
--         ∨ (1 ≤ a ∧ ¬ ∀ᵐ x ∂μ, (κ x) ≪ (η x))
--         ∨ ¬ Integrable (fun x ↦ (hellingerDiv a (κ x) (η x)).toReal) μ := by
--   constructor
--   · contrapose!
--     rintro ⟨h_int, h_ac, h_int2⟩
--     rw [condHellingerDiv_of_ae_integrable_of_ae_ac_of_integrable h_int h_ac h_int2]
--     exact EReal.coe_ne_top _
--   · rintro (h_int | ⟨ha, h_ac⟩ | h_int2)
--     · exact condHellingerDiv_of_not_ae_integrable' h_int
--     · exact condHellingerDiv_of_not_ae_ac_of_one_le ha h_ac
--     · exact condHellingerDiv_of_not_integrable h_int2

-- lemma condHellingerDiv_ne_top_iff [IsFiniteKernel κ] [IsFiniteKernel η] :
--     condHellingerDiv a κ η μ ≠ ∞
--       ↔ (∀ᵐ x ∂μ, Integrable (fun b ↦ hellingerFun a ((∂κ x/∂η x) b).toReal) (η x))
--         ∧ (1 ≤ a → ∀ᵐ x ∂μ, (κ x) ≪ (η x))
--         ∧ Integrable (fun x ↦ (hellingerDiv a (κ x) (η x)).toReal) μ := by
--   rw [ne_eq, condHellingerDiv_eq_top_iff]
--   push_neg
--   rfl

-- lemma condHellingerDiv_ne_top_iff' (ha_pos : 0 < a) (ha_ne_one : a ≠ 1)
--     [IsFiniteMeasure μ] [IsFiniteKernel κ] [IsFiniteKernel η] :
--     condHellingerDiv a κ η μ ≠ ∞
--       ↔ (∀ᵐ x ∂μ, Integrable (fun b ↦ ((∂κ x/∂η x) b).toReal ^ a) (η x))
--         ∧ (1 ≤ a → ∀ᵐ x ∂μ, (κ x) ≪ (η x))
--         ∧ Integrable (fun x ↦ ∫ b, ((∂κ x/∂η x) b).toReal ^ a ∂η x) μ := by
--   simp_rw [condHellingerDiv_ne_top_iff, integrable_hellingerFun_iff_integrable_rpow ha_ne_one]
--   refine and_congr_right (fun h_int ↦ and_congr_right (fun h_ac ↦ ?_))
--   rw [integrable_hellingerDiv_iff' ha_pos ha_ne_one h_int h_ac]

-- lemma condHellingerDiv_eq_top_iff' (ha_pos : 0 < a) (ha_ne_one : a ≠ 1)
--     [IsFiniteMeasure μ] [IsFiniteKernel κ] [IsFiniteKernel η] :
--     condHellingerDiv a κ η μ = ∞
--       ↔ ¬ (∀ᵐ x ∂μ, Integrable (fun b ↦ ((∂κ x/∂η x) b).toReal ^ a) (η x))
--         ∨ (1 ≤ a ∧ ¬ ∀ᵐ x ∂μ, (κ x) ≪ (η x))
--         ∨ ¬ Integrable (fun x ↦ ∫ b, ((∂κ x/∂η x) b).toReal ^ a ∂η x) μ := by
--   rw [← not_not (a := _ = ∞), ← ne_eq, condHellingerDiv_ne_top_iff' ha_pos ha_ne_one]
--   tauto

-- lemma condHellingerDiv_ne_top_iff_of_one_lt (ha : 1 < a)
--     [IsFiniteMeasure μ] [IsFiniteKernel κ] [IsFiniteKernel η] :
--     condHellingerDiv a κ η μ ≠ ∞
--       ↔ (∀ᵐ x ∂μ, Integrable (fun b ↦ ((∂κ x/∂η x) b).toReal ^ a) (η x))
--         ∧ (∀ᵐ x ∂μ, (κ x) ≪ (η x))
--         ∧ Integrable (fun x ↦ ∫ b, ((∂κ x/∂η x) b).toReal ^ a ∂η x) μ := by
--   simp_rw [condHellingerDiv_ne_top_iff' (zero_lt_one.trans ha) ha.ne.symm, ha.le, true_implies]

-- lemma condHellingerDiv_eq_top_iff_of_one_lt (ha : 1 < a)
--     [IsFiniteMeasure μ] [IsFiniteKernel κ] [IsFiniteKernel η] :
--     condHellingerDiv a κ η μ = ∞
--       ↔ ¬ (∀ᵐ x ∂μ, Integrable (fun b ↦ ((∂κ x/∂η x) b).toReal ^ a) (η x))
--         ∨ (1 ≤ a ∧ ¬ ∀ᵐ x ∂μ, (κ x) ≪ (η x))
--         ∨ ¬ Integrable (fun x ↦ ∫ b, ((∂κ x/∂η x) b).toReal ^ a ∂η x) μ := by
--   rw [← not_not (a := _ = ∞), ← ne_eq, condHellingerDiv_ne_top_iff_of_one_lt ha]
--   have ha' : 1 ≤ a := ha.le
--   tauto

-- lemma condHellingerDiv_eq_top_iff_of_lt_one (ha : a < 1) [IsFiniteKernel κ] [IsFiniteKernel η] :
--     condHellingerDiv a κ η μ = ∞
--       ↔ ¬ (∀ᵐ x ∂μ, Integrable (fun b ↦ hellingerFun a ((∂κ x/∂η x) b).toReal) (η x))
--         ∨ ¬ Integrable (fun x ↦ (hellingerDiv a (κ x) (η x)).toReal) μ := by
--   simp only [condHellingerDiv_eq_top_iff, not_eventually, ha.not_le, false_and, false_or]

-- lemma condHellingerDiv_ne_top_iff_of_lt_one (ha : a < 1) [IsFiniteKernel κ] [IsFiniteKernel η] :
--     condHellingerDiv a κ η μ ≠ ∞
--       ↔ (∀ᵐ x ∂μ, Integrable (fun b ↦ hellingerFun a ((∂κ x/∂η x) b).toReal) (η x))
--         ∧ Integrable (fun x ↦ (hellingerDiv a (κ x) (η x)).toReal) μ := by
--   simp only [condHellingerDiv_ne_top_iff, ha.not_le, false_implies, true_and]

-- lemma condHellingerDiv_eq_top_iff_of_lt_one' (ha_pos : 0 < a) (ha : a < 1)
--     [IsFiniteMeasure μ] [IsFiniteKernel κ] [IsFiniteKernel η] :
--     condHellingerDiv a κ η μ = ∞
--       ↔ ¬ Integrable (fun x ↦ ∫ b, ((∂κ x/∂η x) b).toReal ^ a ∂η x) μ := by
--   simp_rw [condHellingerDiv_eq_top_iff_of_lt_one ha,
--     (Eventually.of_forall <| fun _ ↦ integrable_hellingerFun_rnDeriv_of_lt_one ha_pos.le ha),
--     integrable_hellingerDiv_iff'_of_lt_one ha_pos ha, not_true, false_or]

-- lemma condHellingerDiv_ne_top_iff_of_lt_one' (ha_pos : 0 < a) (ha : a < 1)
--     [IsFiniteMeasure μ] [IsFiniteKernel κ] [IsFiniteKernel η] :
--     condHellingerDiv a κ η μ ≠ ∞ ↔ Integrable (fun x ↦ ∫ b, ((∂κ x/∂η x) b).toReal ^ a ∂η x) μ := by
--   rw [ne_eq, condHellingerDiv_eq_top_iff_of_lt_one' ha_pos ha, not_not]

-- lemma condHellingerDiv_eq_integral_iff_ne_top (ha_pos : 0 < a) (ha_ne_one : a ≠ 1)
--     [IsFiniteMeasure μ] [IsFiniteKernel κ] [IsFiniteKernel η] :
--     condHellingerDiv a κ η μ ≠ ∞
--       ↔ condHellingerDiv a κ η μ = ∫ x, (hellingerDiv a (κ x) (η x)).toReal ∂μ := by
--   refine ⟨fun h ↦ ?_, fun h ↦ h ▸ EReal.coe_ne_top _⟩
--   rw [condHellingerDiv_ne_top_iff' ha_pos ha_ne_one] at h
--   exact condHellingerDiv_of_ae_integrable_of_ae_ac_of_integrable' ha_pos ha_ne_one h.1 h.2.1 h.2.2

-- lemma condHellingerDiv_eq_integral_iff_of_one_lt (ha : 1 < a)
--     [IsFiniteMeasure μ] [IsFiniteKernel κ] [IsFiniteKernel η] :
--     condHellingerDiv a κ η μ = ∫ x, (hellingerDiv a (κ x) (η x)).toReal ∂μ
--       ↔ (∀ᵐ x ∂μ, Integrable (fun b ↦ ((∂κ x/∂η x) b).toReal ^ a) (η x))
--         ∧ (∀ᵐ x ∂μ, (κ x) ≪ (η x))
--         ∧ Integrable (fun x ↦ ∫ b, ((∂κ x/∂η x) b).toReal ^ a ∂η x) μ :=
--   (condHellingerDiv_eq_integral_iff_ne_top (zero_lt_one.trans ha) ha.ne.symm).symm.trans
--     (condHellingerDiv_ne_top_iff_of_one_lt ha)

-- lemma condHellingerDiv_eq_integral_iff_of_lt_one (ha_pos : 0 < a) (ha : a < 1)
--     [IsFiniteMeasure μ] [IsFiniteKernel κ] [IsFiniteKernel η] :
--     condHellingerDiv a κ η μ = ∫ x, (hellingerDiv a (κ x) (η x)).toReal ∂μ
--       ↔ Integrable (fun x ↦ ∫ b, ((∂κ x/∂η x) b).toReal ^ a ∂η x) μ :=
--   (condHellingerDiv_eq_integral_iff_ne_top ha_pos ha.ne).symm.trans
--     (condHellingerDiv_ne_top_iff_of_lt_one' ha_pos ha)

-- lemma condHellingerDiv_eq_integral'_of_one_lt (ha : 1 < a)
--     [IsFiniteMeasure μ] [IsFiniteKernel κ] [IsFiniteKernel η]
--     (h_int : ∀ᵐ x ∂μ, Integrable (fun b ↦ ((∂κ x/∂η x) b).toReal ^ a) (η x))
--     (h_ac : ∀ᵐ x ∂μ, (κ x) ≪ (η x))
--     (h_int' : Integrable (fun x ↦ ∫ b, ((∂κ x/∂η x) b).toReal ^ a ∂η x) μ) :
--     condHellingerDiv a κ η μ = (a - 1)⁻¹ * ∫ x, ∫ b, ((∂κ x/∂η x) b).toReal ^ a ∂η x ∂μ
--       - (a - 1)⁻¹ * ((μ ⊗ₘ η) .univ).toReal := by
--   rw [condHellingerDiv_eq_integral_iff_of_one_lt ha |>.mpr ⟨h_int, h_ac, h_int'⟩]
--   norm_cast
--   calc
--     _ = ∫ x, ((a - 1)⁻¹ * ∫ b, ((∂κ x/∂η x) b).toReal ^ a ∂η x
--         - (a - 1)⁻¹ * ((η x) .univ).toEReal).toReal ∂μ := by
--       apply integral_congr_ae
--       filter_upwards [h_int, h_ac] with x hx_int hx_ac
--       congr
--       exact hellingerDiv_eq_integral_of_ne_top' (by positivity) ha.ne.symm <|
--         hellingerDiv_ne_top_iff_of_one_lt ha _ _ |>.mpr ⟨hx_int, hx_ac⟩
--     _ = ∫ x, ((a - 1)⁻¹ * ∫ b, ((∂κ x/∂η x) b).toReal ^ a ∂η x
--         - (a - 1)⁻¹ * ((η x) .univ).toReal) ∂μ := by
--       refine integral_congr_ae (.of_forall fun x ↦ ?_)
--       dsimp
--       rw [EReal.toReal_sub (ne_of_beq_false (by rfl)) (ne_of_beq_false (by rfl))]
--       congr
--       rw [EReal.toReal_mul, EReal.toReal_coe, EReal.toReal_coe_ennreal]
--       all_goals
--         simp only [ne_eq, EReal.mul_eq_top, EReal.mul_eq_bot, EReal.coe_ne_bot, false_and,
--           EReal.coe_neg', EReal.coe_ennreal_ne_bot, and_false, EReal.coe_ne_top,
--           EReal.coe_ennreal_pos, Measure.measure_univ_pos, EReal.coe_pos,
--           EReal.coe_ennreal_eq_top_iff, measure_ne_top, or_self, not_false_eq_true]
--     _ = ∫ x, ((a - 1)⁻¹ * ∫ b, ((∂κ x/∂η x) b).toReal ^ a ∂η x) ∂μ
--         - ∫ x, ((a - 1)⁻¹ * ((η x) .univ).toReal) ∂μ :=
--       integral_sub (Integrable.const_mul h_int' _)
--         (Integrable.const_mul (Integrable.Kernel _ .univ) _)
--     _ = _ := by
--       rw [integral_mul_left, integral_mul_left, compProd_univ_toReal]

-- lemma condHellingerDiv_eq_integral'_of_one_lt' (ha : 1 < a)
--     [IsFiniteMeasure μ] [IsFiniteKernel κ] [IsMarkovKernel η]
--     (h_int : ∀ᵐ x ∂μ, Integrable (fun b ↦ ((∂κ x/∂η x) b).toReal ^ a) (η x))
--     (h_ac : ∀ᵐ x ∂μ, (κ x) ≪ (η x))
--     (h_int' : Integrable (fun x ↦ ∫ b, ((∂κ x/∂η x) b).toReal ^ a ∂η x) μ) :
--     condHellingerDiv a κ η μ = (a - 1)⁻¹ * ∫ x, ∫ b, ((∂κ x/∂η x) b).toReal ^ a ∂η x ∂μ
--       - (a - 1)⁻¹ * (μ .univ).toReal := by
--   simp_rw [condHellingerDiv_eq_integral'_of_one_lt ha h_int h_ac h_int',
--     compProd_univ_toReal, measure_univ, ENNReal.one_toReal, integral_const, smul_eq_mul, mul_one]

-- lemma condHellingerDiv_eq_integral'_of_one_lt'' (ha : 1 < a)
--     [IsProbabilityMeasure μ] [IsFiniteKernel κ] [IsMarkovKernel η]
--     (h_int : ∀ᵐ x ∂μ, Integrable (fun b ↦ ((∂κ x/∂η x) b).toReal ^ a) (η x))
--     (h_ac : ∀ᵐ x ∂μ, (κ x) ≪ (η x))
--     (h_int' : Integrable (fun x ↦ ∫ b, ((∂κ x/∂η x) b).toReal ^ a ∂η x) μ) :
--     condHellingerDiv a κ η μ = (a - 1)⁻¹ * ∫ x, ∫ b, ((∂κ x/∂η x) b).toReal ^ a ∂η x ∂μ
--       - (a - 1)⁻¹ := by
--   rw [condHellingerDiv_eq_integral'_of_one_lt' ha h_int h_ac h_int', measure_univ,
--     ENNReal.one_toReal, EReal.coe_one, mul_one]

-- lemma condHellingerDiv_eq_integral'_of_lt_one (ha_pos : 0 < a) (ha : a < 1)
--     [IsFiniteMeasure μ] [IsFiniteKernel κ] [IsFiniteKernel η]
--     (h_int' : Integrable (fun x ↦ ∫ b, ((∂κ x/∂η x) b).toReal ^ a ∂η x) μ) :
--     condHellingerDiv a κ η μ = (a - 1)⁻¹ * ∫ x, ∫ b, ((∂κ x/∂η x) b).toReal ^ a ∂η x ∂μ
--       - (a - 1)⁻¹ * ((μ ⊗ₘ η) .univ).toReal := by
--   rw [condHellingerDiv_eq_integral_iff_of_lt_one ha_pos ha |>.mpr h_int']
--   norm_cast
--   calc
--     _ = ∫ x, ((a - 1)⁻¹ * ∫ b, ((∂κ x/∂η x) b).toReal ^ a ∂η x
--         - (a - 1)⁻¹ * ((η x) .univ).toEReal).toReal ∂μ := by
--       apply integral_congr_ae
--       filter_upwards with x
--       congr
--       exact hellingerDiv_eq_integral_of_lt_one' ha_pos ha _ _
--     _ = ∫ x, ((a - 1)⁻¹ * ∫ b, ((∂κ x/∂η x) b).toReal ^ a ∂η x --from here to the end the proof is the same as the one of `condHellingerDiv_eq_integral'_of_one_lt`, consider separating this part as a lemma
--         - (a - 1)⁻¹ * ((η x) .univ).toReal) ∂μ := by
--       refine integral_congr_ae (.of_forall fun x ↦ ?_)
--       dsimp
--       rw [EReal.toReal_sub (ne_of_beq_false (by rfl)) (ne_of_beq_false (by rfl))]
--       congr
--       rw [EReal.toReal_mul, EReal.toReal_coe, EReal.toReal_coe_ennreal]
--       all_goals
--         simp only [ne_eq, EReal.mul_eq_top, EReal.mul_eq_bot, EReal.coe_ne_bot, false_and,
--           EReal.coe_neg', EReal.coe_ennreal_ne_bot, and_false, EReal.coe_ne_top,
--           EReal.coe_ennreal_pos, Measure.measure_univ_pos, EReal.coe_pos,
--           EReal.coe_ennreal_eq_top_iff, measure_ne_top, or_self, not_false_eq_true]
--     _ = ∫ x, ((a - 1)⁻¹ * ∫ b, ((∂κ x/∂η x) b).toReal ^ a ∂η x) ∂μ
--         - ∫ x, ((a - 1)⁻¹ * ((η x) .univ).toReal) ∂μ :=
--       integral_sub (Integrable.const_mul h_int' _)
--         (Integrable.const_mul (Integrable.Kernel _ .univ) _)
--     _ = _ := by
--       rw [integral_mul_left, integral_mul_left, compProd_univ_toReal]

-- lemma condHellingerDiv_eq_integral'_of_lt_one' (ha_pos : 0 < a) (ha : a < 1)
--     [IsFiniteMeasure μ] [IsFiniteKernel κ] [IsMarkovKernel η]
--     (h_int' : Integrable (fun x ↦ ∫ b, ((∂κ x/∂η x) b).toReal ^ a ∂η x) μ) :
--     condHellingerDiv a κ η μ = (a - 1)⁻¹ * ∫ x, ∫ b, ((∂κ x/∂η x) b).toReal ^ a ∂η x ∂μ
--       - (a - 1)⁻¹ * (μ .univ).toReal := by
--   simp_rw [condHellingerDiv_eq_integral'_of_lt_one ha_pos ha h_int', compProd_univ_toReal,
--     measure_univ, ENNReal.one_toReal, integral_const, smul_eq_mul, mul_one]

-- lemma condHellingerDiv_eq_integral'_of_lt_one'' (ha_pos : 0 < a) (ha : a < 1)
--     [IsProbabilityMeasure μ] [IsFiniteKernel κ] [IsMarkovKernel η]
--     (h_int' : Integrable (fun x ↦ ∫ b, ((∂κ x/∂η x) b).toReal ^ a ∂η x) μ) :
--     condHellingerDiv a κ η μ = (a - 1)⁻¹ * ∫ x, ∫ b, ((∂κ x/∂η x) b).toReal ^ a ∂η x ∂μ
--       - (a - 1)⁻¹ := by
--   rw [condHellingerDiv_eq_integral'_of_lt_one' ha_pos ha h_int', measure_univ,
--     ENNReal.one_toReal, EReal.coe_one, mul_one]

end CondHellingerEq

end ProbabilityTheory
