/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Decomposition.RadonNikodym
import TestingLowerBounds.ForMathlib.LeftRightDeriv
import TestingLowerBounds.Convex
import TestingLowerBounds.DerivAtTop
import TestingLowerBounds.ForMathlib.Integrable
import TestingLowerBounds.ForMathlib.RnDeriv

/-!

# f-Divergences functions

-/

open Real MeasureTheory Filter Set MeasurableSpace

open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μ ν : Measure α}

structure DivFunction where
  toFun : ℝ → ℝ≥0∞
  one : toFun 1 = 0
  rightDerivOne : rightDeriv (fun x ↦ (toFun x).toReal) 1 = 0
  convexOn' : ConvexOn ℝ≥0 (Ici 0) toFun
  continuousOn' : ContinuousOn toFun (Ici 0)

namespace DivFunction

attribute [coe] toFun

instance instCoeFun : CoeFun DivFunction fun _ ↦ ℝ → ℝ≥0∞ := ⟨toFun⟩

initialize_simps_projections DivFunction (toFun → apply)

@[ext] lemma ext {f g : DivFunction} (h : ∀ x, f x = g x) : f = g := by
  exact (DivFunction.mk.injEq ..).mpr (funext h)

variable (f : DivFunction)

@[simp] lemma apply_one : f 1 = 0 := f.one

@[simp] lemma rightDeriv_one : rightDeriv (fun x ↦ (f x).toReal) 1 = 0 := f.rightDerivOne

lemma convexOn : ConvexOn ℝ≥0 (Ici 0) f := f.convexOn'

lemma convexOn_toReal : ConvexOn ℝ (Ici 0) (fun x ↦ (f x).toReal) := sorry

lemma continuousOn : ContinuousOn f (Ici 0) := f.continuousOn'

lemma continuousOn_toReal (h : ∀ x, 0 ≤ x → f x ≠ ∞) :
    ContinuousOn (fun x ↦ (f x).toReal) (Ici 0) :=
  ENNReal.continuousOn_toReal.comp f.continuousOn h

variable {f}
variable {g : DivFunction}

noncomputable def xmin (f : DivFunction) : ℝ := sInf {x | 0 ≤ x ∧ f x ≠ ∞}
noncomputable def xmax (f : DivFunction) : ℝ := sSup {x | f x ≠ ∞}

lemma xmin_lt_one : f.xmin < 1 := by sorry

lemma one_lt_xmax : 1 < f.xmax := by sorry

lemma eq_infty_of_lt {x : ℝ} (hx_nonneg : 0 ≤ x) (hx_le : x ≤ f.xmin) : f x = ∞ := by
  sorry

lemma eq_infty_of_ge {x : ℝ} (hx_ge : f.xmax ≤ x) : f x = ∞ := by
  sorry

lemma lt_top_of_mem_Ioo {x : ℝ} (hx : x ∈ Ioo f.xmin f.xmax) : f x < ∞ := by
  sorry

protected def zero : DivFunction where
  toFun := 0
  one := rfl
  rightDerivOne := by simp
  convexOn' := convexOn_const _ (convex_Ici _)
  continuousOn' := continuousOn_const

protected noncomputable def add (f g : DivFunction) : DivFunction where
  toFun := fun x ↦ f x + g x
  one := by simp
  rightDerivOne := by
    simp only [Pi.add_apply]
    sorry
  convexOn' := sorry
  continuousOn' := f.continuousOn.add g.continuousOn

noncomputable
instance : AddZeroClass DivFunction where
  add := DivFunction.add
  zero := DivFunction.zero
  zero_add _ := ext fun _ ↦ zero_add _
  add_zero _ := ext fun _ ↦ add_zero _

@[simp] lemma zero_apply (x : ℝ) : (0 : DivFunction) x = 0 := rfl

@[simp] lemma add_apply (f g : DivFunction) (x : ℝ) : (f + g) x = f x + g x := rfl

noncomputable
instance : AddCommMonoid DivFunction where
  nsmul n f := nsmulRec n f
  add_assoc _ _ _ := ext fun _ ↦ add_assoc _ _ _
  add_comm _ _ := ext fun _ ↦ add_comm _ _
  __ := DivFunction.instAddZeroClass

noncomputable
instance : Module ℝ≥0 DivFunction where
  smul c f := {
    toFun := fun x ↦ c * f x
    one := sorry
    rightDerivOne := sorry
    convexOn' := sorry
    continuousOn' := sorry}
  one_smul _ := ext fun _ ↦ one_mul _
  mul_smul _ _ _ := ext fun _ ↦ sorry  -- mul_assoc _ _ _
  smul_zero _ := ext fun _ ↦ mul_zero _
  smul_add _ _ _ := ext fun _ ↦ mul_add _ _ _
  add_smul _ _ _ := ext fun _ ↦ sorry  -- add_mul _ _ _
  zero_smul _ := ext fun _ ↦ zero_mul _

@[simp] lemma smul_apply (c : ℝ≥0) (f : DivFunction) (x : ℝ) : (c • f) x = c * f x := rfl

def derivAtTop (f : DivFunction) : ℝ≥0∞ := sorry

@[simp]
lemma derivAtTop_zero : derivAtTop (0 : DivFunction) = 0 := sorry

lemma derivAtTop_congr (h : f =ᶠ[atTop] g) : f.derivAtTop = g.derivAtTop := sorry

lemma derivAtTop_congr_nonneg (h : ∀ x, 0 ≤ x → f x = g x) : f.derivAtTop = g.derivAtTop := by
  sorry

@[simp]
lemma derivAtTop_add : (f + g).derivAtTop = f.derivAtTop + g.derivAtTop := sorry

@[simp]
lemma derivAtTop_smul {c : ℝ≥0} : (c • f).derivAtTop = c * f.derivAtTop := sorry

lemma lintegral_comp_rnDeriv_ne_top (μ ν : Measure α) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (hf_deriv : f.derivAtTop ≠ ∞) :
    ∫⁻ x, f (μ.rnDeriv ν x).toReal ∂ν ≠ ∞ := by
  obtain ⟨c, c', h⟩ : ∃ c c', ∀ x, _ → c * x + c' ≤ (f x).toReal :=
    f.convexOn_toReal.exists_affine_le (convex_Ici 0)
  sorry
  -- refine integrable_of_le_of_le (f := fun x ↦ f (μ.rnDeriv ν x).toReal)
  --   (g₁ := fun x ↦ c * (μ.rnDeriv ν x).toReal + c')
  --   (g₂ := fun x ↦ (derivAtTop f).toReal * (μ.rnDeriv ν x).toReal + f 0)
  --   ?_ ?_ ?_ ?_ ?_
  -- · exact (hf.comp_measurable (μ.measurable_rnDeriv ν).ennreal_toReal).aestronglyMeasurable
  -- · exact ae_of_all _ (fun x ↦ h _ ENNReal.toReal_nonneg)
  -- · refine ae_of_all _ (fun x ↦ ?_)
  --   have h := le_add_derivAtTop'' hf_cvx hf_deriv le_rfl
  --     (ENNReal.toReal_nonneg : 0 ≤ (μ.rnDeriv ν x).toReal)
  --   rwa [zero_add, add_comm] at h
  -- · refine (Integrable.const_mul ?_ _).add (integrable_const _)
  --   exact Measure.integrable_toReal_rnDeriv
  -- · refine (Integrable.const_mul ?_ _).add (integrable_const _)
  --   exact Measure.integrable_toReal_rnDeriv

end DivFunction

end ProbabilityTheory
