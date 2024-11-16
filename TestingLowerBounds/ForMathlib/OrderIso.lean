/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!

# Order isos between real intervals

-/

open Set

noncomputable
def IooOrderIsoIoo {a b : ℝ} (hab : a < b) : Ioo a b ≃o Ioo (0 : ℝ) 1 where
  toFun := fun x ↦ ⟨(x - a) / (b - a), by
    rw [mem_Ioo]
    constructor
    · refine div_pos ?_ ?_
      · simp [x.2.1]
      · simp [hab]
    · rw [div_lt_one]
      · simp [x.2.2]
      · simp [hab]⟩
  invFun x := ⟨a + (b - a) * x, by
    simp only [mem_Ioo, lt_add_iff_pos_right]
    constructor
    · exact mul_pos (by simp [hab]) x.2.1
    · rw [← lt_sub_iff_add_lt']
      exact mul_lt_of_lt_one_right (by simp [hab]) x.2.2⟩
  left_inv x := by
    ext
    simp only
    rw [mul_div_cancel₀]
    · ring
    · rw [sub_ne_zero]
      exact hab.ne'
  right_inv x := by
    ext
    simp only [add_sub_cancel_left]
    rw [mul_div_cancel_left₀]
    rw [sub_ne_zero]
    exact hab.ne'
  map_rel_iff' {x y} := by
    simp only [Equiv.coe_fn_mk, Subtype.mk_le_mk]
    rw [div_le_div_right, sub_le_sub_iff_right]
    · norm_cast
    · simp [hab]

@[simp]
lemma IooOrderIsoIoo_apply_coe {a b : ℝ} {hab : a < b} (x : Ioo a b) :
    (IooOrderIsoIoo hab x : ℝ) = (x - a) / (b - a) := rfl

@[simp]
lemma IooOrderIsoIoo_symm_apply_coe {a b : ℝ} {hab : a < b} (x : Ioo (0 : ℝ) 1) :
    ((IooOrderIsoIoo hab).symm x : ℝ) = a + (b - a) * x := rfl

noncomputable
def IooOrderIsoReal : (Ioo (0 : ℝ) 1) ≃o ℝ where
  toFun x := Real.log (x / (1 - x))
  invFun y := ⟨Real.exp y / (1 + Real.exp y), by
    simp only [mem_Ioo]
    constructor
    · rw [lt_div_iff₀]
      · simp [Real.exp_pos]
      · positivity
    · rw [div_lt_iff₀]
      · simp
      · positivity⟩
  left_inv x := by
    ext
    simp only
    rw [Real.exp_log (div_pos x.2.1 (by simp [x.2.2]))]
    field_simp
    rw [mul_add, mul_one, mul_div_cancel₀]
    · simp
    · rw [sub_ne_zero]
      exact x.2.2.ne'
  right_inv x := by
    simp only
    have h_pos x : 1 + Real.exp x ≠ 0 := (ne_of_lt (by positivity)).symm
    rw [one_sub_div, Real.log_div, Real.log_div, add_sub_cancel_right, one_div, Real.log_inv,
      Real.log_exp]
    · ring
    · exact (Real.exp_pos _).ne'
    · exact h_pos _
    · simp [h_pos]
    · simp [h_pos]
    · simp [h_pos]
  map_rel_iff' := by
    intro x y
    simp only [Equiv.coe_fn_mk]
    rw [Real.log_le_log_iff]
    rotate_left
    · exact div_pos x.2.1 (by simp [x.2.2])
    · exact div_pos y.2.1 (by simp [y.2.2])
    rw [div_le_div_iff, mul_sub, mul_sub, mul_one, mul_one, mul_comm, sub_le_sub_iff_right]
    · norm_cast
    · simp [x.2.2]
    · simp [y.2.2]

@[simp]
lemma IooOrderIsoReal_apply (x : Ioo (0 : ℝ) 1) :
    IooOrderIsoReal x = Real.log (x / (1 - x)) := rfl

@[simp]
lemma IooOrderIsoReal_symm_apply_coe (x : ℝ) :
    (IooOrderIsoReal.symm x : ℝ) = Real.exp x / (1 + Real.exp x) := rfl
