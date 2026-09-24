/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
module

public import Mathlib.Basic.ENNReal.Action
public import Mathlib.Basic.ENNReal.Real
public import Mathlib.Tactic.FieldSimp

/-!
# Auxiliary lemmas about `ℝ≥0∞`

-/

@[expose] public section

open Set

open scoped ENNReal NNReal

namespace ENNReal

lemma toReal_image_Ioo {x y : ℝ≥0∞} (hx : x ≠ ∞) (hy : y ≠ ∞) :
    ENNReal.toReal '' (Ioo x y) = Ioo x.toReal y.toReal := by
  ext a
  refine
    ⟨fun ⟨a', ⟨hxa, hay⟩, ha⟩ ↦ ha ▸ ⟨toReal_strict_mono hay.ne_top hxa, toReal_strict_mono hy hay⟩,
    fun ⟨hxa, hay⟩ ↦ ⟨.ofReal a, ⟨?_, ?_⟩, toReal_ofReal (toReal_nonneg.trans_lt hxa).le⟩⟩
  · rw [← ofReal_toReal hx, ofReal_lt_ofReal_iff']
    exact ⟨hxa, toReal_nonneg.trans_lt hxa⟩
  · rw [← ofReal_toReal hy, ofReal_lt_ofReal_iff']
    exact ⟨hay, (toReal_nonneg.trans_lt hxa).trans hay⟩

@[simp]
lemma toReal_image_Ioo_top {x : ℝ≥0∞} (hx : x ≠ ∞) :
    ENNReal.toReal '' (Ioo x ∞) = Ioi x.toReal := by
  ext a
  refine ⟨fun ⟨a', ⟨hxa, hay⟩, ha⟩ ↦ ha ▸ toReal_strict_mono hay.ne_top hxa,
    fun hxa ↦ ⟨.ofReal a, ⟨?_, ofReal_lt_top⟩, toReal_ofReal (toReal_nonneg.trans_lt hxa).le⟩⟩
  rw [← ofReal_toReal hx, ofReal_lt_ofReal_iff']
  exact ⟨hxa, toReal_nonneg.trans_lt hxa⟩

lemma preimage_toReal_Ioc {a b : ℝ} (h : 0 ≤ a) :
    ENNReal.toReal ⁻¹' Ioc a b = Ioc (ENNReal.ofReal a) (ENNReal.ofReal b) := by
  ext x
  rcases lt_or_ge b a with hb | hb
  · rw [Ioc_eq_empty (not_lt.mpr hb.le), Ioc_eq_empty]
    · simp
    · rw [not_lt, ENNReal.ofReal_le_ofReal_iff h]
      exact hb.le
  simp only [mem_preimage, mem_Ioc]
  by_cases hx_top : x = ∞
  · simp [hx_top, not_lt.mpr h]
  rw [ENNReal.le_ofReal_iff_toReal_le hx_top (h.trans hb),
    ENNReal.ofReal_lt_iff_lt_toReal h hx_top]

/-- A point of `[x, y]` (with `y ≠ ∞`) is a convex combination of `x` and `y` with `ℝ≥0` weights. -/
lemma exists_nnreal_smul_add_eq {x y z : ℝ≥0∞} (hy : y ≠ ∞) (hxz : x ≤ z) (hzy : z ≤ y) :
    ∃ u v : ℝ≥0, u + v = 1 ∧ u • x + v • y = z := by
  have hz : z ≠ ∞ := ne_top_of_le_ne_top hy hzy
  have hx : x ≠ ∞ := ne_top_of_le_ne_top hz hxz
  rcases eq_or_lt_of_le (hxz.trans hzy) with rfl | hxy
  · obtain rfl := le_antisymm hxz hzy
    exact ⟨1, 0, by simp, by simp⟩
  have hxy' : x.toReal < y.toReal := toReal_strict_mono hy hxy
  have hxy_ne : y.toReal - x.toReal ≠ 0 := (sub_pos.mpr hxy').ne'
  set v : ℝ := (z.toReal - x.toReal) / (y.toReal - x.toReal) with hv
  have hv0 : 0 ≤ v := div_nonneg (sub_nonneg.mpr (toReal_mono hz hxz)) (sub_nonneg.mpr hxy'.le)
  have hv1 : v ≤ 1 :=
    (div_le_one (sub_pos.mpr hxy')).mpr (sub_le_sub_right (toReal_mono hy hzy) _)
  refine ⟨(1 - v).toNNReal, v.toNNReal, ?_, ?_⟩
  · rw [← Real.toNNReal_add (sub_nonneg.mpr hv1) hv0, sub_add_cancel, Real.toNNReal_one]
  · rw [← toReal_eq_toReal_iff' (by simp [smul_def, mul_ne_top, hx, hy]) hz]
    simp only [smul_def, smul_eq_mul, toReal_add (mul_ne_top coe_ne_top hx)
        (mul_ne_top coe_ne_top hy), toReal_mul, coe_toReal,
      Real.coe_toNNReal _ (sub_nonneg.mpr hv1), Real.coe_toNNReal _ hv0]
    rw [hv]
    field_simp
    ring

/-- The truncated subtraction of finite extended nonnegative reals, as a real number. -/
lemma toReal_sub_eq_max_zero {a b : ℝ≥0∞} (ha : a ≠ ∞) (hb : b ≠ ∞) :
    (a - b).toReal = max 0 (a.toReal - b.toReal) := by
  rcases le_total a b with h | h
  · rw [tsub_eq_zero_of_le h, toReal_zero, max_eq_left (sub_nonpos.2 (toReal_mono hb h))]
  · rw [toReal_sub_of_le h ha, max_eq_right (sub_nonneg.2 (toReal_mono ha h))]

end ENNReal
