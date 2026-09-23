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

end ENNReal
