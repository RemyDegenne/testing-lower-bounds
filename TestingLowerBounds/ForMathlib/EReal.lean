import Mathlib.Data.Real.EReal
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

open scoped ENNReal NNReal Topology
open Filter

namespace EReal

instance : CharZero EReal := inferInstanceAs (CharZero (WithBot (WithTop ℝ)))

lemma eq_coe_of_ne_top_of_ne_bot {x : EReal} (hx : x ≠ ⊤) (hx' : x ≠ ⊥) : ∃ r : ℝ, x = r := by
  induction x <;> tauto

lemma coe_ennreal_toReal {x : ℝ≥0∞} (hx : x ≠ ∞) : (x.toReal : EReal) = x := by
  lift x to ℝ≥0 using hx
  rfl

lemma lt_neg_iff_lt_neg {x y : EReal} : x < -y ↔ y < -x := by
  nth_rw 1 [← neg_neg x, neg_lt_neg_iff]

lemma le_neg_iff_le_neg {x y : EReal} : x ≤ -y ↔ y ≤ -x := by
  nth_rw 1 [← neg_neg x, neg_le_neg_iff]

lemma neg_le_iff_neg_le {x y : EReal} : -x ≤ y ↔ -y ≤ x := by
  nth_rw 1 [← neg_neg y, neg_le_neg_iff]

lemma top_mul_ennreal_coe {x : ℝ≥0∞} (hx : x ≠ 0) : ⊤ * (x : EReal) = ⊤ := by
  by_cases hx_top : x = ∞
  · simp [hx_top]
  · rw [← coe_ennreal_toReal hx_top, top_mul_coe_of_pos]
    exact ENNReal.toReal_pos hx hx_top

lemma ennreal_coe_mul_top {x : ℝ≥0∞} (hx : x ≠ 0) : (x : EReal) * ⊤ = ⊤ := by
  rw [mul_comm, top_mul_ennreal_coe hx]

lemma mul_eq_top (a b : EReal) :
    a * b = ⊤ ↔ (a = ⊥ ∧ b < 0) ∨ (a < 0 ∧ b = ⊥) ∨ (a = ⊤ ∧ 0 < b) ∨ (0 < a ∧ b = ⊤) := by
  induction a, b using EReal.induction₂_symm with
  | symm h =>
    rw [mul_comm, h]
    refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
      <;> cases h with
      | inl h => exact Or.inr (Or.inl ⟨h.2, h.1⟩)
      | inr h => cases h with
        | inl h => exact Or.inl ⟨h.2, h.1⟩
        | inr h => cases h with
          | inl h => exact Or.inr (Or.inr (Or.inr ⟨h.2, h.1⟩))
          | inr h => exact Or.inr (Or.inr (Or.inl ⟨h.2, h.1⟩))
  | top_top => simp
  | top_pos _ hx => simp [EReal.top_mul_coe_of_pos hx, hx]
  | top_zero => simp
  | top_neg _ hx => simp [hx.le, EReal.top_mul_coe_of_neg hx]
  | top_bot => simp
  | pos_bot _ hx => simp [hx.le, EReal.coe_mul_bot_of_pos hx]
  | coe_coe x y =>
    simp only [EReal.coe_ne_bot, EReal.coe_neg', false_and, and_false, EReal.coe_ne_top,
      EReal.coe_pos, or_self, iff_false]
    rw [← EReal.coe_mul]
    exact EReal.coe_ne_top _
  | zero_bot => simp
  | neg_bot _ hx => simp [hx, EReal.coe_mul_bot_of_neg hx]
  | bot_bot => simp

lemma mul_ne_top (a b : EReal) :
    a * b ≠ ⊤ ↔ (a ≠ ⊥ ∨ 0 ≤ b) ∧ (0 ≤ a ∨ b ≠ ⊥) ∧ (a ≠ ⊤ ∨ b ≤ 0) ∧ (a ≤ 0 ∨ b ≠ ⊤) := by
  rw [ne_eq, mul_eq_top]
  set_option push_neg.use_distrib true in push_neg
  rfl

lemma mul_eq_bot (a b : EReal) :
    a * b = ⊥ ↔ (a = ⊥ ∧ 0 < b) ∨ (0 < a ∧ b = ⊥) ∨ (a = ⊤ ∧ b < 0) ∨ (a < 0 ∧ b = ⊤) := by
  induction a, b using EReal.induction₂_symm with
  | symm h =>
    rw [mul_comm, h]
    refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
      <;> cases h with
      | inl h => exact Or.inr (Or.inl ⟨h.2, h.1⟩)
      | inr h => cases h with
        | inl h => exact Or.inl ⟨h.2, h.1⟩
        | inr h => cases h with
          | inl h => exact Or.inr (Or.inr (Or.inr ⟨h.2, h.1⟩))
          | inr h => exact Or.inr (Or.inr (Or.inl ⟨h.2, h.1⟩))
  | top_top => simp
  | top_pos x hx => simp [EReal.top_mul_coe_of_pos hx, hx.le]
  | top_zero => simp
  | top_neg _ hx => simp [hx, EReal.top_mul_coe_of_neg hx]
  | top_bot => simp
  | pos_bot _ hx => simp [hx, EReal.coe_mul_bot_of_pos hx]
  | coe_coe x y =>
    simp only [EReal.coe_ne_bot, EReal.coe_neg', false_and, and_false, EReal.coe_ne_top,
      EReal.coe_pos, or_self, iff_false]
    rw [← EReal.coe_mul]
    exact EReal.coe_ne_bot _
  | zero_bot => simp
  | neg_bot _ hx => simp [hx.le, EReal.coe_mul_bot_of_neg hx]
  | bot_bot => simp

lemma mul_ne_bot (a b : EReal) :
    a * b ≠ ⊥ ↔ (a ≠ ⊥ ∨ b ≤ 0) ∧ (a ≤ 0 ∨ b ≠ ⊥) ∧ (a ≠ ⊤ ∨ 0 ≤ b) ∧ (0 ≤ a ∨ b ≠ ⊤) := by
  rw [ne_eq, mul_eq_bot]
  set_option push_neg.use_distrib true in push_neg
  rfl

lemma mul_pos_iff {a b : EReal} : 0 < a * b ↔ 0 < a ∧ 0 < b ∨ a < 0 ∧ b < 0 := by
  induction a, b using EReal.induction₂_symm with
  | symm h =>
    simp [mul_comm, h, and_comm]
  | top_top => simp
  | top_pos _ hx => simp [EReal.top_mul_coe_of_pos hx, hx]
  | top_zero => simp
  | top_neg _ hx => simp [hx, EReal.top_mul_coe_of_neg hx, le_of_lt]
  | top_bot => simp
  | pos_bot _ hx => simp [hx, EReal.coe_mul_bot_of_pos hx, le_of_lt]
  | coe_coe x y => simp [← coe_mul, _root_.mul_pos_iff]
  | zero_bot => simp
  | neg_bot _ hx => simp [hx, EReal.coe_mul_bot_of_neg hx]
  | bot_bot => simp

lemma mul_neg_iff {a b : EReal} : a * b < 0 ↔ 0 < a ∧ b < 0 ∨ a < 0 ∧ 0 < b := by
  nth_rw 1 [← neg_zero]
  rw [lt_neg_iff_lt_neg, ← mul_neg, mul_pos_iff, neg_lt_iff_neg_lt, lt_neg_iff_lt_neg, neg_zero]

lemma mul_nonneg_iff {a b : EReal} : 0 ≤ a * b ↔ 0 ≤ a ∧ 0 ≤ b ∨ a ≤ 0 ∧ b ≤ 0 := by
  induction a, b using EReal.induction₂_symm with
  | symm h =>
    simp [mul_comm, h, and_comm]
  | top_top => simp
  | top_pos _ hx => simp [EReal.top_mul_coe_of_pos hx, hx, le_of_lt]
  | top_zero => simp
  | top_neg _ hx => simp [hx, EReal.top_mul_coe_of_neg hx]
  | top_bot => simp
  | pos_bot _ hx => simp [hx, EReal.coe_mul_bot_of_pos hx]
  | coe_coe x y => simp [← coe_mul, _root_.mul_nonneg_iff]
  | zero_bot => simp
  | neg_bot _ hx => simp [hx, EReal.coe_mul_bot_of_neg hx, le_of_lt]
  | bot_bot => simp

lemma mul_nonpos_iff {a b : EReal} : a * b ≤ 0 ↔ 0 ≤ a ∧ b ≤ 0 ∨ a ≤ 0 ∧ 0 ≤ b := by
  nth_rw 1 [← neg_zero]
  rw [le_neg_iff_le_neg, ← mul_neg, mul_nonneg_iff, neg_le_iff_neg_le, le_neg_iff_le_neg, neg_zero]

lemma add_ne_top {x y : EReal} (hx : x ≠ ⊤) (hy : y ≠ ⊤) : x + y ≠ ⊤ := by
  induction x <;> tauto
  induction y <;> tauto
  exact ne_of_beq_false rfl

lemma add_ne_top_iff_of_ne_bot {x y : EReal} (hx : x ≠ ⊥) (hy : y ≠ ⊥) :
    x + y ≠ ⊤ ↔ x ≠ ⊤ ∧ y ≠ ⊤ := by
  refine ⟨?_, fun h ↦ add_ne_top h.1 h.2⟩
  induction x <;> simp_all
  induction y <;> simp_all

lemma add_ne_top_iff_of_ne_bot_of_ne_top {x y : EReal} (hy : y ≠ ⊥) (hy' : y ≠ ⊤) :
    x + y ≠ ⊤ ↔ x ≠ ⊤ := by
  induction x <;> simp [add_ne_top_iff_of_ne_bot, hy, hy']

lemma add_ne_bot_iff {x y : EReal} : x + y ≠ ⊥ ↔ x ≠ ⊥ ∧ y ≠ ⊥ := by
  simp_rw [ne_eq, EReal.add_eq_bot_iff]
  push_neg
  rfl

lemma add_ne_bot {x y : EReal} (hx : x ≠ ⊥) (hy : y ≠ ⊥) : x + y ≠ ⊥ :=
  add_ne_bot_iff.mpr ⟨hx, hy⟩

lemma coe_mul_add_of_nonneg {x : ℝ} (hx_nonneg : 0 ≤ x) (y z : EReal) :
    x * (y + z) = x * y + x * z := by
  by_cases hx0 : x = 0
  · simp [hx0]
  have hx_pos : 0 < x := hx_nonneg.lt_of_ne' hx0
  induction y
  · simp [EReal.coe_mul_bot_of_pos hx_pos]
  · induction z
    · simp [EReal.coe_mul_bot_of_pos hx_pos]
    · norm_cast
      rw [mul_add]
    · simp only [coe_add_top, EReal.coe_mul_top_of_pos hx_pos]
      rw [← EReal.coe_mul, EReal.coe_add_top]
  · simp only [EReal.coe_mul_top_of_pos hx_pos]
    induction z
    · simp [EReal.coe_mul_bot_of_pos hx_pos]
    · simp only [top_add_coe, EReal.coe_mul_top_of_pos hx_pos]
      rw [← EReal.coe_mul, EReal.top_add_coe]
    · simp [EReal.coe_mul_top_of_pos hx_pos]

lemma add_mul_coe_of_nonneg {x : ℝ} (hx_nonneg : 0 ≤ x) (y z : EReal) :
    (y + z) * x = y * x + z * x := by
  simp_rw [mul_comm _ (x : EReal)]
  exact EReal.coe_mul_add_of_nonneg hx_nonneg y z

lemma add_sub_cancel (x : EReal) (y : ℝ) : x + y - y = x := by
  induction x
  · simp
  · norm_cast
    ring
  · simp

lemma add_sub_cancel' (x : EReal) (y : ℝ) : y + x - y = x := by
  rw [add_comm, EReal.add_sub_cancel]

@[simp]
lemma sub_self {x : EReal} (h_top : x ≠ ⊤) (h_bot : x ≠ ⊥) : x - x = 0 := by
  induction x <;> simp_all [← coe_sub]

lemma sub_self_le_zero {x : EReal} : x - x ≤ 0 := by
  induction x <;> simp

lemma top_sub_of_ne_top {x : EReal} (hx : x ≠ ⊤) : ⊤ - x = ⊤ := by
  induction x <;> tauto

lemma top_mul_add_of_nonneg {x y : EReal} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    ⊤ * (x + y) = ⊤ * x + ⊤ * y := by
  induction x, y using EReal.induction₂_symm with
  | symm h =>
    rw [add_comm, add_comm (⊤ * _)]
    exact h hy hx
  | top_top => simp
  | top_pos _ h =>
    rw [top_add_coe, top_mul_top, top_mul_of_pos, top_add_top]
    exact mod_cast h
  | top_zero => simp
  | top_neg _ h =>
    refine absurd hy ?_
    exact mod_cast h.not_le
  | top_bot => simp
  | pos_bot => simp
  | coe_coe x y =>
    by_cases hx0 : x = 0
    · simp [hx0]
    by_cases hy0 : y = 0
    · simp [hy0]
    have hx_pos : 0 < (x : EReal) := by
      refine hx.lt_of_ne' ?_
      exact mod_cast hx0
    have hy_pos : 0 < (y : EReal) := by
      refine hy.lt_of_ne' ?_
      exact mod_cast hy0
    rw [top_mul_of_pos hx_pos, top_mul_of_pos hy_pos, top_mul_of_pos]
    · simp
    · exact add_pos hx_pos hy_pos
  | zero_bot => simp
  | neg_bot => simp
  | bot_bot => simp

lemma mul_add_coe_of_nonneg (x : EReal) {y z : ℝ} (hy : 0 ≤ y) (hz : 0 ≤ z) :
    x * (y + z) = x * y + x * z := by
  by_cases hx_top : x = ⊤
  · rw [hx_top]
    exact top_mul_add_of_nonneg (mod_cast hy) (mod_cast hz)
  by_cases hx_bot : x = ⊥
  · rw [hx_bot]
    by_cases hy0 : y = 0
    · simp [hy0]
    by_cases hz0 : z = 0
    · simp [hz0]
    have hy_pos : 0 < (y : EReal) := lt_of_le_of_ne' (mod_cast hy) (mod_cast hy0)
    have hz_pos : 0 < (z : EReal) := lt_of_le_of_ne' (mod_cast hz) (mod_cast hz0)
    rw [bot_mul_of_pos hy_pos, bot_mul_of_pos hz_pos, bot_mul_of_pos]
    · simp
    · exact add_pos hy_pos hz_pos
  lift x to ℝ using ⟨hx_top, hx_bot⟩
  norm_cast
  rw [mul_add]

lemma coe_add_mul_of_nonneg (x : EReal) {y z : ℝ} (hy : 0 ≤ y) (hz : 0 ≤ z) :
    (y + z) * x =  y * x + z * x := by
  simp_rw [mul_comm _ x]
  exact EReal.mul_add_coe_of_nonneg x hy hz

lemma toReal_nonneg {x : EReal} (hx : 0 ≤ x) : 0 ≤ x.toReal := by
  induction x
  · norm_num
  · simp only [toReal_coe]
    exact EReal.coe_nonneg.mp hx
  · norm_num

lemma toReal_nonpos {x : EReal} (hx : x ≤ 0) : x.toReal ≤ 0 := by
  induction x
  · norm_num
  · simp only [toReal_coe]
    exact EReal.coe_nonpos.mp hx
  · norm_num

lemma toReal_ne_zero_iff {x : EReal} : x.toReal ≠ 0 ↔ x ≠ 0 ∧ x ≠ ⊤ ∧ x ≠ ⊥ := by
  induction x <;> norm_num

lemma toReal_eq_zero_iff {x : EReal} : x.toReal = 0 ↔ x = 0 ∨ x = ⊤ ∨ x = ⊥ := by
  induction x <;> norm_num

lemma sub_nonneg {x y : EReal} (hy : y ≠ ⊤) (hy' : y ≠ ⊥) : 0 ≤ x - y ↔ y ≤ x := by
  obtain ⟨_, ha⟩ := eq_coe_of_ne_top_of_ne_bot hy hy'
  induction x <;> simp [← EReal.coe_sub, ha]

lemma sub_nonpos {x y : EReal} (hy : y ≠ ⊤) (hy' : y ≠ ⊥) : x - y ≤ 0 ↔ x ≤ y := by
  obtain ⟨_, ha⟩ := eq_coe_of_ne_top_of_ne_bot hy hy'
  induction x <;> simp [← EReal.coe_sub, ha]

@[simp]
lemma nsmul_eq_mul {n : ℕ} {x : EReal} : n • x = n * x := by
  induction n with
  | zero => rw [zero_smul, Nat.cast_zero, zero_mul]
  | succ n ih =>
    rw [succ_nsmul, ih, Nat.cast_succ]
    convert (EReal.coe_add_mul_of_nonneg x _ _).symm <;> simp

lemma lowerSemicontinuous_add : LowerSemicontinuous fun (p : EReal × EReal) ↦ p.1 + p.2 := by
  intro x
  by_cases hx1_bot : x.1 = ⊥
  · intro y
    simp [hx1_bot]
  by_cases hx2_bot : x.2 = ⊥
  · intro y
    simp [hx2_bot]
  refine ContinuousAt.lowerSemicontinuousAt ?_
  exact EReal.continuousAt_add (Or.inr hx2_bot) (Or.inl hx1_bot)

instance : MeasurableAdd₂ EReal := ⟨EReal.lowerSemicontinuous_add.measurable⟩

instance : MeasurableMul₂ EReal := by
  constructor
  sorry

theorem nhdsWithin_top : 𝓝[≠] (⊤ : EReal) = (atTop).map Real.toEReal := by
  apply (nhdsWithin_hasBasis nhds_top_basis_Ici _).ext (atTop_basis.map Real.toEReal)
  · simp only [EReal.image_coe_Ici, true_and]
    intro x hx
    by_cases hx_bot : x = ⊥
    · simp [hx_bot]
    lift x to ℝ using ⟨hx.ne_top, hx_bot⟩
    refine ⟨x, fun x ⟨h1, h2⟩ ↦ ?_⟩
    simp [h1, h2.ne_top]
  · simp only [EReal.image_coe_Ici, true_implies]
    refine fun x ↦ ⟨x, ⟨EReal.coe_lt_top x, fun x ⟨(h1 : _ ≤ x), h2⟩ ↦ ?_⟩⟩
    simp [h1, Ne.lt_top' fun a ↦ h2 a.symm]

lemma nhdsWithin_bot : 𝓝[≠] (⊥ : EReal) = (atBot).map Real.toEReal := by
  apply (nhdsWithin_hasBasis nhds_bot_basis_Iic _).ext (atBot_basis.map Real.toEReal)
  · simp only [EReal.image_coe_Iic, Set.subset_compl_singleton_iff, Set.mem_Ioc, lt_self_iff_false,
      bot_le, and_true, not_false_eq_true, true_and]
    intro x hx
    by_cases hx_top : x = ⊤
    · simp [hx_top]
    lift x to ℝ using ⟨hx_top, hx.ne_bot⟩
    refine ⟨x, fun x ⟨h1, h2⟩ ↦ ?_⟩
    simp [h2, h1.ne_bot]
  · simp only [EReal.image_coe_Iic, true_implies]
    refine fun x ↦ ⟨x, ⟨EReal.bot_lt_coe x, fun x ⟨(h1 : x ≤ _), h2⟩ ↦ ?_⟩⟩
    simp [h1, Ne.bot_lt' fun a ↦ h2 a.symm]

theorem tendsto_toReal_atTop : Tendsto EReal.toReal (𝓝[≠] ⊤) atTop := by
  rw [nhdsWithin_top, tendsto_map'_iff]
  exact tendsto_id

theorem tendsto_toReal_atBot : Tendsto EReal.toReal (𝓝[≠] ⊥) atBot := by
  rw [nhdsWithin_bot, tendsto_map'_iff]
  exact tendsto_id

/-- Reinterpret an EReal number `x` as an ENNReal number. Returns `0` if `x < 0`. -/
noncomputable def toENNReal (x : EReal) : ENNReal :=
  if x = ⊤ then ⊤
  else ENNReal.ofReal x.toReal

@[simp]
theorem toENNReal_top : (⊤ : EReal).toENNReal = ⊤ := rfl

@[simp]
lemma toENNReal_of_ne_top {x : EReal} (hx : x ≠ ⊤) : x.toENNReal = ENNReal.ofReal x.toReal :=
  if_neg hx

@[simp]
theorem toENNReal_eq_top_iff {x : EReal} : x.toENNReal = ⊤ ↔ x = ⊤ := by
  by_cases h : x = ⊤
  · simp [h]
  · simp [h, toENNReal]

theorem toENNReal_ne_top_iff {x : EReal} : x.toENNReal ≠ ⊤ ↔ x ≠ ⊤ := toENNReal_eq_top_iff.not

@[simp]
theorem toENNReal_of_nonpos {x : EReal} (hx : x ≤ 0) : x.toENNReal = 0 := by
  rw [toENNReal, if_neg ?_]
  exact ENNReal.ofReal_of_nonpos (toReal_nonpos hx)
  intro h
  rw [h, top_le_iff] at hx
  exact zero_ne_top hx

theorem toENNReal_eq_zero_iff {x : EReal} : x.toENNReal = 0 ↔ x ≤ 0 := by
  induction x <;> simp [toENNReal]

theorem toENNReal_ne_zero_iff {x : EReal} : x.toENNReal ≠ 0 ↔ 0 < x := by
  simp [toENNReal_eq_zero_iff.not]

@[simp]
theorem coe_toENNReal {x : EReal} (hx : 0 ≤ x) : (x.toENNReal : EReal) = x := by
  rw [toENNReal]
  by_cases h_top : x = ⊤
  · rw [if_pos h_top, h_top]
    rfl
  rw [if_neg h_top]
  simp only [coe_ennreal_ofReal, ge_iff_le, hx, toReal_nonneg, max_eq_left]
  exact coe_toReal h_top fun _ ↦ by simp_all only [le_bot_iff, zero_ne_bot]

@[simp]
theorem toENNReal_coe {x : ENNReal} : (x : EReal).toENNReal = x := by
  by_cases h_top : x = ⊤
  · rw [h_top, coe_ennreal_top, toENNReal_top]
  rw [toENNReal, if_neg _, toReal_coe_ennreal, ENNReal.ofReal_toReal_eq_iff]
  · exact h_top
  · simp [h_top]

theorem toENNReal_le_toENNReal {x y : EReal} (h : x ≤ y) : x.toENNReal ≤ y.toENNReal := by
  induction x
  · simp
  · by_cases hy_top : y = ⊤
    · simp [hy_top]
    simp_all [h, toENNReal]
    refine ENNReal.ofReal_le_ofReal ?_
    refine EReal.toReal_le_toReal h (coe_ne_bot _) hy_top
  · simp_all

@[simp]
lemma real_coe_toENNReal (x : ℝ) : (x : EReal).toENNReal = ENNReal.ofReal x := rfl

@[simp]
lemma toReal_toENNReal {x : EReal} (hx : 0 ≤ x) : x.toENNReal.toReal = x.toReal := by
  by_cases h : x = ⊤
  · simp [h]
  · simp [h, toReal_nonneg hx]

@[measurability]
theorem _root_.measurable_ereal_toENNReal : Measurable EReal.toENNReal :=
  EReal.measurable_of_measurable_real (by simpa using ENNReal.measurable_ofReal)

@[measurability, fun_prop]
theorem _root_.Measurable.ereal_toENNReal {α : Type*} {_ : MeasurableSpace α}
    {f : α → EReal} (hf : Measurable f) :
    Measurable fun x => (f x).toENNReal :=
  measurable_ereal_toENNReal.comp hf

lemma toENNReal_add {x y : EReal} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (x + y).toENNReal = x.toENNReal + y.toENNReal := by
  induction x <;> induction y <;> try {· simp_all}
  norm_cast
  simp_rw [real_coe_toENNReal]
  simp_all [ENNReal.ofReal_add]

lemma toENNReal_sub {x y : EReal} (hy : 0 ≤ y) :
    (x - y).toENNReal = x.toENNReal - y.toENNReal := by
  induction x <;> induction y <;> try {· simp_all}
  · rename_i x y
    simp only [ne_eq, coe_ne_top, not_false_eq_true, toENNReal_of_ne_top, toReal_coe]
    by_cases hxy : x ≤ y
    · rw [toENNReal_of_nonpos]
      swap; · exact (sub_nonpos (coe_ne_top y) (coe_ne_bot y)).mpr <| EReal.coe_le_coe_iff.mpr hxy
      simp_all
    · rw [toENNReal_of_ne_top, ← EReal.coe_sub, toReal_coe,
        ENNReal.ofReal_sub x (EReal.coe_nonneg.mp hy)]
      exact Ne.symm (ne_of_beq_false rfl)
  · rw [ENNReal.sub_eq_top_iff.mpr (by simp), top_sub_of_ne_top (coe_ne_top _), toENNReal_top]

lemma toENNReal_mul {x y : EReal} (hx : 0 ≤ x) :
    (x * y).toENNReal = x.toENNReal * y.toENNReal := by
  induction x <;> induction y
    <;> try {· simp_all [mul_nonpos_iff, ENNReal.ofReal_mul, ← EReal.coe_mul]}
  · rcases eq_or_lt_of_le hx with (hx | hx)
    · simp [← hx]
    · simp_all [EReal.mul_top_of_pos hx]
  · rename_i a
    rcases lt_trichotomy a 0 with (ha | ha | ha)
    · simp_all [le_of_lt, top_mul_of_neg (EReal.coe_neg'.mpr ha)]
    · simp [ha]
    · simp_all [top_mul_of_pos (EReal.coe_pos.mpr ha)]

lemma toENNReal_mul' {x y : EReal} (hy : 0 ≤ y) :
    (x * y).toENNReal = x.toENNReal * y.toENNReal := by
  rw [mul_comm, toENNReal_mul hy, mul_comm]

end EReal

namespace ENNReal

variable {a b c x y : ℝ≥0∞}

lemma toEReal_sub (hy_top : y ≠ ⊤) (h_le : y ≤ x) :
    (x - y).toEReal = x.toEReal - y.toEReal := by
  by_cases hx_top : x = ⊤
  · lift y to ℝ≥0 using hy_top
    simp only [hx_top, top_sub_coe, EReal.coe_ennreal_top]
    norm_cast
  have h_top : x - y ≠ ⊤ := by
    simp only [ne_eq, sub_eq_top_iff, hx_top, hy_top, not_false_eq_true, and_true]
  nth_rw 2 [← ENNReal.ofReal_toReal_eq_iff.mpr hy_top, ← ENNReal.ofReal_toReal_eq_iff.mpr hx_top]
  rw [← ENNReal.ofReal_toReal_eq_iff.mpr h_top]
  simp only [EReal.coe_ennreal_ofReal, ge_iff_le, toReal_nonneg, max_eq_left]
  rw [toReal_sub_of_le h_le hx_top]
  exact EReal.coe_sub _ _

--PR these 2 lemmas to mathlib, just after ENNReal.mul_max
-- #check ENNReal.mul_max
theorem min_mul : min a b * c = min (a * c) (b * c) := mul_right_mono.map_min

theorem mul_min : a * min b c = min (a * b) (a * c) := mul_left_mono.map_min

@[simp]
lemma toReal_toEReal_of_ne_top (hx : x ≠ ⊤) : x.toReal.toEReal = x.toEReal := by
  cases x <;> tauto

end ENNReal
