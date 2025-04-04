import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

open scoped ENNReal NNReal Topology
open Filter Set

@[simp]
lemma frontier_singleton {X : Type*} [TopologicalSpace X] [T1Space X] (x : X) [(𝓝[≠] x).NeBot] :
    frontier {x} = {x} := by simp [frontier]

namespace EReal

instance : CharZero EReal := inferInstanceAs (CharZero (WithBot (WithTop ℝ)))

instance : NoZeroDivisors EReal where
  eq_zero_or_eq_zero_of_mul_eq_zero := by
    intro a b h
    contrapose! h
    induction a <;> induction b <;> try {· simp_all [← EReal.coe_mul]}
    · rcases lt_or_gt_of_ne h.2 with (h | h)
        <;> simp [EReal.bot_mul_of_neg, EReal.bot_mul_of_pos, h]
    · rcases lt_or_gt_of_ne h.1 with (h | h)
        <;> simp [EReal.mul_bot_of_pos, EReal.mul_bot_of_neg, h]
    · rcases lt_or_gt_of_ne h.1 with (h | h)
        <;> simp [EReal.mul_top_of_neg, EReal.mul_top_of_pos, h]
    · rcases lt_or_gt_of_ne h.2 with (h | h)
        <;> simp [EReal.top_mul_of_pos, EReal.top_mul_of_neg, h]

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
  | symm h => simp [mul_comm, h, and_comm]
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
  | symm h => simp [mul_comm, h, and_comm]
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

lemma add_eq_top_iff {x y : EReal} : x + y = ⊤ ↔ x = ⊤ ∧ y ≠ ⊥ ∨ x ≠ ⊥ ∧ y = ⊤ := by
  induction x <;> induction y
  · simp
  · simp
  · simp
  · simp
  · simp only [coe_ne_top, ne_eq, coe_ne_bot, not_false_eq_true, and_true, and_false,
      or_self, iff_false]
    norm_cast
    exact coe_ne_top _
  · simp
  · simp
  · simp
  · simp

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

lemma sub_nonneg' {x y : EReal} (h : x ≠ ⊤ ∨ y ≠ ⊤) (h' : x ≠ ⊥ ∨ y ≠ ⊥) :
    0 ≤ x - y ↔ y ≤ x := by
  induction x <;> induction y
  · simp at h'
  · simp
  · simp
  · simp
  · norm_cast
    simp
  · simp
  · simp
  · simp
  · simp at h

lemma sub_nonneg {x y : EReal} (hy : y ≠ ⊤) (hy' : y ≠ ⊥) : 0 ≤ x - y ↔ y ≤ x := by
  refine sub_nonneg' (Or.inr hy) (Or.inr hy')

lemma sub_nonpos {x y : EReal} : x - y ≤ 0 ↔ x ≤ y := by
  by_cases hy : y = ⊤
  · simp [hy]
  by_cases hy' : y = ⊥
  · simp only [hy', le_bot_iff]
    rw [sub_eq_add_neg, neg_bot]
    induction x <;> simp
  lift y to ℝ using ⟨hy, hy'⟩
  induction x <;> simp [← EReal.coe_sub]

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

section MeasurableMul

variable {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}

theorem measurable_from_prod_countable'' [Countable β] [MeasurableSingletonClass β]
    {f : β × α → γ} (hf : ∀ y, Measurable fun x => f (y, x)) :
    Measurable f := by
  change Measurable ((fun (p : α × β) ↦ f (p.2, p.1)) ∘ Prod.swap)
  exact (measurable_from_prod_countable hf).comp measurable_swap

theorem measurable_of_measurable_real_prod {f : EReal × β → γ}
    (h_real : Measurable fun p : ℝ × β ↦ f (p.1, p.2))
    (h_bot : Measurable fun x ↦ f (⊥, x)) (h_top : Measurable fun x ↦ f (⊤, x)) :
    Measurable f := by
  have : (univ : Set (EReal × β)) = ({⊥, ⊤} ×ˢ univ) ∪ ({⊥, ⊤}ᶜ ×ˢ univ) := by
    ext x
    simp only [mem_univ, mem_union, mem_prod, mem_insert_iff, mem_singleton_iff, and_true,
      mem_compl_iff, not_or, true_iff]
    tauto
  refine measurable_of_measurable_union_cover ({⊥, ⊤} ×ˢ univ)
    ({⊥, ⊤}ᶜ ×ˢ univ) ?_ ?_ ?_ ?_ ?_
  · refine MeasurableSet.prod ?_ MeasurableSet.univ
    simp only [measurableSet_insert, MeasurableSet.singleton]
  · refine (MeasurableSet.compl ?_).prod MeasurableSet.univ
    simp only [measurableSet_insert, MeasurableSet.singleton]
  · rw [this]
  · let e : ({⊥, ⊤} ×ˢ univ : Set (EReal × β)) ≃ᵐ ({⊥, ⊤} : Set EReal) × β :=
      (MeasurableEquiv.Set.prod ({⊥, ⊤} : Set EReal) (univ : Set β)).trans
        (MeasurableEquiv.prodCongr (MeasurableEquiv.refl _) (MeasurableEquiv.Set.univ β))
    have : ((fun (a : ({⊥, ⊤} : Set EReal) × β) ↦ f (a.1, a.2)) ∘ e)
        = fun (a : ({⊥, ⊤} ×ˢ univ : Set (EReal × β))) ↦ f a := rfl
    rw [← this]
    refine Measurable.comp ?_ e.measurable
    refine measurable_from_prod_countable'' fun y ↦ ?_
    simp only
    have h' := y.2
    simp only [mem_insert_iff, mem_singleton_iff, bot_ne_top, or_false, top_ne_bot, or_true] at h'
    cases h' with
    | inl h => rwa [h]
    | inr h => rwa [h]
  · let e : ({⊥, ⊤}ᶜ ×ˢ univ : Set (EReal × β)) ≃ᵐ ℝ × β :=
      (MeasurableEquiv.Set.prod ({⊥, ⊤}ᶜ : Set EReal) (univ : Set β)).trans
        (MeasurableEquiv.prodCongr MeasurableEquiv.erealEquivReal (MeasurableEquiv.Set.univ β))
    rw [← MeasurableEquiv.measurable_comp_iff e.symm]
    exact h_real

theorem measurable_of_measurable_real_real {f : EReal × EReal → β}
    (h_real : Measurable fun p : ℝ × ℝ ↦ f (p.1, p.2))
    (h_bot_left : Measurable fun r : ℝ ↦ f (⊥, r))
    (h_top_left : Measurable fun r : ℝ ↦ f (⊤, r))
    (h_bot_right : Measurable fun r : ℝ ↦ f (r, ⊥))
    (h_top_right : Measurable fun r : ℝ ↦ f (r, ⊤)) :
    Measurable f := by
  refine measurable_of_measurable_real_prod ?_ ?_ ?_
  · refine measurable_swap_iff.mp <| measurable_of_measurable_real_prod ?_ h_bot_right h_top_right
    exact h_real.comp measurable_swap
  · exact measurable_of_measurable_real h_bot_left
  · exact measurable_of_measurable_real h_top_left

private lemma measurable_const_mul (c : EReal) : Measurable fun (x : EReal) ↦ c * x := by
  refine measurable_of_measurable_real ?_
  induction c with
  | h_bot =>
    have : (fun (p : ℝ) ↦ (⊥ : EReal) * p)
        = fun p ↦ if p = 0 then (0 : EReal) else (if p < 0 then ⊤ else ⊥) := by
      ext p
      split_ifs with h1 h2
      · simp [h1]
      · rw [bot_mul_coe_of_neg h2]
      · rw [bot_mul_coe_of_pos]
        exact lt_of_le_of_ne (not_lt.mp h2) (Ne.symm h1)
    rw [this]
    refine Measurable.piecewise (measurableSet_singleton _) measurable_const ?_
    exact Measurable.piecewise measurableSet_Iio measurable_const measurable_const
  | h_real c => exact (measurable_id.const_mul _).coe_real_ereal
  | h_top =>
    have : (fun (p : ℝ) ↦ (⊤ : EReal) * p)
        = fun p ↦ if p = 0 then (0 : EReal) else (if p < 0 then ⊥ else ⊤) := by
      ext p
      split_ifs with h1 h2
      · simp [h1]
      · rw [top_mul_coe_of_neg h2]
      · rw [top_mul_coe_of_pos]
        exact lt_of_le_of_ne (not_lt.mp h2) (Ne.symm h1)
    rw [this]
    refine Measurable.piecewise (measurableSet_singleton _) measurable_const ?_
    exact Measurable.piecewise measurableSet_Iio measurable_const measurable_const

instance : MeasurableMul₂ EReal := by
  refine ⟨measurable_of_measurable_real_real ?_ ?_ ?_ ?_ ?_⟩
  · exact (measurable_fst.mul measurable_snd).coe_real_ereal
  · exact (measurable_const_mul _).comp measurable_coe_real_ereal
  · exact (measurable_const_mul _).comp measurable_coe_real_ereal
  · simp_rw [mul_comm _ ⊥]
    exact (measurable_const_mul _).comp measurable_coe_real_ereal
  · simp_rw [mul_comm _ ⊤]
    exact (measurable_const_mul _).comp measurable_coe_real_ereal

end MeasurableMul

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

lemma toENNReal_eq_toENNReal {x y : EReal} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    x.toENNReal = y.toENNReal ↔ x = y := by
  induction x <;> induction y
  · simp
  · simp at hx
  · simp
  · simp at hy
  · simp only [ne_eq, coe_ne_top, not_false_eq_true, toENNReal_of_ne_top,
      toReal_coe, EReal.coe_eq_coe_iff]
    rw [ENNReal.ofReal_eq_ofReal_iff]
    · exact mod_cast hx
    · exact mod_cast hy
  · simp
  · simp
  · simp
  · simp

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

lemma toENNReal_add_le {x y : EReal} :
    (x + y).toENNReal ≤ x.toENNReal + y.toENNReal := by
  induction x <;> induction y <;> try {· simp_all}
  norm_cast
  simp_rw [real_coe_toENNReal]
  exact ENNReal.ofReal_add_le

lemma toENNReal_add {x y : EReal} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (x + y).toENNReal = x.toENNReal + y.toENNReal := by
  induction x <;> induction y <;> try {· simp_all}
  norm_cast
  simp_rw [real_coe_toENNReal]
  simp_all [ENNReal.ofReal_add]

lemma toENNReal_sub {x y : EReal} (hy : 0 ≤ y) :
    (x - y).toENNReal = x.toENNReal - y.toENNReal := by
  induction x <;> induction y <;> try {· simp_all}
  rename_i x y
  simp only [ne_eq, coe_ne_top, not_false_eq_true, toENNReal_of_ne_top, toReal_coe]
  by_cases hxy : x ≤ y
  · rw [toENNReal_of_nonpos]
    swap; · exact sub_nonpos.mpr <| EReal.coe_le_coe_iff.mpr hxy
    simp_all
  · rw [toENNReal_of_ne_top, ← EReal.coe_sub, toReal_coe,
      ENNReal.ofReal_sub x (EReal.coe_nonneg.mp hy)]
    exact Ne.symm (ne_of_beq_false rfl)

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

@[simp]
lemma toENNReal_one : (1 : EReal).toENNReal = 1 := by
  rw [toENNReal, if_neg (ne_of_beq_false rfl)]
  simp

lemma sub_add_sub_cancel (b a : EReal) (c : ℝ) :
    b - c + (c - a) = b - a := by
  induction a <;> induction b
  · simp
  · simp only [coe_sub_bot]
    rw [← coe_sub, coe_add_top]
  · simp
  · simp
  · norm_cast
    ring
  · simp only [top_sub_coe]
    rw [← coe_sub, top_add_coe]
  · simp
  · simp
  · simp

lemma toENNReal_sub_le_add (b a c : EReal) :
    (b - a).toENNReal ≤ (b - c).toENNReal + (c - a).toENNReal := by
  by_cases hc_top : c = ⊤
  · simp only [hc_top, sub_top, ne_eq, bot_ne_top, not_false_eq_true,
      toENNReal_of_ne_top, toReal_bot, ENNReal.ofReal_zero, zero_add]
    by_cases ha : a = ⊤
    · simp [ha]
    · simp [top_sub_of_ne_top ha]
  by_cases hc_bot : c = ⊥
  · simp [hc_bot, sub_eq_add_neg]
    by_cases hb_bot : b = ⊥
    · simp [hb_bot]
    · simp [add_top_of_ne_bot hb_bot]
  refine (toENNReal_le_toENNReal ?_).trans toENNReal_add_le
  lift c to ℝ using ⟨hc_top, hc_bot⟩ with c
  rw [sub_add_sub_cancel]

lemma toENNReal_sub_add_cancel {b a c : EReal} (hac : a ≤ c) (hcb : c ≤ b) :
    (b - c).toENNReal + (c - a).toENNReal = (b - a).toENNReal := by
  induction c
  · have ha : a = ⊥ := eq_bot_iff.mpr hac
    simp [ha]
  · rw [← toENNReal_add, sub_add_sub_cancel]
    · rwa [sub_nonneg (coe_ne_top _) (coe_ne_bot _)]
    · by_cases ha : a = ⊥
      · simp [ha]
      rwa [sub_nonneg _ ha]
      exact (hac.trans_lt (coe_lt_top _)).ne
  · have hb : b = ⊤ := eq_top_iff.mpr hcb
    simp [hb]

lemma continuousAt_sub {p : EReal × EReal} (h : p.1 ≠ ⊤ ∨ p.2 ≠ ⊤) (h' : p.1 ≠ ⊥ ∨ p.2 ≠ ⊥) :
    ContinuousAt (fun p : EReal × EReal ↦ p.1 - p.2) p := by
  simp_rw [sub_eq_add_neg]
  change ContinuousAt ((fun p : EReal × EReal => p.1 + p.2) ∘ (fun p ↦ (p.1, -p.2))) p
  refine ContinuousAt.comp ?_ ?_
  · refine EReal.continuousAt_add ?_ ?_
    · simp [h]
    · simp [h']
  · fun_prop

lemma continuousAt_const_sub {c x : EReal} (h' : x ≠ ⊤ ∨ c ≠ ⊤) :
    ContinuousAt (fun x : EReal ↦ c - x) x := by
  by_cases hc_top : c = ⊥
  · simp [hc_top]
    exact continuous_const.continuousAt
  change ContinuousAt ((fun p : EReal × EReal ↦ p.1 - p.2) ∘ (fun x ↦ (c, x))) x
  exact (EReal.continuousAt_sub h'.symm (Or.inl hc_top)).comp (by fun_prop)

lemma continuousAt_sub_const {c x : EReal} (h' : x ≠ ⊥ ∨ c ≠ ⊥) :
    ContinuousAt (fun x : EReal ↦ x - c) x := by
  by_cases hc_top : c = ⊤
  · simp [hc_top]
    exact continuous_const.continuousAt
  change ContinuousAt ((fun p : EReal × EReal ↦ p.1 - p.2) ∘ (fun x ↦ (x, c))) x
  exact (EReal.continuousAt_sub (Or.inr hc_top) h').comp (by fun_prop)

lemma continuous_coe_mul {c : ℝ} : Continuous (fun x : EReal ↦ c * x) := by
  by_cases hc0 : c = 0
  · simp only [hc0, EReal.coe_zero, zero_mul]
    exact continuous_const
  rw [continuous_iff_continuousAt]
  intro x
  have h_cont : ContinuousAt (fun p : EReal × EReal ↦ p.1 * p.2) (c, x) := by
    refine EReal.continuousAt_mul ?_ ?_ ?_ ?_ <;> exact Or.inl (by simp [hc0])
  refine h_cont.comp ?_
  fun_prop

lemma continuous_toENNReal : Continuous EReal.toENNReal := by
  refine continuous_if' ?_ ?_ ?_ ?_
  · simp only [setOf_eq_eq_singleton]
    intro a ha
    simp only [frontier_singleton, mem_singleton_iff] at ha
    simp [ha]
  · intro a ha
    simp only [setOf_eq_eq_singleton, frontier_singleton, mem_singleton_iff] at ha
    simp only [ha, ↓reduceIte, ENNReal.tendsto_ofReal_nhds_top]
    exact EReal.tendsto_toReal_atTop
  · fun_prop
  · intro x hx
    by_cases hx_bot : x = ⊥
    · simp only [hx_bot]
      refine (tendsto_congr' ?_).mpr tendsto_const_nhds
      simp only [EReal.toReal_bot, ENNReal.ofReal_zero]
      suffices (fun x : EReal ↦ ENNReal.ofReal x.toReal) =ᶠ[𝓝 ⊥] fun _ ↦ 0 from
        EventuallyEq.filter_mono this nhdsWithin_le_nhds
      rw [EventuallyEq, eventually_nhds_iff]
      refine ⟨Iio 0, fun y hy ↦ ?_, isOpen_Iio, by simp⟩
      rw [ENNReal.ofReal_eq_zero]
      exact EReal.toReal_nonpos hy.le
    refine ENNReal.continuous_ofReal.continuousAt.comp_continuousWithinAt ?_
    refine ContinuousAt.continuousWithinAt ?_
    refine EReal.continuousOn_toReal.continuousAt ?_
    rw [← EReal.range_coe, EReal.range_coe_eq_Ioo, mem_nhds_iff]
    exact ⟨Ioo ⊥ ⊤, subset_rfl, isOpen_Ioo, ⟨Ne.bot_lt hx_bot, Ne.lt_top hx⟩⟩

lemma tendsto_atTop_toENNReal : Tendsto EReal.toENNReal atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro b
  refine ⟨b, fun a hba ↦ ?_⟩
  have : b = (b : EReal).toENNReal := by simp
  rw [this]
  exact EReal.toENNReal_le_toENNReal hba

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
