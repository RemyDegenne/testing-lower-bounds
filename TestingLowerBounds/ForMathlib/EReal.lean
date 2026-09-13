import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

open scoped ENNReal NNReal Topology
open Filter Set

@[simp]
lemma frontier_singleton {X : Type*} [TopologicalSpace X] [T1Space X] (x : X) [(𝓝[≠] x).NeBot] :
    frontier {x} = {x} := by simp [frontier]

namespace EReal

-- TODO: Deprecate this file

instance : CharZero EReal := inferInstanceAs (CharZero (WithBot (WithTop ℝ)))

instance : NoZeroDivisors EReal where
  eq_zero_or_eq_zero_of_mul_eq_zero := by
    intro a b h
    exact mul_eq_zero.mp h

lemma lt_neg_iff_lt_neg {x y : EReal} : x < -y ↔ y < -x := lt_neg_comm

lemma le_neg_iff_le_neg {x y : EReal} : x ≤ -y ↔ y ≤ -x := EReal.le_neg

lemma neg_le_iff_neg_le {x y : EReal} : -x ≤ y ↔ -y ≤ x := EReal.neg_le

lemma top_mul_ennreal_coe {x : ℝ≥0∞} (hx : x ≠ 0) : ⊤ * (x : EReal) = ⊤ :=
  top_mul_coe_ennreal hx

lemma ennreal_coe_mul_top {x : ℝ≥0∞} (hx : x ≠ 0) : (x : EReal) * ⊤ = ⊤ :=
  coe_ennreal_mul_top hx

lemma add_ne_top_iff_of_ne_bot {x y : EReal} (hx : x ≠ ⊥) (hy : y ≠ ⊥) :
    x + y ≠ ⊤ ↔ x ≠ ⊤ ∧ y ≠ ⊤ := add_ne_top_iff_ne_top₂ hx hy

lemma add_ne_bot {x y : EReal} (hx : x ≠ ⊥) (hy : y ≠ ⊥) : x + y ≠ ⊥ :=
  add_ne_bot_iff.mpr ⟨hx, hy⟩

lemma add_eq_top_iff {x y : EReal} : x + y = ⊤ ↔ x = ⊤ ∧ y ≠ ⊥ ∨ x ≠ ⊥ ∧ y = ⊤ := by
  induction x <;> induction y <;> try · simp
  simp only [coe_ne_top, ne_eq, coe_ne_bot, not_false_eq_true, and_true, and_false,
    or_self, iff_false]
  norm_cast
  exact coe_ne_top _

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

lemma add_sub_cancel (x : EReal) (y : ℝ) : x + y - y = x := add_sub_cancel_right

lemma add_sub_cancel' (x : EReal) (y : ℝ) : y + x - y = x := add_sub_cancel_left

lemma top_sub_of_ne_top {x : EReal} (hx : x ≠ ⊤) : ⊤ - x = ⊤ := top_sub hx

lemma top_mul_add_of_nonneg {x y : EReal} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    ⊤ * (x + y) = ⊤ * x + ⊤ * y := left_distrib_of_nonneg hx hy

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
    · exact EReal.add_pos hy_pos hz_pos
  lift x to ℝ using ⟨hx_top, hx_bot⟩
  norm_cast
  rw [mul_add]

lemma coe_add_mul_of_nonneg (x : EReal) {y z : ℝ} (hy : 0 ≤ y) (hz : 0 ≤ z) :
    (y + z) * x =  y * x + z * x := by
  simp_rw [mul_comm _ x]
  exact EReal.mul_add_coe_of_nonneg x hy hz

lemma sub_nonneg' {x y : EReal} (h : x ≠ ⊤ ∨ y ≠ ⊤) (h' : x ≠ ⊥ ∨ y ≠ ⊥) :
    0 ≤ x - y ↔ y ≤ x := by
  induction x <;> induction y <;> try · simp
  · simp at h'
  · norm_cast
    simp
  · simp at h

instance : MeasurableAdd₂ EReal := ⟨EReal.lowerSemicontinuous_add.measurable⟩

section MeasurableMul

variable {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}

theorem measurable_from_prod_countable'' [Countable β] [MeasurableSingletonClass β]
    {f : β × α → γ} (hf : ∀ y, Measurable fun x => f (y, x)) :
    Measurable f := by
  change Measurable ((fun (p : α × β) ↦ f (p.2, p.1)) ∘ Prod.swap)
  exact measurable_from_prod_countable_right hf

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
    simp only [mem_insert_iff, mem_singleton_iff] at h'
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
  | bot =>
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
  | coe c => exact (measurable_id.const_mul _).coe_real_ereal
  | top =>
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
    · rwa [sub_nonneg (.inr <| coe_ne_top _) (.inr <| coe_ne_bot _)]
    · by_cases ha : a = ⊥
      · simp [ha]
      rwa [sub_nonneg _ (.inr ha)]
      exact .inr (hac.trans_lt (coe_lt_top _)).ne
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

--PR these 2 lemmas to mathlib, just after ENNReal.mul_max
-- #check ENNReal.mul_max
theorem min_mul : min a b * c = min (a * c) (b * c) := (min_mul_mul_right ..).symm

theorem mul_min : a * min b c = min (a * b) (a * c) := (min_mul_mul_left ..).symm

@[simp]
lemma toReal_toEReal_of_ne_top (hx : x ≠ ⊤) : x.toReal.toEReal = x.toEReal := by
  cases x <;> tauto

end ENNReal
