import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

open scoped ENNReal NNReal Topology
open Filter Set

namespace EReal

@[simp]
lemma toENNReal_one : (1 : EReal).toENNReal = 1 := by
  rw [toENNReal, ite_eq_right (ne_of_beq_false rfl)]
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
    · simp [top_sub ha]
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

end EReal

namespace ENNReal

@[simp]
lemma toReal_toEReal_of_ne_top {x : ℝ≥0∞} (hx : x ≠ ⊤) : x.toReal.toEReal = x.toEReal :=
  EReal.coe_ennreal_toReal hx

end ENNReal
