/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
import TestingLowerBounds.FDiv.DivFunction.Basic

/-!

# f-Divergences functions

-/

open Real MeasureTheory Filter Set MeasurableSpace

open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μ ν : Measure α}

namespace DivFunction

variable {f g : DivFunction}

section RightDeriv

lemma rightDeriv_mono (f : DivFunction) {x y : ℝ} (hxy : x ≤ y)
    (hx : f.xmin < ENNReal.ofReal x) (hy : ENNReal.ofReal y < f.xmax) :
    rightDeriv f.realFun x ≤ rightDeriv f.realFun y := by
  sorry

lemma continuousWithinAt_rightDeriv (f : DivFunction) {x : ℝ}
    (hx : f.xmin < ENNReal.ofReal x) (hx' : ENNReal.ofReal x < f.xmax) :
    ContinuousWithinAt (rightDeriv f.realFun) (Ici x) x := by
  sorry

lemma rightLim_congr {α β : Type*} [LinearOrder α] [TopologicalSpace α] [OrderTopology α]
    [TopologicalSpace β] [T2Space β] {f g : α → β}
    {a : α} (h_ne_bot : 𝓝[>] a ≠ ⊥) {y : β} (h_tendsto : Tendsto f (𝓝[>] a) (𝓝 y))
    (h : f =ᶠ[𝓝[>] a] g) :
    Function.rightLim f a = Function.rightLim g a := by
  rw [rightLim_eq_of_tendsto h_ne_bot h_tendsto,
    rightLim_eq_of_tendsto h_ne_bot ((tendsto_congr' h).mp h_tendsto)]

-- the `rightLim` matters only at `f.xmin`: `rightDeriv` could be 0 because it has no limit in `ℝ`,
-- but in that case it should be `⊥`.
noncomputable def rightDerivFun (f : DivFunction) : ℝ → EReal :=
  fun x ↦
    if x < f.xmin.toReal then ⊥
    else if f.xmax ≤ ENNReal.ofReal x then ⊤
    else Function.rightLim (fun y ↦ (rightDeriv f.realFun y : EReal)) x

lemma monotone_rightDerivFun (f : DivFunction) : Monotone f.rightDerivFun := by
  intro x y hxy
  rcases lt_or_le x f.xmin.toReal with hx_lt_min | hx_ge_min
  · simp [rightDerivFun, hx_lt_min]
  rcases le_or_lt f.xmax (ENNReal.ofReal y) with hy_ge_max | hy_lt_max
  · simp only [rightDerivFun, not_lt.mpr (hx_ge_min.trans hxy), ↓reduceIte, hy_ge_max, le_top]
  simp only [rightDerivFun, not_lt.mpr hx_ge_min, ↓reduceIte, not_le.mpr hy_lt_max,
    not_lt.mpr (hx_ge_min.trans hxy)]
  rw [if_neg]
  swap
  · refine not_le.mpr (lt_of_le_of_lt ?_ hy_lt_max)
    rwa [ENNReal.ofReal_le_ofReal_iff]
    exact ENNReal.toReal_nonneg.trans (hx_ge_min.trans hxy)
  have h_mono := f.convexOn_Ioo_realFun.rightDeriv_monotoneOn
  sorry

lemma rightLim_rightDerivFun_of_lt_xmin (f : DivFunction) {x : ℝ} (h : x < f.xmin.toReal) :
    Function.rightLim f.rightDerivFun x = ⊥ := by
  refine rightLim_eq_of_tendsto (NeBot.ne inferInstance) ?_
  refine (tendsto_congr' ?_).mpr tendsto_const_nhds
  filter_upwards [eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds h)] with x hx
  rw [rightDerivFun, if_pos hx]

lemma rightLim_rightDerivFun_of_ge_xmax (f : DivFunction) {x : ℝ} (h : f.xmax ≤ ENNReal.ofReal x) :
    Function.rightLim f.rightDerivFun x = ⊤ := by
  refine rightLim_eq_of_tendsto (NeBot.ne inferInstance) ?_
  refine (tendsto_congr' ?_).mpr tendsto_const_nhds
  refine eventually_nhdsWithin_of_forall fun y hy ↦ ?_
  have h' : f.xmax ≤ ENNReal.ofReal y := h.trans <| ENNReal.ofReal_le_ofReal hy.le
  simp [rightDerivFun, h']
  refine ENNReal.toReal_le_of_le_ofReal (le_trans ?_ hy.le) (xmin_lt_xmax.le.trans h')
  suffices 1 ≤ x by linarith
  rw [← ENNReal.one_le_ofReal]
  exact one_lt_xmax.le.trans h

lemma rightLim_rightDerivFun_of_mem_Ico (f : DivFunction) {x : ℝ}
    (h1 : f.xmin.toReal ≤ x) (h2 : ENNReal.ofReal x < f.xmax) :
    Function.rightLim f.rightDerivFun x
      = Function.rightLim (fun y ↦ (rightDeriv f.realFun y : EReal)) x := by
  have : f.rightDerivFun =ᶠ[𝓝[>] x]
      fun x' ↦ Function.rightLim (fun y ↦ ↑(rightDeriv f.realFun y)) x' := by
    unfold rightDerivFun
    by_cases h_top : f.xmax = ∞
    · refine eventually_nhdsWithin_of_forall fun y hy ↦ ?_
      simp only
      rw [if_neg, if_neg]
      · simp [h_top]
      · exact not_lt.mpr (h1.trans_lt hy).le
    have h2' : x < f.xmax.toReal := by
      rw [← ENNReal.toReal_ofReal (ENNReal.toReal_nonneg.trans h1),
        ENNReal.toReal_lt_toReal ENNReal.ofReal_ne_top h_top]
      exact h2
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds h2'),
      eventually_nhdsWithin_of_forall (fun y hy ↦ h1.trans hy.le)] with y hy1 hy2
    rw [if_neg (not_lt.mpr hy2), if_neg]
    rwa [not_le, ENNReal.ofReal_lt_iff_lt_toReal (ENNReal.toReal_nonneg.trans hy2) h_top]
  rw [rightLim_congr (NeBot.ne inferInstance) (f.monotone_rightDerivFun.tendsto_rightLim x) this]
  sorry

lemma right_continuous_rightDerivFun (f : DivFunction) (x : ℝ) :
    ContinuousWithinAt f.rightDerivFun (Ici x) x := by
  rw [← continuousWithinAt_Ioi_iff_Ici,
    f.monotone_rightDerivFun.continuousWithinAt_Ioi_iff_rightLim_eq]
  unfold rightDerivFun
  split_ifs with h1 h2
  · exact f.rightLim_rightDerivFun_of_lt_xmin h1
  · exact f.rightLim_rightDerivFun_of_ge_xmax h2
  · push_neg at h1 h2
    exact f.rightLim_rightDerivFun_of_mem_Ico h1 h2

protected noncomputable def rightDerivStieltjes (f : DivFunction) : ERealStieltjes where
  toFun := f.rightDerivFun
  mono' := f.monotone_rightDerivFun
  right_continuous' := f.right_continuous_rightDerivFun

@[simp] lemma rightDerivFun_zero :
    (0 : DivFunction).rightDerivFun = fun x ↦ if x < 0 then ⊥ else 0 := by
  ext ; simp [rightDerivFun]

@[simp] lemma rightDerivStieltjes_zero :
    (0 : DivFunction).rightDerivStieltjes =
    { toFun := fun x ↦ if x < 0 then ⊥ else 0
      mono' := by convert (0 : DivFunction).monotone_rightDerivFun; simp
      right_continuous' := by convert (0 : DivFunction).right_continuous_rightDerivFun; simp } := by
  ext x; simp [DivFunction.rightDerivStieltjes]

lemma rightDerivStieltjes_of_lt_xmin {x : ℝ} (hx : x < f.xmin.toReal) :
    f.rightDerivStieltjes x = ⊥ := if_pos hx

lemma rightDerivStieltjes_of_ge_xmax {x : ℝ} (hx : f.xmax ≤ ENNReal.ofReal x) :
    f.rightDerivStieltjes x = ⊤ := by
  simp only [DivFunction.rightDerivStieltjes, rightDerivFun]
  rw [if_neg, if_pos hx]
  rw [not_lt]
  refine ENNReal.toReal_le_of_le_ofReal ?_ (xmin_lt_xmax.le.trans hx)
  have hx' : 0 < ENNReal.ofReal x := xmax_pos.trans_le hx
  simp only [ENNReal.ofReal_pos] at hx'
  exact hx'.le

lemma rightDerivStieltjes_of_neg {x : ℝ} (hx : x < 0) :
    f.rightDerivStieltjes x = ⊥ :=
  rightDerivStieltjes_of_lt_xmin (hx.trans_le ENNReal.toReal_nonneg)

-- lemma rightDerivStieltjes_eq_bot_iff {x : ℝ} :
--     f.rightDerivStieltjes x = ⊥ ↔ x < f.xmin.toReal := by
--   refine ⟨fun h ↦ ?_, fun h ↦ rightDerivStieltjes_of_lt_xmin h⟩
--   sorry

lemma rightDerivStieltjes_eq_top_iff {x : ℝ} :
    f.rightDerivStieltjes x = ⊤ ↔ f.xmax ≤ ENNReal.ofReal x := by
  refine ⟨fun h ↦ ?_, fun h ↦ rightDerivStieltjes_of_ge_xmax h⟩
  simp only [DivFunction.rightDerivStieltjes, rightDerivFun] at h
  split_ifs at h with h1 h2
  · exact h2
  sorry

lemma rightDerivStieltjes_of_ne_top (hf : ∀ x, 0 < x → f x ≠ ∞) (x : ℝ) :
    f.rightDerivStieltjes x = Function.rightLim (fun y ↦ (rightDeriv f.realFun y : EReal)) x := by
  sorry

lemma rightDerivStieltjes_ne_top (hf : ∀ x, 0 < x → f x ≠ ∞) (x : ℝ) :
    f.rightDerivStieltjes x ≠ ⊤ := by
  sorry

@[simp]
lemma rightDerivStieltjes_one : f.rightDerivStieltjes 1 = rightDeriv f.realFun 1 := by
  sorry

lemma rightDerivStieltjes_one_nonneg : 0 ≤ f.rightDerivStieltjes 1 := by
  rw [rightDerivStieltjes_one]
  norm_cast
  exact f.rightDeriv_one_nonneg

@[simp]
lemma toReal_max_xmin : (max f.xmin g.xmin).toReal = max f.xmin.toReal g.xmin.toReal := by
  sorry

lemma rightDerivStieltjes_add :
    (f + g).rightDerivStieltjes = f.rightDerivStieltjes + g.rightDerivStieltjes := by
  ext x
  by_cases hf_top : f.rightDerivStieltjes x = ⊤
  · rw [ERealStieltjes.add_apply_of_eq_top_left hf_top]
    simp only [rightDerivStieltjes_eq_top_iff, xmax_add, min_le_iff]
    left
    rwa [rightDerivStieltjes_eq_top_iff] at hf_top
  by_cases hg_top : g.rightDerivStieltjes x = ⊤
  · rw [ERealStieltjes.add_apply_of_eq_top_right hg_top]
    simp only [rightDerivStieltjes_eq_top_iff, xmax_add, min_le_iff]
    right
    rwa [rightDerivStieltjes_eq_top_iff] at hg_top
  rw [ERealStieltjes.add_apply_of_ne_top hf_top hg_top]
  have hx_lt_f : ENNReal.ofReal x < f.xmax := by
    rw [rightDerivStieltjes_eq_top_iff] at hf_top
    simpa using hf_top
  have hx_lt_g : ENNReal.ofReal x < g.xmax := by
    rw [rightDerivStieltjes_eq_top_iff] at hg_top
    simpa using hg_top
  simp only [DivFunction.rightDerivStieltjes, xmin_add, toReal_max_xmin, lt_max_iff, xmax_add,
    min_le_iff, not_le.mpr hx_lt_f, not_le.mpr hx_lt_g, or_self, ↓reduceIte]
  by_cases hx_fmin : x < f.xmin.toReal
  · simp [hx_fmin, rightDerivFun]
  by_cases hx_gmin : x < g.xmin.toReal
  · simp [hx_gmin, rightDerivFun]
  simp only [hx_fmin, hx_gmin, or_self, ↓reduceIte, rightDerivFun]
  sorry

end RightDeriv

end DivFunction

end ProbabilityTheory
