/-
Copyright (c) 2024 Lorenzo Luccioli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import TestingLowerBounds.ForMathlib.LeftRightDeriv
import TestingLowerBounds.FDiv.DivFunction.RightDeriv

/-! # Curvature measure of a divergence function

The curvature measure of a `DivFunction` `f` is the Lebesgue-Stieltjes measure associated to its
right derivative. Its main use is the Taylor formula expressing `f x` as an integral against the
curvature measure (`convex_taylor_one_right'`, `convex_taylor_one_left'`).
-/

open MeasureTheory Set StieltjesFunction Function Filter

open scoped ENNReal Topology

namespace ProbabilityTheory

lemma ENNReal.preimage_toReal_Ioc {a b : ℝ} (h : 0 ≤ a) :
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

namespace DivFunction

variable {𝒳 : Type*} {m𝒳 : MeasurableSpace 𝒳} {μ ν : Measure 𝒳} {f g : DivFunction} {β γ x t : ℝ}

/-- The curvature measure induced by a convex function. It is defined as the only measure that has
the right derivative of the function as a CDF. -/
noncomputable
irreducible_def curvatureMeasure (f : DivFunction) : Measure ℝ≥0∞ :=
  f.rightDerivStieltjes.measure.map ENNReal.ofReal

lemma curvatureMeasure_Ioi (a : ℝ≥0∞) (ha : a ≠ ∞) :
    f.curvatureMeasure (Ioi a) = f.rightDerivStieltjes.measure (Ioi a.toReal) := by
  rw [curvatureMeasure, Measure.map_apply]
  · congr 1
    ext x
    simp only [mem_preimage, mem_Ioi]
    rw [ENNReal.lt_ofReal_iff_toReal_lt ha]
  · fun_prop
  · simp

lemma curvatureMeasure_singleton_top : f.curvatureMeasure {∞} = 0 := by
  rw [curvatureMeasure, Measure.map_apply]
  · have : ENNReal.ofReal ⁻¹' {⊤} = ∅ := by ext; simp
    simp [this]
  · exact ENNReal.measurable_ofReal
  · simp

@[simp]
lemma curvatureMeasure_Ioo_top_eq_curvatureMeasure_Ioi {a : ℝ≥0∞} (ha : a ≠ ∞) :
    f.curvatureMeasure (Ioo a ∞) = f.curvatureMeasure (Ioi a) := by
  have : Ioi a = Ioo a ∞ ∪ {∞} := by
    ext x
    simp only [mem_Ioi, union_singleton, mem_insert_iff, mem_Ioo]
    by_cases hx : x = ∞
    · simp [hx, ha.lt_top]
    · simp [Ne.lt_top hx, hx]
  rw [this, measure_union _ (measurableSet_singleton _), curvatureMeasure_singleton_top, add_zero]
  simp

section ConvexTaylor

/-! ### Taylor formula at `1` for a `DivFunction`

We prove `f b = c * (b - 1) + ∫⁻ x in Ioc 1 b, (b - x) ∂f.curvatureMeasure` for `1 ≤ b` and
`f b + c * (1 - b) = ∫⁻ x in Ioc b 1, (x - b) ∂f.curvatureMeasure` for `b ≤ 1`, where
`c = rightDeriv f.realFun 1`. In the interior of the effective domain this is the fundamental
theorem of calculus for the (monotone) right derivative of `f.realFun`, followed by Tonelli's
theorem. The formulas extend to the boundary of the effective domain by monotonicity and
monotone convergence. -/

lemma measure_Ioc_one_right {s : ℝ} (hs : 1 < s) (hs' : ENNReal.ofReal s < f.xmax) :
    f.rightDerivStieltjes.measure (Ioc 1 s)
      = ENNReal.ofReal (rightDeriv f.realFun s - rightDeriv f.realFun 1) := by
  rw [ERealStieltjes.measure_Ioc, rightDerivStieltjes_one,
    rightDerivStieltjes_of_mem_interior (xmin_lt_one.trans (ENNReal.one_lt_ofReal.mpr hs)) hs',
    ← EReal.coe_sub, EReal.toENNReal_of_ne_top (EReal.coe_ne_top _), EReal.toReal_coe]

lemma measure_Ioc_one_left {s : ℝ} (hs : f.xmin < ENNReal.ofReal s) (hs' : s ≤ 1) :
    f.rightDerivStieltjes.measure (Ioc s 1)
      = ENNReal.ofReal (rightDeriv f.realFun 1 - rightDeriv f.realFun s) := by
  rw [ERealStieltjes.measure_Ioc, rightDerivStieltjes_one,
    rightDerivStieltjes_of_mem_interior hs ((ENNReal.ofReal_le_one.mpr hs').trans_lt one_lt_xmax),
    ← EReal.coe_sub, EReal.toENNReal_of_ne_top (EReal.coe_ne_top _), EReal.toReal_coe]

lemma monotoneOn_rightDeriv_realFun_Icc {a b : ℝ} (ha : f.xmin < ENNReal.ofReal a)
    (hb : ENNReal.ofReal b < f.xmax) :
    MonotoneOn (rightDeriv f.realFun) (Icc a b) := fun _ hx _ hy hxy ↦
  f.rightDeriv_mono hxy (ha.trans_le (ENNReal.ofReal_le_ofReal hx.1))
    ((ENNReal.ofReal_le_ofReal hy.2).trans_lt hb)

lemma continuousOn_realFun_Icc {a b : ℝ} (ha : f.xmin < ENNReal.ofReal a)
    (hb : ENNReal.ofReal b < f.xmax) :
    ContinuousOn f.realFun (Icc a b) :=
  f.continuousOn_realFun_Ioo.mono fun _ hx ↦ mem_toReal_Ioo_iff.mpr
    ⟨ha.trans_le (ENNReal.ofReal_le_ofReal hx.1), (ENNReal.ofReal_le_ofReal hx.2).trans_lt hb⟩

lemma hasDerivWithinAt_realFun {x : ℝ} (hx : f.xmin < ENNReal.ofReal x)
    (hx' : ENNReal.ofReal x < f.xmax) :
    HasDerivWithinAt f.realFun (rightDeriv f.realFun x) (Ioi x) x := by
  have hx0 : 0 ≤ x := by
    by_contra h
    rw [ENNReal.ofReal_of_nonpos (not_le.mp h).le] at hx
    exact ENNReal.not_lt_zero hx
  exact (f.differentiableWithinAt hx0 ⟨hx, hx'⟩).hasDerivWithinAt

lemma intervalIntegrable_rightDeriv_realFun {a b : ℝ} (hab : a ≤ b)
    (ha : f.xmin < ENNReal.ofReal a) (hb : ENNReal.ofReal b < f.xmax) :
    IntervalIntegrable (rightDeriv f.realFun) volume a b := by
  refine MonotoneOn.intervalIntegrable ?_
  rw [uIcc_of_le hab]
  exact f.monotoneOn_rightDeriv_realFun_Icc ha hb

/-- Fundamental theorem of calculus for `f.realFun` on an interval inside the effective domain. -/
lemma integral_rightDeriv_realFun {a b : ℝ} (hab : a ≤ b) (ha : f.xmin < ENNReal.ofReal a)
    (hb : ENNReal.ofReal b < f.xmax) :
    ∫ s in a..b, rightDeriv f.realFun s = f.realFun b - f.realFun a := by
  refine intervalIntegral.integral_eq_sub_of_hasDeriv_right ?_ ?_
    (f.intervalIntegrable_rightDeriv_realFun hab ha hb)
  · rw [uIcc_of_le hab]
    exact f.continuousOn_realFun_Icc ha hb
  · intro x hx
    rw [min_eq_left hab, max_eq_right hab] at hx
    exact f.hasDerivWithinAt_realFun (ha.trans_le (ENNReal.ofReal_le_ofReal hx.1.le))
      ((ENNReal.ofReal_le_ofReal hx.2.le).trans_lt hb)

lemma integral_rightDeriv_realFun_sub_one {t : ℝ} (ht : 1 ≤ t)
    (ht' : ENNReal.ofReal t < f.xmax) :
    ∫ s in (1)..t, (rightDeriv f.realFun s - rightDeriv f.realFun 1)
      = f.realFun t - rightDeriv f.realFun 1 * (t - 1) := by
  rw [intervalIntegral.integral_sub
    (f.intervalIntegrable_rightDeriv_realFun ht (by simpa using xmin_lt_one) ht')
    intervalIntegrable_const,
    f.integral_rightDeriv_realFun ht (by simpa using xmin_lt_one) ht',
    intervalIntegral.integral_const, realFun_one, smul_eq_mul]
  ring

lemma integral_one_sub_rightDeriv_realFun {t : ℝ} (ht : f.xmin < ENNReal.ofReal t)
    (ht' : t ≤ 1) :
    ∫ s in t..(1), (rightDeriv f.realFun 1 - rightDeriv f.realFun s)
      = f.realFun t + rightDeriv f.realFun 1 * (1 - t) := by
  rw [intervalIntegral.integral_sub intervalIntegrable_const
    (f.intervalIntegrable_rightDeriv_realFun ht' ht (by simpa using one_lt_xmax)),
    f.integral_rightDeriv_realFun ht' ht (by simpa using one_lt_xmax),
    intervalIntegral.integral_const, realFun_one, smul_eq_mul]
  ring

/-- Tonelli: `∫⁻ x in Ioc 1 t, (t - x) ∂μ = ∫⁻ s in Ioc 1 t, μ (Ioc 1 s)`. -/
lemma setLIntegral_Ioc_sub_right {t : ℝ} (ht : 1 ≤ t) (ht' : ENNReal.ofReal t < f.xmax) :
    ∫⁻ x in Ioc 1 t, ENNReal.ofReal (t - x) ∂f.rightDerivStieltjes.measure
      = ∫⁻ s in Ioc 1 t, f.rightDerivStieltjes.measure (Ioc 1 s) := by
  set μ := f.rightDerivStieltjes.measure with hμ_def
  have hμ : IsFiniteMeasure (μ.restrict (Ioc 1 t)) := by
    rw [isFiniteMeasure_restrict, hμ_def, ERealStieltjes.measure_Ioc, rightDerivStieltjes_one,
      rightDerivStieltjes_of_mem_interior (xmin_lt_one.trans_le (ENNReal.one_le_ofReal.mpr ht)) ht',
      ← EReal.coe_sub, EReal.toENNReal_of_ne_top (EReal.coe_ne_top _)]
    exact ENNReal.ofReal_ne_top
  let g : ℝ → ℝ → ℝ≥0∞ := fun x s ↦ if x ≤ s then 1 else 0
  have hg : Measurable (Function.uncurry g) := by
    change Measurable fun p : ℝ × ℝ ↦ if p.1 ≤ p.2 then (1 : ℝ≥0∞) else 0
    exact Measurable.ite (measurableSet_le measurable_fst measurable_snd) measurable_const
      measurable_const
  have h1 : ∀ x ∈ Ioc 1 t, ∫⁻ s in Ioc 1 t, g x s = ENNReal.ofReal (t - x) := by
    intro x hx
    have : (fun s ↦ g x s) = (Ici x).indicator 1 := by
      ext s
      simp [g, indicator_apply]
    rw [this, lintegral_indicator_one measurableSet_Ici, Measure.restrict_apply measurableSet_Ici]
    have : Ici x ∩ Ioc 1 t = Icc x t := by
      ext s
      simp only [mem_inter_iff, mem_Ici, mem_Ioc, mem_Icc]
      exact ⟨fun h ↦ ⟨h.1, h.2.2⟩, fun h ↦ ⟨h.1, hx.1.trans_le h.1, h.2⟩⟩
    rw [this, Real.volume_Icc]
  have h2 : ∀ s ∈ Ioc 1 t, ∫⁻ x in Ioc 1 t, g x s ∂μ = μ (Ioc 1 s) := by
    intro s hs
    have : (fun x ↦ g x s) = (Iic s).indicator 1 := by
      ext x
      simp [g, indicator_apply]
    rw [this, lintegral_indicator_one measurableSet_Iic, Measure.restrict_apply measurableSet_Iic]
    congr 1
    ext x
    simp only [mem_inter_iff, mem_Iic, mem_Ioc]
    exact ⟨fun h ↦ ⟨h.2.1, h.1⟩, fun h ↦ ⟨h.2, h.1, h.2.trans hs.2⟩⟩
  calc ∫⁻ x in Ioc 1 t, ENNReal.ofReal (t - x) ∂μ
      = ∫⁻ x in Ioc 1 t, (∫⁻ s in Ioc 1 t, g x s ∂volume) ∂μ :=
        setLIntegral_congr_fun measurableSet_Ioc fun x hx ↦ (h1 x hx).symm
    _ = ∫⁻ s in Ioc 1 t, (∫⁻ x in Ioc 1 t, g x s ∂μ) ∂volume :=
        lintegral_lintegral_swap hg.aemeasurable
    _ = ∫⁻ s in Ioc 1 t, μ (Ioc 1 s) := setLIntegral_congr_fun measurableSet_Ioc h2

/-- Tonelli: `∫⁻ x in Ioc t 1, (x - t) ∂μ = ∫⁻ s in Ioc t 1, μ (Ioc s 1)`. -/
lemma setLIntegral_Ioc_sub_left {t : ℝ} (ht : f.xmin < ENNReal.ofReal t) (ht' : t ≤ 1) :
    ∫⁻ x in Ioc t 1, ENNReal.ofReal (x - t) ∂f.rightDerivStieltjes.measure
      = ∫⁻ s in Ioc t 1, f.rightDerivStieltjes.measure (Ioc s 1) := by
  set μ := f.rightDerivStieltjes.measure with hμ_def
  have hμ : IsFiniteMeasure (μ.restrict (Ioc t 1)) := by
    rw [isFiniteMeasure_restrict, hμ_def, ERealStieltjes.measure_Ioc, rightDerivStieltjes_one,
      rightDerivStieltjes_of_mem_interior ht ((ENNReal.ofReal_le_one.mpr ht').trans_lt one_lt_xmax),
      ← EReal.coe_sub, EReal.toENNReal_of_ne_top (EReal.coe_ne_top _)]
    exact ENNReal.ofReal_ne_top
  let g : ℝ → ℝ → ℝ≥0∞ := fun x s ↦ if s < x then 1 else 0
  have hg : Measurable (Function.uncurry g) := by
    change Measurable fun p : ℝ × ℝ ↦ if p.2 < p.1 then (1 : ℝ≥0∞) else 0
    exact Measurable.ite (measurableSet_lt measurable_snd measurable_fst) measurable_const
      measurable_const
  have h1 : ∀ x ∈ Ioc t 1, ∫⁻ s in Ioc t 1, g x s = ENNReal.ofReal (x - t) := by
    intro x hx
    have : (fun s ↦ g x s) = (Iio x).indicator 1 := by
      ext s
      simp [g, indicator_apply]
    rw [this, lintegral_indicator_one measurableSet_Iio, Measure.restrict_apply measurableSet_Iio]
    have : Iio x ∩ Ioc t 1 = Ioo t x := by
      ext s
      simp only [mem_inter_iff, mem_Iio, mem_Ioc, mem_Ioo]
      exact ⟨fun h ↦ ⟨h.2.1, h.1⟩, fun h ↦ ⟨h.2, h.1, h.2.le.trans hx.2⟩⟩
    rw [this, Real.volume_Ioo]
  have h2 : ∀ s ∈ Ioc t 1, ∫⁻ x in Ioc t 1, g x s ∂μ = μ (Ioc s 1) := by
    intro s hs
    have : (fun x ↦ g x s) = (Ioi s).indicator 1 := by
      ext x
      simp [g, indicator_apply]
    rw [this, lintegral_indicator_one measurableSet_Ioi, Measure.restrict_apply measurableSet_Ioi]
    congr 1
    ext x
    simp only [mem_inter_iff, mem_Ioi, mem_Ioc]
    exact ⟨fun h ↦ ⟨h.1, h.2.2⟩, fun h ↦ ⟨h.1, hs.1.trans h.1, h.2⟩⟩
  calc ∫⁻ x in Ioc t 1, ENNReal.ofReal (x - t) ∂μ
      = ∫⁻ x in Ioc t 1, (∫⁻ s in Ioc t 1, g x s ∂volume) ∂μ :=
        setLIntegral_congr_fun measurableSet_Ioc fun x hx ↦ (h1 x hx).symm
    _ = ∫⁻ s in Ioc t 1, (∫⁻ x in Ioc t 1, g x s ∂μ) ∂volume :=
        lintegral_lintegral_swap hg.aemeasurable
    _ = ∫⁻ s in Ioc t 1, μ (Ioc s 1) := setLIntegral_congr_fun measurableSet_Ioc h2

lemma setLIntegral_Ioc_sub_right_eq_ofReal {t : ℝ} (ht : 1 ≤ t)
    (ht' : ENNReal.ofReal t < f.xmax) :
    ∫⁻ x in Ioc 1 t, ENNReal.ofReal (t - x) ∂f.rightDerivStieltjes.measure
      = ENNReal.ofReal (f.realFun t - rightDeriv f.realFun 1 * (t - 1)) := by
  rw [f.setLIntegral_Ioc_sub_right ht ht']
  have h_eq : ∀ s ∈ Ioc 1 t, f.rightDerivStieltjes.measure (Ioc 1 s)
      = ENNReal.ofReal (rightDeriv f.realFun s - rightDeriv f.realFun 1) := fun s hs ↦
    f.measure_Ioc_one_right hs.1 ((ENNReal.ofReal_le_ofReal hs.2).trans_lt ht')
  rw [setLIntegral_congr_fun measurableSet_Ioc h_eq, ← ofReal_integral_eq_lintegral_ofReal,
    ← intervalIntegral.integral_of_le ht, f.integral_rightDeriv_realFun_sub_one ht ht']
  · exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le ht).mp
      (f.intervalIntegrable_rightDeriv_realFun ht (by simpa using xmin_lt_one) ht')).sub
      (integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top))
  · refine ae_restrict_of_forall_mem measurableSet_Ioc fun s hs ↦ sub_nonneg.mpr ?_
    exact f.rightDeriv_mono hs.1.le (by simpa using xmin_lt_one)
      ((ENNReal.ofReal_le_ofReal hs.2).trans_lt ht')

lemma setLIntegral_Ioc_sub_left_eq_ofReal {t : ℝ} (ht : f.xmin < ENNReal.ofReal t)
    (ht' : t ≤ 1) :
    ∫⁻ x in Ioc t 1, ENNReal.ofReal (x - t) ∂f.rightDerivStieltjes.measure
      = ENNReal.ofReal (f.realFun t + rightDeriv f.realFun 1 * (1 - t)) := by
  rw [f.setLIntegral_Ioc_sub_left ht ht']
  have h_eq : ∀ s ∈ Ioc t 1, f.rightDerivStieltjes.measure (Ioc s 1)
      = ENNReal.ofReal (rightDeriv f.realFun 1 - rightDeriv f.realFun s) := fun s hs ↦
    f.measure_Ioc_one_left (ht.trans_le (ENNReal.ofReal_le_ofReal hs.1.le)) hs.2
  rw [setLIntegral_congr_fun measurableSet_Ioc h_eq, ← ofReal_integral_eq_lintegral_ofReal,
    ← intervalIntegral.integral_of_le ht', f.integral_one_sub_rightDeriv_realFun ht ht']
  · exact (integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)).sub
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le ht').mp
        (f.intervalIntegrable_rightDeriv_realFun ht' ht (by simpa using one_lt_xmax)))
  · refine ae_restrict_of_forall_mem measurableSet_Ioc fun s hs ↦ sub_nonneg.mpr ?_
    exact f.rightDeriv_mono hs.2 (ht.trans_le (ENNReal.ofReal_le_ofReal hs.1.le))
      (by simpa using one_lt_xmax)

lemma realFun_sub_rightDeriv_one_mul_nonneg {t : ℝ} (ht : 1 ≤ t)
    (ht' : ENNReal.ofReal t < f.xmax) :
    0 ≤ f.realFun t - rightDeriv f.realFun 1 * (t - 1) := by
  rw [← f.integral_rightDeriv_realFun_sub_one ht ht']
  refine intervalIntegral.integral_nonneg ht fun u hu ↦ sub_nonneg.mpr ?_
  exact f.rightDeriv_mono hu.1 (by simpa using xmin_lt_one)
    ((ENNReal.ofReal_le_ofReal hu.2).trans_lt ht')

/-- Taylor formula at `1` on the right, inside the effective domain. -/
lemma convex_taylor_one_right_of_lt_xmax {b : ℝ≥0∞} (hb : 1 ≤ b) (hb' : b < f.xmax) :
    f b = ENNReal.ofReal (rightDeriv f.realFun 1) * (b - 1)
      + ∫⁻ x in Ioc 1 b, b - x ∂f.curvatureMeasure := by
  have hb_top : b ≠ ∞ := hb'.ne_top
  have hbt : b = ENNReal.ofReal b.toReal := (ENNReal.ofReal_toReal hb_top).symm
  have ht1 : 1 ≤ b.toReal := by
    rw [← ENNReal.toReal_one]
    exact ENNReal.toReal_mono hb_top hb
  have ht' : ENNReal.ofReal b.toReal < f.xmax := by
    rw [← hbt]
    exact hb'
  have h_lint : ∫⁻ x in Ioc 1 b, b - x ∂f.curvatureMeasure
      = ∫⁻ x in Ioc 1 b.toReal, ENNReal.ofReal (b.toReal - x) ∂f.rightDerivStieltjes.measure := by
    rw [curvatureMeasure, setLIntegral_map (f := fun x ↦ b - x) measurableSet_Ioc (by fun_prop)
      ENNReal.measurable_ofReal]
    have h_pre : ENNReal.ofReal ⁻¹' Ioc 1 b = Ioc 1 b.toReal := by
      ext x
      simp only [mem_preimage, mem_Ioc]
      rw [ENNReal.one_lt_ofReal, ENNReal.ofReal_le_iff_le_toReal hb_top]
    rw [h_pre]
    refine setLIntegral_congr_fun measurableSet_Ioc fun x hx ↦ ?_
    rw [ENNReal.ofReal_sub _ (zero_le_one.trans hx.1.le), ENNReal.ofReal_toReal hb_top]
  rw [h_lint, f.setLIntegral_Ioc_sub_right_eq_ofReal ht1 ht']
  have hfb : f b ≠ ∞ := (lt_top_of_mem_Ioo ⟨xmin_lt_one.trans_le hb, hb'⟩).ne
  calc f b = ENNReal.ofReal (f.realFun b.toReal) := by
        rw [realFun_toReal f hb_top, ENNReal.ofReal_toReal hfb]
  _ = ENNReal.ofReal (rightDeriv f.realFun 1 * (b.toReal - 1)
        + (f.realFun b.toReal - rightDeriv f.realFun 1 * (b.toReal - 1))) := by
        congr 1
        ring
  _ = ENNReal.ofReal (rightDeriv f.realFun 1 * (b.toReal - 1))
        + ENNReal.ofReal (f.realFun b.toReal - rightDeriv f.realFun 1 * (b.toReal - 1)) :=
        ENNReal.ofReal_add (mul_nonneg f.rightDeriv_one_nonneg (sub_nonneg.mpr ht1))
          (f.realFun_sub_rightDeriv_one_mul_nonneg ht1 ht')
  _ = _ := by
        rw [ENNReal.ofReal_mul f.rightDeriv_one_nonneg, ENNReal.ofReal_sub _ zero_le_one,
          ENNReal.ofReal_one, ENNReal.ofReal_toReal hb_top]

/-- Taylor formula at `1` on the left, inside the effective domain. -/
lemma convex_taylor_one_left_of_xmin_lt {b : ℝ≥0∞} (hb : f.xmin < b) (hb' : b ≤ 1) :
    f b + ENNReal.ofReal (rightDeriv f.realFun 1) * (1 - b)
      = ∫⁻ x in Ioc b 1, x - b ∂f.curvatureMeasure := by
  have hb_top : b ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top hb'
  have hbt : b = ENNReal.ofReal b.toReal := (ENNReal.ofReal_toReal hb_top).symm
  have ht0 : 0 ≤ b.toReal := ENNReal.toReal_nonneg
  have ht1 : b.toReal ≤ 1 := by
    rw [← ENNReal.toReal_one]
    exact ENNReal.toReal_mono ENNReal.one_ne_top hb'
  have ht' : f.xmin < ENNReal.ofReal b.toReal := by
    rw [← hbt]
    exact hb
  have h_lint : ∫⁻ x in Ioc b 1, x - b ∂f.curvatureMeasure
      = ∫⁻ x in Ioc b.toReal 1, ENNReal.ofReal (x - b.toReal) ∂f.rightDerivStieltjes.measure := by
    rw [curvatureMeasure, setLIntegral_map (f := fun x ↦ x - b) measurableSet_Ioc (by fun_prop)
      ENNReal.measurable_ofReal]
    have h_pre : ENNReal.ofReal ⁻¹' Ioc b 1 = Ioc b.toReal 1 := by
      ext x
      simp only [mem_preimage, mem_Ioc]
      rw [ENNReal.lt_ofReal_iff_toReal_lt hb_top, ENNReal.ofReal_le_one]
    rw [h_pre]
    refine setLIntegral_congr_fun measurableSet_Ioc fun x hx ↦ ?_
    rw [ENNReal.ofReal_sub _ ht0, ENNReal.ofReal_toReal hb_top]
  rw [h_lint, f.setLIntegral_Ioc_sub_left_eq_ofReal ht' ht1]
  have hfb : f b ≠ ∞ := (lt_top_of_mem_Ioo ⟨hb, hb'.trans_lt one_lt_xmax⟩).ne
  rw [ENNReal.ofReal_add f.realFun_nonneg
    (mul_nonneg f.rightDeriv_one_nonneg (sub_nonneg.mpr ht1)),
    ENNReal.ofReal_mul f.rightDeriv_one_nonneg, ENNReal.ofReal_sub _ ht0, ENNReal.ofReal_one,
    ENNReal.ofReal_toReal hb_top, realFun_toReal f hb_top, ENNReal.ofReal_toReal hfb]

/-- Taylor formula at `1` on the right, for any finite `b ≥ 1`. -/
theorem convex_taylor_one_right' {b : ℝ≥0∞} (hb : 1 ≤ b) (hb_top : b ≠ ∞) :
    f b = ENNReal.ofReal (rightDeriv f.realFun 1) * (b - 1)
      + ∫⁻ x in Ioc 1 b, b - x ∂f.curvatureMeasure := by
  by_cases hb' : b < f.xmax
  · exact f.convex_taylor_one_right_of_lt_xmax hb hb'
  push Not at hb'
  have hxmax : f.xmax ≠ ∞ := ne_top_of_le_ne_top hb_top hb'
  have hfb : f b = ∞ := by
    rcases eq_or_lt_of_le hb' with h | h
    · rw [← h]
      exact apply_xmax_eq_top hxmax
    · exact eq_top_of_xmax_lt h
  rw [hfb]
  -- the right-hand side dominates `f t` for every `t ∈ [1, xmax)`, and `f t → ∞` as `t → xmax`
  symm
  by_contra h_ne
  have h_lt := lt_top_iff_ne_top.mpr h_ne
  have h_ne_bot : (𝓝[<] f.xmax).NeBot := by
    refine mem_closure_iff_nhdsWithin_neBot.mp ?_
    rw [closure_Iio' ⟨0, xmax_pos⟩]
    simp
  have h_tendsto : Tendsto f (𝓝[<] f.xmax) (𝓝 ∞) := by
    rw [← apply_xmax_eq_top hxmax]
    exact (f.continuous.tendsto _).mono_left nhdsWithin_le_nhds
  obtain ⟨t, ht_lt, ht⟩ :=
    ((h_tendsto.eventually (Ioi_mem_nhds h_lt)).and (Ioo_mem_nhdsLT one_lt_xmax)).exists
  refine absurd ht_lt (not_lt.mpr ?_)
  rw [f.convex_taylor_one_right_of_lt_xmax ht.1.le ht.2]
  have htb : t ≤ b := ht.2.le.trans hb'
  refine add_le_add (mul_le_mul' le_rfl (tsub_le_tsub_right htb 1)) ?_
  exact (lintegral_mono fun x ↦ tsub_le_tsub_right htb x).trans
    (lintegral_mono_set (Ioc_subset_Ioc_right htb))

/-- Taylor formula at `1` on the left, for any `b ≤ 1`. -/
theorem convex_taylor_one_left' {b : ℝ≥0∞} (hb : b ≤ 1) :
    f b + ENNReal.ofReal (rightDeriv f.realFun 1) * (1 - b)
      = ∫⁻ x in Ioc b 1, x - b ∂f.curvatureMeasure := by
  by_cases hb' : f.xmin < b
  · exact f.convex_taylor_one_left_of_xmin_lt hb' hb
  push Not at hb'
  -- the right-hand side is antitone in `b`
  have h_anti : ∀ t, b ≤ t → ∫⁻ x in Ioc t 1, x - t ∂f.curvatureMeasure
      ≤ ∫⁻ x in Ioc b 1, x - b ∂f.curvatureMeasure := fun t hbt ↦
    (lintegral_mono fun x ↦ tsub_le_tsub_left hbt x).trans
      (lintegral_mono_set (Ioc_subset_Ioc_left hbt))
  rcases eq_or_lt_of_le (zero_le (a := f.xmin)) with hxmin | hxmin
  · -- `xmin = 0`, so `b = 0`: monotone convergence along `t n → 0`
    obtain rfl : b = 0 := le_antisymm (hb'.trans hxmin.symm.le) zero_le
    set t : ℕ → ℝ≥0∞ := fun n ↦ ENNReal.ofReal (1 / (n + 1)) with ht_def
    have ht_pos : ∀ n, 0 < t n := fun n ↦ ENNReal.ofReal_pos.mpr Nat.one_div_pos_of_nat
    have ht_le : ∀ n, t n ≤ 1 := fun n ↦ by
      rw [ht_def, ENNReal.ofReal_le_one]
      exact (div_le_one (Nat.cast_add_one_pos n)).mpr
        (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
    have ht_anti : Antitone t := fun n m hnm ↦ ENNReal.ofReal_le_ofReal
      (one_div_le_one_div_of_le (Nat.cast_add_one_pos n)
        (by exact_mod_cast Nat.add_le_add_right hnm 1))
    have ht_tendsto : Tendsto t atTop (𝓝 0) := by
      rw [← ENNReal.ofReal_zero]
      exact ENNReal.tendsto_ofReal tendsto_one_div_add_atTop_nhds_zero_nat
    have ht_iInf : ⨅ n, t n = 0 := tendsto_nhds_unique (tendsto_atTop_iInf ht_anti) ht_tendsto
    have h_rhs : ∫⁻ x in Ioc 0 1, x - 0 ∂f.curvatureMeasure
        = ⨆ n, ∫⁻ x in Ioc (t n) 1, x - t n ∂f.curvatureMeasure := by
      simp_rw [← lintegral_indicator measurableSet_Ioc]
      rw [← lintegral_iSup]
      · congr 1
        ext x
        by_cases hx : x ∈ Ioc 0 1
        · rw [indicator_of_mem hx, tsub_zero]
          have : ∀ n, (Ioc (t n) 1).indicator (fun y ↦ y - t n) x = x - t n := by
            intro n
            by_cases hxn : x ∈ Ioc (t n) 1
            · rw [indicator_of_mem hxn]
            · rw [indicator_of_notMem hxn, eq_comm, tsub_eq_zero_iff_le]
              exact not_lt.mp fun h ↦ hxn ⟨h, hx.2⟩
          simp_rw [this]
          rw [← ENNReal.sub_iInf, ht_iInf, tsub_zero]
        · rw [indicator_of_notMem hx]
          symm
          exact ENNReal.iSup_eq_zero.mpr fun n ↦
            indicator_of_notMem (fun h ↦ hx ⟨(ht_pos n).trans h.1, h.2⟩) _
      · exact fun n ↦ (measurable_id.sub measurable_const).indicator measurableSet_Ioc
      · intro n m hnm x
        dsimp only
        by_cases hx : x ∈ Ioc (t n) 1
        · have hxm : x ∈ Ioc (t m) 1 := ⟨(ht_anti hnm).trans_lt hx.1, hx.2⟩
          rw [indicator_of_mem hx, indicator_of_mem hxm]
          exact tsub_le_tsub_left (ht_anti hnm) x
        · rw [indicator_of_notMem hx]
          exact zero_le
    have h_lhs : f 0 + ENNReal.ofReal (rightDeriv f.realFun 1) * (1 - 0)
        = ⨆ n, (f (t n) + ENNReal.ofReal (rightDeriv f.realFun 1) * (1 - t n)) := by
      rw [← ENNReal.iSup_add_iSup_of_monotone]
      · congr 1
        · refine tendsto_nhds_unique ((f.continuous.tendsto 0).comp ht_tendsto)
            (tendsto_atTop_iSup fun n m hnm ↦ ?_)
          exact f.antitoneOn (ht_le m) (ht_le n) (ht_anti hnm)
        · rw [← ENNReal.mul_iSup, ← ENNReal.sub_iInf, ht_iInf]
      · exact fun n m hnm ↦ f.antitoneOn (ht_le m) (ht_le n) (ht_anti hnm)
      · exact fun n m hnm ↦ mul_le_mul' le_rfl (tsub_le_tsub_left (ht_anti hnm) 1)
    rw [h_lhs, h_rhs]
    congr 1
    ext n
    refine f.convex_taylor_one_left_of_xmin_lt ?_ (ht_le n)
    rw [← hxmin]
    exact ht_pos n
  · -- `0 < xmin`, so `f b = ∞`: the right-hand side dominates `f t → ∞` as `t → xmin`
    have hfb : f b = ∞ := by
      rcases eq_or_lt_of_le hb' with h | h
      · rw [h]
        exact apply_xmin_eq_top hxmin
      · exact eq_top_of_lt_xmin h
    rw [hfb, top_add]
    symm
    by_contra h_ne
    have h_lt := lt_top_iff_ne_top.mpr h_ne
    have h_ne_bot : (𝓝[>] f.xmin).NeBot := by
      refine mem_closure_iff_nhdsWithin_neBot.mp ?_
      rw [closure_Ioi' ⟨1, xmin_lt_one⟩]
      simp
    have h_tendsto : Tendsto f (𝓝[>] f.xmin) (𝓝 ∞) := by
      rw [← apply_xmin_eq_top hxmin]
      exact (f.continuous.tendsto _).mono_left nhdsWithin_le_nhds
    obtain ⟨t, ht_lt, ht⟩ :=
      ((h_tendsto.eventually (Ioi_mem_nhds h_lt)).and (Ioo_mem_nhdsGT xmin_lt_one)).exists
    refine absurd ht_lt (not_lt.mpr ?_)
    calc f t ≤ f t + ENNReal.ofReal (rightDeriv f.realFun 1) * (1 - t) := le_self_add
    _ = ∫⁻ x in Ioc t 1, x - t ∂f.curvatureMeasure :=
        f.convex_taylor_one_left_of_xmin_lt ht.1 ht.2.le
    _ ≤ _ := h_anti t (hb'.trans ht.1.le)

theorem convex_taylor_one_right (hf : rightDeriv f.realFun 1 = 0) {b : ℝ≥0∞} (hb : 1 ≤ b)
    (hb_top : b ≠ ∞) :
    f b = ∫⁻ x in Ioc 1 b, b - x ∂f.curvatureMeasure := by
  rw [f.convex_taylor_one_right' hb hb_top, hf, ENNReal.ofReal_zero, zero_mul, zero_add]

theorem convex_taylor_one_left (hf : rightDeriv f.realFun 1 = 0) {b : ℝ≥0∞} (hb : b ≤ 1) :
    f b = ∫⁻ x in Ioc b 1, x - b ∂f.curvatureMeasure := by
  have h := f.convex_taylor_one_left' hb
  rwa [hf, ENNReal.ofReal_zero, zero_mul, add_zero] at h

/-- The curvature measure of `f`, pushed forward to `ℝ` by `ENNReal.toReal`. -/
noncomputable
def curvatureMeasureReal (f : DivFunction) : Measure ℝ := f.curvatureMeasure.map ENNReal.toReal

lemma curvatureMeasureReal_apply (f : DivFunction) {s : Set ℝ} (hs : MeasurableSet s) :
    f.curvatureMeasureReal s = f.curvatureMeasure (ENNReal.toReal ⁻¹' s) := by
  rw [curvatureMeasureReal, Measure.map_apply (by fun_prop) hs]

instance : SFinite f.curvatureMeasure := by
  rw [curvatureMeasure]
  infer_instance

instance : SFinite f.curvatureMeasureReal := by
  rw [curvatureMeasureReal]
  infer_instance

lemma lintegral_curvatureMeasureReal (f : DivFunction) {g : ℝ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ x, g x ∂f.curvatureMeasureReal = ∫⁻ x, g x.toReal ∂f.curvatureMeasure := by
  unfold curvatureMeasureReal
  rw [lintegral_map hg (by fun_prop)]

lemma integral_curvatureMeasureReal {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : DivFunction) {g : ℝ → E} (hg : StronglyMeasurable g) :
    ∫ x, g x ∂f.curvatureMeasureReal = ∫ x, g x.toReal ∂f.curvatureMeasure := by
  unfold curvatureMeasureReal
  rw [integral_map _ hg.aestronglyMeasurable]
  exact Measurable.aemeasurable (by fun_prop)

lemma setLIntegral_curvatureMeasureReal (f : DivFunction) {g : ℝ → ℝ≥0∞} (hg : Measurable g)
    {s : Set ℝ} (hs : MeasurableSet s) :
    ∫⁻ x in s, g x ∂f.curvatureMeasureReal
      = ∫⁻ x in ENNReal.toReal ⁻¹' s, g x.toReal ∂f.curvatureMeasure := by
  unfold curvatureMeasureReal
  rw [setLIntegral_map hs hg (by fun_prop)]

lemma setIntegral_curvatureMeasureReal {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : DivFunction) {g : ℝ → E} (hg : StronglyMeasurable g) {s : Set ℝ} (hs : MeasurableSet s) :
    ∫ x in s, g x ∂f.curvatureMeasureReal
      = ∫ x in ENNReal.toReal ⁻¹' s, g x.toReal ∂f.curvatureMeasure := by
  unfold curvatureMeasureReal
  rw [setIntegral_map hs hg.aestronglyMeasurable]
  exact Measurable.aemeasurable (by fun_prop)

lemma setLIntegral_Ioc_curvatureMeasureReal (f : DivFunction) {g : ℝ → ℝ≥0∞} (hg : Measurable g)
    {a b : ℝ} (h : 0 ≤ a) :
    ∫⁻ x in Ioc a b, g x ∂f.curvatureMeasureReal
      = ∫⁻ x in Ioc (ENNReal.ofReal a) (ENNReal.ofReal b), g x.toReal ∂f.curvatureMeasure := by
  rw [setLIntegral_curvatureMeasureReal f hg measurableSet_Ioc, ENNReal.preimage_toReal_Ioc h]

lemma setIntegral_Ioc_curvatureMeasureReal {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : DivFunction) {g : ℝ → E} (hg : StronglyMeasurable g) {a b : ℝ}
    (h : 0 ≤ a) :
    ∫ x in Ioc a b, g x ∂f.curvatureMeasureReal
      = ∫ x in Ioc (ENNReal.ofReal a) (ENNReal.ofReal b), g x.toReal ∂f.curvatureMeasure := by
  rw [setIntegral_curvatureMeasureReal f hg measurableSet_Ioc, ENNReal.preimage_toReal_Ioc h]

lemma integrable_curvatureMeasureReal_sub_iff_ne_top_of_ge (hf : rightDeriv f.realFun 1 = 0)
    {b : ℝ} (hb : 1 ≤ b) :
    IntegrableOn (fun x ↦ b - x) (Ioc 1 b) f.curvatureMeasureReal ↔ f (ENNReal.ofReal b) ≠ ∞ := by
  have : EqOn (fun x ↦ b - x) (fun x ↦ (ENNReal.ofReal b - ENNReal.ofReal x).toReal)
      (Ioc 1 b) := by
    intro x hx
    simp only
    rw [ENNReal.toReal_sub_of_le _ ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal,
      ENNReal.toReal_ofReal]
    · exact zero_le_one.trans hx.1.le
    · positivity
    · exact ENNReal.ofReal_le_ofReal hx.2
  rw [integrableOn_congr_fun this measurableSet_Ioc, IntegrableOn, integrable_toReal_iff]
  rotate_left
  · exact Measurable.aemeasurable (by fun_prop)
  · refine ae_of_all _ fun x ↦ (tsub_le_self.trans_lt ENNReal.ofReal_lt_top).ne
  rw [setLIntegral_Ioc_curvatureMeasureReal f (by fun_prop) zero_le_one, ENNReal.ofReal_one]
  have : ∫⁻ x in Ioc 1 (ENNReal.ofReal b),
        ENNReal.ofReal b - ENNReal.ofReal x.toReal ∂f.curvatureMeasure
      = ∫⁻ x in Ioc 1 (ENNReal.ofReal b), ENNReal.ofReal b - x ∂f.curvatureMeasure := by
    refine setLIntegral_congr_fun_ae measurableSet_Ioc <| ae_of_all _ fun x hx ↦ ?_
    rw [ENNReal.ofReal_toReal]
    refine (hx.2.trans_lt ?_).ne
    exact ENNReal.ofReal_lt_top
  rw [this, convex_taylor_one_right hf (ENNReal.one_le_ofReal.mpr hb) ENNReal.ofReal_ne_top]

lemma integrable_curvatureMeasureReal_sub_iff_ne_top_of_le (hf : rightDeriv f.realFun 1 = 0)
    {b : ℝ} (hb_nonneg : 0 ≤ b) (hb : b ≤ 1) :
    IntegrableOn (fun x ↦ x - b) (Ioc b 1) f.curvatureMeasureReal ↔ f (ENNReal.ofReal b) ≠ ∞ := by
  have : EqOn (fun x ↦ x - b) (fun x ↦ (ENNReal.ofReal x - ENNReal.ofReal b).toReal)
      (Ioc b 1) := by
    intro x hx
    simp only
    rw [ENNReal.toReal_sub_of_le _ ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal,
      ENNReal.toReal_ofReal]
    · positivity
    · exact hb_nonneg.trans hx.1.le
    · exact ENNReal.ofReal_le_ofReal hx.1.le
  rw [integrableOn_congr_fun this measurableSet_Ioc, IntegrableOn, integrable_toReal_iff]
  rotate_left
  · exact Measurable.aemeasurable (by fun_prop)
  · refine ae_of_all _ fun x ↦ (tsub_le_self.trans_lt ENNReal.ofReal_lt_top).ne
  rw [setLIntegral_Ioc_curvatureMeasureReal f (by fun_prop) hb_nonneg, ENNReal.ofReal_one]
  have : ∫⁻ x in Ioc (ENNReal.ofReal b) 1,
        ENNReal.ofReal x.toReal - ENNReal.ofReal b ∂f.curvatureMeasure
      = ∫⁻ x in Ioc (ENNReal.ofReal b) 1, x - ENNReal.ofReal b ∂f.curvatureMeasure := by
    refine setLIntegral_congr_fun_ae measurableSet_Ioc <| ae_of_all _ fun x hx ↦ ?_
    rw [ENNReal.ofReal_toReal]
    refine (hx.2.trans_lt ?_).ne
    exact ENNReal.one_lt_top
  rw [this, convex_taylor_one_left hf]
  simp [hb]

theorem convex_taylor_one_right_real (hf : rightDeriv f.realFun 1 = 0) {b : ℝ} (hb : 1 ≤ b) :
    f.realFun b = ∫ x in Ioc 1 b, b - x ∂f.curvatureMeasureReal := by
  rw [← ENNReal.ofReal_eq_ofReal_iff]
  rotate_left
  · exact f.realFun_nonneg
  · exact setIntegral_nonneg measurableSet_Ioc fun x hx ↦ sub_nonneg_of_le hx.2
  rw [setIntegral_Ioc_curvatureMeasureReal f _ zero_le_one, ENNReal.ofReal_one]
  swap; · refine Measurable.stronglyMeasurable ?_; fun_prop
  have : ∫ x in Ioc 1 (ENNReal.ofReal b), b - x.toReal ∂f.curvatureMeasure
      = ∫ x in Ioc 1 (ENNReal.ofReal b), (ENNReal.ofReal b - x).toReal ∂f.curvatureMeasure := by
    refine setIntegral_congr_fun measurableSet_Ioc fun x hx ↦ ?_
    rw [ENNReal.toReal_sub_of_le hx.2 ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal (zero_le_one.trans hb)]
  rw [this, integral_toReal]
  rotate_left
  · exact Measurable.aemeasurable (by fun_prop)
  · exact ae_of_all _ fun x ↦ tsub_le_self.trans_lt ENNReal.ofReal_lt_top
  rw [← convex_taylor_one_right hf (ENNReal.one_le_ofReal.mpr hb) ENNReal.ofReal_ne_top, realFun]

theorem convex_taylor_one_left_real (hf : rightDeriv f.realFun 1 = 0) {b : ℝ}
    (hb_zero : 0 ≤ b) (hb : b ≤ 1) :
    f.realFun b = ∫ x in Ioc b 1, x - b ∂f.curvatureMeasureReal := by
  rw [← ENNReal.ofReal_eq_ofReal_iff]
  rotate_left
  · exact f.realFun_nonneg
  · exact setIntegral_nonneg measurableSet_Ioc fun x hx ↦ sub_nonneg_of_le hx.1.le
  rw [setIntegral_Ioc_curvatureMeasureReal f _ hb_zero, ENNReal.ofReal_one]
  swap; · refine Measurable.stronglyMeasurable ?_; fun_prop
  have : ∫ x in Ioc (ENNReal.ofReal b) 1, x.toReal - b ∂f.curvatureMeasure
      = ∫ x in Ioc (ENNReal.ofReal b) 1, (x - ENNReal.ofReal b).toReal ∂f.curvatureMeasure := by
    refine setIntegral_congr_fun measurableSet_Ioc fun x hx ↦ ?_
    rw [ENNReal.toReal_sub_of_le hx.1.le (hx.2.trans_lt ENNReal.one_lt_top).ne,
      ENNReal.toReal_ofReal hb_zero]
  rw [this, integral_toReal]
  rotate_left
  · exact Measurable.aemeasurable (by fun_prop)
  · rw [ae_restrict_iff' measurableSet_Ioc]
    exact ae_of_all _ fun x hx ↦ tsub_le_self.trans_lt (hx.2.trans_lt ENNReal.one_lt_top)
  rw [← convex_taylor_one_left hf, realFun]
  simp [hb]

theorem convex_taylor_one (hf : rightDeriv f.realFun 1 = 0) {b : ℝ} (hb_zero : 0 ≤ b) :
    f.realFun b = ∫ x in (1)..b, b - x ∂f.curvatureMeasureReal := by
  rcases le_or_gt 1 b with hb | hb
  · simp only [intervalIntegral, not_lt, hb, Ioc_eq_empty, Measure.restrict_empty,
      integral_zero_measure, sub_zero]
    exact convex_taylor_one_right_real hf hb
  · simp only [intervalIntegral, not_lt, hb.le, Ioc_eq_empty, Measure.restrict_empty,
      integral_zero_measure, zero_sub]
    simp only [← integral_neg, neg_sub]
    exact convex_taylor_one_left_real hf hb_zero hb.le

end ConvexTaylor

end DivFunction

end ProbabilityTheory
