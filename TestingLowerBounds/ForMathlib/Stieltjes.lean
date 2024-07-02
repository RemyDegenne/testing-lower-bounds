import Mathlib.MeasureTheory.Measure.Stieltjes

--The content of this file has beed PRed to mathlib, see #14115. it is now merged, the next time we bump we can remove this file

open scoped Classical
open Set Filter Function ENNReal NNReal Topology MeasureTheory

open ENNReal (ofReal)

namespace StieltjesFunction

protected def const (c : ℝ) : StieltjesFunction where
  toFun := fun _ ↦ c
  mono' _ _ := by simp
  right_continuous' _ := continuousWithinAt_const

@[simp] lemma const_apply (c x : ℝ) : (StieltjesFunction.const c) x = c := rfl

def add (f g : StieltjesFunction) : StieltjesFunction where
  toFun := fun x => f x + g x
  mono' := f.mono.add g.mono
  right_continuous' := fun x => (f.right_continuous x).add (g.right_continuous x)

instance : AddCommMonoid StieltjesFunction where
  add f g := add f g
  add_assoc _ _ _ := ext fun _ ↦ add_assoc _ _ _
  zero := StieltjesFunction.const 0
  zero_add _ := ext fun _ ↦ zero_add _
  add_zero _ := ext fun _ ↦ add_zero _
  nsmul n f := {
    toFun := fun x ↦ n * f x
    mono' := f.mono.const_mul n.cast_nonneg
    right_continuous' := by
      simp_rw [← smul_eq_mul]
      exact fun x ↦ (f.right_continuous x).const_smul (n : ℝ≥0)}
  nsmul_zero x := by
    simp only [CharP.cast_eq_zero, zero_mul]
    rfl
  nsmul_succ n f := by
    ext x
    simp only [Nat.cast_add, Nat.cast_one]
    exact add_one_mul ↑n (f x)
  add_comm _ _ := ext fun _ ↦ add_comm _ _

instance : Module ℝ≥0 StieltjesFunction where
  smul c f := {
    toFun := fun x ↦ c * f x
    mono' := f.mono.const_mul c.2
    right_continuous' := by
      simp_rw [← smul_eq_mul]
      exact fun x ↦ (f.right_continuous x).const_smul c.1}
  one_smul _ := ext fun _ ↦ one_mul _
  mul_smul _ _ _ := ext fun _ ↦ mul_assoc _ _ _
  smul_zero _ := ext fun _ ↦ mul_zero _
  smul_add _ _ _ := ext fun _ ↦ mul_add _ _ _
  add_smul _ _ _ := ext fun _ ↦ add_mul _ _ _
  zero_smul _ := ext fun _ ↦ zero_mul _

@[simp] lemma add_apply (f g : StieltjesFunction) (x : ℝ) : (f + g) x = f x + g x := rfl

@[simp]
lemma measure_const (c : ℝ) : (StieltjesFunction.const c).measure = 0 :=
  Measure.ext_of_Ioc _ _ (fun _ _ _ ↦ by simp)

@[simp]
lemma measure_add (f g : StieltjesFunction) : (f + g).measure = f.measure + g.measure := by
  refine Measure.ext_of_Ioc _ _ (fun a b h ↦ ?_)
  simp only [measure_Ioc, add_apply, Measure.coe_add, Pi.add_apply]
  rw [← ENNReal.ofReal_add (sub_nonneg_of_le (f.mono h.le)) (sub_nonneg_of_le (g.mono h.le))]
  ring_nf

@[simp]
lemma measure_smul (c : ℝ≥0) (f : StieltjesFunction) : (c • f).measure = c • f.measure := by
  refine Measure.ext_of_Ioc _ _ (fun a b _ ↦ ?_)
  simp only [measure_Ioc, Measure.smul_apply]
  change ofReal (c * f b - c * f a) = c • ofReal (f b - f a)
  rw [← _root_.mul_sub, ENNReal.ofReal_mul zero_le_coe, ofReal_coe_nnreal, ← smul_eq_mul]
  rfl

end StieltjesFunction
