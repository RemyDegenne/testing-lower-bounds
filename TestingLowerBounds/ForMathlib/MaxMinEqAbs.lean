import Mathlib.Tactic.Basic
import Mathlib.Tactic.Bound.Init
import Mathlib.Util.CompileInductive
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Algebra.Order.Monoid.Unbundled.MinMax
import Mathlib.Algebra.Order.Ring.Defs

--PR this to mathlib
--the hp LinearOrderedField may not be optimal
variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]

lemma max_eq_add_add_abs_sub (a b : α) : max a b = 2⁻¹  * (a + b + |a - b|) := by
  rw [← max_add_min a, ← max_sub_min_eq_abs', add_sub_left_comm, add_sub_cancel_right]
  ring

lemma min_eq_add_sub_abs_sub (a b : α) : min a b = 2⁻¹ * (a + b - |a - b|) := by
  rw [← min_add_max a, ← max_sub_min_eq_abs', add_sub_assoc, sub_sub_cancel]
  ring
