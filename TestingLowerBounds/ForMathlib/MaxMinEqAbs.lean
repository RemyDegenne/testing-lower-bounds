import Mathlib.Algebra.Lie.OfAssociative

--PR this to mathlib
--the hp LinearOrderedField may not be optimal
variable {α : Type*} [LinearOrderedField α]

lemma max_eq_add_add_abs_sub (a b : α) : max a b = 2⁻¹  * (a + b + |a - b|) := by
  rw [← max_add_min a, ← max_sub_min_eq_abs', add_sub_left_comm, add_sub_cancel_right]
  ring

lemma min_eq_add_sub_abs_sub (a b : α) : min a b = 2⁻¹ * (a + b - |a - b|) := by
  rw [← min_add_max a, ← max_sub_min_eq_abs', add_sub_assoc, sub_sub_cancel]
  ring
