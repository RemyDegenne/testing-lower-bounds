import Mathlib.Algebra.Group.Indicator
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Monoid.Canonical.Defs
import Mathlib.Order.ConditionallyCompleteLattice.Basic

variable {α M : Type*} [Preorder M] [One M] {s : Set α} {f g : α → M} {a : α}

namespace Set

--PR this to mathlib, just before `Set.mulIndicator_le_mulIndicator`.
@[to_additive]
lemma mulIndicator_le_mulIndicator' (h : a ∈ s → f a ≤ g a) :
    mulIndicator s f a ≤ mulIndicator s g a :=
  mulIndicator_rel_mulIndicator le_rfl fun ha ↦ h ha

end Set
