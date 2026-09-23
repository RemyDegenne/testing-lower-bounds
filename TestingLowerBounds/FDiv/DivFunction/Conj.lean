/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import TestingLowerBounds.FDiv.DivFunction.DerivAtTop

/-! # Conjugate of a divergence function
-/

namespace ProbabilityTheory

namespace DivFunction

noncomputable
def conj (f : DivFunction) : DivFunction where
  toFun x := if x = 0 then f.derivAtTop else x * f x⁻¹
  one := by simp
  convexOn' := sorry
  continuous' := sorry

end DivFunction

end ProbabilityTheory
