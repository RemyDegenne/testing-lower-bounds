/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import TestingLowerBounds.FDiv.Basic

/-!
# Total variation distance

## Main definitions

* `FooBar`

## Main statements

* `fooBar_unique`

## Notation



## Implementation details



## References

* [F. Bar, *Quuxes*][bibkey]

## Tags

Foobars, barfoos
-/

open Real MeasureTheory

open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ ν : Measure α}

/-- Total variation distance between two measures. -/
noncomputable def tv (μ ν : Measure α) : ℝ := (fDiv (fun x ↦ 2⁻¹ * |1 - x|) μ ν).toReal

end ProbabilityTheory
