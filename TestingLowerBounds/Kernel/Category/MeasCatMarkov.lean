/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import TestingLowerBounds.Kernel.Category.MeasCat
import TestingLowerBounds.Kernel.Category.Markov

/-!

# MeasCat is a Markov category

-/

open CategoryTheory MonoidalCategory

universe u v

namespace MeasCat

attribute [local instance] ConcreteCategory.instFunLike

instance : CopyDiscardCategoryStruct MeasCat where
  del _ := ⟨fun _ ↦ (), measurable_const⟩
  copy _ := ⟨fun x ↦ (x, x), measurable_id.prod measurable_id⟩

@[simp]
lemma del_apply (X : MeasCat) (x : (forget MeasCat).obj X) : del X x = () := rfl

@[simp]
lemma copy_apply (X : MeasCat) (x : (forget MeasCat).obj X) : copy X x = (x, x) := rfl

@[simp]
lemma chosenFiniteProducts_fst {X Y : MeasCat}
    (x : (forget MeasCat).obj X) (y : (forget MeasCat).obj Y) :
  (ChosenFiniteProducts.fst X Y) (x, y) = x := rfl

@[simp]
lemma chosenFiniteProducts_snd {X Y : MeasCat}
    (x : (forget MeasCat).obj X) (y : (forget MeasCat).obj Y) :
  (ChosenFiniteProducts.snd X Y) (x, y) = y := rfl

instance : CopyDiscardCategory MeasCat where
  del_copy _ := rfl
  copy_del_left _ := rfl
  copy_del_right _ := rfl
  copy_assoc _ := rfl
  copy_braiding _ := rfl
  copy_tensor _ _ := rfl
  del_tensor _ _ := rfl
  copy_unit := rfl
  del_unit := rfl

instance : MarkovCategory MeasCat where
  del_unique _ := by ext; rfl

end MeasCat
