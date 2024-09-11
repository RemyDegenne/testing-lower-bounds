/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-!

# Copy-discard and Markov categories

-/

open CategoryTheory MonoidalCategory

universe u v

namespace CategoryTheory

section MarkovCategory

class CopyDiscardCategory (C : Type u) [𝒞 : Category.{u} C] [MonoidalCategory C]
    extends SymmetricCategory C where
  del (X : C) : X ⟶ 𝟙_ C
  copy (X : C) : X ⟶ X ⊗ X
  del_copy (X : C) : copy X ≫ (del X ▷ X) = (λ_ X).inv := by aesop_cat
  copy_del (X : C) : copy X ≫ (X ◁ del X) = (ρ_ X).inv := by aesop_cat
  copy_assoc (X : C) : copy X ≫ (X ◁ copy X) ≫ (α_ X X X).inv = copy X ≫ (copy X ▷ X) := by
    aesop_cat
  copy_braiding (X : C) : copy X ≫ (β_ X X).hom = copy X := by aesop_cat
  copy_tensor (X Y : C) :
    copy (X ⊗ Y) = (copy X ⊗ copy Y) ⊗≫ (𝟙 X ⊗ (β_ X Y).hom ⊗ 𝟙 Y) ≫ ⊗𝟙.hom := by aesop_cat
  del_tensor (X Y : C) : del (X ⊗ Y) = (del X ⊗ del Y) ≫ ⊗𝟙.hom := by aesop_cat
  copy_unit : copy (𝟙_ C) = ⊗𝟙.hom := by aesop_cat
  del_unit : del (𝟙_ C) = ⊗𝟙.hom := by aesop_cat

class MarkovCategory (C : Type u) [𝒞 : Category.{u} C] [MonoidalCategory C]
    extends CopyDiscardCategory C where
  /-- Every morphism is discardable. -/
  comp_del ⦃X Y : C⦄ (f : X ⟶ Y) : f ≫ del Y = del X := by aesop_cat

end MarkovCategory

end CategoryTheory
