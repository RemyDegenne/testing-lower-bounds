/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-!

# Copy-discard and Markov categories

-/

universe u v

namespace CategoryTheory

namespace MonoidalCategory

section MarkovCategory

class CopyDiscardCategoryStruct (C : Type u) [𝒞 : Category.{v} C] [MonoidalCategory C] where
  del (X : C) : X ⟶ 𝟙_ C
  copy (X : C) : X ⟶ X ⊗ X

class CopyDiscardCategory (C : Type u) [𝒞 : Category.{v} C] [MonoidalCategory C]
    extends SymmetricCategory C, CopyDiscardCategoryStruct C where
  del_copy X : copy X ≫ (del X ▷ X) = (λ_ X).inv := by aesop_cat
  copy_del_left (X : C) : copy X ≫ (X ◁ del X) = (ρ_ X).inv := by aesop_cat
  copy_del_right (X : C) : copy X ≫ (del X ▷ X) = (λ_ X).inv := by aesop_cat
  copy_assoc (X : C) : copy X ≫ (X ◁ copy X) ≫ (α_ X X X).inv = copy X ≫ (copy X ▷ X) := by
    aesop_cat
  copy_braiding (X : C) : copy X ≫ (β_ X X).hom = copy X := by aesop_cat
  copy_tensor (X Y : C) : copy (X ⊗ Y)
    = (copy X ⊗ copy Y) ≫ (α_ _ _ _).hom ≫ (X ◁ (α_ _ _ _).inv)
      ≫ (𝟙 X ⊗ (β_ X Y).hom ⊗ 𝟙 Y) ≫ (X ◁ (α_ _ _ _).hom) ≫ (α_ _ _ _).inv := by aesop_cat
  del_tensor (X Y : C) : del (X ⊗ Y) = (del X ⊗ del Y) ≫ (λ_ (𝟙_ C)).hom := by aesop_cat
  copy_unit : copy (𝟙_ C) = (λ_ (𝟙_ C)).inv := by aesop_cat
  del_unit : del (𝟙_ C) = 𝟙 (𝟙_ C) := by aesop_cat

export CopyDiscardCategoryStruct (del copy)

variable {C : Type u} [𝒞 : Category.{v} C] [MonoidalCategory C]

-- omitted copy_assoc copy_tensor
attribute [reassoc (attr := simp)] CopyDiscardCategory.del_copy
  CopyDiscardCategory.copy_del_left CopyDiscardCategory.copy_del_right
  CopyDiscardCategory.copy_braiding CopyDiscardCategory.del_tensor
  CopyDiscardCategory.copy_unit CopyDiscardCategory.del_unit

class MarkovCategory (C : Type u) [𝒞 : Category.{v} C] [MonoidalCategory C]
    extends CopyDiscardCategory C where
  /-- The discard morphism is unique. -/
  del_unique {X : C} (f : X ⟶ 𝟙_ C) : f = del X

attribute [simp] MarkovCategory.del_unique

lemma del_congr [MarkovCategory C] {X : C} (f g : X ⟶ 𝟙_ C) : f = g := by simp

@[reassoc (attr := simp)]
lemma comp_del [MarkovCategory C] ⦃X Y : C⦄ (f : X ⟶ Y) : f ≫ del Y = del X := del_congr _ _

@[simp]
lemma del_unit [MarkovCategory C] : del (𝟙_ C) = 𝟙 (𝟙_ C) := del_congr _ _

end MarkovCategory

end MonoidalCategory

end CategoryTheory
