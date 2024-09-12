/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.CategoryTheory.Monad.Kleisli
import TestingLowerBounds.Kernel.Category.CommutativeMonad

/-!

# Categories of measurable spaces and Kernels

-/

open CategoryTheory MonoidalCategory

universe u v

namespace CategoryTheory

namespace Kleisli

variable {C : Type u} [Category.{v} C] {T : Monad C}

lemma id_def {X : Kleisli T} : 𝟙 X = T.η.app X := rfl

lemma comp_def {X Y Z : Kleisli T} (f : X ⟶ Y) (g : Y ⟶ Z) :
    f ≫ g = @CategoryStruct.comp C Category.toCategoryStruct _ _ _ f (T.map g) ≫ T.μ.app Z := by
  simp only [Category.assoc]
  rfl

variable [MonoidalCategory C]

section Strong

variable [Strong T]

instance : MonoidalCategoryStruct (Kleisli T) where
  tensorObj X Y := (Adjunction.toKleisli T).obj (X ⊗ Y)
  whiskerLeft X Y₁ Y₂ f :=
    ((T.η.app X ⊗ f) ≫ T.dStr X Y₂ : @tensorObj C _ _ X Y₁ ⟶ T.obj (X ⊗ Y₂))
  whiskerRight {X₁ X₂} f Y :=
    ((f ⊗ T.η.app Y) ≫ T.dStr X₂ Y : @tensorObj C _ _ X₁ Y ⟶ T.obj (X₂ ⊗ Y))
  tensorUnit := (Adjunction.toKleisli T).obj (𝟙_ C)
  associator X Y Z := (Adjunction.toKleisli T).mapIso
    (@MonoidalCategoryStruct.associator C _ _ X Y Z)
  leftUnitor X := (Adjunction.toKleisli T).mapIso (@MonoidalCategoryStruct.leftUnitor C _ _ X)
  rightUnitor X := (Adjunction.toKleisli T).mapIso (@MonoidalCategoryStruct.rightUnitor C _ _ X)

lemma tensorObj_def (X Y : Kleisli T) : X ⊗ Y = @tensorObj C _ _ X Y := rfl

lemma tensorHom_def {X₁ Y₁ X₂ Y₂ : Kleisli T} (f : X₁ ⟶ Y₁) (g: X₂ ⟶ Y₂) :
    f ⊗ g = (f ▷ X₂) ≫ (Y₁ ◁ g) := rfl

lemma whiskerLeft_def (X : Kleisli T) {Y₁ Y₂ : Kleisli T} (f : Y₁ ⟶ Y₂) :
    X ◁ f = (T.η.app X ⊗ f) ≫ T.dStr X Y₂ := rfl

lemma whiskerRight_def {X₁ X₂ : Kleisli T} (f : X₁ ⟶ X₂) (Y : Kleisli T) :
    f ▷ Y = ((f ⊗ T.η.app Y) ≫ T.dStr X₂ Y : @tensorObj C _ _ X₁ Y ⟶ T.obj (X₂ ⊗ Y)) := rfl

lemma tensorUnit_def : 𝟙_ (Kleisli T) = (Kleisli.Adjunction.toKleisli T).obj (𝟙_ C) := rfl

lemma associator_def (X Y Z : Kleisli T) :
    α_ X Y Z = (Adjunction.toKleisli T).mapIso (@MonoidalCategoryStruct.associator C _ _ X Y Z) :=
  rfl

lemma leftUnitor_def (X : Kleisli T) :
    λ_ X = (Adjunction.toKleisli T).mapIso (@MonoidalCategoryStruct.leftUnitor C _ _ X) := rfl

lemma rightUnitor_def (X : Kleisli T) :
    ρ_ X = (Adjunction.toKleisli T).mapIso (@MonoidalCategoryStruct.rightUnitor C _ _ X) := rfl

lemma wiskerLeft_id {X Y : Kleisli T} : X ◁ 𝟙 Y = 𝟙 (X ⊗ Y) := by
  simp [id_def, whiskerLeft_def, tensorObj_def]

lemma id_whiskerRight {X Y : Kleisli T} : 𝟙 X ▷ Y = 𝟙 (X ⊗ Y) := by
  simp [id_def, whiskerRight_def, tensorObj_def]

lemma whiskerLeft_comp (X : Kleisli T) {Y₁ Y₂ Y₃ : Kleisli T}
    (f : Y₁ ⟶ Y₂) (g : Y₂ ⟶ Y₃) :
    X ◁ (f ≫ g) = X ◁ f ≫ X ◁ g := by
  simp [associator_def, whiskerRight_def, whiskerLeft_def, tensorObj_def, tensorUnit_def,
    leftUnitor_def, rightUnitor_def, comp_def]

end Strong

lemma comp_whiskerRight [CommutativeMonad T] {Y₁ Y₂ Y₃ : Kleisli T}
    (f : Y₁ ⟶ Y₂) (g : Y₂ ⟶ Y₃) (X : Kleisli T) :
    (f ≫ g) ▷ X = f ▷ X ≫ g ▷ X := by
  simp [associator_def, whiskerRight_def, whiskerLeft_def, tensorObj_def, tensorUnit_def,
    leftUnitor_def, rightUnitor_def, comp_def]

lemma whisker_exchange [CommutativeMonad T] {W X Y Z : Kleisli T}
    (f : W ⟶ X) (g : Y ⟶ Z) :
    W ◁ g ≫ f ▷ Z = f ▷ Y ≫ X ◁ g := by
  simp only [tensorObj_def, whiskerLeft_def, Functor.id_obj, Monad.unit_dStr_left, whiskerRight_def,
    Monad.unit_dStr_right, comp_def, Functor.map_comp, Category.assoc]
  slice_rhs 2 3 => rw [← T.rStr_naturality_id_left]
  slice_rhs 1 2 => rw [← MonoidalCategory.whisker_exchange]
  slice_lhs 2 3 => rw [← T.lStr_naturality_id_right]
  simp only [Category.assoc]
  congr 2
  exact T.lStr_rStr_comm X Z

variable {W X Y Z X₁ Y₁ Z₁ X₂ Y₂ Z₂ X₃ Y₃ Z₃ : Kleisli T}

private lemma tensor_comp [CommutativeMonad T]
    (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (g₁ : Y₁ ⟶ Z₁) (g₂ : Y₂ ⟶ Z₂) :
    f₁ ≫ g₁ ⊗ f₂ ≫ g₂ = (f₁ ⊗ f₂) ≫ (g₁ ⊗ g₂) := by
  simp only [tensorHom_def, comp_whiskerRight, whiskerLeft_comp, Category.assoc]
  slice_lhs 2 3 => rw [← whisker_exchange]
  simp

private lemma associator_naturality [CommutativeMonad T]
    (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃) :
    ((f₁ ⊗ f₂) ⊗ f₃) ≫ (α_ Y₁ Y₂ Y₃).hom = (α_ X₁ X₂ X₃).hom ≫ (f₁ ⊗ f₂ ⊗ f₃) := by
  simp only [tensorObj_def, tensorHom_def, whiskerRight_def, Monad.unit_dStr_right, whiskerLeft_def,
    Functor.id_obj, Monad.unit_dStr_left, comp_def, Functor.map_comp, Category.assoc,
    MonoidalCategory.comp_whiskerRight, Monad.rStr_mul_comm, Monad.rStr_naturality_id_right_assoc,
    whisker_assoc, rStr_rStr_assoc, Iso.map_inv_hom_id_assoc, tensor_whiskerLeft,
    μ_naturality_assoc, μ_naturality, Monad.assoc_symm, Functor.comp_obj, associator_def,
    Functor.mapIso_hom, Adjunction.toKleisli_map, Category.comp_id, whiskerRight_tensor,
    MonoidalCategory.whiskerLeft_comp, Monad.lStr_mul_comm, Monad.lStr_naturality_id_left_assoc,
    η_naturality_assoc, η_naturality, Iso.hom_inv_id_assoc, Monad.left_unit]
  congr 4
  simp_rw [← Category.assoc]
  congr 1
  simp_rw [Category.assoc, ← T.map_comp]
  congr 1
  simp only [μ_naturality, Monad.lStr_rStr_assoc, Iso.map_inv_hom_id_assoc, Iso.inv_hom_id_assoc]
  congr 3
  slice_rhs 1 2 => rw [← T.map_comp, lStr_lStr]
  simp

instance [CommutativeMonad T] : MonoidalCategory (Kleisli T) where
  tensorHom_def _ _ := rfl
  tensor_id := by simp [tensorHom_def, wiskerLeft_id, id_whiskerRight]
  tensor_comp := Kleisli.tensor_comp
  whiskerLeft_id := by simp [id_def, whiskerLeft_def, tensorObj_def]
  id_whiskerRight := by simp [id_def, whiskerRight_def, tensorObj_def]
  associator_naturality := Kleisli.associator_naturality
  leftUnitor_naturality := by
    simp [associator_def, whiskerRight_def, whiskerLeft_def, tensorObj_def, tensorUnit_def,
      leftUnitor_def, rightUnitor_def, comp_def]
  rightUnitor_naturality := by
    simp [associator_def, whiskerRight_def, whiskerLeft_def, tensorObj_def, tensorUnit_def,
      leftUnitor_def, rightUnitor_def, comp_def]
  pentagon := by
    simp [associator_def, whiskerRight_def, whiskerLeft_def, tensorObj_def, tensorUnit_def,
      leftUnitor_def, rightUnitor_def, comp_def]
  triangle := by
    simp [associator_def, whiskerRight_def, whiskerLeft_def, tensorObj_def, tensorUnit_def,
      leftUnitor_def, rightUnitor_def, comp_def]

def braiding [BraidedCategory C] [CommutativeMonad T] (X Y : Kleisli T) :
    X ⊗ Y ≅ Y ⊗ X :=
  (Adjunction.toKleisli T).mapIso (@BraidedCategory.braiding C _ _ _ X Y)

lemma braiding_def' [BraidedCategory C] [CommutativeMonad T] (X Y : Kleisli T) :
    Kleisli.braiding X Y
      = (Adjunction.toKleisli T).mapIso (@BraidedCategory.braiding C _ _ _ X Y) := rfl

instance [SymmetricCategory C] [SymmetricMonad T] : BraidedCategory (Kleisli T) where
  braiding := Kleisli.braiding
  braiding_naturality_right := by
    simp [braiding_def', associator_def, whiskerRight_def, whiskerLeft_def, tensorObj_def,
      tensorUnit_def, leftUnitor_def, rightUnitor_def, comp_def]
  braiding_naturality_left :=  by
    simp [braiding_def', associator_def, whiskerRight_def, whiskerLeft_def, tensorObj_def,
      tensorUnit_def, leftUnitor_def, rightUnitor_def, comp_def]
  hexagon_forward :=  by
    simp [braiding_def', associator_def, whiskerRight_def, whiskerLeft_def, tensorObj_def,
      tensorUnit_def, leftUnitor_def, rightUnitor_def, comp_def]
  hexagon_reverse :=  by
    simp [braiding_def', associator_def, whiskerRight_def, whiskerLeft_def, tensorObj_def,
      tensorUnit_def, leftUnitor_def, rightUnitor_def, comp_def]

lemma braiding_def [SymmetricCategory C] [SymmetricMonad T] (X Y : Kleisli T) :
    β_ X Y = (Adjunction.toKleisli T).mapIso (@BraidedCategory.braiding C _ _ _ X Y) := rfl

instance [SymmetricCategory C] [SymmetricMonad T] : SymmetricCategory (Kleisli T) where
  symmetry X Y := by
    simp only [tensorObj_def, braiding_def, Functor.mapIso_hom, Adjunction.toKleisli_map, comp_def,
      Functor.map_comp, Category.assoc, η_naturality_assoc, η_naturality,
      SymmetricCategory.symmetry_assoc, Monad.left_unit, Functor.id_obj, Category.comp_id]
    rfl

end Kleisli

end CategoryTheory
