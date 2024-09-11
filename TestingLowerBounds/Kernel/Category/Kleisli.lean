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

section Kleisli

variable {C : Type u} [Category.{v} C] {T : Monad C}

@[simp]
lemma todo {X Y : C} (f : X ⟶ T.obj Y) :
    T.η.app X ≫ T.map f ≫ T.μ.app Y = f := by
  have h := T.η.naturality f
  simp only [Functor.id_obj, Functor.id_map] at h
  rw [← Category.assoc, ← h, Category.assoc]
  simp

lemma Kleisli.comp_def {X Y Z : Kleisli T} (f : X ⟶ Y) (g : Y ⟶ Z) :
    f ≫ g = @CategoryStruct.comp C Category.toCategoryStruct _ _ _ f (T.map g) ≫ T.μ.app Z := by
  simp only [Category.assoc]
  rfl

variable [MonoidalCategory C]

instance (T : Monad C) [Strong T] : MonoidalCategoryStruct (Kleisli T) where
  tensorObj X Y := (Kleisli.Adjunction.toKleisli T).obj (X ⊗ Y)
  whiskerLeft X Y₁ Y₂ f :=
    ((T.η.app X ⊗ f) ≫ T.dStr X Y₂ : @tensorObj C _ _ X Y₁ ⟶ T.obj (X ⊗ Y₂))
  whiskerRight {X₁ X₂} f Y :=
    ((f ⊗ T.η.app Y) ≫ T.dStr X₂ Y : @tensorObj C _ _ X₁ Y ⟶ T.obj (X₂ ⊗ Y))
  tensorUnit := (Kleisli.Adjunction.toKleisli T).obj (𝟙_ C)
  associator X Y Z := (Kleisli.Adjunction.toKleisli T).mapIso
    (@MonoidalCategoryStruct.associator C _ _ X Y Z)
  leftUnitor X := (Kleisli.Adjunction.toKleisli T).mapIso
    (@MonoidalCategoryStruct.leftUnitor C _ _ X)
  rightUnitor X := (Kleisli.Adjunction.toKleisli T).mapIso
    (@MonoidalCategoryStruct.rightUnitor C _ _ X)

@[simp]
lemma Kleisli.wiskerLeft_id [Strong T] {X Y : Kleisli T} :
    X ◁ 𝟙 Y = 𝟙 (X ⊗ Y) := by
  suffices (T.η.app X ⊗ T.η.app Y) ≫ T.dStr X Y = T.η.app (X ⊗ Y) from this
  simp

@[simp]
lemma Kleisli.id_whiskerRight [Strong T] {X Y : Kleisli T} :
    𝟙 X ▷ Y = 𝟙 (X ⊗ Y) := by
  suffices (T.η.app X ⊗ T.η.app Y) ≫ T.dStr X Y = T.η.app (X ⊗ Y) from this
  simp

lemma Kleisli.tensorObj_def [Strong T] (X Y : Kleisli T) :
    X ⊗ Y = @tensorObj C _ _ X Y := rfl

@[simp]
lemma Kleisli.tensorHom_def [Strong T]
    {X₁ Y₁ X₂ Y₂ : Kleisli T} (f : X₁ ⟶ Y₁) (g: X₂ ⟶ Y₂) :
    f ⊗ g = (f ▷ X₂) ≫ (Y₁ ◁ g) := rfl

lemma Kleisli.whiskerLeft_def [Strong T] (X : Kleisli T) {Y₁ Y₂ : Kleisli T} (f : Y₁ ⟶ Y₂) :
    X ◁ f = (T.η.app X ⊗ f) ≫ T.dStr X Y₂ := rfl

lemma Kleisli.whiskerRight_def [Strong T] {X₁ X₂ : Kleisli T} (f : X₁ ⟶ X₂) (Y : Kleisli T) :
    f ▷ Y = ((f ⊗ T.η.app Y) ≫ T.dStr X₂ Y : @tensorObj C _ _ X₁ Y ⟶ T.obj (X₂ ⊗ Y)) := rfl

lemma Kleisli.tensorUnit_def [Strong T] :
    𝟙_ (Kleisli T) = (Kleisli.Adjunction.toKleisli T).obj (𝟙_ C) := rfl

lemma Kleisli.associator_def [Strong T] (X Y Z : Kleisli T) :
    α_ X Y Z = (Kleisli.Adjunction.toKleisli T).mapIso
      (@MonoidalCategoryStruct.associator C _ _ X Y Z) := rfl

lemma Kleisli.leftUnitor_def [Strong T] (X : Kleisli T) :
    λ_ X = (Kleisli.Adjunction.toKleisli T).mapIso
      (@MonoidalCategoryStruct.leftUnitor C _ _ X) := rfl

lemma Kleisli.rightUnitor_def [Strong T] (X : Kleisli T) :
    ρ_ X = (Kleisli.Adjunction.toKleisli T).mapIso
      (@MonoidalCategoryStruct.rightUnitor C _ _ X) := rfl

@[simp]
lemma Kleisli.whiskerLeft_comp [Strong T] (X : Kleisli T) {Y₁ Y₂ Y₃ : Kleisli T}
    (f : Y₁ ⟶ Y₂) (g : Y₂ ⟶ Y₃) :
    X ◁ (f ≫ g) = X ◁ f ≫ X ◁ g := by
  simp only [comp_def, Category.assoc, whiskerLeft_def, Functor.id_obj, Monad.unit_dStr_left,
    MonoidalCategory.whiskerLeft_comp, Functor.map_comp]
  slice_rhs 2 3 => rw [← T.lStr_naturality_id_left]
  simp only [Category.assoc]
  rw [T.lStr_mul_comm]
  rfl

@[simp]
lemma Kleisli.comp_whiskerRight [CommutativeMonad T] {Y₁ Y₂ Y₃ : Kleisli T}
    (f : Y₁ ⟶ Y₂) (g : Y₂ ⟶ Y₃) (X : Kleisli T) :
    (f ≫ g) ▷ X = f ▷ X ≫ g ▷ X := by
  simp only [comp_def, Category.assoc, whiskerRight_def, Monad.unit_dStr_right, comp_whiskerRight,
    MonoidalCategory.comp_whiskerRight, Functor.map_comp]
  slice_rhs 2 3 => rw [← T.rStr_naturality_id_right]
  simp only [Category.assoc]
  rw [T.rStr_mul_comm]
  rfl

lemma Kleisli.whisker_exchange [CommutativeMonad T] {W X Y Z : Kleisli T}
    (f : W ⟶ X) (g : Y ⟶ Z) :
    W ◁ g ≫ f ▷ Z = f ▷ Y ≫ X ◁ g := by
  simp only [whiskerLeft_def, Functor.id_obj, Monad.unit_dStr_left, whiskerRight_def,
    Monad.unit_dStr_right]
  simp only [comp_def, Functor.map_comp, ← Category.assoc]
  slice_rhs 2 3 => rw [← T.rStr_naturality_id_left]
  slice_rhs 1 2 => rw [← MonoidalCategory.whisker_exchange]
  slice_lhs 2 3 => rw [← T.lStr_naturality_id_right]
  simp only [Category.assoc]
  congr 2
  exact T.lStr_rStr_comm X Z

lemma todo' (X Y : C) :
    (α_ X (𝟙_ C) Y).hom ≫ T.η.app (X ⊗ 𝟙_ C ⊗ Y) ≫ T.map (X ◁ (λ_ Y).hom)
      = (ρ_ X).hom ▷ Y ≫ T.η.app (X ⊗ Y) := by
  have h := T.η.naturality
  simp only [Functor.id_obj, Functor.id_map] at h
  slice_lhs 2 3 => rw [← h]
  simp only [triangle_assoc]

namespace Kleisli

variable {W X Y Z X₁ Y₁ Z₁ X₂ Y₂ Z₂ X₃ Y₃ Z₃ : Kleisli T}

private lemma tensor_comp [CommutativeMonad T]
    (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (g₁ : Y₁ ⟶ Z₁) (g₂ : Y₂ ⟶ Z₂) :
    f₁ ≫ g₁ ⊗ f₂ ≫ g₂ = (f₁ ⊗ f₂) ≫ (g₁ ⊗ g₂) := by
  simp only [tensorHom_def, comp_whiskerRight, whiskerLeft_comp, Category.assoc]
  slice_lhs 2 3 => rw [← whisker_exchange]
  simp

private lemma leftUnitor_naturality [CommutativeMonad T] (f : X ⟶ Y) :
    𝟙_ (Kleisli T) ◁ f ≫ (λ_ Y).hom = (λ_ X).hom ≫ f := by
  simp only [Kleisli.whiskerLeft_def, Monad.unit_dStr_left, Kleisli.leftUnitor_def,
    Functor.mapIso_hom, Kleisli.Adjunction.toKleisli_map, Kleisli.comp_def, Functor.map_comp,
    Category.assoc, Monad.right_unit, Category.comp_id]
  simp only [Kleisli.tensorUnit_def, Kleisli.Adjunction.toKleisli_obj, id_whiskerLeft,
    Category.assoc, Iso.cancel_iso_hom_left]
  slice_lhs 2 3 => rw [T.lStr_unit_comp Y]
  rw [← T.map_comp]
  simp

private lemma rightUnitor_naturality [CommutativeMonad T] (f : X ⟶ Y) :
    f ▷ 𝟙_ (Kleisli T) ≫ (ρ_ Y).hom = (ρ_ X).hom ≫ f := by
  simp only [Kleisli.whiskerRight_def, Monad.unit_dStr_right, Kleisli.rightUnitor_def,
    Functor.mapIso_hom, Kleisli.Adjunction.toKleisli_map, Kleisli.comp_def, Functor.map_comp,
    Category.assoc, Monad.right_unit, Category.comp_id, todo]
  simp only [Kleisli.tensorUnit_def, Kleisli.Adjunction.toKleisli_obj,
    MonoidalCategory.whiskerRight_id, Category.assoc, Iso.cancel_iso_hom_left]
  slice_lhs 2 3 => rw [T.rStr_unit_comp Y]
  rw [← T.map_comp]
  simp

private lemma pentagon [CommutativeMonad T] (W X Y Z : Kleisli T) :
    (α_ W X Y).hom ▷ Z ≫ (α_ W (X ⊗ Y) Z).hom ≫ W ◁ (α_ X Y Z).hom
      = (α_ (W ⊗ X) Y Z).hom ≫ (α_ W X (Y ⊗ Z)).hom := by
  simp only [Kleisli.associator_def, Functor.mapIso_hom, Kleisli.Adjunction.toKleisli_map]
  simp only [Kleisli.whiskerRight_def, Kleisli.whiskerLeft_def, Functor.id_obj]
  simp only [Kleisli.tensorObj_def, Monad.unit_dStr_right, comp_whiskerRight, Category.assoc,
    Monad.rStr_unit_comm, Monad.unit_dStr_left, MonoidalCategory.whiskerLeft_comp,
    Monad.lStr_unit_comm, Kleisli.comp_def, Functor.map_comp, Monad.right_unit, Category.comp_id]
  simp only [MonoidalCategory.comp_whiskerRight]
  slice_lhs 2 3 => rw [Monad.rStr_unit_comm]
  simp only [Functor.id_obj, Functor.map_id, Category.id_comp,
    Category.assoc, Category.comp_id]
  have h := T.η.naturality
  simp only [Functor.id_obj, Functor.id_map] at h
  slice_rhs 2 3 => rw [← h]
  slice_lhs 1 2 => rw [h]
  slice_lhs 2 3 => rw [← T.map_comp]
  slice_lhs 2 3 => rw [← T.map_comp]
  rw [← T.map_comp]
  rw [todo]
  slice_lhs 3 4 => rw [← h]
  simp only [Functor.id_obj, Category.comp_id, pentagon_assoc]

private lemma triangle [CommutativeMonad T] (X Y : Kleisli T) :
    (α_ X (𝟙_ (Kleisli T)) Y).hom ≫ X ◁ (λ_ Y).hom = (ρ_ X).hom ▷ Y := by
  simp only [Kleisli.associator_def, Functor.mapIso_hom, Kleisli.Adjunction.toKleisli_map,
    Kleisli.leftUnitor_def, Kleisli.rightUnitor_def]
  simp only [Kleisli.tensorUnit_def, Kleisli.Adjunction.toKleisli_obj]
  simp only [Kleisli.whiskerLeft_def, Functor.id_obj, Monad.unit_dStr_left,
    MonoidalCategory.whiskerLeft_comp, Category.assoc, Monad.lStr_unit_comm, Kleisli.comp_def,
    Functor.map_comp, Kleisli.whiskerRight_def, Monad.unit_dStr_right, comp_whiskerRight,
    Monad.rStr_unit_comm]
  simp only [Kleisli.tensorObj_def, Monad.right_unit, Category.comp_id]
  simp only [Functor.id_obj, Category.comp_id, MonoidalCategory.comp_whiskerRight, Category.assoc,
    Monad.rStr_unit_comm]
  exact todo' (T := T) _ _

instance [CommutativeMonad T] : MonoidalCategory (Kleisli T) where
  tensor_comp := Kleisli.tensor_comp
  associator_naturality f₁ f₂ f₃ := by
    simp only [Kleisli.associator_def, Functor.mapIso_hom, Kleisli.Adjunction.toKleisli_map]
    simp only [Kleisli.tensorObj_def, Kleisli.tensorHom_def, Kleisli.comp_whiskerRight,
      Category.assoc, Kleisli.whiskerLeft_comp]
    simp only [Kleisli.whiskerRight_def, Monad.unit_dStr_right, comp_whiskerRight, Category.assoc,
      Kleisli.whiskerLeft_def, Functor.id_obj, Monad.unit_dStr_left, whisker_assoc,
      tensor_whiskerLeft, whiskerRight_tensor, MonoidalCategory.whiskerLeft_comp]
    simp only [Kleisli.comp_def, Functor.map_comp, Category.assoc, Monad.right_unit,
      Category.comp_id]
    simp only [Functor.id_obj, Functor.map_id, Category.id_comp]
    have h1 := T.η.naturality
    simp only [Functor.id_obj, Functor.id_map] at h1
    sorry
  leftUnitor_naturality := Kleisli.leftUnitor_naturality
  rightUnitor_naturality := Kleisli.rightUnitor_naturality
  pentagon := Kleisli.pentagon
  triangle := Kleisli.triangle

def braiding [BraidedCategory C] [CommutativeMonad T] (X Y : Kleisli T) :
    X ⊗ Y ≅ Y ⊗ X :=
  (Kleisli.Adjunction.toKleisli T).mapIso (@BraidedCategory.braiding C _ _ _ X Y)

lemma braiding_def [BraidedCategory C] [CommutativeMonad T] (X Y : Kleisli T) :
    Kleisli.braiding X Y
      = (Kleisli.Adjunction.toKleisli T).mapIso (@BraidedCategory.braiding C _ _ _ X Y) := rfl

instance [SymmetricCategory C] [SymmetricMonad T] : BraidedCategory (Kleisli T) where
  braiding := Kleisli.braiding
  braiding_naturality_right X Y Z f := by
    simp only [Kleisli.braiding_def, Functor.mapIso_hom, Kleisli.Adjunction.toKleisli_map]
    simp only [Kleisli.tensorObj_def, Kleisli.whiskerLeft_def, Functor.id_obj, Monad.unit_dStr_left,
      Functor.mapIso_hom, Kleisli.Adjunction.toKleisli_map, Kleisli.comp_def, Functor.map_comp,
      Category.assoc, Monad.right_unit, Category.comp_id, Kleisli.whiskerRight_def,
      Monad.unit_dStr_right]
    have hη := T.η.naturality
    simp only [Functor.id_obj, Functor.id_map] at hη
    slice_rhs 2 3 => rw [← hη]
    slice_rhs 1 2 => rw [← BraidedCategory.braiding_naturality_right]
    simp
  braiding_naturality_left {X Y} f Z := by
    simp only [Kleisli.braiding_def, Functor.mapIso_hom, Kleisli.Adjunction.toKleisli_map]
    simp only [Kleisli.tensorObj_def, Kleisli.whiskerRight_def, Monad.unit_dStr_right,
      Functor.mapIso_hom, Kleisli.Adjunction.toKleisli_map, Kleisli.comp_def, Functor.map_comp,
      Category.assoc, Monad.right_unit, Category.comp_id, Kleisli.whiskerLeft_def, Functor.id_obj,
      Monad.unit_dStr_left]
    have hη := T.η.naturality
    simp only [Functor.id_obj, Functor.id_map] at hη
    slice_rhs 2 3 => rw [← hη]
    slice_rhs 1 2 => rw [← BraidedCategory.braiding_naturality_left]
    simp
  hexagon_forward X Y Z := by
    simp only [Kleisli.braiding_def, Functor.mapIso_hom, Kleisli.Adjunction.toKleisli_map]
    simp only [Kleisli.tensorObj_def, Kleisli.associator_def, Functor.mapIso_hom,
      Kleisli.Adjunction.toKleisli_map, BraidedCategory.braiding_tensor_right, Category.assoc,
      Kleisli.comp_def, Functor.map_comp, Monad.right_unit, Category.comp_id,
      Kleisli.whiskerRight_def, Monad.unit_dStr_right, comp_whiskerRight, Monad.rStr_unit_comm,
      Kleisli.whiskerLeft_def, Functor.id_obj, Monad.unit_dStr_left,
      MonoidalCategory.whiskerLeft_comp, Monad.lStr_unit_comm]
    have hη := T.η.naturality
    simp only [Functor.id_obj, Functor.id_map] at hη
    slice_lhs 1 2 => rw [hη]
    slice_lhs 2 3 => rw [← T.map_comp, Iso.hom_inv_id, Functor.map_id]
    simp only [Category.id_comp, Category.assoc]
    slice_lhs 5 6 => rw [← T.map_comp, hη, T.map_comp]
    slice_lhs 6 7 => rw [← T.map_comp, ← T.map_comp, Iso.inv_hom_id]
    simp only [Functor.map_id, Category.id_comp, Monad.right_unit, Category.comp_id]
    sorry
    -- simp_rw [← T.map_comp, ← @BraidedCategory.hexagon_forward C _ _ _ X Y Z]
    -- slice_rhs 1 2 => rw [hη]
    -- simp only [BraidedCategory.braiding_tensor_right, Category.assoc, Iso.inv_hom_id,
    --   Category.comp_id, Iso.hom_inv_id_assoc, Functor.map_comp]
    -- congr 3
    -- slice_rhs 1 2 => rw [← T.map_comp, ← hη]
    -- simp
  hexagon_reverse X Y Z := by
    simp only [Kleisli.braiding_def, Functor.mapIso_hom, Kleisli.Adjunction.toKleisli_map]
    simp only [Kleisli.tensorObj_def, Kleisli.associator_def, Functor.mapIso_inv,
      Kleisli.Adjunction.toKleisli_map, Functor.mapIso_hom, BraidedCategory.braiding_tensor_left,
      Category.assoc, Kleisli.comp_def, Functor.map_comp, Monad.right_unit, Category.comp_id,
      Kleisli.whiskerLeft_def, Functor.id_obj, Monad.unit_dStr_left,
      MonoidalCategory.whiskerLeft_comp, Monad.lStr_unit_comm, Kleisli.whiskerRight_def,
      Monad.unit_dStr_right, comp_whiskerRight, Monad.rStr_unit_comm]
    have hη := T.η.naturality
    simp only [Functor.id_obj, Functor.id_map] at hη
    slice_lhs 1 2 => rw [hη]
    slice_lhs 2 3 => rw [← T.map_comp, Iso.inv_hom_id, Functor.map_id]
    simp only [Category.id_comp, Category.assoc]
    slice_lhs 5 6 => rw [← T.map_comp, hη, T.map_comp]
    slice_lhs 6 7 => rw [← T.map_comp, ← T.map_comp, Iso.hom_inv_id]
    simp only [Functor.map_id, Category.id_comp, Monad.right_unit, Category.comp_id]
    sorry
    -- simp_rw [← T.map_comp, ← @BraidedCategory.hexagon_reverse C _ _ _ X Y Z]
    -- slice_rhs 1 2 => rw [hη]
    -- simp only [BraidedCategory.braiding_tensor_left, Category.assoc, Iso.hom_inv_id,
    --   Category.comp_id, Iso.inv_hom_id_assoc, Functor.map_comp]
    -- congr 3
    -- slice_rhs 1 2 => rw [← T.map_comp, ← hη]
    -- simp

instance [SymmetricCategory C] [SymmetricMonad T] : SymmetricCategory (Kleisli T) where
  symmetry X Y := by
    simp only [Kleisli.tensorObj_def, Kleisli.braiding_def, Functor.mapIso_hom,
      Kleisli.Adjunction.toKleisli_map, Kleisli.comp_def, Functor.map_comp, Category.assoc,
      Monad.right_unit, Category.comp_id]
    sorry
    -- rw [← T.η.naturality]
    -- simp only [Functor.id_obj, Functor.id_map, SymmetricCategory.symmetry_assoc]
    -- rfl

end Kleisli

end Kleisli

end CategoryTheory
