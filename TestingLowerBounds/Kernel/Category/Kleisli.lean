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

@[reassoc (attr := simp)]
lemma η_naturality {X Y : C} (f : X ⟶ Y) : T.η.app X ≫ T.map f = f ≫ T.η.app Y := by
  simpa using (T.η.naturality f).symm

--@[reassoc (attr := simp)]
lemma μ_naturality {X Y : C} (f : X ⟶ Y) : T.map (T.map f) ≫ T.μ.app Y = T.μ.app X ≫ T.map f := by
  simpa using (T.μ.naturality f)

@[reassoc (attr := simp)]
lemma μ_naturality' {X Y : C} (f : X ⟶ Y) : T.μ.app X ≫ T.map f = T.map (T.map f) ≫ T.μ.app Y := by
  simpa using (T.μ.naturality f).symm

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
  simp [associator_def, whiskerRight_def, whiskerLeft_def, tensorObj_def, tensorUnit_def,
    leftUnitor_def, rightUnitor_def, comp_def]

@[simp]
lemma Kleisli.comp_whiskerRight [CommutativeMonad T] {Y₁ Y₂ Y₃ : Kleisli T}
    (f : Y₁ ⟶ Y₂) (g : Y₂ ⟶ Y₃) (X : Kleisli T) :
    (f ≫ g) ▷ X = f ▷ X ≫ g ▷ X := by
  simp [associator_def, whiskerRight_def, whiskerLeft_def, tensorObj_def, tensorUnit_def,
    leftUnitor_def, rightUnitor_def, comp_def]

lemma Kleisli.whisker_exchange [CommutativeMonad T] {W X Y Z : Kleisli T}
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
  simp [associator_def, whiskerRight_def, whiskerLeft_def, tensorObj_def, tensorUnit_def,
    leftUnitor_def, rightUnitor_def, comp_def]

private lemma rightUnitor_naturality [CommutativeMonad T] (f : X ⟶ Y) :
    f ▷ 𝟙_ (Kleisli T) ≫ (ρ_ Y).hom = (ρ_ X).hom ≫ f := by
  simp [associator_def, whiskerRight_def, whiskerLeft_def, tensorObj_def, tensorUnit_def,
    rightUnitor_def, comp_def]

private lemma pentagon [CommutativeMonad T] (W X Y Z : Kleisli T) :
    (α_ W X Y).hom ▷ Z ≫ (α_ W (X ⊗ Y) Z).hom ≫ W ◁ (α_ X Y Z).hom
      = (α_ (W ⊗ X) Y Z).hom ≫ (α_ W X (Y ⊗ Z)).hom := by
  simp [associator_def, whiskerRight_def, whiskerLeft_def, tensorObj_def, comp_def]

private lemma triangle [CommutativeMonad T] (X Y : Kleisli T) :
    (α_ X (𝟙_ (Kleisli T)) Y).hom ≫ X ◁ (λ_ Y).hom = (ρ_ X).hom ▷ Y := by
  simp [associator_def, whiskerRight_def, whiskerLeft_def, tensorObj_def,
    tensorUnit_def, leftUnitor_def, rightUnitor_def, comp_def]

@[reassoc (attr := simp)]
lemma rStr_rStr (X Y Z : C) [CommutativeMonad T] :
    T.rStr X Y ▷ Z ≫ T.rStr (X ⊗ Y) Z
      = (α_ (T.obj X) Y Z).hom ≫ T.rStr X (Y ⊗ Z) ≫ T.map (α_ X Y Z).inv := by
  simp [Monad.rStr_assoc]

@[reassoc (attr := simp)]
lemma lStr_lStr (X Y Z : C) [CommutativeMonad T] :
    X ◁ T.lStr Y Z ≫ T.lStr X (Y ⊗ Z)
      = ((α_ X Y (T.obj Z)).inv ≫ T.lStr (X ⊗ Y) Z) ≫ T.map (α_ X Y Z).hom := by
   simp [Monad.lStr_assoc]

@[reassoc (attr := simp)]
lemma Monad.assoc_symm (T : Monad C) (Y₁ Y₂ Y₃ : C) :
    T.μ.app (T.obj (Y₁ ⊗ Y₂ ⊗ Y₃)) ≫ T.μ.app (Y₁ ⊗ Y₂ ⊗ Y₃)
      = T.map (T.μ.app (Y₁ ⊗ Y₂ ⊗ Y₃)) ≫ T.μ.app (Y₁ ⊗ Y₂ ⊗ Y₃) := by
  rw [Monad.assoc]

private lemma associator_naturality [CommutativeMonad T]
    (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃) :
    ((f₁ ⊗ f₂) ⊗ f₃) ≫ (α_ Y₁ Y₂ Y₃).hom = (α_ X₁ X₂ X₃).hom ≫ (f₁ ⊗ f₂ ⊗ f₃) := by
  simp only [tensorObj_def, tensorHom_def, whiskerRight_def, Monad.unit_dStr_right, whiskerLeft_def,
    Functor.id_obj, Monad.unit_dStr_left, comp_def, Functor.map_comp, Category.assoc,
    MonoidalCategory.comp_whiskerRight, Monad.rStr_mul_comm, Monad.rStr_naturality_id_right_assoc,
    whisker_assoc, rStr_rStr_assoc, Iso.map_inv_hom_id_assoc, tensor_whiskerLeft,
    μ_naturality'_assoc, μ_naturality', associator_def, Functor.mapIso_hom,
    Adjunction.toKleisli_map, Monad.assoc_symm, Functor.comp_obj, whiskerRight_tensor,
    MonoidalCategory.whiskerLeft_comp, Monad.lStr_mul_comm, Monad.lStr_naturality_id_left_assoc,
    η_naturality_assoc, η_naturality, Iso.hom_inv_id_assoc, Monad.left_unit, Category.comp_id]
  congr 4
  simp_rw [← Category.assoc]
  congr 2
  simp_rw [Category.assoc]
  simp_rw [← T.map_comp]
  simp

instance [CommutativeMonad T] : MonoidalCategory (Kleisli T) where
  tensor_comp := Kleisli.tensor_comp
  associator_naturality := Kleisli.associator_naturality
  leftUnitor_naturality := Kleisli.leftUnitor_naturality
  rightUnitor_naturality := Kleisli.rightUnitor_naturality
  pentagon := Kleisli.pentagon
  triangle := Kleisli.triangle

def braiding [BraidedCategory C] [CommutativeMonad T] (X Y : Kleisli T) :
    X ⊗ Y ≅ Y ⊗ X :=
  (Adjunction.toKleisli T).mapIso (@BraidedCategory.braiding C _ _ _ X Y)

lemma braiding_def' [BraidedCategory C] [CommutativeMonad T] (X Y : Kleisli T) :
    Kleisli.braiding X Y
      = (Adjunction.toKleisli T).mapIso (@BraidedCategory.braiding C _ _ _ X Y) := rfl

private lemma braiding_naturality_right [SymmetricCategory C] [SymmetricMonad T]
    (X Y Z : Kleisli T) (f : Y ⟶ Z) :
    X ◁ f ≫ (X.braiding Z).hom = (X.braiding Y).hom ≫ f ▷ X := by
  simp [braiding_def', associator_def, whiskerRight_def, whiskerLeft_def, tensorObj_def,
    tensorUnit_def, leftUnitor_def, rightUnitor_def, comp_def]

private lemma braiding_naturality_left [SymmetricCategory C] [SymmetricMonad T]
    (f : X ⟶ Y) (Z : Kleisli T) :
    f ▷ Z ≫ (Y.braiding Z).hom = (X.braiding Z).hom ≫ Z ◁ f := by
  simp [braiding_def', associator_def, whiskerRight_def, whiskerLeft_def, tensorObj_def,
    tensorUnit_def, leftUnitor_def, rightUnitor_def, comp_def]

private lemma hexagon_forward [SymmetricCategory C] [SymmetricMonad T] (X Y Z : Kleisli T) :
    (α_ X Y Z).hom ≫ (X.braiding (Y ⊗ Z)).hom ≫ (α_ Y Z X).hom =
      (X.braiding Y).hom ▷ Z ≫ (α_ Y X Z).hom ≫ Y ◁ (X.braiding Z).hom := by
  simp [braiding_def', associator_def, whiskerRight_def, whiskerLeft_def, tensorObj_def,
    tensorUnit_def, leftUnitor_def, rightUnitor_def, comp_def]

private lemma hexagon_reverse [SymmetricCategory C] [SymmetricMonad T] (X Y Z : Kleisli T) :
    (α_ X Y Z).inv ≫ ((X ⊗ Y).braiding Z).hom ≫ (α_ Z X Y).inv =
      X ◁ (Y.braiding Z).hom ≫ (α_ X Z Y).inv ≫ (X.braiding Z).hom ▷ Y := by
  simp [braiding_def', associator_def, whiskerRight_def, whiskerLeft_def, tensorObj_def,
    tensorUnit_def, leftUnitor_def, rightUnitor_def, comp_def]

instance [SymmetricCategory C] [SymmetricMonad T] : BraidedCategory (Kleisli T) where
  braiding := Kleisli.braiding
  braiding_naturality_right := Kleisli.braiding_naturality_right
  braiding_naturality_left := Kleisli.braiding_naturality_left
  hexagon_forward := Kleisli.hexagon_forward
  hexagon_reverse := Kleisli.hexagon_reverse

lemma braiding_def [SymmetricCategory C] [SymmetricMonad T] (X Y : Kleisli T) :
    β_ X Y = (Adjunction.toKleisli T).mapIso (@BraidedCategory.braiding C _ _ _ X Y) := rfl

instance [SymmetricCategory C] [SymmetricMonad T] : SymmetricCategory (Kleisli T) where
  symmetry X Y := by
    simp only [tensorObj_def, braiding_def, Functor.mapIso_hom, Adjunction.toKleisli_map, comp_def,
      Functor.map_comp, Category.assoc, η_naturality_assoc, η_naturality,
      SymmetricCategory.symmetry_assoc, Monad.left_unit, Functor.id_obj, Category.comp_id]
    rfl

end Kleisli

end Kleisli

end CategoryTheory
