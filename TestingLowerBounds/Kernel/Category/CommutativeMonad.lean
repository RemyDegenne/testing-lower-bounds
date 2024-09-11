/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.CategoryTheory.Monad.Basic
import Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-!

# Categories of measurable spaces and Kernels

-/

open CategoryTheory MonoidalCategory

universe u v

namespace CategoryTheory

section CommutativeMonad

class LeftStrong {C : Type u} [Category.{v} C] [MonoidalCategory C] (T : Monad C) where
  leftStr : ((𝟭 C : C ⥤ C).prod (T : C ⥤ C)) ⋙ (tensor C) ⟶ (tensor C) ⋙ (T : C ⥤ C)
  left_unit_comp (X : C) : (λ_ (T.obj X)).inv ≫ leftStr.app (𝟙_ C, X)
      = T.map (λ_ X).inv := by aesop_cat
  left_assoc (X Y Z : C) : leftStr.app (X ⊗ Y, Z) ≫ T.map (α_ X Y Z).hom
      = (α_ X Y (T.obj Z)).hom ≫ (X ◁ leftStr.app (Y, Z)) ≫ leftStr.app (X, Y ⊗ Z) := by
    aesop_cat
  left_unit_comm (X Y : C) : (X ◁ T.η.app Y) ≫ leftStr.app (X, Y) = T.η.app (X ⊗ Y) := by
    aesop_cat
  left_mul_comm (X Y : C) : (X ◁ T.μ.app Y) ≫ leftStr.app (X, Y)
      = leftStr.app (X, T.obj Y) ≫ T.map (leftStr.app (X, Y)) ≫ T.μ.app (X ⊗ Y) := by aesop_cat

class RightStrong {C : Type u} [Category.{v} C] [MonoidalCategory C] (T : Monad C) where
  rightStr : ((T : C ⥤ C).prod (𝟭 C : C ⥤ C)) ⋙ (tensor C) ⟶ (tensor C) ⋙ (T : C ⥤ C)
  right_unit_comp (X : C) : (ρ_ (T.obj X)).inv ≫ rightStr.app (X, 𝟙_ C)
      = T.map (ρ_ X).inv := by aesop_cat
  right_assoc (X Y Z : C) : rightStr.app (X, Y ⊗ Z) ≫ T.map (α_ X Y Z).inv
      = (α_ (T.obj X) Y Z).inv ≫ (rightStr.app (X, Y) ▷ Z) ≫ rightStr.app (X ⊗ Y, Z) := by
    aesop_cat
  right_unit_comm (X Y : C) : (T.η.app X ▷ Y) ≫ rightStr.app (X, Y) = T.η.app (X ⊗ Y) := by
    aesop_cat
  right_mul_comm (X Y : C) : (T.μ.app X ▷ Y) ≫ rightStr.app (X, Y)
      = rightStr.app (T.obj X, Y) ≫ T.map (rightStr.app (X, Y)) ≫ T.μ.app (X ⊗ Y) := by aesop_cat

class Strong {C : Type u} [Category.{v} C] [MonoidalCategory C] (T : Monad C)
    extends LeftStrong T, RightStrong T where
  left_right (X Y Z : C) : (leftStr.app (X, Y) ▷ Z) ≫ rightStr.app (X ⊗ Y, Z)
    = (α_ X (T.obj Y) Z).hom ≫ (X ◁ rightStr.app (Y, Z)) ≫ leftStr.app (X, Y ⊗ Z)
      ≫ T.map (α_ _ _ _).inv := by aesop_cat

class CommutativeMonad {C : Type u} [Category.{v} C] [MonoidalCategory C] (T : Monad C)
    extends Strong T where
  comm (X Y : C) : leftStr.app (T.obj X, Y) ≫ T.map (rightStr.app (X, Y)) ≫ T.μ.app (X ⊗ Y)
    = rightStr.app (X, T.obj Y) ≫ T.map (leftStr.app (X, Y)) ≫ T.μ.app (X ⊗ Y) := by aesop_cat

-- TODO: does that class make sense?
class SymmetricMonad {C : Type u} [Category.{v} C] [MonoidalCategory C]
    [SymmetricCategory C] (T : Monad C) extends CommutativeMonad T where
  braiding_left_right (X Y : C) : leftStr.app (X, Y) ≫ T.map (β_ X Y).hom
      = (β_ X (T.obj Y)).hom ≫ rightStr.app (Y, X) := by aesop_cat
  braiding_right_left (X Y : C) : rightStr.app (X, Y) ≫ T.map (β_ X Y).hom
      = (β_ (T.obj X) Y).hom ≫ leftStr.app (Y, X) := by aesop_cat

section LeftRightStrength

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

def Monad.lStr (T : Monad C) [LeftStrong T] (X Y : C) :
    X ⊗ T.obj Y ⟶ T.obj (X ⊗ Y) :=
  LeftStrong.leftStr.app (X, Y)

@[simp]
lemma Monad.lStr_unit_comp (T : Monad C) [LeftStrong T] (X : C) :
    (λ_ (T.obj X)).inv ≫ T.lStr (𝟙_ C) X = T.map (λ_ X).inv :=
  LeftStrong.left_unit_comp _

lemma Monad.lStr_assoc (T : Monad C) [LeftStrong T] (X Y Z : C) :
    T.lStr (X ⊗ Y) Z ≫ T.map (α_ X Y Z).hom
      = (α_ X Y (T.obj Z)).hom ≫ (X ◁ T.lStr Y Z) ≫ T.lStr X (Y ⊗ Z) :=
  LeftStrong.left_assoc _ _ _

@[simp]
lemma Monad.lStr_unit_comm (T : Monad C) [LeftStrong T] (X Y : C) :
    (X ◁ T.η.app Y) ≫ T.lStr X Y = T.η.app (X ⊗ Y) :=
  LeftStrong.left_unit_comm _ _

lemma Monad.lStr_mul_comm (T : Monad C) [LeftStrong T] (X Y : C) :
    (X ◁ T.μ.app Y) ≫ T.lStr X Y
      = T.lStr X (T.obj Y) ≫ T.map (T.lStr X Y) ≫ T.μ.app (X ⊗ Y) :=
  LeftStrong.left_mul_comm _ _

lemma Monad.lStr_naturality (T : Monad C) [LeftStrong T] {X₁ X₂ Y₁ Y₂ : C}
    (f : (X₁, X₂) ⟶ (Y₁, Y₂)) :
    (f.1 ⊗ T.map f.2) ≫ T.lStr Y₁ Y₂ = T.lStr X₁ X₂ ≫ T.map (f.1 ⊗ f.2) := by
  simpa using LeftStrong.leftStr.naturality _

lemma Monad.lStr_naturality' (T : Monad C) [LeftStrong T] {X₁ X₂ Y₁ Y₂ : C}
    (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) :
    (f₁ ⊗ T.map f₂) ≫ T.lStr Y₁ Y₂ = T.lStr X₁ X₂ ≫ T.map (f₁ ⊗ f₂) := T.lStr_naturality (f₁, f₂)

lemma Monad.lStr_naturality_id_left (T : Monad C) [LeftStrong T] {X Y₂ : C} (Y₁ : C)
    (f : X ⟶ Y₂) :
    (Y₁ ◁ T.map f) ≫ T.lStr Y₁ Y₂ = T.lStr Y₁ X ≫ T.map (Y₁ ◁ f) := by
  simpa using T.lStr_naturality (𝟙 Y₁, f)

lemma Monad.lStr_naturality_id_right (T : Monad C) [LeftStrong T] {X Y₁ : C}
    (f : X ⟶ Y₁) (Y₂ : C) :
    (f ▷ T.obj Y₂) ≫ T.lStr Y₁ Y₂ = T.lStr X Y₂ ≫ T.map (f ▷ Y₂) := by
  simpa using T.lStr_naturality (f, 𝟙 Y₂)

def Monad.rStr (T : Monad C) [RightStrong T] (X Y : C) :
    T.obj X ⊗ Y ⟶ T.obj (X ⊗ Y) :=
  RightStrong.rightStr.app (X, Y)

@[simp]
lemma Monad.rStr_unit_comp (T : Monad C) [RightStrong T] (X : C) :
    (ρ_ (T.obj X)).inv ≫ T.rStr X (𝟙_ C) = T.map (ρ_ X).inv :=
  RightStrong.right_unit_comp _

lemma Monad.rStr_assoc (T : Monad C) [RightStrong T] (X Y Z : C) :
    T.rStr X (Y ⊗ Z) ≫ T.map (α_ X Y Z).inv
      = (α_ (T.obj X) Y Z).inv ≫ (T.rStr X Y ▷ Z) ≫ T.rStr (X ⊗ Y) Z :=
  RightStrong.right_assoc _ _ _

@[simp]
lemma Monad.rStr_unit_comm (T : Monad C) [RightStrong T] (X Y : C) :
    T.η.app X ▷ Y ≫ T.rStr X Y = T.η.app (X ⊗ Y) :=
  RightStrong.right_unit_comm _ _

lemma Monad.rStr_mul_comm (T : Monad C) [RightStrong T] (X Y : C) :
    T.μ.app X ▷ Y ≫ T.rStr X Y
      = T.rStr (T.obj X) Y ≫ T.map (T.rStr X Y) ≫ T.μ.app (X ⊗ Y) :=
  RightStrong.right_mul_comm _ _

lemma Monad.rStr_naturality (T : Monad C) [RightStrong T] {X₁ X₂ Y₁ Y₂ : C}
    (f : (X₁, X₂) ⟶ (Y₁, Y₂)) :
    (T.map f.1 ⊗ f.2) ≫ T.rStr Y₁ Y₂ = T.rStr X₁ X₂ ≫ T.map (f.1 ⊗ f.2) := by
  simpa using RightStrong.rightStr.naturality _

lemma Monad.rStr_naturality' (T : Monad C) [RightStrong T] {X₁ X₂ Y₁ Y₂ : C}
    (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) :
    (T.map f₁ ⊗ f₂) ≫ T.rStr Y₁ Y₂ = T.rStr X₁ X₂ ≫ T.map (f₁ ⊗ f₂) := T.rStr_naturality (f₁, f₂)

lemma Monad.rStr_naturality_id_left (T : Monad C) [RightStrong T] {X Y₂ : C} (Y₁ : C)
    (f : X ⟶ Y₂) :
    (T.obj Y₁ ◁ f) ≫ T.rStr Y₁ Y₂ = T.rStr Y₁ X ≫ T.map (Y₁ ◁ f) := by
  simpa using T.rStr_naturality (𝟙 Y₁, f)

lemma Monad.rStr_naturality_id_right (T : Monad C) [RightStrong T] {X Y₁ : C}
    (f : X ⟶ Y₁) (Y₂ : C) :
    (T.map f ▷ Y₂) ≫ T.rStr Y₁ Y₂ = T.rStr X Y₂ ≫ T.map (f ▷ Y₂) := by
  simpa using T.rStr_naturality (f, 𝟙 Y₂)

def Monad.dStr (T : Monad C) [Strong T] (X Y : C) :
    T.obj X ⊗ T.obj Y ⟶ T.obj (X ⊗ Y) :=
  (T.lStr (T.obj X) Y) ≫ T.map (T.rStr X Y) ≫ T.μ.app (X ⊗ Y)

lemma Monad.lStr_rStr (T : Monad C) [Strong T] (X Y Z : C) :
    (T.lStr X Y ▷ Z) ≫ T.rStr (X ⊗ Y) Z
      = (α_ X (T.obj Y) Z).hom ≫ (X ◁ T.rStr Y Z) ≫ T.lStr X (Y ⊗ Z) ≫ T.map (α_ _ _ _).inv :=
  Strong.left_right _ _ _

lemma Monad.lStr_rStr_comm (T : Monad C) [CommutativeMonad T] (X Y : C) :
    T.lStr (T.obj X) Y ≫ T.map (T.rStr X Y) ≫ T.μ.app (X ⊗ Y)
      = T.rStr X (T.obj Y) ≫ T.map (T.lStr X Y) ≫ T.μ.app (X ⊗ Y) :=
  CommutativeMonad.comm _ _

lemma Monad.dStr_eq (T : Monad C) [CommutativeMonad T] (X Y : C) :
    T.dStr X Y = T.rStr X (T.obj Y) ≫ T.map (T.lStr X Y) ≫ T.μ.app (X ⊗ Y) :=
  T.lStr_rStr_comm X Y

@[simp]
lemma Monad.unit_whiskerRight_dStr (T : Monad C) [Strong T] (X Y : C) :
    (T.η.app X ▷ T.obj Y) ≫ T.dStr X Y = T.lStr X Y := by
  simp only [dStr, Functor.id_obj]
  simp_rw [← Category.assoc]
  rw [T.lStr_naturality_id_right (T.η.app X) Y]
  suffices (T.map (T.η.app X ▷ Y) ≫ T.map (T.rStr X Y)) ≫ T.μ.app (X ⊗ Y) = 𝟙 _ by simp [this]
  rw [← T.map_comp]
  simp

@[simp]
lemma Monad.unit_whiskerLeft_dStr (T : Monad C) [CommutativeMonad T] (X Y : C) :
    (T.obj X ◁ T.η.app Y) ≫ T.dStr X Y = T.rStr X Y := by
  simp only [T.dStr_eq, Functor.id_obj]
  simp_rw [← Category.assoc]
  rw [T.rStr_naturality_id_left X (T.η.app Y)]
  suffices (T.map (X ◁ T.η.app Y) ≫ T.map (T.lStr X Y)) ≫ T.μ.app (X ⊗ Y) = 𝟙 _ by simp [this]
  rw [← T.map_comp]
  simp

@[simp]
lemma Monad.unit_dStr_left (T : Monad C) [Strong T] (X : C) {Y₁ Y₂ : C}
    (f : Y₁ ⟶ T.obj Y₂) :
    (T.η.app X ⊗ f) ≫ T.dStr X Y₂ = X ◁ f ≫ T.lStr X Y₂ := by
  simp [tensorHom_def']

@[simp]
lemma Monad.unit_dStr_right (T : Monad C) [CommutativeMonad T] (X : C) {Y₁ Y₂ : C}
    (f : Y₁ ⟶ T.obj Y₂) :
    (f ⊗ T.η.app X) ≫ T.dStr Y₂ X = f ▷ X ≫ T.rStr Y₂ X := by
  simp [tensorHom_def]

@[simp]
lemma Monad.lStr_comp_braiding (T : Monad C) [SymmetricCategory C] [SymmetricMonad T] (X Y : C) :
    T.lStr X Y ≫ T.map (β_ X Y).hom = (β_ X (T.obj Y)).hom ≫ T.rStr Y X :=
  SymmetricMonad.braiding_left_right _ _

@[simp]
lemma Monad.rStr_comp_braiding (T : Monad C) [SymmetricCategory C] [SymmetricMonad T] (X Y : C) :
    T.rStr X Y ≫ T.map (β_ X Y).hom = (β_ (T.obj X) Y).hom ≫ T.lStr Y X :=
  SymmetricMonad.braiding_right_left _ _

end LeftRightStrength

class Affine {C : Type u} [Category.{v} C] [MonoidalCategory C] (T : Monad C) where
  affine : T.obj (𝟙_ C) ≅ 𝟙_ C := by aesop_cat

-- The Giry monad is not affine unless we restrict the measures to probability measures.

end CommutativeMonad

end CategoryTheory
