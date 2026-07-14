/-
Copyright (c) 2026 William Hasley. All rights reserved.
Released under GNU GPL3 license as described in the file LICENSE.
Authors: William Hasley
-/


module


public import QuantSem.QuantumLib.HilbertSpaces.Basic
public import Mathlib.CategoryTheory.Monoidal.Category

namespace SyntacticRegister

open QuantumTypes
open CategoryTheory

/-
Quantum registers depend on Quantum Type composition.
Often, the given composition will be the Tensor product of hilbert spaces
-/

public structure QuantumRegister : Type 1 where
  space : Type
  struct : HilbertSpace space

@[default_instance]
public instance (R : QuantumRegister) : HilbertSpace R.space := R.struct

@[default_instance]
public instance QuantumRegisterCat : Category QuantumRegister where
  Hom R1 R2 :=  R1.space →ₗᵢ[ℂ] R2.space
  id R := IdMap R.space
  comp f1 f2 := LinearIsometry.comp f2 f1


@[ext]
public theorem CatRegisterHomExt {R1 R2 : QuantumRegister} (f g : R1 ⟶ R2) :
  (∀ x : R1.space, f.toFun x = g.toFun x) → f = g :=
  by intro h; apply LinearIsometry.ext_iff.mpr; apply h

public theorem CatRegisterHomExtIff {R1 R2 : QuantumRegister} (f g : R1 ⟶ R2) :
  f = g ↔ (∀ x : R1.space, f.toFun x = g.toFun x) :=
  by apply Iff.intro; intro hEq; rw[hEq]; intro x; rfl; apply CatRegisterHomExt

/-
    Isomorphisms in this category are Linear Isometric equivalences
-/

public abbrev LinearIsometryEquivToIso {R1 R2 : QuantumRegister}
  (e : R1.space ≃ₗᵢ[ℂ] R2.space) : R1 ≅ R2 :=
  .mk e.toLinearIsometry e.symm.toLinearIsometry
    (by apply EquivalenceToIsometryOfSymmRight e)
    (by apply EquivalenceToIsometryOfSymmLeft e)

/-
  Registers can be endowed with the structure of a Monoidal Category
-/


@[expose]
public noncomputable def QuantumRegisterTensor (R1 R2 : QuantumRegister) : QuantumRegister :=
  .mk
    (TensorProduct ℂ R1.space R2.space)
    (HilbertTensorFun R1.space R2.space)

notation A "⊗ᵣ" B => QuantumRegisterTensor A B

@[simp]
public theorem SpaceCommutesWithTensor (R1 R2 : QuantumRegister) :
  (R1 ⊗ᵣ R2).space = TensorProduct ℂ R1.space R2.space := by rfl


@[expose]
public noncomputable def QuantRegHomTensor {R1 R2 R3 R4 : QuantumRegister}
  (f : R1 ⟶ R3) (g : R2 ⟶ R4) :
  QuantumRegisterTensor R1 R2 ⟶ QuantumRegisterTensor R3 R4 := TensorLinearIsometries f g

notation f "⊗ₕ" g => QuantRegHomTensor f g


@[simp]
public theorem arrow_is_comp {R1 R2 R3 : QuantumRegister} (f : R1 ⟶ R2) (g : R2 ⟶ R3)
  : (f ≫ g) = (LinearIsometry.comp g f) := by rfl

@[simp]
public theorem comp_apply {R1 R2 R3 : QuantumRegister} (f : R1 ⟶ R2) (g : R2 ⟶ R3)
  (x : R1.space) : (f ≫ g).toFun x = g.toFun (f.toFun x) := by rfl

public abbrev id_map (R : QuantumRegister) : R ⟶ R := IdMap R.space

@[simp]
public theorem id_map_is_neutral_left {R1 R2 : QuantumRegister}
  (f : R1 ⟶ R2) : id_map R1 ≫ f = f := by rfl

@[simp]
public theorem id_map_is_neutral_right {R1 R2 : QuantumRegister}
  (f : R1 ⟶ R2) : f ≫ id_map R2 = f := by rfl

@[simp]
public theorem id_tensor_id : ∀ X Y,
  QuantRegHomTensor (id_map X) (id_map Y) = id_map (X ⊗ᵣ Y) :=
  by intro X Y; apply TensorOfIdIsId

@[simp]
public theorem apply_tensor {R1 R2 R3 R4: QuantumRegister} (f : R1 ⟶ R2) (g : R3 ⟶ R4)
  (x : R1.space) (y : R3.space) : (f ⊗ₕ g).toFun (x ⊗ₜ[ℂ] y) = (f.toFun x) ⊗ₜ[ℂ] (g.toFun y) := by rfl

@[simp]
public theorem one_is_id : ∀ X : QuantumRegister, 𝟙 X = id_map X :=
  by intro X; rfl

@[simp]
public theorem tensor_factorises {A A' C B B' D : QuantumRegister} : ∀ (f : A' ⟶ C) (g : B' ⟶ D)
  (h : A ⟶ A') (i : B ⟶ B'),
  (h ⊗ₕ i) ≫ (f ⊗ₕ g) = (h ≫ f) ⊗ₕ (i ≫ g) :=
  by intro f g h i; apply TensorFactorises f g h i

@[simp]
public theorem id_is_neutral_left : ∀ A B : QuantumRegister, ∀ (f : A ⟶ B),
  f ≫ (id_map B) = f := by intro A B f; apply IdIsNeutralLeft

@[simp]
public theorem id_is_neutral_right : ∀ A B : QuantumRegister, ∀ (f : A ⟶ B),
  (id_map A) ≫ f = f := by intro A B f; apply IdIsNeutralRight


@[expose]
public noncomputable def QuantRegHomTensorAssoc (R1 R2 R3 : QuantumRegister) :
  ((R1 ⊗ᵣ R2) ⊗ᵣ R3) ≅ (R1 ⊗ᵣ (R2 ⊗ᵣ R3)) := LinearIsometryEquivToIso HilbertTensorAssoc

public noncomputable abbrev CRegister : QuantumRegister := .mk ℂ CIsHilbert

public noncomputable abbrev CLeftUnitor (R : QuantumRegister) :
  (CRegister ⊗ᵣ R) ≅ R := LinearIsometryEquivToIso CIsLeftNeutral

public noncomputable abbrev CRightUnitor (R : QuantumRegister) :
  (R ⊗ᵣ CRegister) ≅ R := LinearIsometryEquivToIso CIsRightNeutral

public theorem AssocNaturality {R1 R2 R3 R4 R5 R6 : QuantumRegister}
  (f : R1 ⟶ R4) (g : R2 ⟶ R5) (h : R3 ⟶ R6) :
  (((f ⊗ₕ g) ⊗ₕ h) ≫ (QuantRegHomTensorAssoc R4 R5 R6).hom) =
  ((QuantRegHomTensorAssoc R1 R2 R3).hom ≫ ((f ⊗ₕ (g ⊗ₕ h)))) :=
  by
    unfold QuantRegHomTensorAssoc LinearIsometryEquivToIso QuantumRegisterTensor
    unfold QuantRegHomTensor
    simp;

public theorem LeftUnitorNaturality {R1 R2 : QuantumRegister} (f : R1 ⟶ R2) :
  ((id_map CRegister) ⊗ₕ f) ≫ (CLeftUnitor R2).hom = (CLeftUnitor R1).hom ≫ f :=
  by -- apply LinearIsometryExtOnTensor; intro x y; calc
     -- ((id_map CRegister⊗ₕf) ≫ (CLeftUnitor R2).hom).toFun (x ⊗ₜ[ℂ] y) =
     --   ((CLeftUnitor R2).hom).toFun ((id_map CRegister⊗ₕf).toFun (x ⊗ₜ[ℂ] y)) := by rfl
     -- _ = (CLeftUnitor R2).hom.toFun (x ⊗ₜ[ℂ] (f.toFun y)) := by rfl
     -- _ = f.toFun y := by unfold CLeftUnitor CIsLeftNeutral; simp;
     --
     -- simp; unfold CIsLeftNeutral;
      --rw[LinearIsometryCompApply, TensorLinearIsometriesOnSeparables]
      sorry

public theorem RightUnitorNaturality {R1 R2 : QuantumRegister} (f : R1 ⟶ R2) :
  (f ⊗ₕ (id_map CRegister)) ≫ (CRightUnitor R2).hom = (CRightUnitor R1).hom ≫ f :=
  by apply LinearIsometryExtOnTensor; intro x y; simp;
      --rw[LinearIsometryCompApply, TensorLinearIsometriesOnSeparables]
      sorry


public theorem TriangleEquality (R1 R2 : QuantumRegister) :
  ((QuantRegHomTensorAssoc R1 CRegister R2).hom ≫ (id_map R1) ⊗ₕ (CLeftUnitor R2).hom) =
    (CRightUnitor R1).hom ⊗ₕ (id_map R2) :=
  by apply LinearIsometryExtOnTensor; intro x y; simp; sorry

public theorem PentagonEquality (R1 R2 R3 R4 : QuantumRegister) :
  (((QuantRegHomTensorAssoc R1 R2 R3).hom ⊗ₕ (id_map R4)) ≫
      (QuantRegHomTensorAssoc R1 (R2 ⊗ᵣ R3) R4).hom ≫ (id_map R1) ⊗ₕ(QuantRegHomTensorAssoc R2 R3 R4).hom) =
    (QuantRegHomTensorAssoc (R1 ⊗ᵣ R2) R3 R4).hom ≫ (QuantRegHomTensorAssoc R1 R2 (R3 ⊗ᵣ R4)).hom :=
  by simp; sorry

@[default_instance]
public noncomputable instance QuantumRegisterMonCat : MonoidalCategory QuantumRegister where
  tensorObj := QuantumRegisterTensor
  whiskerLeft X Y1 Y2 f := QuantRegHomTensor LinearIsometry.id f
  whiskerRight f Y := QuantRegHomTensor f LinearIsometry.id
  tensorUnit := CRegister
  associator X Y Z := QuantRegHomTensorAssoc X Y Z
  leftUnitor X := CLeftUnitor X
  rightUnitor X := CRightUnitor X
  tensorHom_def f g := by rw[tensor_factorises]; rfl
  tensorHom_comp_tensorHom f g h i := tensor_factorises h i f g
  associator_naturality f g h := AssocNaturality f g h
  leftUnitor_naturality := LeftUnitorNaturality
  rightUnitor_naturality := RightUnitorNaturality
  triangle := TriangleEquality
  pentagon := PentagonEquality


public noncomputable def QuantumRegister.MulTensor (I : Type) (H : I → QuantumRegister)
  : QuantumRegister :=
    .mk
    (PiTensorProduct ℂ (fun i => (H i).space))
    (HilbertPiTensorFun I (fun i => (H i).space))

end SyntacticRegister
