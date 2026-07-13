/-
Copyright (c) 2026 William Hasley. All rights reserved.
Released under GNU GPL3 license as described in the file LICENSE.
Authors: William Hasley
-/


module


public import QuantSem.QuantumLib.HilbertSpaces.AbstractBasis
public import QuantSem.QuantumLib.Registers.Basic
public import Mathlib.CategoryTheory.Monoidal.Category

namespace AbstractBasisRegister

open QuantumTypes
open BasisTypes
open CategoryTheory


public structure BasisRegister : Type 1 where
  space : Type
  indexing : Type
  struct : HilbertSpaceWithBasis space indexing

@[default_instance]
public instance (R : BasisRegister) : HilbertSpaceWithBasis R.space R.indexing := R.struct

public abbrev BasisRegisterToQuantumRegister (R : BasisRegister)
  : SyntacticRegister.QuantumRegister := .mk R.space R.struct.toHilbertSpace

@[default_instance]
public instance : Coe BasisRegister SyntacticRegister.QuantumRegister where
  coe := BasisRegisterToQuantumRegister

@[default_instance]
public instance BasisRegisterCat : Category BasisRegister where
  Hom R1 R2   := SyntacticRegister.QuantumRegisterCat.Hom R1 R2
  id R        := SyntacticRegister.QuantumRegisterCat.id R
  comp f1 f2  := SyntacticRegister.QuantumRegisterCat.comp f1 f2

@[simp]
public theorem HomPromoteEq (R1 R2 : BasisRegister) :
  BasisRegisterCat.Hom R1 R2 = SyntacticRegister.QuantumRegisterCat.Hom (↑R1) (↑R2) := by rfl

public def HomPromote {R1 R2 : BasisRegister} :
  SyntacticRegister.QuantumRegisterCat.Hom (↑R1) (↑R2) ≃ BasisRegisterCat.Hom R1 R2 := Equiv.cast (HomPromoteEq R1 R2).symm

@[simp]
public theorem HomEqPromote {R1 R2 : BasisRegister} (f g : BasisRegisterToQuantumRegister R1 ⟶ BasisRegisterToQuantumRegister R2)
  (eq : f = g) : (HomPromote f) = (HomPromote g) := by rw[eq]

@[simp]
public theorem HomCompPromote {R1 R2 R3 : BasisRegister} (f : BasisRegisterToQuantumRegister R1 ⟶ BasisRegisterToQuantumRegister R2)
  (g : BasisRegisterToQuantumRegister R2 ⟶ BasisRegisterToQuantumRegister R3) :
  (HomPromote (f ≫ g)) = (HomPromote f) ≫ (HomPromote g) := by rfl


public def IsoPromote {R1 R2 : BasisRegister} :
  (↑R1 ≅ ↑R2) ≃ (R1 ≅ R2) := .mk id id (by intro x; simp) (by intro x; simp)

@[simp]
public theorem IsoPromoteEq {R1 R2 : BasisRegister} :
   (R1 ≅ R2) = (↑R1 ≅ ↑R2) := by rfl

@[expose]
public noncomputable def BasisRegisterTensor (R1 R2 : BasisRegister) : BasisRegister :=
  .mk
    (TensorProduct ℂ R1.space R2.space)
    (R1.indexing × R2.indexing)
    (HilbertBasisTensorFun R1.space R2.space R1.indexing R2.indexing)

notation A "⊗ᵣ" B => BasisRegisterTensor A B

@[simp]
public theorem TensorPromote (R1 R2 : BasisRegister) :
  SyntacticRegister.QuantumRegisterTensor ↑R1 ↑R2 = ↑(BasisRegisterTensor R1 R2) := by rfl

public noncomputable def TensorIso  (R1 R2 : BasisRegister) :
  BasisRegisterToQuantumRegister (R1 ⊗ᵣ R2) ≅ (BasisRegisterToQuantumRegister R1) ⊗ᵣ (BasisRegisterToQuantumRegister R2)
  := .mk
  (SyntacticRegister.QuantumRegisterCat.id (SyntacticRegister.QuantumRegisterTensor ↑R1 ↑R2))
  (SyntacticRegister.QuantumRegisterCat.id (SyntacticRegister.QuantumRegisterTensor ↑R1 ↑R2))
  (by simp; rfl)
  (by simp; rfl)


public noncomputable abbrev CBasisRegister : BasisRegister := .mk ℂ (Fin 1) CHilbertBasis


/-
    From this interface, one can "pull back" the Monoidal Category structure in this setting
    (Formally, we have a Functor F : BasisCat ⟶ RegisterCat that respects tensoring and Hom)
-/


@[default_instance]
public noncomputable instance BasisRegisterMonCat : MonoidalCategory BasisRegister
  :=  sorry
  -- where
  -- tensorObj := BasisRegisterTensor
  -- whiskerLeft X Y1 Y2 f := SyntacticRegister.QuantumRegisterMonCat.whiskerLeft ↑X f
  -- whiskerRight := @fun X1 X2 f Y => SyntacticRegister.QuantumRegisterMonCat.whiskerRight f ↑Y
  -- whiskerLeft_id X Y := SyntacticRegister.QuantumRegisterMonCat.whiskerLeft_id X Y
  -- id_whiskerRight X Y := SyntacticRegister.QuantumRegisterMonCat.id_whiskerRight X Y
  -- tensorUnit := CBasisRegister
  -- -- get this to work, and we're good
  -- associator X Y Z := SyntacticRegister.QuantumRegisterMonCat.associator X Y Z
  -- leftUnitor X :=  SyntacticRegister.QuantumRegisterMonCat.leftUnitor X
  -- rightUnitor X := SyntacticRegister.QuantumRegisterMonCat.rightUnitor X
  -- id_tensorHom_id X Y := SyntacticRegister.QuantumRegisterMonCat.id_tensorHom_id ↑X ↑Y
  -- tensorHom_def f g := SyntacticRegister.QuantumRegisterMonCat.tensorHom_def f g
  -- tensorHom_comp_tensorHom f g h i := SyntacticRegister.QuantumRegisterMonCat.tensorHom_comp_tensorHom f g h i
  -- associator_naturality f g h := SyntacticRegister.QuantumRegisterMonCat.associator_naturality f g h
  -- leftUnitor_naturality := SyntacticRegister.QuantumRegisterMonCat.leftUnitor_naturality
  -- rightUnitor_naturality := SyntacticRegister.QuantumRegisterMonCat.rightUnitor_naturality
  -- triangle := SyntacticRegister.QuantumRegisterMonCat.triangle
  -- pentagon := SyntacticRegister.QuantumRegisterMonCat.pentagon


public noncomputable def QuantumRegister.MulTensor (I : Type) [Finite I] (H : I → BasisRegister) : BasisRegister :=
    .mk
    (PiTensorProduct ℂ (fun i => (H i).space))
    (Π i : I, (H i).indexing)
    (PiHilbertBasisTensorFun I (fun i => (H i).space) (fun i => (H i).indexing))

end AbstractBasisRegister
