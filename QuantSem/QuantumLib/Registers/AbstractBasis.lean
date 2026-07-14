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
  space     : Type
  indexing  : Type
  struct    : HilbertSpaceWithBasis space indexing

@[default_instance]
public instance (R : BasisRegister) : HilbertSpaceWithBasis R.space R.indexing := R.struct

public abbrev BasisRegisterToQuantumRegister (R : BasisRegister)
  : SyntacticRegister.QuantumRegister := .mk R.space R.struct.toHilbertSpace
public abbrev BasisRegisterForget : BasisRegister → SyntacticRegister.QuantumRegister := BasisRegisterToQuantumRegister

@[default_instance, simp]
public instance : Coe BasisRegister SyntacticRegister.QuantumRegister where
  coe := BasisRegisterToQuantumRegister

@[default_instance]
public instance BasisRegisterCat : Category BasisRegister where
  Hom R1 R2   := SyntacticRegister.QuantumRegisterCat.Hom R1 R2
  id R        := SyntacticRegister.QuantumRegisterCat.id R
  comp f1 f2  := SyntacticRegister.QuantumRegisterCat.comp f1 f2

public def IsoPromote {R1 R2 : BasisRegister} :
  (BasisRegisterForget R1 ≅ BasisRegisterForget R2) ≃ (R1 ≅ R2) :=
  .mk
  (fun i => .mk (i.hom) (i.inv) (i.hom_inv_id) (i.inv_hom_id))
  (fun i => .mk (i.hom) (i.inv) (i.hom_inv_id) (i.inv_hom_id))
  (by intro x; simp)
  (by intro x; simp)

@[expose]
public noncomputable def BasisRegisterTensor (R1 R2 : BasisRegister) : BasisRegister :=
  .mk
    (TensorProduct ℂ R1.space R2.space)
    (R1.indexing × R2.indexing)
    (HilbertBasisTensorFun R1.space R2.space R1.indexing R2.indexing)

notation:101 A "⊗ᵣ" B => BasisRegisterTensor A B

@[simp]
public theorem TensorPromote (R1 R2 : BasisRegister) :
  BasisRegisterForget (BasisRegisterTensor R1 R2) =
  SyntacticRegister.QuantumRegisterTensor (BasisRegisterForget R1) (BasisRegisterForget R2) := by rfl

public noncomputable def TensorIso  (R1 R2 : BasisRegister) :
  BasisRegisterToQuantumRegister (R1 ⊗ᵣ R2) ≅ (BasisRegisterToQuantumRegister R1) ⊗ᵣ (BasisRegisterToQuantumRegister R2)
  := Iso.refl (BasisRegisterToQuantumRegister (R1 ⊗ᵣ R2))

public noncomputable abbrev CBasisRegister : BasisRegister := .mk ℂ (Fin 1) CHilbertBasis

/-
    From this interface, one can "pull back" the Monoidal Category structure in this setting
    (Formally, we have a Forgetful Functor F : BasisCat ⟶ RegisterCat that respects tensoring and Hom)
-/


@[default_instance]
public noncomputable instance BasisRegisterMonCat : MonoidalCategory BasisRegister where
  tensorObj := BasisRegisterTensor
  whiskerLeft X Y1 Y2 f := SyntacticRegister.QuantumRegisterMonCat.whiskerLeft X f
  whiskerRight := @fun X1 X2 f Y => SyntacticRegister.QuantumRegisterMonCat.whiskerRight f Y
  whiskerLeft_id X Y := SyntacticRegister.QuantumRegisterMonCat.whiskerLeft_id X Y
  id_whiskerRight X Y := SyntacticRegister.QuantumRegisterMonCat.id_whiskerRight X Y
  tensorUnit := CBasisRegister
  associator X Y Z := IsoPromote (SyntacticRegister.QuantumRegisterMonCat.associator X Y Z)
  leftUnitor X :=  IsoPromote (SyntacticRegister.QuantumRegisterMonCat.leftUnitor X)
  rightUnitor X := IsoPromote (SyntacticRegister.QuantumRegisterMonCat.rightUnitor X)
  id_tensorHom_id X Y := SyntacticRegister.QuantumRegisterMonCat.id_tensorHom_id X Y
  tensorHom_def f g := SyntacticRegister.QuantumRegisterMonCat.tensorHom_def f g
  tensorHom_comp_tensorHom f g h i := SyntacticRegister.QuantumRegisterMonCat.tensorHom_comp_tensorHom f g h i
  -- why does "by apply xx" work but not directly xx  ;(((
  associator_naturality f g h := by apply (SyntacticRegister.QuantumRegisterMonCat.associator_naturality f g h)
  leftUnitor_naturality f := by apply (SyntacticRegister.QuantumRegisterMonCat.leftUnitor_naturality f)
  rightUnitor_naturality f := by apply (SyntacticRegister.QuantumRegisterMonCat.rightUnitor_naturality f)
  triangle X Y := by apply SyntacticRegister.QuantumRegisterMonCat.triangle X Y
  pentagon W X Y Z := by apply SyntacticRegister.QuantumRegisterMonCat.pentagon W X Y Z

@[expose]
public noncomputable def BasisRegister.MulTensor (I : Type) [Finite I] (H : I → BasisRegister) : BasisRegister :=
    .mk
    (PiTensorProduct ℂ (fun i => (H i).space))
    (Π i : I, (H i).indexing)
    (PiHilbertBasisTensorFun I (fun i => (H i).space) (fun i => (H i).indexing))

notation "⨂ᵣ" l => BasisRegister.MulTensor (Fin (List.length l)) (fun i => (List.get l i))

end AbstractBasisRegister
