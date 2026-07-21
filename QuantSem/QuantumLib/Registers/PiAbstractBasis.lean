/-
Copyright (c) 2026 William Hasley. All rights reserved.
Released under GNU GPL3 license as described in the file LICENSE.
Authors: William Hasley
-/


/-
    This should be rewritten along with adding files to better interface with
    already implemented "Pi" constructions (have to redo the hilbert space hierarchy with it)
-/


module

public import QuantSem.LeanTools.Attributes
public import QuantSem.QuantumLib.HilbertSpaces.AbstractBasis
public import QuantSem.QuantumLib.Registers.AbstractBasis
public import QuantSem.QuantumLib.States.AbstractBasis
-- A construction akin to strictification of monoidal categories
-- !!! The natural constructions for lists imposes a right-parenthesing convention !!!
-- !!! Have to reverse left and right operations !!!

-- Source : STRICTIFICATION AND NON-STRICTIFICATION OF MONOIDAL CATEGORIES, JORGE BECERRA https://arxiv.org/pdf/2303.16740v2

namespace PiBasisRegister

open SyntacticRegister
open BasisTypes
open Monoid
open CategoryTheory
open AbstractBasisRegister
open BasisState

@[expose]
public noncomputable def MulTensorPar (famReg : List BasisRegister) : BasisRegister :=
  match famReg with
  | [] => BasisRegisterMonCat.tensorUnit
  | _ => ⨂ᵣ famReg

-- PiTensorProduct.subsingletonEquiv

public noncomputable instance : Coe (List BasisRegister) BasisRegister where
  coe := MulTensorPar

@[simp]
public theorem MulTensorParEmpty : MulTensorPar [] = BasisRegisterMonCat.tensorUnit := by rfl

@[simp]
public theorem MulTensorParAddEmpty (l : List BasisRegister) :
MulTensorPar (l ++ []) = MulTensorPar l := by rw[List.append_nil]

@[simp]
public theorem MulTensorParEmptyAdd (l : List BasisRegister) :
 MulTensorPar ([] ++ l) = MulTensorPar l := by rw[List.nil_append]

public def MulTensorInclusion (R : BasisRegister) : List BasisRegister := [R]


/-

public noncomputable def MulTensorThetaFam (l1 l2 : List BasisRegister) :
  (AbstractBasisRegister.BasisRegisterTensor (MulTensorPar l1) (MulTensorPar l2)) ⟶ (MulTensorPar (l1 ++ l2)) :=
  match l1 with
    | [] => (BasisRegisterMonCat.leftUnitor (MulTensorPar l2)).hom
    | [h] => match l2 with
        |[] => (BasisRegisterMonCat.rightUnitor (MulTensorPar [h])).hom
        |h' :: t' => CatBasisReg''.id (h ⊗ᵣ (MulTensorPar (h' :: t')))
    | h :: (h' :: t) =>
      (BasisRegisterMonCat.associator h (MulTensorPar (h' :: t)) (MulTensorPar l2)).hom ≫
      (BasisRegHomTensor (CatBasisReg''.id h) (MulTensorThetaFam (h' :: t) l2))

notation "⨂ᵣ" l => MulTensorPar l

public noncomputable def MulTensorHomPar {R1 R2 : BasisRegister} (l1 l2 : List BasisRegister)
  (f : R1 ⟶ (MulTensorPar l1)) (g : R2 ⟶ (MulTensorPar l2)) : (R1 ⊗ᵣ R2) ⟶ (MulTensorPar (l1 ++ l2))
  := (BasisRegHomTensor f g) ≫ (MulTensorThetaFam l1 l2)

public noncomputable def MulTensorThetaFamInv (l1 l2 : List BasisRegister) :
  (MulTensorPar (l1 ++ l2)) ⟶ ((MulTensorPar l1) ⊗ᵣ (MulTensorPar l2)) :=
  match l1 with
    | [] => (BasisRegisterMonCat.leftUnitor (MulTensorPar l2)).inv
    | [h] => match l2 with
        |[] => (BasisRegisterMonCat.rightUnitor (MulTensorPar [h])).inv
        |h' :: t' => CatBasisReg''.id (h ⊗ᵣ (MulTensorPar (h' :: t')))
    | h :: (h' :: t) =>
      (BasisRegHomTensor (CatBasisReg''.id h) (MulTensorThetaFamInv (h' :: t) l2)) ≫
        (BasisRegisterMonCat.associator h (MulTensorPar (h' :: t)) (MulTensorPar l2)).inv

public theorem MulTensorThetaLeftInv (l1 l2 : List BasisRegister) :
  (MulTensorThetaFam l1 l2) ≫ (MulTensorThetaFamInv l1 l2) = CatBasisReg''.id ((MulTensorPar l1) ⊗ᵣ (MulTensorPar l2)) :=
  match l1 with
  | [] => by unfold MulTensorThetaFam MulTensorThetaFamInv; simp;
  | [h] => match l2 with
    | [] => by unfold MulTensorThetaFam MulTensorThetaFamInv; simp;
    | h' :: t' => by unfold MulTensorThetaFam MulTensorThetaFamInv; simp; rfl
  | h :: (h' :: t) => by unfold MulTensorThetaFam MulTensorThetaFamInv; sorry -- rw[Category.assoc, ];

public theorem MulTensorThetaRightInv (l1 l2 : List BasisRegister) :
  (MulTensorThetaFamInv l1 l2) ≫ (MulTensorThetaFam l1 l2) = CatBasisReg''.id (MulTensorPar (l1 ++ l2)) :=
  match l1 with
  | [] => by unfold MulTensorThetaFam MulTensorThetaFamInv; simp;
  | [h] => match l2 with
    | [] => by unfold MulTensorThetaFam MulTensorThetaFamInv; simp;
    | h' :: t' => by unfold MulTensorThetaFam MulTensorThetaFamInv; simp; rfl
  | h :: (h' :: t) => by unfold MulTensorThetaFam MulTensorThetaFamInv; sorry

public noncomputable def MulTensorIso (l1 l2 : List BasisRegister) :
  (AbstractBasisRegister.BasisRegisterTensor (MulTensorPar l1) (MulTensorPar l2)) ≅ (MulTensorPar (l1 ++ l2)) :=
    .mk
    (MulTensorThetaFam l1 l2)
    (MulTensorThetaFamInv l1 l2)
    (MulTensorThetaLeftInv l1 l2)
    (MulTensorThetaRightInv l1 l2)
-/

public noncomputable def MulTensorIso (l1 l2 : List BasisRegister) :
  (AbstractBasisRegister.BasisRegisterTensor (⨂ᵣ l1) (⨂ᵣ l2)) ≅ (⨂ᵣ (l1 ++ l2)) :=
  by sorry


-- PiTensorProduct.singleAlgHom

end PiBasisRegister
