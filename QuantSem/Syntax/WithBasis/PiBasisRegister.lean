/-
Copyright (c) 2026 William Hasley. All rights reserved.
Released under GNU GPL3 license as described in the file LICENSE.
Authors: William Hasley
-/

module


public import QuantSem.Syntax.WithBasis.FinSuppBasisTypes
public import QuantSem.Syntax.WithBasis.BasisRegister

-- A construction akin to strictification of monoidal categories
-- !!! The natural constructions for lists imposes a right-parenthesing convention !!!
-- !!! Have to reverse left and right operations !!!

-- Source : STRICTIFICATION AND NON-STRICTIFICATION OF MONOIDAL CATEGORIES, JORGE BECERRA https://arxiv.org/pdf/2303.16740v2

namespace PiBasisRegister

open SyntacticRegister
open BasisTypes
open Monoid
open CategoryTheory
open BasisRegister


@[expose]
public noncomputable def MulTensorPar (famReg : List TypeBasisRegister) : TypeBasisRegister :=
  match famReg with
  | [] => MonCatBasisReg'.tensorUnit
  | [h] => h
  | h :: t => h ⊗ᵣ (MulTensorPar t)

@[simp]
public theorem MulTensorParEmpty : MulTensorPar [] = MonCatBasisReg'.tensorUnit := by rfl

@[simp]
public theorem MulTensorParAddEmpty (l : List TypeBasisRegister) :
 MulTensorPar (l ++ []) = MulTensorPar l := by rw[List.append_nil]

@[simp]
public theorem MulTensorParEmptyAdd (l : List TypeBasisRegister) :
 MulTensorPar ([] ++ l) = MulTensorPar l := by rw[List.nil_append]

public def MulTensorInclusion (R : TypeBasisRegister) : List TypeBasisRegister := [R]

public noncomputable def MulTensorThetaFam (l1 l2 : List TypeBasisRegister) :
  ((MulTensorPar l1) ⊗ᵣ (MulTensorPar l2)) ⟶ (MulTensorPar (l1 ++ l2)) :=
  match l1 with
    | [] => (MonCatBasisReg'.leftUnitor (MulTensorPar l2)).hom
    | [h] => match l2 with
        |[] => (MonCatBasisReg'.rightUnitor (MulTensorPar [h])).hom
        |h' :: t' => CatBasisReg''.id (h ⊗ᵣ (MulTensorPar (h' :: t')))
    | h :: (h' :: t) =>
      (MonCatBasisReg'.associator h (MulTensorPar (h' :: t)) (MulTensorPar l2)).hom ≫
      (BasisRegHomTensor (CatBasisReg''.id h) (MulTensorThetaFam (h' :: t) l2))

notation "⨂ᵣ" l => MulTensorPar l

public noncomputable def MulTensorHomPar {R1 R2 : TypeBasisRegister} (l1 l2 : List TypeBasisRegister)
  (f : R1 ⟶ (MulTensorPar l1)) (g : R2 ⟶ (MulTensorPar l2)) : (R1 ⊗ᵣ R2) ⟶ (MulTensorPar (l1 ++ l2))
  := (BasisRegHomTensor f g) ≫ (MulTensorThetaFam l1 l2)

public noncomputable def MulTensorThetaFamInv (l1 l2 : List TypeBasisRegister) :
  (MulTensorPar (l1 ++ l2)) ⟶ ((MulTensorPar l1) ⊗ᵣ (MulTensorPar l2)) :=
  match l1 with
    | [] => (MonCatBasisReg'.leftUnitor (MulTensorPar l2)).inv
    | [h] => match l2 with
        |[] => (MonCatBasisReg'.rightUnitor (MulTensorPar [h])).inv
        |h' :: t' => CatBasisReg''.id (h ⊗ᵣ (MulTensorPar (h' :: t')))
    | h :: (h' :: t) =>
      (BasisRegHomTensor (CatBasisReg''.id h) (MulTensorThetaFamInv (h' :: t) l2)) ≫
        (MonCatBasisReg'.associator h (MulTensorPar (h' :: t)) (MulTensorPar l2)).inv

public theorem MulTensorThetaLeftInv (l1 l2 : List TypeBasisRegister) :
  (MulTensorThetaFam l1 l2) ≫ (MulTensorThetaFamInv l1 l2) = CatBasisReg''.id ((MulTensorPar l1) ⊗ᵣ (MulTensorPar l2)) :=
  match l1 with
  | [] => by unfold MulTensorThetaFam MulTensorThetaFamInv; simp;
  | [h] => match l2 with
    | [] => by unfold MulTensorThetaFam MulTensorThetaFamInv; simp;
    | h' :: t' => by unfold MulTensorThetaFam MulTensorThetaFamInv; simp; rfl
  | h :: (h' :: t) => by unfold MulTensorThetaFam MulTensorThetaFamInv; sorry -- rw[Category.assoc, ];

public theorem MulTensorThetaRightInv (l1 l2 : List TypeBasisRegister) :
  (MulTensorThetaFamInv l1 l2) ≫ (MulTensorThetaFam l1 l2) = CatBasisReg''.id (MulTensorPar (l1 ++ l2)) :=
  match l1 with
  | [] => by unfold MulTensorThetaFam MulTensorThetaFamInv; simp;
  | [h] => match l2 with
    | [] => by unfold MulTensorThetaFam MulTensorThetaFamInv; simp;
    | h' :: t' => by unfold MulTensorThetaFam MulTensorThetaFamInv; simp; rfl
  | h :: (h' :: t) => by unfold MulTensorThetaFam MulTensorThetaFamInv; sorry

public noncomputable def MulTensorIso (l1 l2 : List TypeBasisRegister) :
  ((MulTensorPar l1) ⊗ᵣ (MulTensorPar l2)) ≅ (MulTensorPar (l1 ++ l2)) :=
    .mk (MulTensorThetaFam l1 l2) (MulTensorThetaFamInv l1 l2) (MulTensorThetaLeftInv l1 l2) (MulTensorThetaRightInv l1 l2)

end PiBasisRegister
