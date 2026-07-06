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


public noncomputable def MulTensorPar (famReg : List TypeBasisRegister) : TypeBasisRegister :=
  match famReg with
  |[] => MonCatBasisReg'.tensorUnit
  |[h] => h
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
      (BasisRegHomTensor
        (CatBasisReg''.id h) (MulTensorThetaFam (h' :: t) l2))


end PiBasisRegister
