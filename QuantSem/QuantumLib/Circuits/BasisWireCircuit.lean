/-
Copyright (c) 2026 William Hasley. All rights reserved.
Released under GNU GPL3 license as described in the file LICENSE.
Authors: William Hasley
-/

module

public import QuantSem.Syntax.WithBasis.BasisRegister
public import QuantSem.Syntax.WithBasis.PiBasisRegister
public import QuantSem.Syntax.WithBasis.BasisState
public import QuantSem.Syntax.WithBasis.BasisGate


namespace WireCircuit

open PiBasisRegister
open BasisRegister
open BasisGate


public abbrev BasisRegisterSignature {n : ℕ} := Vector (TypeBasisRegister) n

-- Have to write it this way for termination --'
def ListExtractIndicesWithBeginning {α : Type*} (l : List α) (indices : List ℕ) (i : ℕ) :
  List α :=
  match l with
    |[] => []
    | hl :: tl => match indices with
      | [] => []
      | _ => if i ∈ indices then
      (hl :: (ListExtractIndicesWithBeginning tl (indices.erase i) (i + 1))) else
      ((ListExtractIndicesWithBeginning tl indices (i + 1)))

public def ListExtractIndices {α : Type*} (l : List α) (indices : List ℕ) :
  List α := ListExtractIndicesWithBeginning l indices 0


public inductive LayerOp {n : ℕ} (s : @BasisRegisterSignature n) : Type where
  | Gate (i j : ℕ) (g : BasisGateType (⨂ᵣ s.toList.extract i j) (⨂ᵣ s.toList.extract i j)) :
    LayerOp s
  | Control (controlList : List ℕ) (i j : ℕ)
    (gFam : (⨂ᵣ (@ListExtractIndices TypeBasisRegister s.toList controlList)).indexing →
                BasisGateType (⨂ᵣ s.toList.extract i j) (⨂ᵣ s.toList.extract i j)) :
    LayerOp s
  | WireSwap (i j : ℕ) : LayerOp s

/-
    A representation of basis indices for a BasisRegisterSignature
-/



/-
    Evolve a state thanks to it's effect on the separated basis
-/


-- public def LayerEvolveState {n : ℕ} {s : @BasisRegisterSignature n}
--   (l : @LayerOp n s) : BasisGateType (⨂ᵣ s.toList) (⨂ᵣ s.toList) :=
--   GateFromBasis (fun b => match l with
--     | LayerOp.Gate i j g =>
--       if(i = 0) then
--         (if (j = s.toList.length) then _ else (MulTensorHomPar _ _ _ (CatBasisReg''.id _))) else (_)
--
--     | LayerOp.Control clist i j gFam => _
--     | LayerOp.WireSwap i j =>_
--     )
--     _

/-
    A circuit is a sequence of layers
-/

public abbrev WireCircuitType (n : ℕ) (s : @BasisRegisterSignature n) := List (@LayerOp n s)

public def WireCircuitCoherent {n : ℕ} {s : @BasisRegisterSignature n}
  (c : WireCircuitType n s) : Bool :=
  match c with
  |[] => true
  | h :: t => (match h with
      | LayerOp.Gate i j _ => (j >= i) && WireCircuitCoherent t
      | LayerOp.Control clist i j _ => (j >= i) && (List.Forall (fun k => k < i || k > j) clist) && (WireCircuitCoherent t)
      | LayerOp.WireSwap i j => i != j && WireCircuitCoherent t
      )



public def WireCircuitInit (n : ℕ) (s : @BasisRegisterSignature n) : WireCircuitType n s := []
public def WireCircuitAddLayer {n : ℕ} {s : @BasisRegisterSignature n} (c : WireCircuitType n s)
  (l : @LayerOp n s) : WireCircuitType n s := c ++ [l]
public def WireCircuitComp {n : ℕ} {s : @BasisRegisterSignature n} (c1 c2 : WireCircuitType n s)
  : WireCircuitType n s := c1 ++ c2

notation a " · " b => WireCircuitComp a b
notation a " · " l => WireCircuitAddLayer a l
