/-
Copyright (c) 2026 William Hasley. All rights reserved.
Released under GNU GPL3 license as described in the file LICENSE.
Authors: William Hasley
-/

module

public import Mathlib.Algebra.Star.Unitary

namespace WireCircuit

public abbrev RegisterSignature (A : Type*) (n : ℕ) := Vector A n


/-
    A circuit is a sequence of layers
-/

/-
    Operations on circuit (aka layer content):
    - One gate on contiguous sublist
    - Control operation with a gate position and a list of controls
    - Wire swap
-/

public inductive LayerOp {n : ℕ} (GateType : Type) : Type where
  | Gate (i j : (Fin n)) (g : GateType) : LayerOp GateType
  | Control (controlList : List (Fin n)) (i j : (Fin n)) : LayerOp GateType
  | WireSwap (i j : (Fin n)) : LayerOp GateType


public abbrev RegisterWireDescription (n : ℕ) (GateType : Type) := List (@LayerOp n GateType)

public def WireCircuitCoherent {n : ℕ} {GateType : Type} (c : RegisterWireDescription n GateType) : Bool :=
  match c with
  |[] => true
  | h :: t => (match h with
      | LayerOp.Gate i j _ => (j >= i) && WireCircuitCoherent t
      | LayerOp.Control clist i j => (j >= i) && (List.Forall (fun k => k < i || k > j) clist) && (WireCircuitCoherent t)
      | LayerOp.WireSwap i j => i != j && WireCircuitCoherent t
      )



public def WireCircuitInit (n : ℕ) (GateType : Type) : RegisterWireDescription n GateType := []
public def WireCircuitAddLayer {n : ℕ} {GateType : Type} (c : RegisterWireDescription n GateType) (l : @LayerOp n GateType)
  : RegisterWireDescription n GateType := c ++ [l]
public def WireCircuitComp {n : ℕ} {GateType : Type} (c1 c2 : RegisterWireDescription n GateType)
  : RegisterWireDescription n GateType := c1 ++ c2


notation a " · " b => WireCircuitComp a b
notation a " · " l => WireCircuitAddLayer a l

end WireCircuit
