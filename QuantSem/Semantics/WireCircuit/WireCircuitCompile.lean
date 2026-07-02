/-
Copyright (c) 2026 William Hasley. All rights reserved.
Released under GNU GPL3 license as described in the file LICENSE.
Authors: William Hasley
-/

module


public import QuantSem.Syntax.WireCircuits.WireCircuit
public import QuantSem.Syntax.WithBasis.WithBasis

namespace WireCircuitCompile

open WireCircuit
open BasisCircuit
open BasisGate
open BasisState
open BasisRegister


public abbrev RegisterSignature := Signature (TypeBasisRegister)
public abbrev GateInterpretation (GateType : Type) := GateType → TypeBasisGate
public abbrev ControlInterpretation (GateType : Type) := Σ ι : Type, ι → GateType

/-
    Control operations are compiled in a gate too big spanning every intermediate wire,
    Optimizations relative to control must be dealt with at the syntactic compilation layer
    (Here!)
-/





end WireCircuitCompile
