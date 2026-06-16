/-
Copyright (c) 2026 William Hasley. All rights reserved.
Released under GNU GPL3 license as described in the file LICENSE.
Authors: William Hasley
-/


module


public import QuantSem.Syntax.Category.Gate
public import QuantSem.Syntax.Category.State
public import QuantSem.Syntax.Category.Register

open SyntacticRegister
open SyntacticState
open SyntacticGate
open CategoryTheory

namespace SyntacticCircuit

/- Simple circuits are always "representable as unitary matrices", no pesky measurement
    or other quantum operations I'm not aware of -/


-- Should the circuit algebra be fixed? Eckman hilton can come in handy ⟶ Only in 1D

public inductive SimpleCircuitOverRegister : (TypeQuantumRegister → Type 1) where
  | Gate {R : TypeQuantumRegister} (g : QuantumGate R R) : SimpleCircuitOverRegister R
  | HorizontalComp {R : TypeQuantumRegister} (c1 c2 : SimpleCircuitOverRegister R) : SimpleCircuitOverRegister R
  | VerticalComp {R₁ R₂ : TypeQuantumRegister} (c1 : SimpleCircuitOverRegister R₁) (c2 :SimpleCircuitOverRegister R₂ ) : SimpleCircuitOverRegister (R₁ ⊗ᵣ R₂)

public abbrev TypeSimpleCircuit := Σ R : TypeQuantumRegister, SimpleCircuitOverRegister R

public abbrev TypeSimpleCircuit.register (c : TypeSimpleCircuit) := c.fst
public abbrev TypeSimpleCircuit.circuit (c : TypeSimpleCircuit) := c.snd

open SimpleCircuitOverRegister

public def SimpleCircuitDepth {R : TypeQuantumRegister} (c : SimpleCircuitOverRegister R) : ℕ :=
  match c with
  | Gate _ => 1
  | HorizontalComp c1 c2 => (SimpleCircuitDepth c1) + (SimpleCircuitDepth c2)
  | VerticalComp c1 c2 => max (SimpleCircuitDepth c1) (SimpleCircuitDepth c2)

public def SimpleCircuitDepth' (c : TypeSimpleCircuit) := SimpleCircuitDepth c.circuit

public def SimpleCircuitGateCount {R : TypeQuantumRegister} (c : SimpleCircuitOverRegister R) : ℕ :=
  match c with
  | Gate _ => 1
  | HorizontalComp c1 c2 => (SimpleCircuitGateCount c1) + (SimpleCircuitGateCount c2)
  | VerticalComp c1 c2 => (SimpleCircuitGateCount c1) + (SimpleCircuitGateCount c2)

public def SimpleCircuitGateCount' (c : TypeSimpleCircuit) := SimpleCircuitGateCount c.circuit

public def SimpleCircuitGetShape {R : TypeQuantumRegister} (c : SimpleCircuitOverRegister R) :
  List TypeQuantumRegister := match c with
    | SimpleCircuitOverRegister.Gate _ => [R]
    | SimpleCircuitOverRegister.HorizontalComp c1 c2 => SimpleCircuitGetShape c1
    | SimpleCircuitOverRegister.VerticalComp c1 c2 => (SimpleCircuitGetShape c1) ++ (SimpleCircuitGetShape c2)

public def SimpleCircuitGetShape' (c : TypeSimpleCircuit) := SimpleCircuitGetShape c.circuit


public noncomputable def SimpleCircuitGateRepr {R : TypeQuantumRegister} (c : SimpleCircuitOverRegister R)
  : QuantumGate R R := match c with
  | Gate g => g
  | HorizontalComp c1 c2 => (SimpleCircuitGateRepr c1) ≫ (SimpleCircuitGateRepr c2)
  | VerticalComp c1 c2 => GateTensor (SimpleCircuitGateRepr c1) (SimpleCircuitGateRepr c2)


public noncomputable def SimpleCircuitGateRepr' (c : TypeSimpleCircuit) : TypeQuantumGate :=
  ⟨c.register, ⟨ c.register, SimpleCircuitGateRepr c.circuit ⟩⟩


public noncomputable def SimpleCircuitCompute {R : TypeQuantumRegister} (c : SimpleCircuitOverRegister R)
  (s : QuantumStateSpace R) : QuantumStateSpace R :=
    GateStateEvolve (SimpleCircuitGateRepr' ⟨R, c⟩) s


public theorem HorizontalIsComp {R : TypeQuantumRegister} (c1 c2 : SimpleCircuitOverRegister R)
  : SimpleCircuitGateRepr (HorizontalComp c1 c2) = SimpleCircuitGateRepr c1 ≫ SimpleCircuitGateRepr c2 :=
  by rfl

public theorem VerticalIsTensor {R1 R2 : TypeQuantumRegister} (c1 : SimpleCircuitOverRegister R1)
  (c2 : SimpleCircuitOverRegister R2)
  : SimpleCircuitGateRepr (VerticalComp c1 c2) = GateTensor (SimpleCircuitGateRepr c1) (SimpleCircuitGateRepr c2)
  := by rfl

/-
    Circuit Equivalence
-/

public def CircuitEquivalence {R : TypeQuantumRegister} (c1 c2 : SimpleCircuitOverRegister R)
  : Prop := ∀ s : QuantumStateSpace R, SimpleCircuitCompute c1 s = SimpleCircuitCompute c2 s

notation c1 "≅ₖ" c2 => CircuitEquivalence c1 c2

public theorem CircuitCompositionsCommute {R1 R2 : TypeQuantumRegister}
(c11 c12 : SimpleCircuitOverRegister R1) (c21 c22 : SimpleCircuitOverRegister R2) :
  VerticalComp (HorizontalComp c11 c12) (HorizontalComp c21 c22) ≅ₖ
  HorizontalComp (VerticalComp c11 c21) (VerticalComp c12 c22) :=
  by unfold CircuitEquivalence; intro s; unfold SimpleCircuitCompute; unfold SimpleCircuitGateRepr'; rw[VerticalIsTensor, HorizontalIsComp, HorizontalIsComp, HorizontalIsComp, VerticalIsTensor, VerticalIsTensor]; rw[GateCompositionCommutation]


end SyntacticCircuit
