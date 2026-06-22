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
-- Better to add IdWire as a separate construction as it now becomes decidable to know
-- whether we are dealing with IdWire or a non-trivial gate (although the trivial gate)
-- is still possible


public inductive SimpleCircuitOverRegister : (TypeQuantumRegister → Type 1) where
  | IdWire {R : TypeQuantumRegister} : SimpleCircuitOverRegister R
  | Gate {R : TypeQuantumRegister} (g : QuantumGate R R) : SimpleCircuitOverRegister R
  | HorizontalComp {R : TypeQuantumRegister} (c1 c2 : SimpleCircuitOverRegister R) : SimpleCircuitOverRegister R
  | VerticalComp {R₁ R₂ : TypeQuantumRegister} (c1 : SimpleCircuitOverRegister R₁) (c2 :SimpleCircuitOverRegister R₂ ) : SimpleCircuitOverRegister (R₁ ⊗ᵣ R₂)

public abbrev TypeSimpleCircuit := Σ R : TypeQuantumRegister, SimpleCircuitOverRegister R

public abbrev TypeSimpleCircuit.register (c : TypeSimpleCircuit) := c.fst
public abbrev TypeSimpleCircuit.circuit (c : TypeSimpleCircuit) := c.snd

open SimpleCircuitOverRegister

public def SimpleCircuitDepth {R : TypeQuantumRegister} (c : SimpleCircuitOverRegister R) : ℕ :=
  match c with
  | IdWire => 1
  | Gate _ => 1
  | HorizontalComp c1 c2 => (SimpleCircuitDepth c1) + (SimpleCircuitDepth c2)
  | VerticalComp c1 c2 => max (SimpleCircuitDepth c1) (SimpleCircuitDepth c2)

public def SimpleCircuitDepth' (c : TypeSimpleCircuit) := SimpleCircuitDepth c.circuit

public def SimpleCircuitGateCount {R : TypeQuantumRegister} (c : SimpleCircuitOverRegister R) : ℕ :=
  match c with
  | IdWire => 0
  | Gate _ => 1
  | HorizontalComp c1 c2 => (SimpleCircuitGateCount c1) + (SimpleCircuitGateCount c2)
  | VerticalComp c1 c2 => (SimpleCircuitGateCount c1) + (SimpleCircuitGateCount c2)

public def SimpleCircuitGateCount' (c : TypeSimpleCircuit) := SimpleCircuitGateCount c.circuit

public def SimpleCircuitGetShape {R : TypeQuantumRegister} (c : SimpleCircuitOverRegister R) :
  List TypeQuantumRegister := match c with
    | IdWire => [R]
    | Gate _ => [R]
    | HorizontalComp c1 c2 => SimpleCircuitGetShape c1
    | VerticalComp c1 c2 => (SimpleCircuitGetShape c1) ++ (SimpleCircuitGetShape c2)

public def SimpleCircuitGetShape' (c : TypeSimpleCircuit) := SimpleCircuitGetShape c.circuit

@[expose]
public noncomputable def SimpleCircuitGateRepr {R : TypeQuantumRegister} (c : SimpleCircuitOverRegister R)
  : QuantumGate R R := match c with
  | IdWire => id_map R
  | Gate g => g
  | HorizontalComp c1 c2 => (SimpleCircuitGateRepr c1) ≫ (SimpleCircuitGateRepr c2)
  | VerticalComp c1 c2 => GateTensor (SimpleCircuitGateRepr c1) (SimpleCircuitGateRepr c2)


public noncomputable abbrev SimpleCircuitGateRepr' (c : TypeSimpleCircuit) : TypeQuantumGate :=
  ⟨c.register, ⟨ c.register, SimpleCircuitGateRepr c.circuit ⟩⟩


@[expose]
public noncomputable def SimpleCircuitCompute {R : TypeQuantumRegister} (c : SimpleCircuitOverRegister R)
  (s : QuantumStateSpace R) : QuantumStateSpace R :=
    GateStateEvolve (SimpleCircuitGateRepr' ⟨R, c⟩) s



/-
    Some Useful theorem translating circuit composition to gate constructions
-/

public theorem HorizontalIsComp {R : TypeQuantumRegister} (c1 c2 : SimpleCircuitOverRegister R)
  : SimpleCircuitGateRepr (HorizontalComp c1 c2) = SimpleCircuitGateRepr c1 ≫ SimpleCircuitGateRepr c2 :=
  by rfl

public theorem HorizontalComputation {R : TypeQuantumRegister} (c1 c2 : SimpleCircuitOverRegister R)
  : ∀ s : QuantumStateSpace R, SimpleCircuitCompute (HorizontalComp c1 c2) s = SimpleCircuitCompute c2 (SimpleCircuitCompute c1 s)
  := by intro s; rfl

public theorem VerticalIsTensor {R1 R2 : TypeQuantumRegister} (c1 : SimpleCircuitOverRegister R1)
  (c2 : SimpleCircuitOverRegister R2)
  : SimpleCircuitGateRepr (VerticalComp c1 c2) = GateTensor (SimpleCircuitGateRepr c1) (SimpleCircuitGateRepr c2)
  := by rfl

public theorem IdWireIsNeutral (R : TypeQuantumRegister) :
  ∀ s : QuantumStateSpace R, SimpleCircuitCompute (IdWire) s = s :=
  by apply GateId

public theorem GateRepr'IsGateRepr {R : TypeQuantumRegister} (c : SimpleCircuitOverRegister R) :
  (SimpleCircuitGateRepr' ⟨R, c⟩).gate = SimpleCircuitGateRepr c :=
  by rfl


/-
    Circuit Equivalence
-/

@[expose]
public def CircuitEquivalence {R : TypeQuantumRegister} (c1 c2 : SimpleCircuitOverRegister R)
  : Prop := ∀ s : QuantumStateSpace R, SimpleCircuitCompute c1 s = SimpleCircuitCompute c2 s

notation c1 "≅ₖ" c2 => CircuitEquivalence c1 c2

@[simp]
public theorem CircuitEquivalenceRefl {R : TypeQuantumRegister} (c : SimpleCircuitOverRegister R)
  : c ≅ₖ c := by intro s; rfl

@[simp]
public theorem CircuitEquivalenceSym {R : TypeQuantumRegister} (c1 c2 : SimpleCircuitOverRegister R)
  : (c1 ≅ₖ c2) → (c2 ≅ₖ c1) := by intro h s; rw[h]

public theorem CircuitEquivalenceTrans {R : TypeQuantumRegister} (c1 c2 c3 : SimpleCircuitOverRegister R)
  : (c1 ≅ₖ c2) → (c2 ≅ₖ c3) → (c1 ≅ₖ c3) := by intro h1 h2 s; rw[h1, h2]

/-
    Theorems on Equivalence
-/

@[simp]
public theorem CircuitCompositionsCommute {R1 R2 : TypeQuantumRegister}
(c11 c12 : SimpleCircuitOverRegister R1) (c21 c22 : SimpleCircuitOverRegister R2) :
  VerticalComp (HorizontalComp c11 c12) (HorizontalComp c21 c22) ≅ₖ
  HorizontalComp (VerticalComp c11 c21) (VerticalComp c12 c22) :=
  by unfold CircuitEquivalence; intro s; unfold SimpleCircuitCompute; unfold SimpleCircuitGateRepr'; rw[VerticalIsTensor, HorizontalIsComp, HorizontalIsComp, HorizontalIsComp, VerticalIsTensor, VerticalIsTensor]; rw[GateCompositionCommutation]

@[simp]
public theorem CircuitEquivalenceToGateCircuit {R : TypeQuantumRegister} (c : SimpleCircuitOverRegister R) :
  c ≅ₖ Gate (SimpleCircuitGateRepr c) :=
  by unfold CircuitEquivalence; intro s; rfl

public theorem GateEquivalenceIff  {R : TypeQuantumRegister} (g1 g2 : QuantumGate R R) :
  ((Gate g1) ≅ₖ (Gate g2)) ↔ (g1 = g2) := by apply Iff.intro; intro h; rw[GateExtIff]; apply h; intro h; rw[h]; apply CircuitEquivalenceRefl

public theorem CircuitEquivalenceGateIff  {R : TypeQuantumRegister} (c1 c2 : SimpleCircuitOverRegister R) :
  (c1 ≅ₖ c2) ↔ (SimpleCircuitGateRepr c1) = (SimpleCircuitGateRepr c2) :=
  by apply Iff.intro; intro h; rw [GateExtIff]; intro s; unfold CircuitEquivalence at h; apply h; intro h; unfold CircuitEquivalence; unfold SimpleCircuitCompute; unfold GateStateEvolve; rw[GateRepr'IsGateRepr, GateRepr'IsGateRepr]; intro s; rw[h];

@[simp]
public theorem IdWireIsIdLeft {R : TypeQuantumRegister} (c : SimpleCircuitOverRegister R)
  : HorizontalComp (IdWire) c ≅ₖ c :=
  by unfold CircuitEquivalence; intro s; rw[HorizontalComputation, IdWireIsNeutral]

@[simp]
public theorem IdWireIsIdRight {R : TypeQuantumRegister} (c : SimpleCircuitOverRegister R)
  : HorizontalComp c (IdWire) ≅ₖ c :=
  by unfold CircuitEquivalence; intro s; rw[HorizontalComputation, IdWireIsNeutral]

@[simp]
public theorem HorizontalRewriteLeft {R : TypeQuantumRegister} (c1 c1' c2 : SimpleCircuitOverRegister R)
  (hEquiv : c1 ≅ₖ c1') : HorizontalComp c1 c2 ≅ₖ HorizontalComp c1' c2 :=
  by unfold CircuitEquivalence; intro s; rw[HorizontalComputation, HorizontalComputation]; rw[hEquiv s]

@[simp]
public theorem HorizontalRewriteRight {R : TypeQuantumRegister} (c1 c2 c2' : SimpleCircuitOverRegister R)
  (hEquiv : c2 ≅ₖ c2') : HorizontalComp c1 c2 ≅ₖ HorizontalComp c1 c2' :=
  by unfold CircuitEquivalence; intro s; rw[HorizontalComputation, HorizontalComputation]; rw[hEquiv]

@[simp]
public theorem ParallelRewriteUp {R1 R2 : TypeQuantumRegister} (c1 c1' : SimpleCircuitOverRegister R1)
  (c2 : SimpleCircuitOverRegister R2) (hEquiv:  c1 ≅ₖ c1') :
  VerticalComp c1 c2 ≅ₖ VerticalComp c1' c2 :=
  by rw[CircuitEquivalenceGateIff, VerticalIsTensor, VerticalIsTensor]; rw[CircuitEquivalenceGateIff] at hEquiv; rw[hEquiv]

@[simp]
public theorem ParallelRewriteDown {R1 R2 : TypeQuantumRegister} (c1 : SimpleCircuitOverRegister R1)
  (c2 c2' : SimpleCircuitOverRegister R2) (hEquiv:  c2 ≅ₖ c2') :
  VerticalComp c1 c2 ≅ₖ VerticalComp c1 c2' :=
  by rw[CircuitEquivalenceGateIff, VerticalIsTensor, VerticalIsTensor]; rw[CircuitEquivalenceGateIff] at hEquiv; rw[hEquiv]


/-
    Other Circuit Theorems
-/


end SyntacticCircuit
