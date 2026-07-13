/-
Copyright (c) 2026 William Hasley. All rights reserved.
Released under GNU GPL3 license as described in the file LICENSE.
Authors: William Hasley
-/


module


public import QuantSem.QuantumLib.Gates.Basic
public import QuantSem.QuantumLib.States.Basic
public import QuantSem.QuantumLib.Registers.Basic

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


public inductive SimpleCircuitOverRegister : (QuantumRegister → Type 1) where
  | IdWire {R : QuantumRegister} : SimpleCircuitOverRegister R
  | RegisterSwap {R1 R2 : QuantumRegister} (iso : R1 ≅ R2) (c : SimpleCircuitOverRegister R1) : SimpleCircuitOverRegister R2
  | Gate {R : QuantumRegister} (g : QuantumGate R R) : SimpleCircuitOverRegister R
  | HorizontalComp {R : QuantumRegister} (c1 c2 : SimpleCircuitOverRegister R) : SimpleCircuitOverRegister R
  | VerticalComp {R₁ R₂ : QuantumRegister} (c1 : SimpleCircuitOverRegister R₁) (c2 :SimpleCircuitOverRegister R₂ ) : SimpleCircuitOverRegister (R₁ ⊗ᵣ R₂)

public structure SimpleCircuit : Type 1 where
  register : QuantumRegister
  circuit : SimpleCircuitOverRegister register

public instance (R : QuantumRegister) : Coe (QuantumGate R R) (SimpleCircuitOverRegister R) where
  coe := fun g => SimpleCircuitOverRegister.Gate g

open SimpleCircuitOverRegister

notation c1 "⋙" c2 =>
  SimpleCircuit.mk
  (SimpleCircuit.register c1)
  (HorizontalComp (SimpleCircuit.circuit c1) (SimpleCircuit.circuit c2))

notation c1 "⋮" c2 =>
  SimpleCircuit.mk
  ((SimpleCircuit.register c1) ⊗ᵣ (SimpleCircuit.register c2))
  (VerticalComp (SimpleCircuit.circuit c1) (SimpleCircuit.circuit c2))


public def SimpleCircuitDepth' {R : QuantumRegister} (c : SimpleCircuitOverRegister R) : ℕ :=
  match c with
  | IdWire => 1
  | RegisterSwap _ _ => 0
  | Gate _ => 1
  | HorizontalComp c1 c2 => (SimpleCircuitDepth' c1) + (SimpleCircuitDepth' c2)
  | VerticalComp c1 c2 => max (SimpleCircuitDepth' c1) (SimpleCircuitDepth' c2)
public abbrev SimpleCircuitDepth (c : SimpleCircuit) : ℕ := SimpleCircuitDepth' c.circuit

public def SimpleCircuitGateCount' {R : QuantumRegister} (c : SimpleCircuitOverRegister R) : ℕ :=
  match c with
  | IdWire => 0
  | RegisterSwap _ _ => 0
  | Gate _ => 1
  | HorizontalComp c1 c2 => (SimpleCircuitGateCount' c1) + (SimpleCircuitGateCount' c2)
  | VerticalComp c1 c2 => (SimpleCircuitGateCount' c1) + (SimpleCircuitGateCount' c2)
public abbrev SimpleCircuitGateCount (c : SimpleCircuit) : ℕ := SimpleCircuitGateCount' c.circuit


public def SimpleCircuitGetShape' {R : QuantumRegister} (c : SimpleCircuitOverRegister R) :
  List QuantumRegister := match c with
    | IdWire => [R]
    | RegisterSwap _ c => SimpleCircuitGetShape' c
    | Gate _ => [R]
    | HorizontalComp c1 c2 => SimpleCircuitGetShape' c1
    | VerticalComp c1 c2 => (SimpleCircuitGetShape' c1) ++ (SimpleCircuitGetShape' c2)
public abbrev SimpleCircuitGetShape (c : SimpleCircuit) := SimpleCircuitGetShape' c.circuit

@[expose]
public noncomputable def SimpleCircuitGateRepr' {R : QuantumRegister} (c : SimpleCircuitOverRegister R)
  : QuantumGate R R := match c with
  | IdWire => id_map R
  | RegisterSwap iso c => iso.symm.hom ≫ (SimpleCircuitGateRepr' c) ≫ iso.hom
  | Gate g => g
  | HorizontalComp c1 c2 => (SimpleCircuitGateRepr' c1) ≫ (SimpleCircuitGateRepr' c2)
  | VerticalComp c1 c2 => GateTensor (SimpleCircuitGateRepr' c1) (SimpleCircuitGateRepr' c2)
public noncomputable abbrev SimpleCircuitGateRepr (c : SimpleCircuit) :
  QuantumGate c.register c.register := SimpleCircuitGateRepr' c.circuit

@[expose]
public noncomputable def SimpleCircuitCompute' {R : QuantumRegister} (c : SimpleCircuitOverRegister R)
  (s : QuantumStateSpace R) : QuantumStateSpace R := GateStateEvolve (SimpleCircuitGateRepr' c) s
public noncomputable def SimpleCircuitCompute (c : SimpleCircuit) (s : QuantumStateSpace c.register)
  : QuantumStateSpace c.register := SimpleCircuitCompute' c.circuit s


/-
    Some Useful theorem translating circuit composition to gate constructions
-/

public theorem HorizontalIsComp {R : QuantumRegister} (c1 c2 : SimpleCircuitOverRegister R)
  : SimpleCircuitGateRepr' (HorizontalComp c1 c2) = SimpleCircuitGateRepr' c1 ≫ SimpleCircuitGateRepr' c2 :=
  by rfl

public theorem HorizontalComputation {R : QuantumRegister} (c1 c2 : SimpleCircuitOverRegister R)
  : ∀ s : QuantumStateSpace R, SimpleCircuitCompute' (HorizontalComp c1 c2) s = SimpleCircuitCompute' c2 (SimpleCircuitCompute' c1 s)
  := by intro s; rfl

public theorem VerticalIsTensor {R1 R2 : QuantumRegister} (c1 : SimpleCircuitOverRegister R1)
  (c2 : SimpleCircuitOverRegister R2)
  : SimpleCircuitGateRepr' (VerticalComp c1 c2) = GateTensor (SimpleCircuitGateRepr' c1) (SimpleCircuitGateRepr' c2)
  := by rfl

@[simp]
public theorem IdWireIsNeutral (R : QuantumRegister) :
  ∀ s : QuantumStateSpace R, SimpleCircuitCompute' (IdWire) s = s :=
  by apply GateId

@[simp]
public theorem GateRepr'IsGateRepr {R : QuantumRegister} (c : SimpleCircuitOverRegister R) :
  (SimpleCircuitGateRepr' c) = SimpleCircuitGateRepr' c :=
  by rfl

public theorem RegisterSwapIsComp {R1 R2 : QuantumRegister} {iso : R1 ≅ R2}
 (c : SimpleCircuitOverRegister R1) :
 ∀ s : QuantumStateSpace R2, SimpleCircuitCompute' (RegisterSwap iso c) s = iso.hom.comp (SimpleCircuitCompute' c (s ≫ iso.symm.hom)) :=
by intro s; rfl

public theorem RegisterSwapComp {R1 R2 R3 : QuantumRegister} {iso1 : R1 ≅ R2} {iso2 : R2 ≅ R3}
  (c : SimpleCircuitOverRegister R1) :
  ∀ s : QuantumStateSpace R3,
    SimpleCircuitCompute' (RegisterSwap iso2 (RegisterSwap iso1 c)) s =
    SimpleCircuitCompute' (RegisterSwap (iso1.trans iso2) c) s :=
    by intro s; rw[RegisterSwapIsComp, RegisterSwapIsComp]; rfl

public theorem DoubleRegisterSwap {R1 R2 : QuantumRegister} {iso : R1 ≅ R2}
 (c : SimpleCircuitOverRegister R1) :
 ∀ s : QuantumStateSpace R1, SimpleCircuitCompute' (RegisterSwap iso.symm (RegisterSwap iso c)) s
  = SimpleCircuitCompute' c s :=
 by intro s; rw[RegisterSwapComp]; rw[CategoryTheory.Iso.self_symm_id]; rfl


/-
    Circuit Equivalence
-/

@[expose]
public def CircuitEquivalence {R : QuantumRegister} (c1 c2 : SimpleCircuitOverRegister R)
  : Prop := ∀ s : QuantumStateSpace R, SimpleCircuitCompute' c1 s = SimpleCircuitCompute' c2 s

notation c1 "≅ₖ" c2 => CircuitEquivalence c1 c2

@[simp]
public theorem CircuitEquivalenceRefl {R : QuantumRegister} (c : SimpleCircuitOverRegister R)
  : c ≅ₖ c := by intro s; rfl

@[simp]
public theorem CircuitEquivalenceSym {R : QuantumRegister} (c1 c2 : SimpleCircuitOverRegister R)
  : (c1 ≅ₖ c2) → (c2 ≅ₖ c1) := by intro h s; rw[h]

public theorem CircuitEquivalenceTrans {R : QuantumRegister} (c1 c2 c3 : SimpleCircuitOverRegister R)
  : (c1 ≅ₖ c2) → (c2 ≅ₖ c3) → (c1 ≅ₖ c3) := by intro h1 h2 s; rw[h1, h2]

/-
    Theorems on Equivalence
-/

@[simp]
public theorem CircuitCompositionsCommute {R1 R2 : QuantumRegister}
(c11 c12 : SimpleCircuitOverRegister R1) (c21 c22 : SimpleCircuitOverRegister R2) :
  VerticalComp (HorizontalComp c11 c12) (HorizontalComp c21 c22) ≅ₖ
  HorizontalComp (VerticalComp c11 c21) (VerticalComp c12 c22) :=
  by unfold CircuitEquivalence; intro s; unfold SimpleCircuitCompute'; unfold SimpleCircuitGateRepr'; rw[VerticalIsTensor, HorizontalIsComp, HorizontalIsComp, VerticalIsTensor]; rw[GateCompositionCommutation]

@[simp]
public theorem CircuitEquivalenceToGateCircuit {R : QuantumRegister} (c : SimpleCircuitOverRegister R) :
  c ≅ₖ Gate (SimpleCircuitGateRepr' c) :=
  by unfold CircuitEquivalence; intro s; rfl

-- public theorem CircuitEquivalenceGateIff  {R : QuantumRegister} (c1 c2 : SimpleCircuitOverRegister R) :
--   (c1 ≅ₖ c2) ↔ (SimpleCircuitGateRepr' c1) = (SimpleCircuitGateRepr' c2) :=
--   by apply Iff.intro; intro h; rw [GateExtIff]; intro s; unfold CircuitEquivalence at h; apply h; intro h; unfold CircuitEquivalence; unfold SimpleCircuitCompute; unfold GateStateEvolve; rw[GateRepr'IsGateRepr, GateRepr'IsGateRepr]; intro s; rw[h];

@[simp]
public theorem IdWireIsIdLeft {R : QuantumRegister} (c : SimpleCircuitOverRegister R)
  : HorizontalComp (IdWire) c ≅ₖ c :=
  by unfold CircuitEquivalence; intro s; rw[HorizontalComputation, IdWireIsNeutral]

@[simp]
public theorem IdWireIsIdRight {R : QuantumRegister} (c : SimpleCircuitOverRegister R)
  : HorizontalComp c (IdWire) ≅ₖ c :=
  by unfold CircuitEquivalence; intro s; rw[HorizontalComputation, IdWireIsNeutral]

@[simp]
public theorem HorizontalRewriteLeft {R : QuantumRegister} (c1 c1' c2 : SimpleCircuitOverRegister R)
  (hEquiv : c1 ≅ₖ c1') : HorizontalComp c1 c2 ≅ₖ HorizontalComp c1' c2 :=
  by unfold CircuitEquivalence; intro s; rw[HorizontalComputation, HorizontalComputation]; rw[hEquiv s]

@[simp]
public theorem HorizontalRewriteRight {R : QuantumRegister} (c1 c2 c2' : SimpleCircuitOverRegister R)
  (hEquiv : c2 ≅ₖ c2') : HorizontalComp c1 c2 ≅ₖ HorizontalComp c1 c2' :=
  by unfold CircuitEquivalence; intro s; rw[HorizontalComputation, HorizontalComputation]; rw[hEquiv]

-- @[simp]
-- public theorem ParallelRewriteUp {R1 R2 : QuantumRegister} (c1 c1' : SimpleCircuitOverRegister R1)
--   (c2 : SimpleCircuitOverRegister R2) (hEquiv:  c1 ≅ₖ c1') :
--   VerticalComp c1 c2 ≅ₖ VerticalComp c1' c2 :=
--   by rw[CircuitEquivalenceGateIff, VerticalIsTensor, VerticalIsTensor]; rw[CircuitEquivalenceGateIff] at hEquiv; rw[hEquiv]
--   --by unfold CircuitEquivalence;
--   --   apply Submodule.span_induction
--   --    (_) _ _ _ _ _ _
--
-- @[simp]
-- public theorem ParallelRewriteDown {R1 R2 : QuantumRegister} (c1 : SimpleCircuitOverRegister R1)
--   (c2 c2' : SimpleCircuitOverRegister R2) (hEquiv:  c2 ≅ₖ c2') :
--   VerticalComp c1 c2 ≅ₖ VerticalComp c1 c2' :=
--   by rw[CircuitEquivalenceGateIff, VerticalIsTensor, VerticalIsTensor]; rw[CircuitEquivalenceGateIff] at hEquiv; rw[hEquiv]


@[simp]
public theorem RegisterSwapCong {R1 R2 : QuantumRegister} {iso : R1 ≅ R2} (c1 c2 : SimpleCircuitOverRegister R1)
  : (c1 ≅ₖ c2) ↔ (RegisterSwap iso c1) ≅ₖ (RegisterSwap iso c2) :=
  by apply Iff.intro; intro h; unfold CircuitEquivalence; intro s;
      unfold CircuitEquivalence at h; rw[RegisterSwapIsComp, RegisterSwapIsComp];
      rw[h]; intro h; unfold CircuitEquivalence at h; unfold CircuitEquivalence; intro s; rw[<- @DoubleRegisterSwap R1 R2 iso];
      rw[RegisterSwapIsComp, h, <- RegisterSwapIsComp]; rw[@DoubleRegisterSwap R1 R2 iso];


/-
    Other Circuit Theorems
-/


end SyntacticCircuit
