/-
Copyright (c) 2026 William Hasley. All rights reserved.
Released under GNU GPL3 license as described in the file LICENSE.
Authors: William Hasley
-/


module

public import QuantSem.QuantumLib.Registers.AbstractBasis
public import QuantSem.QuantumLib.States.AbstractBasis
public import QuantSem.QuantumLib.Gates.AbstractBasis
public import QuantSem.QuantumLib.Circuits.Basic

namespace BasisCircuit

open SyntacticCircuit
open AbstractBasisRegister
open BasisState
open BasisGate


public abbrev BasisCircuitOverRegister (R : BasisRegister) : Type 1 := SimpleCircuitOverRegister R

open SimpleCircuitOverRegister


@[expose, simp]
public def BasisCircuitEquivalence {R : BasisRegister}
  (c1 c2 : BasisCircuitOverRegister R)
  : Prop := ∀ i : R.indexing, SimpleCircuitCompute' c1 (GetBasisState i) = SimpleCircuitCompute' c2 (GetBasisState i)

notation c1 "≅ₖ₂" c2 => BasisCircuitEquivalence c1 c2

@[simp]
public theorem BasisEquivalenceRefl {R : BasisRegister} (c : BasisCircuitOverRegister R)
  : c ≅ₖ₂ c := by intro s; rfl

@[simp]
public theorem BasisEquivalenceSym {R : BasisRegister} (c1 c2 : BasisCircuitOverRegister R)
  : (c1 ≅ₖ₂ c2) → (c2 ≅ₖ₂ c1) := by intro h s; rw[h]

public theorem BasisEquivalenceTrans {R : BasisRegister} (c1 c2 c3 : BasisCircuitOverRegister R)
  : (c1 ≅ₖ₂ c2) → (c2 ≅ₖ₂ c3) → (c1 ≅ₖ₂ c3) := by intro h1 h2 s; rw[h1, h2]


public theorem BasisEquivalenceOverBasisState {R : BasisRegister} (c1 c2 : BasisCircuitOverRegister R) :
  (c1 ≅ₖ₂ c2) ↔ ((SimpleCircuitGateRepr' c1) = (SimpleCircuitGateRepr' c2)) :=
  by apply Iff.intro; intro h; simp at h; apply GateExtBasis; intro i;
     unfold SyntacticCircuit.SimpleCircuitCompute' at h; unfold SyntacticGate.GateStateEvolve at h;
     specialize h i; apply h;
     intro h; simp; intro i; unfold SimpleCircuitCompute'; rw[h]


public theorem BasisEquivalenceIsEquivalence {R : BasisRegister} (c1 c2 : BasisCircuitOverRegister R) :
  (c1 ≅ₖ₂ c2) ↔ (c1 ≅ₖ c2) :=
  by apply Iff.intro; intro h; unfold CircuitEquivalence; intro s; unfold SimpleCircuitCompute';
     rw[BasisEquivalenceOverBasisState] at h; rw[h];
     intro h; unfold CircuitEquivalence at h; intro i; apply h


public theorem GateEquivalenceIff  {R : BasisRegister} (g1 g2 : BasisGateType R R) :
  ((Gate g1) ≅ₖ₂ (Gate g2)) ↔ (g1 = g2) := by apply Iff.intro; intro h; apply GateExtBasis; apply h; intro h; rw[h]; apply BasisEquivalenceRefl

/-
    Parallel rewrites are now unconditionally true
-/

-- @[simp]
-- public theorem ParallelRewriteUp {R1 R2 : BasisRegister} (c1 c1' : BasisCircuitOverRegister R1)
--   (c2 : BasisCircuitOverRegister R2) (hEquiv:  c1 ≅ₖ₂ c1') :
--   (VerticalComp c1 c2) ≅ₖ (VerticalComp c1' c2) :=
--   by apply (BasisEquivalenceIsEquivalence (VerticalComp c1 c2) (VerticalComp c1' c2)).mp;
--
-- @[simp]
-- public theorem ParallelRewriteDown {R1 R2 : BasisRegister} (c1 : BasisCircuitOverRegister R1)
--   (c2 c2' : BasisCircuitOverRegister R2) (hEquiv:  c2 ≅ₖ c2') :
--   VerticalComp c1 c2 ≅ₖ VerticalComp c1 c2' :=
--   by rw[CircuitEquivalenceGateIff, VerticalIsTensor, VerticalIsTensor]; rw[CircuitEquivalenceGateIff] at hEquiv; rw[hEquiv]



end BasisCircuit
