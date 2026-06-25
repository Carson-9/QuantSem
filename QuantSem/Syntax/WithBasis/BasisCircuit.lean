/-
Copyright (c) 2026 William Hasley. All rights reserved.
Released under GNU GPL3 license as described in the file LICENSE.
Authors: William Hasley
-/


module

public import QuantSem.Syntax.WithBasis.FinSuppBasisTypes
public import QuantSem.Syntax.WithBasis.BasisRegister
public import QuantSem.Syntax.WithBasis.BasisState
public import QuantSem.Syntax.WithBasis.BasisGate
public import QuantSem.Syntax.Category.Circuit

namespace BasisCircuit

open SyntacticCircuit
open BasisTypes
open BasisRegister
open BasisState
open BasisGate
open CategoryTheory


public inductive BasisCircuitOverRegister : (TypeBasisRegister → Type 1) where
  | IdWire {R : TypeBasisRegister} : BasisCircuitOverRegister R
  | RegisterSwap {R1 R2 : TypeBasisRegister} (iso : BasisRegToQuantReg R1 ≅ BasisRegToQuantReg R2) (c : BasisCircuitOverRegister R1) : BasisCircuitOverRegister R2
  | Gate {R : TypeBasisRegister} (g : BasisGateType R R) : BasisCircuitOverRegister R
  | HorizontalComp {R : TypeBasisRegister} (c1 c2 : BasisCircuitOverRegister R) : BasisCircuitOverRegister R
  | VerticalComp {R₁ R₂ : TypeBasisRegister} (c1 : BasisCircuitOverRegister R₁) (c2 :BasisCircuitOverRegister R₂)
    : BasisCircuitOverRegister (R₁ ⊗ᵣ R₂)

public abbrev TypeBasisCircuit := Σ R : TypeBasisRegister, BasisCircuitOverRegister R

public abbrev TypeBasisCircuit.register (c : TypeBasisCircuit) := c.fst
public abbrev TypeBasisCircuit.circuit (c : TypeBasisCircuit) := c.snd

open BasisCircuitOverRegister

@[coe, expose, simp]
public noncomputable def BasisCircuitAreSimpleCircuit {R : TypeBasisRegister} (c : BasisCircuitOverRegister R)
  : SimpleCircuitOverRegister (BasisRegToQuantReg R) :=
  match c with
  | IdWire => SimpleCircuitOverRegister.IdWire
  | RegisterSwap iso c => SimpleCircuitOverRegister.RegisterSwap iso (BasisCircuitAreSimpleCircuit c)
  | Gate g => SimpleCircuitOverRegister.Gate g
  | HorizontalComp c1 c2 => SimpleCircuitOverRegister.HorizontalComp (BasisCircuitAreSimpleCircuit c1) (BasisCircuitAreSimpleCircuit c2)
  | VerticalComp c1 c2 => SimpleCircuitOverRegister.VerticalComp (BasisCircuitAreSimpleCircuit c1) (BasisCircuitAreSimpleCircuit c2)

public noncomputable instance (R : TypeBasisRegister) : Coe (BasisCircuitOverRegister R) (SimpleCircuitOverRegister (BasisRegToQuantReg R)) where
  coe := BasisCircuitAreSimpleCircuit

@[simp]
public noncomputable def BasisCircuitGateRepr {R : TypeBasisRegister} (c : BasisCircuitOverRegister R)
  : BasisGateType R R := match c with
  | IdWire => IdGate R
  | RegisterSwap iso c => iso.symm.hom ≫ BasisCircuitGateRepr c ≫ iso.hom
  | Gate g => g
  | HorizontalComp c1 c2 => (BasisCircuitGateRepr c1) ≫ (BasisCircuitGateRepr c2)
  | VerticalComp c1 c2 => (BasisCircuitGateRepr c1) ⊗ₕ (BasisCircuitGateRepr c2)


@[simp]
public theorem BasisGateReprIsSimpleGateRepr {R : TypeBasisRegister} (c : BasisCircuitOverRegister R) :
  (BasisCircuitGateRepr c) = (SyntacticCircuit.SimpleCircuitGateRepr c) :=
  by induction c with
    | IdWire => unfold BasisCircuitGateRepr; unfold SyntacticCircuit.SimpleCircuitGateRepr;
                simp; unfold SyntacticRegister.id_map; rfl
    | RegisterSwap iso c c_ih => simp; unfold SyntacticCircuit.SimpleCircuitGateRepr; rw[c_ih]; rfl
    | Gate g => rfl
    | HorizontalComp c1 c2 c1h c2h => simp; rw[c1h, c2h]; rfl
    | VerticalComp c1 c2 c1h c2h => simp; rw[c1h, c2h]; rfl



@[expose, simp]
public def BasisCircuitEquivalence {R : TypeBasisRegister}
  (c1 c2 : BasisCircuitOverRegister R)
  : Prop := ∀ i : R.indexing, SimpleCircuitCompute c1 (GetBasisState i) = SimpleCircuitCompute c2 (GetBasisState i)

notation c1 "≅ₖ₂" c2 => BasisCircuitEquivalence c1 c2

@[simp]
public theorem BasisEquivalenceRefl {R : TypeBasisRegister} (c : BasisCircuitOverRegister R)
  : c ≅ₖ₂ c := by intro s; rfl

@[simp]
public theorem BasisEquivalenceSym {R : TypeBasisRegister} (c1 c2 : BasisCircuitOverRegister R)
  : (c1 ≅ₖ₂ c2) → (c2 ≅ₖ₂ c1) := by intro h s; rw[h]

public theorem BasisEquivalenceTrans {R : TypeBasisRegister} (c1 c2 c3 : BasisCircuitOverRegister R)
  : (c1 ≅ₖ₂ c2) → (c2 ≅ₖ₂ c3) → (c1 ≅ₖ₂ c3) := by intro h1 h2 s; rw[h1, h2]



public theorem BasisEquivalenceOverBasisState {R : TypeBasisRegister} (c1 c2 : BasisCircuitOverRegister R) :
  (c1 ≅ₖ₂ c2) ↔ ((BasisCircuitGateRepr c1) = (BasisCircuitGateRepr c2)) :=
  by apply Iff.intro; intro h; simp at h; apply GateExtBasis; intro i;
     unfold SyntacticCircuit.SimpleCircuitCompute at h; unfold SyntacticGate.GateStateEvolve at h;
     specialize h i; rw[BasisGateReprIsSimpleGateRepr, BasisGateReprIsSimpleGateRepr];
     unfold SyntacticCircuit.SimpleCircuitGateRepr' at h; simp at h; apply h;
     intro h; simp; intro i; unfold SimpleCircuitCompute; unfold SyntacticCircuit.SimpleCircuitGateRepr';
     simp; rw[GateExtBasisIff] at h; specialize h i; rw[BasisGateReprIsSimpleGateRepr, BasisGateReprIsSimpleGateRepr] at h; apply h


public theorem BasisEquivalenceIsEquivalence {R : TypeBasisRegister} (c1 c2 : BasisCircuitOverRegister R) :
  (c1 ≅ₖ₂ c2) ↔ ((BasisCircuitAreSimpleCircuit c1) ≅ₖ (BasisCircuitAreSimpleCircuit c2)) :=
  by apply Iff.intro; intro h; unfold CircuitEquivalence; intro s; unfold SimpleCircuitCompute;
     simp; unfold SimpleCircuitGateRepr'; rw[BasisEquivalenceOverBasisState] at h;
     rw [BasisGateReprIsSimpleGateRepr, BasisGateReprIsSimpleGateRepr] at h; rw[h]; simp;
     intro h; unfold CircuitEquivalence at h; intro i; apply h


public theorem GateEquivalenceIff  {R : TypeBasisRegister} (g1 g2 : BasisGateType R R) :
  ((Gate g1) ≅ₖ₂ (Gate g2)) ↔ (g1 = g2) := by apply Iff.intro; intro h; apply GateExtBasis; apply h; intro h; rw[h]; apply BasisEquivalenceRefl



end BasisCircuit
