/-
Copyright (c) 2026 William Hasley. All rights reserved.
Released under GNU GPL3 license as described in the file LICENSE.
Authors: William Hasley
-/


module

public import QuantSem.QuantumLib.HilbertSpaces.AbstractBasis
public import QuantSem.QuantumLib.Registers.PiAbstractBasis
public import QuantSem.QuantumLib.Registers.AbstractBasis
public import QuantSem.QuantumLib.States.AbstractBasis
public import QuantSem.QuantumLib.Gates.AbstractBasis
public import QuantSem.QuantumLib.Circuits.AbstractBasis
public import QuantSem.QuantumLib.Circuits.Basic

namespace BasisCircuitList

open BasisCircuit
open SyntacticCircuit
open BasisTypes
open PiBasisRegister
open BasisRegister
open BasisState
open BasisGate
open CategoryTheory


public inductive BasisCircuitOverList : ((List TypeBasisRegister) → Type 1) where
  | IdWire {R : TypeBasisRegister} : BasisCircuitOverList [R]
  | Gate {R : List TypeBasisRegister} (g : BasisGateType (⨂ᵣ R) (⨂ᵣ R)) : BasisCircuitOverList R
  | HorizontalComp {R : List TypeBasisRegister} (c1 c2 : BasisCircuitOverList R) : BasisCircuitOverList R
  | VerticalComp {R₁ R₂ : List TypeBasisRegister} (c1 : BasisCircuitOverList R₁) (c2 :BasisCircuitOverList R₂)
    : BasisCircuitOverList (R₁ ++ R₂)

public abbrev TypeBasisCircuitList := Σ R : List TypeBasisRegister, BasisCircuitOverList R

public abbrev TypeBasisCircuitList.register (c : TypeBasisCircuitList) := c.fst
public abbrev TypeBasisCircuitList.circuit (c : TypeBasisCircuitList) := c.snd

@[simp]
public theorem BasisCircuitRewriteList {l1 l2 : List TypeBasisRegister} (eq : l1 = l2) :
  (BasisCircuitOverList l1) = (BasisCircuitOverList l2) := by rw[eq]

public def BasisCircuitListCoe {l1 l2 : List TypeBasisRegister} (eq : l1 = l2) :
  (BasisCircuitOverList l1) ≃ (BasisCircuitOverList l2) :=
  Equiv.cast (BasisCircuitRewriteList eq)


-- public instance CircuitSameList {l1 l2 : List TypeBasisRegister} (hl : l1 = l2) :
--   Coe (BasisCircuitOverList l1) (BasisCircuitOverList l2) where
--   coe := BasisCircuitListCoe hl

open BasisCircuitOverList

@[coe, expose, simp]
public noncomputable def BasisCircuit'AreBasisCircuit {R : List TypeBasisRegister} (c : BasisCircuitOverList R)
  : BasisCircuitOverRegister (⨂ᵣ R)  :=
  match c with
  | IdWire => BasisCircuitOverRegister.IdWire
  | Gate g => BasisCircuitOverRegister.Gate g
  | HorizontalComp c1 c2 => BasisCircuitOverRegister.HorizontalComp (BasisCircuit'AreBasisCircuit c1) (BasisCircuit'AreBasisCircuit c2)
  | @VerticalComp R1 R2 c1 c2 => BasisCircuitOverRegister.RegisterSwap (MulTensorIso R1 R2) (BasisCircuitOverRegister.VerticalComp (BasisCircuit'AreBasisCircuit c1) (BasisCircuit'AreBasisCircuit c2))

public noncomputable instance (R : TypeBasisRegister) : Coe (BasisCircuitOverRegister R) (SimpleCircuitOverRegister (BasisRegToQuantReg R)) where
  coe := BasisCircuitAreSimpleCircuit

public theorem BasisCircuitListCoeVert {R1 R2 : List TypeBasisRegister} (c1 : BasisCircuitOverList R1)
  (c2 : BasisCircuitOverList R2) :
  BasisCircuit'AreBasisCircuit (@VerticalComp R1 R2 c1 c2) =
   BasisCircuitOverRegister.RegisterSwap (MulTensorIso R1 R2) (BasisCircuitOverRegister.VerticalComp (BasisCircuit'AreBasisCircuit c1) (BasisCircuit'AreBasisCircuit c2)) :=
   by rfl

@[simp]
public noncomputable def BasisCircuit'GateRepr {R : List TypeBasisRegister} (c : BasisCircuitOverList R)
  : BasisGateType (⨂ᵣ R) (⨂ᵣ R) := match c with
  | @IdWire R' => IdGate R'
  | Gate g => g
  | HorizontalComp c1 c2 => (BasisCircuit'GateRepr c1) ≫ (BasisCircuit'GateRepr c2)
  | @VerticalComp R1 R2 c1 c2 => (MulTensorIso R1 R2).inv ≫ ((BasisCircuit'GateRepr c1) ⊗ₕ (BasisCircuit'GateRepr c2)) ≫ (MulTensorIso R1 R2).hom


@[simp]
public theorem BasisGateReprIsSimpleGateRepr {R : List TypeBasisRegister} (c : BasisCircuitOverList R) :
  (BasisCircuit'GateRepr c) = (BasisCircuitGateRepr (BasisCircuit'AreBasisCircuit c)) :=
  by induction c with
    | IdWire => unfold BasisCircuit'GateRepr; simp; rfl
    | Gate g => unfold BasisCircuit'GateRepr; simp; rfl
    | HorizontalComp c1 c2 c1h c2h => simp; rw[c1h, c2h]; simp; rfl
    | @VerticalComp R1 R2 c1 c2 c1h c2h =>
      unfold BasisCircuit'GateRepr; rw[c1h, c2h];
      rw[BasisCircuitListCoeVert]; sorry


/-
    Definition of a circuit by induction
-/

public def InductiveCircuit (baseRegList : List TypeBasisRegister)
  (baseCase : BasisCircuitOverList baseRegList) (f : List TypeBasisRegister → List TypeBasisRegister)
  (ind : (R : List TypeBasisRegister) → BasisCircuitOverList R → BasisCircuitOverList (f R))
  : ℕ → TypeBasisCircuitList := fun n => match n with
  | 0 => ⟨baseRegList, baseCase⟩
  | Nat.succ k =>
    ⟨f ((InductiveCircuit baseRegList baseCase f ind k).register) , ind (InductiveCircuit baseRegList baseCase f ind k).register (InductiveCircuit baseRegList baseCase f ind k).circuit⟩

public def InductiveCircuit' (f : ℕ → List TypeBasisRegister)
  (baseCase : BasisCircuitOverList (f 0))
  (ind : (n : ℕ) →  BasisCircuitOverList (f n) → BasisCircuitOverList (f (n + 1)))
  (n : ℕ) : BasisCircuitOverList (f n) := match n with
  | 0 => baseCase
  | Nat.succ k => ind k (InductiveCircuit' f baseCase ind k)

public def InductiveCircuit'' (f : ℕ → List TypeBasisRegister)
  (baseCase : BasisCircuitOverList (f 0))
  (ind : (n : ℕ) →  BasisCircuitOverList (f n) → BasisCircuitOverList (f (n + 1)))
  (n : ℕ) : TypeBasisCircuitList :=
  ⟨f n, InductiveCircuit' f baseCase ind n⟩


end BasisCircuitList
