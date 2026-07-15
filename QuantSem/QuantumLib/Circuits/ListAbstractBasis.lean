/-
Copyright (c) 2026 William Hasley. All rights reserved.
Released under GNU GPL3 license as described in the file LICENSE.
Authors: William Hasley
-/


module

public import QuantSem.QuantumLib.Registers.PiAbstractBasis
public import QuantSem.QuantumLib.Gates.AbstractBasis
public import QuantSem.QuantumLib.Registers.AbstractBasis
public import QuantSem.QuantumLib.Circuits.AbstractBasis
public import QuantSem.QuantumLib.Circuits.Basic

namespace BasisCircuitList

open BasisCircuit
open SyntacticCircuit
open PiBasisRegister
open AbstractBasisRegister
open BasisGate
open CategoryTheory


public inductive BasisCircuitOverList : ((List BasisRegister) → Type 1) where
  | IdWire {R : BasisRegister} : BasisCircuitOverList [R]
  | Gate {R : List BasisRegister} (g : BasisGateType (⨂ᵣ R) (⨂ᵣ R)) : BasisCircuitOverList R
  | HorizontalComp {R : List BasisRegister} (c1 c2 : BasisCircuitOverList R) : BasisCircuitOverList R
  | VerticalComp {R₁ R₂ : List BasisRegister} (c1 : BasisCircuitOverList R₁) (c2 :BasisCircuitOverList R₂)
    : BasisCircuitOverList (R₁ ++ R₂)

public structure BasisListCircuit : Type 1 where
  regList : List BasisRegister
  circuit : BasisCircuitOverList regList


@[simp]
public theorem BasisCircuitRewriteList {l1 l2 : List BasisRegister} (eq : l1 = l2) :
  (BasisCircuitOverList l1) = (BasisCircuitOverList l2) := by rw[eq]

public def BasisCircuitListCoe {l1 l2 : List BasisRegister} (eq : l1 = l2) :
  (BasisCircuitOverList l1) ≃ (BasisCircuitOverList l2) :=
  Equiv.cast (BasisCircuitRewriteList eq)


open BasisCircuitOverList

@[coe, expose, simp]
public noncomputable def BasisCircuitListAreBasisCircuit {R : List BasisRegister} (c : BasisCircuitOverList R)
  : BasisCircuitOverRegister (⨂ᵣ R)  :=
  match c with
  | IdWire => SimpleCircuitOverRegister.IdWire
  | Gate g => SimpleCircuitOverRegister.Gate g
  | HorizontalComp c1 c2 => SimpleCircuitOverRegister.HorizontalComp (BasisCircuitListAreBasisCircuit c1) (BasisCircuitListAreBasisCircuit c2)
  | @VerticalComp R1 R2 c1 c2 => SimpleCircuitOverRegister.RegisterSwap (IsoPromote.symm (MulTensorIso R1 R2)) (SimpleCircuitOverRegister.VerticalComp (BasisCircuitListAreBasisCircuit c1) (BasisCircuitListAreBasisCircuit c2))


public theorem BasisCircuitListCoeVert {R1 R2 : List BasisRegister} (c1 : BasisCircuitOverList R1)
  (c2 : BasisCircuitOverList R2) :
  BasisCircuitListAreBasisCircuit (@VerticalComp R1 R2 c1 c2) =
   SimpleCircuitOverRegister.RegisterSwap (IsoPromote.symm (MulTensorIso R1 R2)) (SimpleCircuitOverRegister.VerticalComp (BasisCircuitListAreBasisCircuit c1) (BasisCircuitListAreBasisCircuit c2)) :=
   by rfl

@[simp]
public noncomputable def ListCircuitGateRepr {R : List BasisRegister} (c : BasisCircuitOverList R)
  : BasisGateType (⨂ᵣ R) (⨂ᵣ R) := match c with
  | @IdWire R' => IdGate (⨂ᵣ [R'])
  | Gate g => g
  | HorizontalComp c1 c2 => (ListCircuitGateRepr c1) ≫ (ListCircuitGateRepr c2)
  | @VerticalComp R1 R2 c1 c2 => (MulTensorIso R1 R2).inv ≫ ((ListCircuitGateRepr c1) ⊗ₕ (ListCircuitGateRepr c2)) ≫ (MulTensorIso R1 R2).hom


@[simp]
public theorem BasisGateReprIsSimpleGateRepr {R : List BasisRegister} (c : BasisCircuitOverList R) :
  (ListCircuitGateRepr c) = (SimpleCircuitGateRepr' (BasisCircuitListAreBasisCircuit c)) :=
  by induction c with
    | IdWire => unfold ListCircuitGateRepr; simp; rfl
    | Gate g => unfold ListCircuitGateRepr; simp; rfl
    | HorizontalComp c1 c2 c1h c2h => simp; rw[c1h, c2h]; simp; rfl
    | @VerticalComp R1 R2 c1 c2 c1h c2h =>
      unfold ListCircuitGateRepr; rw[c1h, c2h];
      rw[BasisCircuitListCoeVert]; sorry




/-
    Definition of a circuit by induction
-/

public def InductiveCircuit'' (baseRegList : List BasisRegister)
  (baseCase : BasisCircuitOverList baseRegList) (f : List BasisRegister → List BasisRegister)
  (ind : (R : List BasisRegister) → BasisCircuitOverList R → BasisCircuitOverList (f R))
  : ℕ → BasisListCircuit := fun n => match n with
  | 0 => .mk baseRegList baseCase
  | Nat.succ k =>
    .mk
    (f (InductiveCircuit'' baseRegList baseCase f ind k).regList)
    (ind (InductiveCircuit'' baseRegList baseCase f ind k).regList (InductiveCircuit'' baseRegList baseCase f ind k).circuit)

public def InductiveCircuit' (f : ℕ → List BasisRegister)
  (baseCase : BasisCircuitOverList (f 0))
  (ind : (n : ℕ) →  BasisCircuitOverList (f n) → BasisCircuitOverList (f (n + 1)))
  (n : ℕ) : BasisCircuitOverList (f n) := match n with
  | 0 => baseCase
  | Nat.succ k => ind k (InductiveCircuit' f baseCase ind k)

public def InductiveCircuit (f : ℕ → List BasisRegister)
  (baseCase : BasisCircuitOverList (f 0))
  (ind : (n : ℕ) →  BasisCircuitOverList (f n) → BasisCircuitOverList (f (n + 1)))
  (n : ℕ) : BasisListCircuit :=
  .mk (f n) (InductiveCircuit' f baseCase ind n)


end BasisCircuitList
