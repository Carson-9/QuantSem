/-
Copyright (c) 2026 William Hasley. All rights reserved.
Released under GNU GPL3 license as described in the file LICENSE.
Authors: William Hasley
-/


module


public import QuantSem.Syntax.HighLevel.Gate
public import QuantSem.Syntax.HighLevel.State
public import QuantSem.Syntax.HighLevel.Register

open SyntacticGate
open SyntacticRegister
open SyntacticState

namespace SyntacticCircuit

/- Simple circuits are always representable as unitary matrices, no pesky measurement
    or other quantum operations I'm not aware of -/

variable [QuantumRegisterAlgebra] [S : QuantumStateAlgebra] [G : QuantumGateAlgebra]


-- Should the circuit algebra be fixed? Eckman hilton can come in handy

public inductive SimpleCircuitOverRegister : (TypeQuantumRegister → Type 1) where
  | Gate {R : TypeQuantumRegister} (g : QuantumGate' R R) : SimpleCircuitOverRegister R
  | HorizontalComp {R : TypeQuantumRegister} (c1 c2 : SimpleCircuitOverRegister R) : SimpleCircuitOverRegister R
  | VerticalComp {R₁ R₂ : TypeQuantumRegister} (c1 : SimpleCircuitOverRegister R₁) (c2 :SimpleCircuitOverRegister R₂ ) : SimpleCircuitOverRegister (R₁ ⊗ᵣ R₂)

public abbrev TypeSimpleCircuit := Σ R : TypeQuantumRegister, SimpleCircuitOverRegister R

public def SimpleCircuitDepth {R : TypeQuantumRegister} (c : SimpleCircuitOverRegister R) : ℕ :=
  match c with
  | SimpleCircuitOverRegister.Gate _ => 1
  | SimpleCircuitOverRegister.HorizontalComp c1 c2 => (SimpleCircuitDepth c1) + (SimpleCircuitDepth c2)
  | SimpleCircuitOverRegister.VerticalComp c1 c2 => max (SimpleCircuitDepth c1) (SimpleCircuitDepth c2)


public def SimpleCircuitGateCount {R : TypeQuantumRegister} (c : SimpleCircuitOverRegister R) : ℕ :=
  match c with
  | SimpleCircuitOverRegister.Gate _ => 1
  | SimpleCircuitOverRegister.HorizontalComp c1 c2 => (SimpleCircuitGateCount c1) + (SimpleCircuitGateCount c2)
  | SimpleCircuitOverRegister.VerticalComp c1 c2 => (SimpleCircuitGateCount c1) + (SimpleCircuitGateCount c2)

public def SimpleCircuitGetSignature {R : TypeQuantumRegister} :
    SimpleCircuitOverRegister R → TypeQuantumRegister :=
    fun _ => R

public def SimpleCircuitGetShape {R : TypeQuantumRegister} (c : SimpleCircuitOverRegister R) :
  List TypeQuantumRegister := match c with
    | SimpleCircuitOverRegister.Gate _ => [R]
    | SimpleCircuitOverRegister.HorizontalComp c1 c2 => SimpleCircuitGetShape c1
    | SimpleCircuitOverRegister.VerticalComp c1 c2 => (SimpleCircuitGetShape c1) ++ (SimpleCircuitGetShape c2)



open SimpleCircuitOverRegister

public def SimpleCircuitGateRepr {R : TypeQuantumRegister} (c : SimpleCircuitOverRegister R)
  : QuantumGate' R R := match c with
  | Gate g => g
  | HorizontalComp c1 c2 => (SimpleCircuitGateRepr c2) ∘' (SimpleCircuitGateRepr c1)
  | @VerticalComp _ R1 R2 c1 c2 => TypeGateToGate' (G.liftMap
     (⟨R1, ⟨R1, (SimpleCircuitGateRepr c1)⟩⟩ ⊗ₘ ⟨R2, ⟨R2, (SimpleCircuitGateRepr c2)⟩⟩))

/-

  State evolution through a circuit is a relation, as one must decide whether
  some state is separable to some degree in order to apply a vertical composition of circuits
  This is always true in finite dimension, where each state can be written ∑ αᵢⱼ eᵢ ⊗ eⱼ
  However, in general, one cannot decide.
-/

public inductive SimpleCircuitReduces : {R : TypeQuantumRegister} → QuantumStateSpace' R →
  SimpleCircuitOverRegister R → QuantumStateSpace' R → Prop where

    | GateApply {R : TypeQuantumRegister} (g : QuantumGate' R R) (s : QuantumStateSpace' R) :
      SimpleCircuitReduces s (Gate g) (GateStateEvolve' g s)

    | Horizontal {R : TypeQuantumRegister} (c1 c2 : SimpleCircuitOverRegister R) (s s' s'' : QuantumStateSpace' R)
        (hc1 : SimpleCircuitReduces s c1 s') (hc2 : SimpleCircuitReduces s' c1 s'') :
      SimpleCircuitReduces s (SimpleCircuitOverRegister.HorizontalComp c1 c2) s''

    | Vertical {R1 R2 : TypeQuantumRegister} (c1 : SimpleCircuitOverRegister R1) (c2 : SimpleCircuitOverRegister R2)
      (s1 s1' : QuantumStateSpace' R1) (s2 s2' : QuantumStateSpace' R2)
      (hc1 : SimpleCircuitReduces s1 c1 s1') (hc2 : SimpleCircuitReduces s2 c2 s2') :
      SimpleCircuitReduces (S.liftMap ⟨R1, s1⟩ ⟨R2, s2⟩ (S.mul ⟨R1, s1⟩ ⟨R2, s2⟩).snd.val)
        (SimpleCircuitOverRegister.VerticalComp c1 c2) (S.liftMap ⟨R1, s1'⟩ ⟨R2, s2'⟩ (S.mul ⟨R1, s1'⟩ ⟨R2, s2'⟩).snd.val)

notation s "-" "[" c "]" "->" s' => SimpleCircuitReduces s c s'

/-
  Two circuits are considered equivalent when every "computation" is the same
-/

public def CircuitEquivalence {R : TypeQuantumRegister} (c1 c2 : SimpleCircuitOverRegister R) : Prop
  := ∀ s s' : QuantumStateSpace' R, (s -[c1]-> s') <-> (s -[c2]-> s')

notation c1 "≅" c2 => CircuitEquivalence c1 c2

/-
  Horizontal composition and Vertical composition commute with respect to equivalence
-/

open SimpleCircuitOverRegister
open SimpleCircuitReduces

public theorem CompositionsCommute {R1 R2 : TypeQuantumRegister}
  (c11 c12 : SimpleCircuitOverRegister R1)
  (c21 c22 : SimpleCircuitOverRegister R2) :
  CircuitEquivalence  -- cannot match this with smth else
    (VerticalComp (HorizontalComp c11 c12) (HorizontalComp c21 c22))
    (HorizontalComp (VerticalComp c11 c21) (VerticalComp c12 c22))
  :=
  by
  unfold CircuitEquivalence;
  intro s s';
  apply Iff.intro;
  intro hred;
  rcases hred;

end SyntacticCircuit
