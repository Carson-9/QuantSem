/-
Copyright (c) 2026 William Hasley. All rights reserved.
Released under GNU GPL3 license as described in the file LICENSE.
Authors: William Hasley
-/


module


public import QuantSem.Syntax.HighLevelInstance.Gate

open SyntacticGate
open SyntacticRegister
open SyntacticState

namespace SyntacticCircuit

variable {C : QuantumRegisterAlgebra} {S : QuantumStateAlgebra} {G : QuantumGateAlgebra}
--variable (R : Type) [QuantReg R]
/- Simple circuits are always representable as unitary matrices, no pesky measurement
    or other quantum operations I'm not aware of -/


-- Should the circuit algebra be fixed? Eckman hilton can come in handy
public inductive SimpleCircuitOverRegister : TypeQuantumRegister → Type 1 where
  | Gate (R : Type) [QuantReg R] (g : QuantumGate R R) : SimpleCircuitOverRegister (QuantRegToTypeQuantumRegister R)| HorizontalComp {R : TypeQuantumRegister} (c1 c2 : SimpleCircuitOverRegister R) : SimpleCircuitOverRegister R| VerticalComp (R₁ R₂ : TypeQuantumRegister) {C : QuantumRegisterAlgebra} (c1 : SimpleCircuitOverRegister R₁) (c2 :SimpleCircuitOverRegister R₂ ): SimpleCircuitOverRegister (C.mul R₁ R₂)

public abbrev TypeSimpleCircuit := Σ R : TypeQuantumRegister, SimpleCircuitOverRegister R

public def SimpleCircuitDepth {R : TypeQuantumRegister} (c : SimpleCircuitOverRegister R) : ℕ :=
  match c with
  | SimpleCircuitOverRegister.Gate _ _ => 1
  | @SimpleCircuitOverRegister.HorizontalComp _ c1 c2 => (SimpleCircuitDepth c1) + (SimpleCircuitDepth c2)
  | SimpleCircuitOverRegister.VerticalComp _ _ c1 c2 => max (SimpleCircuitDepth c1) (SimpleCircuitDepth c2)


public def SimpleCircuitGateCount {R : TypeQuantumRegister} (c : SimpleCircuitOverRegister R) : ℕ :=
  match c with
  | SimpleCircuitOverRegister.Gate _ _ => 1
  | SimpleCircuitOverRegister.HorizontalComp c1 c2 =>
    (SimpleCircuitGateCount c1) + (SimpleCircuitGateCount c2)
  | SimpleCircuitOverRegister.VerticalComp R1 R2 c1 c2 =>
    (SimpleCircuitGateCount c1) + (SimpleCircuitGateCount c2)

public def SimpleCircuitGetSignature {R : TypeQuantumRegister} :
    SimpleCircuitOverRegister R → TypeQuantumRegister :=
    fun _ => R

public def SimpleCircuitGetShape {R : TypeQuantumRegister} (c : SimpleCircuitOverRegister R) :
  List TypeQuantumRegister := match c with
    | @SimpleCircuitOverRegister.Gate R R' _ => [⟨R, R'⟩]
    | @SimpleCircuitOverRegister.HorizontalComp _ c1 c2 => SimpleCircuitGetShape c1
    | @SimpleCircuitOverRegister.VerticalComp _ _ _ c1 c2 => (SimpleCircuitGetShape c1) ++ (SimpleCircuitGetShape c2)

/-

  State evolution through a circuit is a relation, as one must decide whether
    some state is separable in order to apply a vertical composition of circuits

-/

public inductive SimpleCircuitReduces : (R : TypeQuantumRegister) →
    @QuantumStateSpace R.fst R.snd → SimpleCircuitOverRegister R → @QuantumStateSpace R.fst R.snd → Prop where
    | GateApply {R : TypeQuantumRegister} (g : @QuantumGate R.fst R.fst R.snd R.snd) (s : @QuantumStateSpace R.fst R.snd) :
      SimpleCircuitReduces R s (@SimpleCircuitOverRegister.Gate R.fst R.snd g) (@GateStateEvolve R.fst R.fst R.snd R.snd g s)| Horizontal {R : TypeQuantumRegister} (c1 c2 : SimpleCircuitOverRegister R) (s s' s'' : @QuantumStateSpace R.fst R.snd)
        (hc1 : SimpleCircuitReduces R s c1 s') (hc2 : SimpleCircuitReduces R s' c1 s'') :
      SimpleCircuitReduces R s (@SimpleCircuitOverRegister.HorizontalComp R c1 c2) s''|Vertical
      {R1 R2 : TypeQuantumRegister} {C : QuantumRegisterAlgebra} {S : QuantumStateAlgebra} (c1 : SimpleCircuitOverRegister R1) (c2 : SimpleCircuitOverRegister R2)
      (s1 s1' : @QuantumStateSpace R1.fst R1.snd) (s2 s2' : @QuantumStateSpace R2.fst R2.snd)
      (hc1 : SimpleCircuitReduces R1 s1 c1 s1') (hc1 : SimpleCircuitReduces R2 s2 c2 s2') :
      SimpleCircuitReduces (C.mul R1 R2) (S.liftMap ⟨R1, s1⟩ ⟨R2, s2⟩ (S.mul ⟨R1, s1⟩ ⟨R2, s2⟩).snd.val)
        (SimpleCircuitOverRegister.VerticalComp R1 R2 c1 c2) (S.liftMap ⟨R1, s1'⟩ ⟨R2, s2'⟩ (S.mul ⟨R1, s1'⟩ ⟨R2, s2'⟩).snd.val)

notation s "-" "[" R "," C "]" "->" s' => SimpleCircuitReduces R s C s'


/-
  Two circuits are considered equivalent when every "computation" is the same
-/

public def CircuitEquivalence {R : TypeQuantumRegister} (c1 c2 : SimpleCircuitOverRegister R) : Prop
  := ∀ s s' : @QuantumStateSpace R.fst R.snd, (s -[R, c1]-> s') <-> (s -[R, c2]-> s')

notation c1 "≅" c2 => CircuitEquivalence c1 c2

/-
  Horizontal composition and Vertical composition commute with respect to equivalence
-/

open SimpleCircuitOverRegister

public theorem CompositionsCommute {R1 R2 : TypeQuantumRegister} {C : QuantumRegisterAlgebra}
  (c11 c12 : SimpleCircuitOverRegister R1)
  (c21 c22 : SimpleCircuitOverRegister R2) :
  (@VerticalComp R1 R2 C (HorizontalComp c11 c12) (HorizontalComp c21 c22)) ≅
  (HorizontalComp (@VerticalComp R1 R2 C c11 c21) (@VerticalComp R1 R2 C c12 c22))
  :=
  by unfold CircuitEquivalence; intro s s'; apply Iff.intro; intro hred; sorry --rcases hred;
  -- I need to fix my lean...

end SyntacticCircuit
