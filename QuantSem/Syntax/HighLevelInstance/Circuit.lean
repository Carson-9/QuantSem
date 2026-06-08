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

public inductive SimpleCircuitOverRegister (R : Type) [QuantReg R] where
  | Gate (g : QuantumGate R R)
  | HorizontalComp (c1 c2 : SimpleCircuitOverRegister R)

public abbrev TypeSimpleCircuit := Σ R : TypeQuantumRegister, @SimpleCircuitOverRegister R.fst R.snd

public class SimpleCircuitAlgebra extends Monoid TypeSimpleCircuit where
  mul := Mul.mul
  liftMap (c1 c2 : TypeSimpleCircuit) :
    ((mul c1 c2).fst.fst) →
      @SimpleCircuitOverRegister (C.mul (c1.fst) (c2.fst)).fst (C.mul (c1.fst) (c2.fst)).snd
  /- univPropertyInj : Injective liftMap -/
/-
     C(R) ⊗ₖ C(R)
         /\         \
         |            \   ∃!
         |             \/
      R ⊗ₖ R --------> C(R ⊗ₖ R)

  Intuition : Composed circuits are a subclass of circuits over the composed space
-/

notation A "⊗ₖ" B =>  SimpleCircuitAlgebra.mul A B

--public def SimpleCircuit.MulTensor
--  {K : SimpleCircuitAlgebra}
--  (famReg : List TypeSimpleCircuit) (buffer : TypeSimpleCircuit) (fstRound : Bool) :=
--  match famReg with
--  | [] => buffer
--  | h :: t => if fstRound then @SimpleCircuit.MulTensor C S G K t h false
--                          else @SimpleCircuit.MulTensor C S G K t (@K.mul buffer h) false

--notation "⨂ₖ" l => SimpleCircuit.MulTensor l SimpleCircuitAlgebra.one true

variable (R : Type) [QuantReg R]

public def SimpleCircuitDepth (c : SimpleCircuitOverRegister R) : ℕ :=
  match c with
  | SimpleCircuitOverRegister.Gate _ => 1
  | SimpleCircuitOverRegister.HorizontalComp c1 c2 =>
    (SimpleCircuitDepth c1) + (SimpleCircuitDepth c2)


public def SimpleCircuitGateCount (c : SimpleCircuitOverRegister R) : ℕ :=
  match c with
  | SimpleCircuitOverRegister.Gate _ => 1
  | SimpleCircuitOverRegister.HorizontalComp c1 c2 =>
    (SimpleCircuitGateCount c1) + (SimpleCircuitGateCount c2)

public def SimpleCircuitGetShape {E : Type} [I : QuantReg E] :
  SimpleCircuitOverRegister E → TypeQuantumRegister :=
    fun _ => ⟨E, I⟩


public def EvolveState (c : SimpleCircuitOverRegister R)
  (s : QuantumStateSpace R) :
  QuantumStateSpace R :=
  match c with
  | SimpleCircuitOverRegister.Gate g => GateStateEvolve R R g s
  | SimpleCircuitOverRegister.HorizontalComp c1 c2 => EvolveState c2 (EvolveState c1 s)

end SyntacticCircuit
