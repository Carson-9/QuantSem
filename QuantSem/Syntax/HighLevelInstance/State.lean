/-
Copyright (c) 2026 William Hasley. All rights reserved.
Released under GNU GPL3 license as described in the file LICENSE.
Authors: William Hasley
-/


module

public import QuantSem.Syntax.HighLevelInstance.Register
public import QuantSem.Syntax.HighLevelInstance.QuantumTypes

open SyntacticRegister QuantumTypes
namespace SyntacticState

variable (R : Type) [QuantReg R]

@[expose]
public def QuantumStateSpace := { x : R // ‖x‖ = 1}
public abbrev TypeQuantumStates : Type 1 :=
  Σ E : TypeQuantumRegister, @QuantumStateSpace E.fst E.snd

public class QuantumStateAlgebra extends Monoid TypeQuantumStates where
  mul := Mul.mul
  liftMap {C : QuantumRegisterAlgebra} (s1 s2 : TypeQuantumStates) :
    ((mul s1 s2).fst.fst) →
      @QuantumStateSpace (C.mul (s1.fst) (s2.fst)).fst (C.mul (s1.fst) (s2.fst)).snd
  /- Not useful here for now, may have surprises later, but very easily fixable! -/
  /- univPropertyInj : Injective liftMap -/
/-

We may wish to respect the universal property of tensor product : Lifting must
respect the intended injection of decomposable state into the state of register-tensor

     S(R) ⊗ₛ S(R)
         /\         \
         |            \   ∃!
         |             \/
      R ⊗ᵣ R --------> S(R ⊗ᵣ R)


-/

notation A "⊗ₛ" B => QuantumStateAlgebra.mul A B

public def QuantumState.MulTensor {S : QuantumStateAlgebra}
  (famReg : List TypeQuantumStates) (buffer : TypeQuantumStates) (fstRound : Bool) :=
  match famReg with
  | [] => buffer
  | h :: t => if fstRound then @QuantumState.MulTensor S t h false
                          else @QuantumState.MulTensor S t (S.mul buffer h) false

notation "⨂ₛ" l => QuantumState.MulTensor l QuantumStateAlgebra.one true


notation "| " ψ " ⟩" => (ψ : QuantumStateSpace)

/- TODO : Continue denotational stuff.
notation "⟨ " ψ " |" => (ψ†)
-/

end SyntacticState
