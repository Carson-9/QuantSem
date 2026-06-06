/-
Copyright (c) 2026 William Hasley. All rights reserved.
Released under GNU GPL3 license as described in the file LICENSE.
Authors: William Hasley
-/


module

public import QuantSem.Syntax.HighLevel.Register
public import QuantSem.Syntax.HighLevel.State

namespace SyntacticGate


open SyntacticRegister
open SyntacticState
open ContinuousLinearMap

@[default_instance 100]
instance (R : QuantumRegister) : SeminormedAddCommGroup R.fst :=
  R.snd.toSeminormedAddCommGroup

public def QuantumGate (R : QuantumRegister) : Type := (R.fst →ₗᵢ[ℂ] R.fst)
public abbrev TypeQuantumGate := Σ R : QuantumRegister, QuantumGate R

public class QuantumGateAlgebra extends Monoid TypeQuantumGate where
  mul := Mul.mul
  liftMap {C : QuantumRegisterAlgebra} (G1 G2 : TypeQuantumGate) :
    ((mul G1 G2).fst.fst) → QuantumGate ( C.mul (G1.fst) (G2.fst))

/-
        G(R) ⊗ₘ G(R)
         /\         \
         |            \   ∃!
         |             \/
      R ⊗ᵣ R --------> G(R ⊗ᵣ R)
-/



notation A "⊗ₘ" B => QuantumGateAlgebra.mul A B

def GateStateEvolve (R : QuantumRegister) (g : QuantumGate R) (s : QuantumStateSpace R)
  : QuantumStateSpace R :=
  ⟨(g.toFun s.val), by trans; apply (LinearIsometry.norm_map' g s.val); apply s.prop ⟩

end SyntacticGate
end
