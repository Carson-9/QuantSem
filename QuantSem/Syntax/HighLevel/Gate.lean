/-
Copyright (c) 2026 William Hasley. All rights reserved.
Released under GNU GPL3 license as described in the file LICENSE.
Authors: William Hasley
-/


module

public import QuantSem.Syntax.HighLevel.Register
public import QuantSem.Syntax.HighLevel.State
public import QuantSem.Syntax.HighLevel.QuantumTypes

namespace SyntacticGate


open SyntacticRegister
open SyntacticState
open QuantumTypes
open ContinuousLinearMap

@[default_instance 101]
instance (R : QuantumRegister) : SeminormedAddCommGroup R.fst :=
  R.snd.toSeminormedAddCommGroup

@[default_instance]
instance (R : QuantumRegister) : QuantumTypes.HilbertSpace R.fst :=
  R.snd.toHilbertSpace

@[expose]
public def QuantumGate (R : QuantumRegister) [HilbertSpace R.fst] : Type := R.fst →ₗᵢ[ℂ] R.fst where
  need := R.snd.toSeminormedAddCommGroup
public abbrev TypeQuantumGate := Σ R : QuantumRegister, @QuantumGate R R.snd.toHilbertSpace


public def GateStateEvolve (R : QuantumRegister) [HilbertSpace R.fst] (g : QuantumGate R) (s : QuantumStateSpace R)
  : QuantumStateSpace R :=
  Subtype.mk (g.toFun)
  (by trans; apply (LinearIsometry.norm_map' g s.val); apply s.prop)


public class QuantumGateAlgebra extends Monoid TypeQuantumGate where
  mul := Mul.mul
  liftMap {C : QuantumRegisterAlgebra} (G1 G2 : TypeQuantumGate) :
    ((mul G1 G2).fst.fst) → @QuantumGate (C.mul (G1.fst) (G2.fst))
      ((C.mul (G1.fst) (G2.fst)).snd.toHilbertSpace)

/-
        G(R) ⊗ₘ G(R)
         /\         \
         |            \   ∃!
         |             \/
      R ⊗ᵣ R --------> G(R ⊗ᵣ R)
-/



notation A "⊗ₘ" B => QuantumGateAlgebra.mul A B

end SyntacticGate
