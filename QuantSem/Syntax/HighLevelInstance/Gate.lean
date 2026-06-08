/-
Copyright (c) 2026 William Hasley. All rights reserved.
Released under GNU GPL3 license as described in the file LICENSE.
Authors: William Hasley
-/


module

public import QuantSem.Syntax.HighLevelInstance.Register
public import QuantSem.Syntax.HighLevelInstance.State
public import QuantSem.Syntax.HighLevelInstance.QuantumTypes

namespace SyntacticGate


open SyntacticRegister
open SyntacticState
open QuantumTypes
open ContinuousLinearMap

variable (R₁ R₂ : Type) [QuantReg R₁] [QuantReg R₂]

@[expose]
public def QuantumGate : Type :=  R₁ →ₗᵢ[ℂ] R₂
public abbrev TypeQuantumGate := Σ E : TypeQuantumRegister, Σ F : TypeQuantumRegister,
  @QuantumGate E.fst F.fst E.snd F.snd


public def GateStateEvolve (g : QuantumGate R₁ R₂) (s : QuantumStateSpace R₁)
  : QuantumStateSpace R₂ :=
  Subtype.mk (g.toLinearMap s.val)
  (by rw [LinearIsometry.norm_map' g s.val]; apply s.prop)


public class QuantumGateAlgebra extends Monoid TypeQuantumGate where
  mul := Mul.mul
  liftMap {C : QuantumRegisterAlgebra} (G1 G2 : TypeQuantumGate) :
    ((mul G1 G2).fst.fst) →
      @QuantumGate (C.mul (G1.fst) (G2.fst)).fst (C.mul (G1.snd.fst) (G2.snd.fst)).fst
        ((C.mul (G1.fst) (G2.fst)).snd) ((C.mul (G1.snd.fst) (G2.snd.fst)).snd)

/-
        G(R) ⊗ₘ G(R)
         /\         \
         |            \   ∃!
         |             \/
      R ⊗ᵣ R --------> G(R ⊗ᵣ R)
-/



notation A "⊗ₘ" B => QuantumGateAlgebra.mul A B

end SyntacticGate
