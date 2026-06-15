/-
Copyright (c) 2026 William Hasley. All rights reserved.
Released under GNU GPL3 license as described in the file LICENSE.
Authors: William Hasley
-/


module

public import Mathlib.Analysis.Normed.Operator.LinearIsometry
public import Mathlib.Algebra.Module.LinearMap.Defs

public import QuantSem.Syntax.HighLevel.Register
public import QuantSem.Syntax.HighLevel.State
public import QuantSem.Syntax.HighLevel.QuantumTypes

namespace SyntacticGate


open SyntacticRegister
open SyntacticState
open QuantumTypes
open ContinuousLinearMap

variable [QuantumRegisterAlgebra]
variable (R₁ R₂ : Type) [R₁' : QuantReg R₁] [R₂' : QuantReg R₂]

@[expose]
public def QuantumGate : Type :=  R₁ →ₗᵢ[ℂ] R₂
public abbrev TypeQuantumGate := Σ E : TypeQuantumRegister, Σ F : TypeQuantumRegister,
  @QuantumGate E.fst F.fst E.snd F.snd


@[expose, coe]
public def QuantumGateToTypeQuantumGate (g : QuantumGate R₁ R₂) :
  TypeQuantumGate := ⟨⟨R₁, R₁'⟩, ⟨⟨R₂, R₂'⟩, g⟩⟩

@[expose, coe, reducible]
public def TypeQuantumGateToGate (g : TypeQuantumGate) :
  @QuantumGate g.fst.fst g.snd.fst.fst g.fst.snd g.snd.fst.snd := g.snd.snd

public def GateStateEvolve (g : QuantumGate R₁ R₂) (s : QuantumStateSpace R₁)
  : QuantumStateSpace R₂ :=
  Subtype.mk (g.toLinearMap s.val)
  (by rw [LinearIsometry.norm_map' g s.val]; apply s.prop)

public def GateComp {R₁ R₂ R₃ : Type} [QuantReg R₁] [QuantReg R₂] [QuantReg R₃]
  (g1 : QuantumGate R₁ R₂) (g2 : QuantumGate R₂ R₃) : QuantumGate R₁ R₃ :=
    LinearIsometry.comp g2 g1


@[expose]
public def QuantumGate' (R1 R2 : TypeQuantumRegister) : Type :=
  @QuantumGate R1.fst R2.fst R1.snd R2.snd

@[expose, coe]
public def GateToGate' {R1 R2: Type} [R1' : QuantReg R1] [R2' : QuantReg R2]
  (g : @QuantumGate R1 R2 R1' R2') : QuantumGate' ⟨R1, R1'⟩ ⟨R2, R2'⟩ := g

@[default_instance]
instance (R1 R2 : Type) [QuantReg R1] [QuantReg R2] : Coe (QuantumGate R1 R2) (QuantumGate' (QuantRegToTypeQuantumRegister R1) (QuantRegToTypeQuantumRegister R2)) where
  coe := GateToGate'

@[expose, coe]
public def Gate'ToGate {R1 R2 : TypeQuantumRegister} (g : QuantumGate' R1 R2) :
  @QuantumGate R1.fst R2.fst R1.snd R2.snd := g

@[default_instance]
instance (R1 R2 : TypeQuantumRegister) : Coe (QuantumGate' R1 R2) (@QuantumGate R1.fst R2.fst R1.snd R2.snd) where
  coe := Gate'ToGate

@[expose, coe]
public def Gate'ToTypeGate {R1 R2 : TypeQuantumRegister} (g : QuantumGate' R1 R2)
  : TypeQuantumGate := ⟨R1, ⟨R2, g⟩⟩

@[expose, coe]
public def TypeGateToGate' (g : TypeQuantumGate) : QuantumGate' g.fst g.snd.fst :=
  g.snd.snd
--instance {R1 R2 : TypeQuantumRegister} : Coe (QuantumGate' R1 R2) TypeQuantumGate where
--  coe := Gate'ToTypeGate


public def GateStateEvolve' {R1 R2 : TypeQuantumRegister} (g : QuantumGate' R1 R2)
  (s : QuantumStateSpace' R1) : QuantumStateSpace' R2 :=
    @GateStateEvolve R1.fst R2.fst R1.snd R2.snd g s

public def GateComp' {R1 R2 R3 : TypeQuantumRegister} (g1 : QuantumGate' R1 R2) (g2 : QuantumGate' R2 R3)
  : QuantumGate' R1 R3 :=
  @GateComp R1.fst R2.fst R3.fst R1.snd R2.snd R3.snd (Gate'ToGate g1) (Gate'ToGate g2)


public class QuantumGateAlgebra extends Monoid TypeQuantumGate where
  mulFun := toSemigroup.toMul.mul
  liftMap (G1 G2 : TypeQuantumGate) :
     ((toSemigroup.toMul.mul G1 G2).fst.fst) →
      QuantumGate' ((G1.fst) ⊗ᵣ (G2.fst)) ((G1.snd.fst) ⊗ᵣ (G2.snd.fst))

/-
        G(R) ⊗ₘ G(R)
         /\         \
         |            \   ∃!
         |             \/
      R ⊗ᵣ R --------> G(R ⊗ᵣ R)
-/



notation A "⊗ₘ" B => QuantumGateAlgebra.mulFun A B
notation g2 "∘" g1 => GateComp g1 g2
notation g2 "∘'" g1 => GateComp' g1 g2

end SyntacticGate
