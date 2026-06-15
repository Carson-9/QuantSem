/-
Copyright (c) 2026 William Hasley. All rights reserved.
Released under GNU GPL3 license as described in the file LICENSE.
Authors: William Hasley
-/


module

public import Mathlib.CategoryTheory.Monoidal.Category
public import QuantSem.Syntax.HighLevel.Register

open SyntacticRegister QuantumTypes
namespace SyntacticState

variable (R : Type) [QuantReg R]

@[expose]
public def QuantumStateSpace := { x : R // ‖x‖ = 1}
public abbrev TypeQuantumStates : Type 1 :=
  Σ E : TypeQuantumRegister, @QuantumStateSpace E.fst E.snd

@[expose, coe]
public def QuantumSpaceInSpaceCoe (x : TypeQuantumStates)
  : @QuantumStateSpace x.fst.fst x.fst.snd :=
  Subtype.mk x.snd.val x.snd.prop

@[expose, coe, reducible]
public def TypeQuantumStatesToQuantumStateSpace (s : TypeQuantumStates) :
  @QuantumStateSpace s.fst.fst s.fst.snd := s.snd


@[expose]
public def QuantumStateSpace' (R : TypeQuantumRegister) : Type := @QuantumStateSpace R.fst R.snd

@[expose, coe]
public def StateToState' {R : Type} [R' : QuantReg R] (s : QuantumStateSpace R)
  : QuantumStateSpace' (QuantRegToTypeQuantumRegister R) :=
    Subtype.mk s.val s.prop

@[default_instance]
instance (R : Type) [QuantReg R] : Coe (QuantumStateSpace R) (QuantumStateSpace' (QuantRegToTypeQuantumRegister R)) where
  coe := StateToState'

@[expose, coe]
public def State'ToState {R : TypeQuantumRegister} (s : @QuantumStateSpace' R) :
  @QuantumStateSpace R.fst R.snd := Subtype.mk s.val s.prop

@[default_instance]
instance (R : TypeQuantumRegister) : Coe (QuantumStateSpace' R) (@QuantumStateSpace R.fst R.snd) where
  coe := State'ToState



variable [C : QuantumRegisterAlgebra]

@[expose]
public def QuantumStateSpace'' (R : TypeQuantumRegister) : Type := C.Hom C.tensorUnit R
@[expose]
public def TypeQuantumStates'' : Type 1 := Σ R : TypeQuantumRegister, QuantumStateSpace'' R

public def StateTensor {R1 R2 : TypeQuantumRegister} (s1 : QuantumStateSpace'' R1)
  (s2 : QuantumStateSpace'' R2) : QuantumStateSpace'' (R1 ⊗ᵣ R2) :=
  @C.compHom
    C.tensorUnit
    (C.tensorUnit ⊗ᵣ C.tensorUnit)
    (R1 ⊗ᵣ R2)

    (((C.lUnit (C.tensorUnit)).inv) : C.tensorUnit ⟶ (C.tensorUnit ⊗ᵣ C.tensorUnit))    -- I ⟶ I ⊗ I
    (C.morphMul s1 s2)                -- I ⊗ I ⟶ s1 ⊗ s2

notation A "⊗ₛ" B => QuantumRegisterAlgebra.morphMul A B

public def QuantumState.MulTensor
  (famReg : List TypeQuantumStates'') (buffer : TypeQuantumStates'') (fstRound : Bool) :=
  match famReg with
  | [] => buffer
  | h :: t => if fstRound then QuantumState.MulTensor t h false
                          else QuantumState.MulTensor t (buffer ⊗ₛ h) false

notation "⨂ₛ" l => QuantumState.MulTensor l QuantumStateAlgebra.one true



end SyntacticState
