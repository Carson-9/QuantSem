/-
Copyright (c) 2026 William Hasley. All rights reserved.
Released under GNU GPL3 license as described in the file LICENSE.
Authors: William Hasley
-/


module

public import Mathlib.CategoryTheory.Monoidal.Category
public import QuantSem.Syntax.Category.Register

open SyntacticRegister QuantumTypes
open CategoryTheory
namespace SyntacticState


/-
    A State is represented as a Morphism S : ℂ ⟶ R, where the "actual" content is S(1 / ‖1‖)
 -/

public abbrev QuantumStateSpace (R : TypeQuantumRegister) : Type := MonCatRegister.tensorUnit ⟶ R
public abbrev TypeQuantumState : Type 1 := Σ R : TypeQuantumRegister, QuantumStateSpace R

public abbrev TypeQuantumState.space (S : TypeQuantumState) := S.fst
public abbrev TypeQuantumState.state (S : TypeQuantumState) := S.snd

public noncomputable def QuantumStateTensor {R1 R2 : TypeQuantumRegister} (S1 : QuantumStateSpace R1)
  (S2 : QuantumStateSpace R2) : MonCatRegister.tensorUnit ⟶ R1 ⊗ᵣ R2 :=
  ((MonCatRegister.leftUnitor MonCatRegister.tensorUnit).inv ≫ (S1 ⊗ₕ S2))

public noncomputable def QuantumStateTensor' (S1 S2 : TypeQuantumState) : TypeQuantumState :=
  ⟨ S1.space ⊗ᵣ S2.space, @QuantumStateTensor S1.space S2.space S1.state S2.state ⟩


notation S1 "⊗ₛ" S2 => QuantumStateTensor' S1 S2

public noncomputable def QuantumState.MulTensor
  (famReg : List TypeQuantumState) (buffer : TypeQuantumState) (fstRound : Bool) :=
  match famReg with
  | [] => buffer
  | h :: t => if fstRound then QuantumState.MulTensor t h false
                          else QuantumState.MulTensor t (buffer ⊗ₛ h) false

notation "⨂ₛ" l => QuantumState.MulTensor l MonCatRegister.tensorUnit true



end SyntacticState
