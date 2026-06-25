/-
Copyright (c) 2026 William Hasley. All rights reserved.
Released under GNU GPL3 license as described in the file LICENSE.
Authors: William Hasley
-/


module

public import Mathlib.CategoryTheory.Monoidal.Category
public import Mathlib.LinearAlgebra.TensorProduct.Defs
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


@[expose]
public noncomputable def QuantumStateSelection {R : TypeQuantumRegister} (x : R.space) (hNorm : ‖x‖ = 1)
  : QuantumStateSpace R :=
  ElementInSpaceAsIso R.space x (by intro hAbs; rw[hAbs] at hNorm; rw[norm_zero] at hNorm; apply zero_ne_one at hNorm; apply hNorm)

@[simp]
public theorem StateSelectionOfOne  {R : TypeQuantumRegister} (x : R.space) (hNorm : ‖x‖ = 1) :
  (QuantumStateSelection x hNorm).toFun (1 : ℂ) = x := by unfold QuantumStateSelection; rw[ElementInSpacePointsTo]; rw[hNorm]; simp

@[simp]
public theorem StateExtAtOne {R : TypeQuantumRegister} (x y : R.space) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
  : (QuantumStateSelection x hx).toFun (1 : ℂ) = (QuantumStateSelection y hy).toFun (1 : ℂ)
    → (QuantumStateSelection x hx) = (QuantumStateSelection y hy) :=
  by intro hyp; unfold QuantumStateSelection; apply LinearIsometry.ext; intro z;
     unfold ElementInSpaceAsIso; simp; simp at hyp; rw [hyp];

public theorem StateEqualAreAtOne {R : TypeQuantumRegister} (x y : R.space) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
  : (QuantumStateSelection x hx) = (QuantumStateSelection y hy) →
    (QuantumStateSelection x hx).toFun (1 : ℂ) = (QuantumStateSelection y hy).toFun (1 : ℂ)
  := by intro hyp; rw[hyp]


/-
    True extensionality for states
-/

@[ext]
public theorem StateExt {R : TypeQuantumRegister} (s1 s2 : QuantumStateSpace R) :
  s1.toFun (1 : ℂ) = s2.toFun (1 : ℂ) → s1 = s2 :=
  by rw[LinearIsometriesOnCAgree' s1 s2]; intro h; apply h

/-
    States are "unitaries"
-/

public theorem StateNormAtOne {R : TypeQuantumRegister} (s : QuantumStateSpace R) :
  ‖s.toFun (1 : ℂ)‖ = ‖(1 : ℂ)‖ := by apply LinearIsometry.norm_map


end SyntacticState
