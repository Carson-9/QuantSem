/-
Copyright (c) 2026 William Hasley. All rights reserved.
Released under GNU GPL3 license as described in the file LICENSE.
Authors: William Hasley
-/


module

public import Mathlib.CategoryTheory.Monoidal.Category
public import QuantSem.Syntax.WithBasis.BasisRegister
public import QuantSem.Syntax.Category.State

open BasisRegister
open SyntacticState
open CategoryTheory
namespace BasisState

public abbrev BasisStateSpace (R : TypeBasisRegister) : Type := QuantumStateSpace (BasisRegToQuantReg R)
public abbrev TypeBasisState : Type 1 := Σ R : TypeBasisRegister, BasisStateSpace R

public abbrev TypeBasisState.space (S : TypeBasisState) := S.fst
public abbrev TypeBasisState.state (S : TypeBasisState) := S.snd

@[expose]
public noncomputable def GetBasisState {R : TypeBasisRegister} (i : R.indexing) : BasisStateSpace R :=
  (QuantumStateSelection (R.struct.toBasis i) (R.struct.isOrthonormal.left i))

public theorem BasisStatesOrthogonal {R : TypeBasisRegister} (i j : R.indexing) :
  i ≠ j →
  R.struct.inner ((GetBasisState i).toFun (1 : ℂ)) ((GetBasisState j).toFun (1 : ℂ)) = 0 :=
  by unfold GetBasisState; simp; apply R.struct.isOrthonormal.right

public theorem GetBasisStateAtOne {R : TypeBasisRegister} (i : R.indexing) :
  (GetBasisState i).toFun (1 : ℂ) = R.struct.toBasis i := by unfold GetBasisState; simp

-- This does not obscure the register's norm down the line
public noncomputable def BasisStateSelection {R : TypeBasisRegister} (x : R.space) (hNorm : ‖x‖ = 1) :
  BasisStateSpace R := QuantumTypes.ElementInSpaceAsIso R.space x (by intro hAbs; rw[hAbs] at hNorm; rw[norm_zero] at hNorm; apply zero_ne_one at hNorm; apply hNorm)

/-
    Basis state tensor / NEED BECAUSE BRUTEFORCE CATEGORY
-/

@[expose]
public noncomputable def BasisStateTensor {R1 R2 : TypeBasisRegister} (S1 : BasisStateSpace R1)
  (S2 : BasisStateSpace R2) : MonCatBasisReg'.tensorUnit ⟶ R1 ⊗ᵣ R2 :=
  ((MonCatBasisReg'.leftUnitor MonCatBasisReg'.tensorUnit).inv ≫ (S1 ⊗ₕ S2))

@[expose]
public noncomputable def BasisStateTensor' (S1 S2 : TypeBasisState) : TypeBasisState :=
  ⟨ S1.space ⊗ᵣ S2.space, @BasisStateTensor S1.space S2.space S1.state S2.state ⟩


notation S1 "⊗ₛ" S2 => BasisStateTensor' S1 S2


end BasisState
