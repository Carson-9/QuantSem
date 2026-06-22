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


@[expose]
public noncomputable def GetBasisState {R : TypeBasisRegister} (i : R.indexing) : BasisStateSpace R :=
  (QuantumStateSelection (R.struct.toBasis i) (R.struct.isOrthonormal.left i))

public theorem BasisStatesOrthogonal {R : TypeBasisRegister} (i j : R.indexing) :
  i ≠ j →
  R.struct.inner ((GetBasisState i).toFun (1 : ℂ)) ((GetBasisState j).toFun (1 : ℂ)) = 0 :=
  by unfold GetBasisState; simp; apply R.struct.isOrthonormal.right

public theorem GetBasisStateAtOne {R : TypeBasisRegister} (i : R.indexing) :
  (GetBasisState i).toFun (1 : ℂ) = R.struct.toBasis i := by unfold GetBasisState; simp

end BasisState
