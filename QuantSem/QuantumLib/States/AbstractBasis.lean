/-
Copyright (c) 2026 William Hasley. All rights reserved.
Released under GNU GPL3 license as described in the file LICENSE.
Authors: William Hasley
-/


module

public import QuantSem.LeanTools.Attributes
public import Mathlib.CategoryTheory.Monoidal.Category
public import QuantSem.QuantumLib.Registers.AbstractBasis
public import QuantSem.QuantumLib.States.Basic

open AbstractBasisRegister
open SyntacticState
open CategoryTheory
namespace BasisState

public abbrev BasisStateSpace (R : BasisRegister) : Type := QuantumStateSpace R

@[expose]
public noncomputable def GetBasisState {R : BasisRegister} (i : R.indexing) : BasisStateSpace R :=
  (QuantumStateSelection (R.struct.toBasis i) (R.struct.isOrthonormal.left i))

public theorem BasisStatesOrthogonal {R : BasisRegister} (i j : R.indexing) :
  i ≠ j →
  R.struct.inner ((GetBasisState i).toFun (1 : ℂ)) ((GetBasisState j).toFun (1 : ℂ)) = 0 :=
  by unfold GetBasisState; simp; apply R.struct.isOrthonormal.right

public theorem GetBasisStateAtOne {R : BasisRegister} (i : R.indexing) :
  (GetBasisState i).toFun (1 : ℂ) = R.struct.toBasis i := by unfold GetBasisState; simp

-- nice instance lol
-- @[find_better]
public noncomputable instance {R : BasisRegister} : Coe (BasisStateSpace R) (BasisStateSpace (⨂ᵣ [R])) where
  coe := fun s => by simp; exact s ≫ (IsoPromote.symm (BasisMulTensorSingletonIso R)).hom

end BasisState
