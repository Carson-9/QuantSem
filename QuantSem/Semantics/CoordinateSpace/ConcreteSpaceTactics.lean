/-
Copyright (c) 2026 William Hasley. All rights reserved.
Released under GNU GPL3 license as described in the file LICENSE.
Authors: William Hasley
-/

module

import QuantSem.Semantics.CoordinateSpace.ComplexSpaces
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.LinearAlgebra.Matrix.Reindex
public import Mathlib.Data.Matrix.Reflection
import Lean.Elab.Tactic

public theorem two_by_two_mul (M N : Matrix (Fin 2) (Fin 2) ℂ) :
  M * N = !![((M 0 0) * (N 0 0) + (M 0 1) * (N 1 0)), ((M 0 0) * (N 0 1) + (M 0 1) * (N 1 1));
            ((M 1 0) * (N 0 0) + (M 1 1) * (N 1 0)), ((M 1 0) * (N 0 1) + (M 1 1) * (N 1 1))] :=

  (Matrix.mulᵣ_eq _ _).symm

macro "unit_vector_simple" : tactic => `(tactic| rw[EuclideanSpace.norm_eq] <;> simp <;> field)
macro "unit_matrix_simple" : tactic => `(tactic| rw[Matrix.mem_unitaryGroup_iff] <;> ext i j <;> rw[ComplexSpaces.FinDimMatrixMul] <;> apply Complex.ext <;> fin_cases i <;> fin_cases j <;> simp <;> grind)
macro "two_by_two_matrix_simple" : tactic => `(tactic| rw[Matrix.mem_unitaryGroup_iff, two_by_two_mul] <;> simp)
