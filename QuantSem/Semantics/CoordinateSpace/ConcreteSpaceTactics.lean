/-
Copyright (c) 2026 William Hasley. All rights reserved.
Released under GNU GPL3 license as described in the file LICENSE.
Authors: William Hasley
-/

module

import QuantSem.Semantics.CoordinateSpace.ComplexSpaces
import Lean.Elab.Tactic

macro "unit_vector_simple" : tactic => `(tactic| rw[EuclideanSpace.norm_eq] <;> simp <;> field)
macro "unit_matrix_simple" : tactic => `(tactic| rw[Matrix.mem_unitaryGroup_iff])
