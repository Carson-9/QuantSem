/-
Copyright (c) 2026 William Hasley. All rights reserved.
Released under GNU GPL3 license as described in the file LICENSE.
Authors: William Hasley
-/


module


public import Mathlib.Analysis.InnerProductSpace.Adjoint

open ContinuousLinearMap InnerProductSpace
open scoped InnerProduct ComplexInnerProductSpace

namespace QuantumTypes

public class HilbertSpace (E : Type) extends NormedAddCommGroup E, InnerProductSpace ℂ E
  -- where
  -- An inner product space defines a norm (more than the seminorm promised)
  -- norm_derived_from_inner : norm = InnerProductSpace.toNormedSpace.norm

public class QuantumType (E : Type) extends HilbertSpace E where
  vecAdd : E → E → E := HilbertSpace.toNormedAddCommGroup.add
  innerProd : E → E → ℂ := HilbertSpace.toInnerProductSpace.inner
  norm := Norm.norm

@[expose]
public def TypeQuantumTypes : Type 1 := Σ E, QuantumType E

end QuantumTypes
