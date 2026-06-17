/-
Copyright (c) 2026 William Hasley. All rights reserved.
Released under GNU GPL3 license as described in the file LICENSE.
Authors: William Hasley
-/

module

public import QuantSem.Syntax.Category.Circuit

open SyntacticCircuit
namespace SyntacticCircuitComplexity


-- public theorem SimpleCircuitDepthGeOne {R : TypeQuantumRegister}
--   : ∀ c : SimpleCircuitOverRegister R, 1 ≤ SimpleCircuitDepth c
--   :=  by intro c; induction c with
--   | IdWire => unfold SimpleCircuitDepth; rfl
--   | Gate g => unfold SimpleCircuitDepth; rfl
--   | HorizontalComp c1 c2 i1 i2 => unfold SimpleCircuitDepth; calc
--       1 ≤ 1 + 1 := by simp
--       _ ≤ SimpleCircuitDepth c1 + 1 := by apply (@ENat.add_le_add_iff_right (SimpleCircuitDepth c1) 1 1 (by apply ENat.coe_ne_top (SimpleCircuitDepth c1)))
--       _ ≤ SimpleCircuitDepth c1 + SimpleCircuitDepth c2
--   | VerticalComp c1 c2 =>
--
-- public theorem SimpleCircuitDepthDecreasesHL {R : TypeQuantumRegister}
--   : ∀ c1 c2 : SimpleCircuitOverRegister R, SimpleCircuitDepth c1 < SimpleCircuitDepth (HorizontalComp c1 c2)
--   := by intro c1 c2; unf



end SyntacticCircuitComplexity
