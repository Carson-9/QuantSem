/-
Copyright (c) 2026 William Hasley. All rights reserved.
Released under GNU GPL3 license as described in the file LICENSE.
Authors: William Hasley
-/

import QuantSem.StdLib.CoordinateSpace.CoordinateSpace
import QuantSem.StdLib.Constructions.QubitControl
import Mathlib.Data.Complex.Basic

open BasisCircuitList
open AbstractBasisRegister
open BasisState
open BasisGate
open ComplexSpaces
open CoordinateSpace
open QubitControl


noncomputable def qubit_zero : BasisStateSpace QubitSpace := UnitVectorToState ⟨ !₂[(1 : ℂ), 0], by unit_vector_simple ⟩
noncomputable def qubit_one : BasisStateSpace QubitSpace := UnitVectorToState ⟨ !₂[(0 : ℂ), 1], by unit_vector_simple ⟩
noncomputable def qubit_plus  : BasisStateSpace QubitSpace := UnitVectorToState ⟨ (√2)⁻¹ • !₂[(1 : ℂ), 1], by unit_vector_simple ⟩
noncomputable def qubit_minus  : BasisStateSpace QubitSpace := UnitVectorToState ⟨ (√2)⁻¹ • !₂[(1 : ℂ), -1], by unit_vector_simple ⟩

noncomputable def hadamard : BasisGateType QubitSpace QubitSpace := MatrixToGate ⟨ (((√2)⁻¹ : ℂ) • !![(1 : ℂ), 1; 1, -1]), by unit_matrix_simple ⟩
noncomputable def rotation (k : ℤ) : BasisGateType QubitSpace QubitSpace :=
  MatrixToGate ⟨!![(1 : ℂ), 0; 0, (Complex.exp (2 * Real.pi * Complex.I * (2 ^ (-k))))],
   by sorry⟩



noncomputable def WireFamily (n : ℕ) : List BasisRegister := List.replicate (n + 1) QubitSpace
@[simp]
public theorem WireFamiltyAtZero : WireFamily 0 = [QubitSpace] := by rfl

noncomputable def QFT (n : ℕ) : BasisListCircuit :=
  InductiveCircuit WireFamily baseCase ind n where
  baseCase : BasisCircuitOverList (WireFamily 0) := BasisCircuitOverList.Gate (↑hadamard)
  ind (k : ℕ) (c : BasisCircuitOverList (WireFamily k)) : BasisCircuitOverList (WireFamily (k + 1))
  :=  _ -- BasisCircuitOverList.HorizontalComp
      -- (BasisCircuitOverList.VerticalComp )
      -- (BasisCircuitOverList.HorizontalComp
      -- ()
      -- ())
