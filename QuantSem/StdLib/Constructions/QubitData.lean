/-
Copyright (c) 2026 William Hasley. All rights reserved.
Released under GNU GPL3 license as described in the file LICENSE.
Authors: William Hasley
-/

module

public import QuantSem.StdLib.CoordinateSpace.ComplexSpaces
public import QuantSem.StdLib.CoordinateSpace.ConcreteSpaceTactics

namespace QubitData

open AbstractBasisRegister
open BasisState
open BasisGate
open SyntacticGate
open ComplexSpaces
open CategoryTheory

public noncomputable def qubit_zero    : BasisStateSpace QubitSpace  := UnitVectorToState ⟨ !₂[(1 : ℂ), 0], by unit_vector_simple ⟩
public noncomputable def qubit_one     : BasisStateSpace QubitSpace  := UnitVectorToState ⟨ !₂[(0 : ℂ), 1], by unit_vector_simple ⟩
public noncomputable def qubit_plus    : BasisStateSpace QubitSpace  := UnitVectorToState ⟨ (√2)⁻¹ • !₂[(1 : ℂ), 1], by unit_vector_simple ⟩
public noncomputable def qubit_minus   : BasisStateSpace QubitSpace  := UnitVectorToState ⟨ (√2)⁻¹ • !₂[(1 : ℂ), -1], by unit_vector_simple ⟩

notation "|0⟩" => qubit_zero
notation "|1⟩" => qubit_one
notation "|+⟩" => qubit_plus
notation "|-⟩" => qubit_minus

public noncomputable def hadamard   : BasisGateType QubitSpace QubitSpace  := MatrixToGate ⟨ (((√2)⁻¹ : ℂ) • !![(1 : ℂ), 1; 1, -1]), by unit_matrix_simple ⟩
public noncomputable def pauli_x    : BasisGateType QubitSpace QubitSpace  := MatrixToGate ⟨!![0, 1 ; 1 , 0], by unit_matrix_simple  ⟩
public noncomputable def pauli_y    : BasisGateType QubitSpace QubitSpace  := MatrixToGate ⟨!![0, -Complex.I ; Complex.I , 0], by unit_matrix_simple  ⟩
public noncomputable def pauli_z    : BasisGateType QubitSpace QubitSpace  := MatrixToGate ⟨!![1, 0 ; 0 , -1], by unit_matrix_simple ⟩

public noncomputable def rotation (k : ℤ) : BasisGateType QubitSpace QubitSpace := MatrixToGate ⟨!![(1 : ℂ), 0; 0, (Complex.exp ((2 : ℝ) * Real.pi * Complex.I * ((2 ^ (-k)) : ℝ)))],
   by two_by_two_matrix_simple; rw[mul_comm, <- Complex.normSq_eq_conj_mul_self]; simp; rw[mul_comm, <- mul_assoc, Complex.normSq_eq_norm_sq];
         simp; left; rw[Complex.norm_exp]; simp; left; rw[Complex.im_eq_zero_iff_isSelfAdjoint]; unfold IsSelfAdjoint; simp⟩


public theorem hadamard_zero : |0⟩ ≫ hadamard = |+⟩ := by
    --unfold qubit_zero hadamard qubit_plus; rw[MatrixStateEvolve]; simp; ext i;
    --      fin_cases i; simp;
    sorry


end QubitData
