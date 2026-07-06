/-
Copyright (c) 2026 William Hasley. All rights reserved.
Released under GNU GPL3 license as described in the file LICENSE.
Authors: William Hasley
-/

import QuantSem.Semantics.CoordinateSpace.CoordinateSpace

open BasisRegister
open BasisState
open BasisGate
open ComplexSpaces
open CoordinateSpace



noncomputable def qubit_zero : BasisStateSpace QubitSpace :=
  UnitVectorToState ⟨ !₂[(1 : ℂ), 0], by unit_vector_simple ⟩
noncomputable def qubit_one : BasisStateSpace QubitSpace :=
  UnitVectorToState ⟨ !₂[(0 : ℂ), 1], by unit_vector_simple ⟩
noncomputable def qubit_plus  : BasisStateSpace QubitSpace :=
  UnitVectorToState ⟨ (√2)⁻¹ • !₂[(1 : ℂ), 1], by unit_vector_simple ⟩
noncomputable def qubit_minus  : BasisStateSpace QubitSpace :=
  UnitVectorToState ⟨ (√2)⁻¹ • !₂[(1 : ℂ), -1], by unit_vector_simple ⟩

noncomputable def hadamard : BasisGateType QubitSpace QubitSpace := MatrixToGate ⟨ (((√2)⁻¹ : ℂ) • !![(1 : ℂ), 1; 1, -1]), by unit_matrix_simple ⟩
noncomputable def pauli_x : BasisGateType QubitSpace QubitSpace  := MatrixToGate ⟨!![0, 1 ; 1 , 0], by unit_matrix_simple  ⟩
noncomputable def pauli_z : BasisGateType QubitSpace QubitSpace  := MatrixToGate ⟨!![1, 0 ; 0 , -1], by unit_matrix_simple ⟩


open BasisCircuitList
open BasisCircuitOverList

noncomputable def a_simple_circuit_part : BasisCircuitOverList [QubitSpace, QubitSpace]
  := VerticalComp (HorizontalComp (@Gate [QubitSpace] hadamard) (Gate pauli_z)) (Gate pauli_x)

-- Build a circuit by Induction
noncomputable def a_bad_recursive_circuit_explained (n : ℕ) : TypeBasisCircuitList :=
  InductiveCircuit [QubitSpace, QubitSpace] a_simple_circuit_part (fun l => QubitSpace :: l)
    (fun R c =>
    HorizontalComp
      (VerticalComp c (@Gate [QubitSpace] pauli_x))
      (VerticalComp (@Gate [QubitSpace] pauli_z) c))


-- Another inductive notion that allows for a restrained family of circuit signature,
-- which allows lean to typecheck the circuit family

@[simp]
noncomputable def my_shape_iter (n : ℕ) : List TypeBasisRegister := List.replicate (n + 2) QubitSpace

@[simp]
theorem my_shape_iter_induction (n : ℕ) : my_shape_iter (n + 1) = ((my_shape_iter n) ++ [QubitSpace])
  := by unfold my_shape_iter; sorry -- to prove

noncomputable def a_bad_recursive_circuit_better (n : ℕ) : TypeBasisCircuitList :=
  ⟨my_shape_iter n, (InductiveCircuit' my_shape_iter base_case ind) n⟩ where

  base_case : BasisCircuitOverList (my_shape_iter 0) := a_simple_circuit_part
  ind (n : ℕ) (c : BasisCircuitOverList (my_shape_iter n)) : BasisCircuitOverList (my_shape_iter (n + 1))
    :=
    HorizontalComp
    (VerticalComp c (@Gate [QubitSpace] pauli_x))
    (VerticalComp (@Gate [QubitSpace] pauli_z) c)
