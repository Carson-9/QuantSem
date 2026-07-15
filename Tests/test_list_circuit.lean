/-
Copyright (c) 2026 William Hasley. All rights reserved.
Released under GNU GPL3 license as described in the file LICENSE.
Authors: William Hasley
-/

import QuantSem.StdLib.CoordinateSpace.CoordinateSpace

open AbstractBasisRegister
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
noncomputable def my_shape_iter (n : ℕ) : List TypeBasisRegister := match n with
  | 0 => [QubitSpace, QubitSpace]
  | Nat.succ k => (my_shape_iter k) ++ [QubitSpace]
--List.replicate (n + 2) QubitSpace

@[simp]
theorem my_shape_iter_induction (n : ℕ) : my_shape_iter (n + 1) = ((my_shape_iter n) ++ [QubitSpace])
  := by rfl
@[simp]
theorem my_shape_iter_induction' (n : ℕ) : my_shape_iter (n + 1) = ([QubitSpace] ++ (my_shape_iter n))
  := by induction n with
    |zero => rfl
    |succ k ih => unfold my_shape_iter; rw[<- List.append_assoc]; rw[ih];

noncomputable def a_bad_recursive_circuit_better (n : ℕ) : TypeBasisCircuitList :=
  ⟨my_shape_iter n, (InductiveCircuit' my_shape_iter base_case ind) n⟩ where

  base_case : BasisCircuitOverList (my_shape_iter 0) := a_simple_circuit_part
  ind (n : ℕ) (c : BasisCircuitOverList (my_shape_iter n)) : BasisCircuitOverList (my_shape_iter (n + 1))
    :=
    HorizontalComp
    (VerticalComp c (@Gate [QubitSpace] pauli_x))
    (BasisCircuitListCoe (my_shape_iter_induction' n).symm (VerticalComp (@Gate [QubitSpace] pauli_z) c)) -- relies on my_shape_iter_induction'

noncomputable def a_bad_recursive_circuit_better' (n : ℕ) : TypeBasisCircuitList :=
  InductiveCircuit my_shape_iter base_case ind n where
  base_case : BasisCircuitOverList (my_shape_iter 0) := a_simple_circuit_part
  ind (n : ℕ) (c : BasisCircuitOverList (my_shape_iter n)) : BasisCircuitOverList (my_shape_iter (n + 1))
    :=
    HorizontalComp
    (VerticalComp c (@Gate [QubitSpace] pauli_x))
    (BasisCircuitListCoe (my_shape_iter_induction' n).symm (VerticalComp (@Gate [QubitSpace] pauli_z) c)) -- relies on my_shape_iter_induction'
