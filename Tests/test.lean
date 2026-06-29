/-
Copyright (c) 2026 William Hasley. All rights reserved.
Released under GNU GPL3 license as described in the file LICENSE.
Authors: William Hasley
-/

import QuantSem.Semantics.CoordinateSpace.CoordinateSpace

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


-- Since this is using √2, we have to fight with algebra to prove things,
-- Work is currently being done to identify √2 with it's galois representation
-- Which simplifies the work down to identifying different conjugates, but is heavy computationally
noncomputable def hadamard : BasisGateType QubitSpace QubitSpace :=
  MatrixToGate ⟨ (((√2)⁻¹ : ℂ) • !![(1 : ℂ), 1; 1, -1]), by unit_matrix_simple ⟩

-- This is simpler on nice matrices
noncomputable def pauli_x : BasisGateType QubitSpace QubitSpace := MatrixToGate ⟨!![0, 1 ; 1 , 0], by unit_matrix_simple  ⟩
noncomputable def pauli_z : BasisGateType QubitSpace QubitSpace := MatrixToGate ⟨!![1, 0 ; 0 , -1], by unit_matrix_simple ⟩



open SyntacticCircuit
open BasisCircuit
open BasisCircuitOverRegister

noncomputable def a_simple_circuit_part : BasisCircuit.BasisCircuitOverRegister (QubitSpace ⊗ᵣ QubitSpace)
  := VerticalComp (HorizontalComp (Gate hadamard) (Gate pauli_z)) (Gate pauli_x)

-- Sanity check, cannot glue incoherent circuits!
noncomputable def a_bad_recursive_circuit (n : ℕ) : TypeBasisCircuit := match n with
  |0 => ⟨_, a_simple_circuit_part⟩
  |Nat.succ k =>
    ⟨_, HorizontalComp
    (VerticalComp (a_bad_recursive_circuit k).circuit (Gate pauli_x))
    (VerticalComp (Gate pauli_z) (a_bad_recursive_circuit k).circuit)⟩

noncomputable def a_correct_recursive_circuit (n : ℕ) : TypeBasisCircuit := match n with
  |0 => ⟨_, a_simple_circuit_part⟩
  |Nat.succ k =>
    ⟨_, HorizontalComp
    (VerticalComp (Gate pauli_x) (a_correct_recursive_circuit k).circuit)
    (VerticalComp (Gate pauli_z) (a_correct_recursive_circuit k).circuit)⟩


-- This kind of isomorphism is always producible by a tactic, this will be moved in the lib
noncomputable def reparenthesing_iso (X Y Z : BasisRegister.TypeBasisRegister) :
  (X ⊗ᵣ (Y ⊗ᵣ Z)) ≅ ((X ⊗ᵣ Y) ⊗ᵣ Z) := _

noncomputable def fixed_the_bad_recursive_circuit (n : ℕ) : TypeBasisCircuit := match n with
  |0 => ⟨_, a_simple_circuit_part⟩
  |Nat.succ k =>
    ⟨_,
    HorizontalComp (
      RegisterSwap reparenthesing_iso
    (VerticalComp (a_bad_recursive_circuit k).circuit (Gate pauli_x)))
    (VerticalComp (Gate pauli_z) (a_bad_recursive_circuit k).circuit)⟩



noncomputable def turning_a_two_qubit_circuit_in_a_quadradit_circuit : BasisCircuitOverRegister (ComplexSpace 4) :=
  RegisterSwap iso base_circuit where
  base_circuit := VerticalComp (Gate hadamard) (Gate pauli_z)
  iso : (BasisRegister.MonCatBasisReg.tensorObj QubitSpace QubitSpace) ≅ (ComplexSpace 4) := _ -- todo, need to fix axiom of choice thingy


#check (SimpleCircuitGetShape (BasisCircuitAreSimpleCircuit (a_correct_recursive_circuit 4).circuit))
