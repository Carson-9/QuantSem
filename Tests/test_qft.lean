/-
Copyright (c) 2026 William Hasley. All rights reserved.
Released under GNU GPL3 license as described in the file LICENSE.
Authors: William Hasley
-/

import QuantSem.StdLib.CoordinateSpace.CoordinateSpace
import QuantSem.StdLib.Constructions.QubitControl
import QuantSem.StdLib.Constructions.QubitData
import Mathlib.Data.Complex.Basic

open BasisCircuitList
open AbstractBasisRegister
open BasisState
open BasisGate
open ComplexSpaces
open CoordinateSpace
open QubitControl
open QubitData


@[reducible]
noncomputable def WireFamily (n : ℕ) : List BasisRegister := List.replicate (n + 1) QubitSpace

@[simp, defeq]
public theorem WireFamiltyAtZero : WireFamily 0 = [QubitSpace] := by rfl

@[simp]
public theorem WireFamilyInduction (k : ℕ) : WireFamily (k + 1) = (WireFamily k) ++ [QubitSpace]
  := by induction k with
    | zero => rfl
    | succ n ih => unfold WireFamily; unfold WireFamily at ih; unfold List.replicate; rw[ih]; rfl

@[simp]
public theorem WireFamilyLen (k : ℕ) : (WireFamily k).length = k + 1
  := by simp

@[simp]
public theorem WireFamilyGet (k : ℕ) (i : Fin (WireFamily k).length)
  : (WireFamily k).get i = QubitSpace := by simp

public noncomputable def hadamard' : BasisGateType (⨂ᵣ [QubitSpace]) (⨂ᵣ [QubitSpace]) := hadamard

open BasisCircuitOverList

noncomputable def QFT (n : ℕ) : BasisListCircuit :=
  InductiveCircuit WireFamily baseCase ind n where
  baseCase : BasisCircuitOverList (WireFamily 0) := Gate (hadamard')
  ind (k : ℕ) (c : BasisCircuitOverList (WireFamily k)) : BasisCircuitOverList (WireFamily (k + 1))
  :=  HorizontalComp
        (HorizontalComp
          (BasisCircuitListCoe (WireFamilyInduction k).symm (VerticalComp c IdWire))
          (Gate (DirtyControlGate (WireFamily (k + 1)) (.mk (k + 1) (by simp)) (.mk 0 (by simp)) (fun b => if b == 1 then rotation (k + 1) else (SyntacticGate.IdGate QubitSpace)))))
          --(Gate (SingleQubitControlGate (k + 2) (.mk (k + 1) (by simp)) 0 (rotation (k + 1)))))
          -- typechecking helped with the indices!


        (VerticalComp IdWire c)
