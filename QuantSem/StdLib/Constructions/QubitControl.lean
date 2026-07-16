/-
Copyright (c) 2026 William Hasley. All rights reserved.
Released under GNU GPL3 license as described in the file LICENSE.
Authors: William Hasley
-/

module

public import QuantSem.StdLib.CoordinateSpace.ComplexSpaces
public import QuantSem.StdLib.CoordinateSpace.BitStringIndexing


open AbstractBasisRegister
open BasisState
open BasisGate
open SyntacticGate
open ComplexSpaces
open BitStringIndexing

namespace QubitControl

public noncomputable def SingleQubitControlGate {n : ℕ}
  (controlWire controlledGate : Fin n)
  (actualGate : BasisGateType QubitSpace QubitSpace)
  : BasisGateType (BasisRegister.MulTensor (Fin n) (fun _ => QubitSpace)) (BasisRegister.MulTensor (Fin n) (fun _ => QubitSpace)) :=
  GateFromBasis
    (fun i => if (BitVecBasis n i)[controlWire] then
      (GateStateEvolve (BasisGateMulTensorGateMulTensor (fun k => if k == controlledGate then actualGate else (IdGate QubitSpace))) (GetBasisState i))
      else (GetBasisState i))
    (by sorry)


end QubitControl
