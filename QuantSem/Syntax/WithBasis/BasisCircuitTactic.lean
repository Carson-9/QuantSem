/-
Copyright (c) 2026 William Hasley. All rights reserved.
Released under GNU GPL3 license as described in the file LICENSE.
Authors: William Hasley
-/


module

public import QuantSem.Syntax.WithBasis.BasisCircuit

open BasisRegister
open BasisState
open BasisGate
open BasisCircuit

namespace BasisCircuitTactic

open BasisCircuitOverRegister

/-
    Circuit "Gate" Normal Form
-/

public noncomputable def BasisCircuitNF {R : TypeBasisRegister} (c : BasisCircuitOverRegister R)
  : BasisGateType R R := BasisCircuitGateRepr c

public theorem BasisCircuitIsNF  {R : TypeBasisRegister}
  : ∀ c1 c2 : BasisCircuitOverRegister R, (c1 ≅ₖ₂ c2) ↔ (BasisCircuitNF c1) = (BasisCircuitNF c2) := BasisEquivalenceOverBasisState
