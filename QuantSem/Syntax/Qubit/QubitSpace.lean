/-
Copyright (c) 2026 William Hasley. All rights reserved.
Released under GNU GPL3 license as described in the file LICENSE.
Authors: William Hasley
-/


module

public import QuantSem.Syntax.HighLevel.HighLevel

open QuantumTypes


public class QubitSpace (E : Type) extends QuantumType E where
  qubitZero : E
  qubitOne : E
  zeroUnit : ‖qubitZero‖ = 1
  oneUnit : ‖qubitOne‖ = 1
  orthogonalBasis : inner qubitZero qubitOne = 0


public abbrev TypeQubitSpace := Σ E, QubitSpace E
