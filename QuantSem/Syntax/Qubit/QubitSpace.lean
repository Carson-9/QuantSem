/-
Copyright (c) 2026 William Hasley. All rights reserved.
Released under GNU GPL3 license as described in the file LICENSE.
Authors: William Hasley
-/


module

public import QuantSem.Syntax.HighLevelInstance.HighLevelInstance

open QuantumTypes
open SyntacticRegister
namespace QubitSpaces

public class QubitLikeReg (E : Type) extends QuantReg E where
  qubitZero : E
  qubitOne : E
  zeroUnit : ‖qubitZero‖ = 1
  oneUnit : ‖qubitOne‖ = 1
  orthogonalBasis : inner qubitZero qubitOne = 0

public abbrev TypeQubitRegister := Σ E, QubitLikeReg E

@[coe]
def QubitAsTypeInclusion (Q : TypeQubitRegister) : TypeQuantumRegister :=
  ⟨ Q.fst, Q.snd.toQuantReg ⟩


end QubitSpaces
