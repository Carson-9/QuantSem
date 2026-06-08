/-
Copyright (c) 2026 William Hasley. All rights reserved.
Released under GNU GPL3 license as described in the file LICENSE.
Authors: William Hasley
-/


module

public import QuantSem.Syntax.HighLevelInstance.HighLevelInstance
public import QuantSem.Syntax.FinDim.FinDimRegister
public import QuantSem.Syntax.FinDim.FinDimState

open FinDimRegisters
open FinDimStates
open SyntacticGate
namespace FinDimGates

variable (R : Type) [FinDimReg R]

@[expose]
public def FinDimGate : Type :=  R →ₗᵢ[ℂ] R
public abbrev TypeFinDimGate := Σ E : TypeFinRegister, @FinDimGate E.fst E.snd

@[expose, coe]
public def FinDimGateAsGate (g : TypeFinDimGate) : TypeQuantumGate :=
  ⟨ FinRegAsRegFun g.fst, g.snd ⟩

end FinDimGates
