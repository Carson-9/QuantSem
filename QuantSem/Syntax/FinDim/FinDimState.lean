/-
Copyright (c) 2026 William Hasley. All rights reserved.
Released under GNU GPL3 license as described in the file LICENSE.
Authors: William Hasley
-/


module

public import QuantSem.Syntax.HighLevelInstance.HighLevelInstance
public import QuantSem.Syntax.FinDim.FinDimRegister

open FinDimRegisters
open SyntacticState
namespace FinDimStates

variable (R : Type) [R' : FinDimReg R]
@[expose]
public def FinDimStateSpace := { x : R // ‖x‖ = 1}
public abbrev TypeFinDimState := Σ E : TypeFinRegister, @FinDimStateSpace E.fst E.snd

@[expose, coe]
public def FinDimStateAsState (s : TypeFinDimState) : TypeQuantumStates :=
  ⟨ FinRegAsRegFun s.fst, s.snd ⟩

@[expose]
public noncomputable def basisAreStates (E : TypeFinRegister) (i : Fin E.snd.dim)
  : TypeFinDimState := ⟨ E, Subtype.mk (E.snd.computationalBasis i) (E.snd.normalBasis i) ⟩


public class FinDimStateAlgebra extends Monoid TypeFinDimState where
  mulFun := toSemigroup.toMul.mul
  liftMap {C : FiniteDimRegTensorAlgebra} (s1 s2 : TypeFinDimState) :
    ((mul s1 s2).fst.fst) →
      @FinDimStateSpace (C.mul (s1.fst) (s2.fst)).fst (C.mul (s1.fst) (s2.fst)).snd

  liftRespectsBasis {C : FiniteDimRegTensorAlgebra} {E F : TypeFinRegister}
    (i : Fin (E.snd.dim)) (j : Fin F.snd.dim) :
    liftMap (basisAreStates E i) (basisAreStates F j)
    (mul (basisAreStates E i) (basisAreStates F j)).snd.val
      = (basisAreStates (C.mul E F) (C.basisFactorization E F (i, j))).snd



public noncomputable def StateInBasis (s : FinDimStateSpace R) : Fin (R'.dim) → ℂ :=
  R'.computationalBasis.repr s.val

--public noncomputable def StateFromBasis (f : Fin (R'.dim) →₀ ℂ) : FinDimStateSpace R :=
-- Need for unitarity in this format, TODO
--  Subtype.mk
--    (R'.computationalBasis.repr.invFun f)
--    ()

end FinDimStates
