/-
module

public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Data.Complex.Basic

namespace SyntacticRegister

open Complex

public structure Register (n : Nat) [NeZero n] [RCLike ℂ] where
  Register ::
  WireType : Fin n → ∃ T, InnerProductSpace ℂ T
-/
