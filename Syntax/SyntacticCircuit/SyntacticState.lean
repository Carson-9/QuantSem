/-
module

/- [InnerProductSpace 𝕜 E] -/

import Mathlib.Analysis.InnerProductSpace.Basic
import Qml.SyntacticCircuit.SyntacticRegister

namespace SyntacticState
open SyntacticRegister

structure State {n : Nat} [NeZero n] (RegType : Register n) where
  State ::
  superposition : ⨂ₖ ι : Finset n, (RegType.WireType ι)



end SyntacticState
-/
