/-
module

public import Qml.SyntacticCircuit.SyntacticRegister

namespace SyntacticGate
section GateDefinition
open SyntacticRegister

structure Gate {n : Nat} [NeZero n] (RegType : Register n) :
  Gate ::
  Transform :

end SyntacticGate
+/
