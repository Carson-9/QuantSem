
module

import Lean.Attributes
import Lean.LabelAttribute

initialize find_better : Lean.TagAttribute ←
  Lean.registerTagAttribute  `find_better  "[QuantSem] - This attribute indicates that the definition / theorem should be rewritten at some point to compile better / rely on better definitions" (
    fun name => do
    Lean.logWarning ("[QuantSem] - Find a better implementation for : " ++ name)
    pure ())
    (applicationTime := Lean.AttributeApplicationTime.afterTypeChecking)

--register_label_attr find_better

--initialize typecheck_simp_attr : Lean.TagAttribute ← Lean.registerTagAttribute `typecheck_simp "[QuantSem] - This attribute is used when some type should always be unfolded during typechecking as some equalities rely on unfolding"
