import Proof.Gates.Target
import Bindings.CTW26_Lemma3_2
import Bindings.Williams14_Corollary4_4
import Proof.Gates.Main.ShortPCP
import Bindings.CLW20_Theorem1_13
import Bindings.CLW20_Lemma3_9_TM2
import Proof.Gates.PublishedSources.Witness
import Proof.Gates.PublishedSources.PrimeDensity
import Proof.Gates.PublishedSources.PCPP
import StatementSupport

/-! This module only imports: its definitions are part of the trusted statement, `Statement.lean`. -/

/-!
# The main statement: nine published inputs imply the main theorem

`FinalStatement` is the exact shape of the main result: the nine published inputs imply
`NearCubicGates.Target.MainStatement` (paper v2 thm:main, line 206). `Check.lean` asserts a closed proof of
exactly this proposition with the axioms `propext`, `Classical.choice`, `Quot.sound`.
-/

set_option autoImplicit false

namespace NearCubicGates.Close

end NearCubicGates.Close
