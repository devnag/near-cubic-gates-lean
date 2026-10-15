import StatementSupport

/-! This module only imports: its definitions are part of the trusted statement, `Statement.lean`. -/

/-!
# Input 6: the short PCP as an oracle circuit (Murray–Williams 2020)

Paper v2 imp:short-pcp: the short PCP in the form of Murray–Williams, SIAM J. Comput. 49(5) 2020, Section 5, in the
proof of Theorem 1.4, pp. STOC18-316–STOC18-317 (PDF pp. 18–19), a restatement of Ben-Sasson–Viola's short PCP with
verifier size poly(n, log T); Ben-Sasson–Viola's Theorem 1.1 as printed claims more and is false for polynomial T unless
P = NP (paper v2 rem:bv14-printed). The machine vocabulary is that of the other inputs: `OrdinaryVerifier`,
`InputRequest`, framed words, `T(n)` in binary, and a Mathlib polynomial-time TM2 machine for the construction. The new
objects are oracle circuits and their word.
-/

/-! ## Oracle circuits (used by input 6) -/

section

namespace NearCubicWires.Bindings.MW20

open NearCubicWires NearCubicWires.CanonicalBinary NearCubicWires.ExecutableInterfaces
open NearCubicWires.RepairSource NearCubicWires.RepairRepresentation NearCubicWires.LocalBitMultitape

set_option autoImplicit false

end NearCubicWires.Bindings.MW20
end
