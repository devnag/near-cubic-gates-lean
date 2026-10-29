import SourceAdapters.Joins.SingleRun

/-!
# The time of the single-run affine verifier

The proof of `thm:short-pcp-ours`, Step 2, "Time and queries", supplies one ordinary oracle
program with polynomial runtime. `lem:patch-r` applies the finite family of masks, and Step 4
compiles its exact run on the framed data and random string. The data and verdict are defined
in `Joins/SingleRun.lean`.

Correctness and runtime are required for every valid structured request, every bijective field
representation, every oracle, and every coin string. No malformed-input validity tester is asserted.
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Joins

open NearCubicWires NearCubicWires.RepairSource NearCubicWires.RepairRepresentation
open NearCubicWires.LocalBitMultitape

open SingleRun

/-- **The join.** One ordinary oracle program, fixed before its constants, that on the compiler's input
`frame data ++ frame R` with the oracle `o` outputs the patched verdict on the proof table `o` encodes, within
`K·(|data| + |R| + 1)^e` steps (`thm:short-pcp-ours`, Step 2, "Time and queries", for `V0`; `lem:patch-r` for the
patch; Step 4 for the run that is compiled), and every halting run outputs that verdict. -/
def SingleRunTime : Prop :=
  ∃ (prog : OrdinaryOracleProgram) (K e : ℕ),
    ∀ q : Request, q.Valid →
    ∀ (F : Type) [Field F] [DecidableEq F] (φ : AdjoinRoot (WireExponent3_5.GF.toPoly q.code.irr) →+* F),
      Function.Bijective φ → ∀ (o : ℕ → Bool) (R : List Bool),
        -- Step 2, "Time and queries" ("V0 runs in time poly(n, log T)"), `lem:patch-r`, Step 4
        OrdinaryOracleRuns o prog (q.input R) [q.patchedVerdict φ (q.decode φ o) R]
          (K * (q.data.length + R.length + 1) ^ e) ∧
        -- Step 4: "outputs the verdict of V1" (the run is deterministic)
        ∀ (out : List Bool) (budget : ℕ), OrdinaryOracleRuns o prog (q.input R) out budget →
          out = [q.patchedVerdict φ (q.decode φ o) R]

end NearCubicGates.Adapters.Joins
