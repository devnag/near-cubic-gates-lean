import SourceAdapters.RAMTrace.Defs
import SourceAdapters.ShortPCP.ClockFits
import SourceAdapters.ACSP.Encoding

/-!
# The RAM event-trace interface

`thm:trace` and `cor:trace-verifier`, in `app:event-trace`, give the two
statements below. `RAMTrace.Holds` expresses the equation trees `timeEq` and
`sortEq` over a commutative ring of characteristic two; the affine assembly
uses `F₂[x]/(irr)`.

The first clause equates satisfiability with bounded RAM acceptance for an
arithmetic unit consisting of add, sub, and and cmp, power-of-two word width,
a compatible time exponent, and a word-aligned padded input. The second
specializes this to the machine of `lem:tm-ram`, for `2 ≤ n ≤ t` and the
explicit runtime promise, preserving the exact t-bit witness quantifier.
The affine embedding in `RAMACSP/Assembly.lean` consumes this equivalence.
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Joins

open NearCubicWires NearCubicWires.RepairSource NearCubicWires.RepairOrdinary NearCubicWires.LocalBitMultitape
open NearCubicGates.Adapters.ACSP

/-- The event-trace theorem and its verifier specialization (`thm:trace`, `cor:trace-verifier`). -/
def RAMEventTrace : Prop :=
  -- `thm:trace`: for the machine and numeric hypotheses below, trace satisfiability
  -- is equivalent to bounded RAM acceptance; the arithmetic unit and width are explicit.
  -- `1 ≤ L ≤ 2^w` (part of `Ram`), `τ ≥ max(1, ω)` with `2^τ < 2^w`, `w ∣ |x̄| ≤ 2^τ`
  (∀ (F : Type) [CommRing F] [CharP F 2] (M : Ram) (kind : Fin M.ops → RAMTrace.AluOp) (τ : ℕ)
      (xbar : List Bool),
    (∀ op, M.alu op = (kind op).fn) → M.w = 2 ^ Nat.log 2 M.w → 1 ≤ τ → Nat.log 2 M.w ≤ τ → τ < M.w →
    M.w ∣ xbar.length → xbar.length ≤ 2 ^ τ →
    (RAMTrace.Satisfiable F M kind τ xbar ↔ M.BHRAM xbar τ τ)) ∧
  -- `cor:trace-verifier`: for `2 ≤ n ≤ t` under `RunsWithin V x t`,
  -- acceptance with a t-bit witness is equivalent to satisfiability of the padded event trace.
  (∀ (F : Type) [CommRing F] [CharP F 2] (V : OrdinaryVerifier) (c : ℕ), ShortPCP.clockConst V ≤ c →
    ∀ (r : ClockRequest) (hfit : ShortPCP.codeLen V ≤ 2 ^ ShortPCP.wordWidth c r.2),
    2 ≤ r.1.1 → r.1.1 ≤ r.2 → RunsWithin V r.1.2 r.2 →
    ((∃ y : BitInput r.2, V.accepts (List.ofFn r.1.2) (List.ofFn y)) ↔
      RAMTrace.Satisfiable F
        (ShortPCP.mnRam V (ShortPCP.wordWidth c r.2) r.1.1 r.2 (2 ^ ShortPCP.timeExp c r.2) hfit)
        RAMTrace.mnKind (ShortPCP.timeExp c r.2) (ShortPCP.padInput c r.2 r.1.2)))

end NearCubicGates.Adapters.Joins
