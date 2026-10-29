import NineInputs

/-!
# Join X1: an ordinary word function is a Mathlib TM2 machine

Paper anchors:
- `app:short-pcp-proof`, "The exact Lean interface": "A fixed multitape implementation can be simulated by finitely many stacks in polynomial time,
  giving the Mathlib TM2 machine required by the interface; clearing work stacks and restoring its final control
  state also take polynomial time."
- `app:sources`, "Full-range amplification interface": "The usual polynomial-overhead simulation into TM2 preserves this bound." (input 8, time `2^{O(n)}`)
- `app:sources`, "Uniform three-query PCPP and code interfaces" and `app:sources`, "Uniform three-query PCPP and code interfaces": "polynomial-time TM2 realizations" (input 9: constructor, honest proof,
  encoder, total decoder).

Quantities delivered: a Mathlib `Turing.TM2ComputableInTime ea eb f` (resp. `…InPolyTime`) whose `time`, evaluated
at the input length `(ea a).length`, is at most `C · (B n + n + 1)^d`, where `B` bounds the ordinary budget by the
input length (resp. a polynomial when the budget is `K · (L + 1)^e`).

Producers: any `RepairOrdinary.WordFunction α ea (fun a => eb (f a)) budget` (input on tape 0 as `frame (ea a)`,
output tape equal to `eb (f a)` after at most `budget a` steps), e.g. `Expand.PolyTab.wordFunction_of_ideal`.
Consumers: `MW20_OracleCircuitPCP_TM2` (input 6), `TruthTableConstructionTM2.machine` (input 8, the `InTime`
form), `PerfectThreeQueryProximityLiteral` and `EfficientLinearCodeLiteral` (input 9).

Encodings are plain functions `α → List Bool`, as in the pinned Mathlib (`TM2ComputableInPolyTime` takes
`ea : α → List αΓ`, not a `FinEncoding`).
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Joins

open NearCubicWires

/-- **X1, explicit-time form** (`app:sources`, "Full-range amplification interface", `app:short-pcp-proof`, "The exact Lean interface"). An ordinary word function whose budget is bounded by a
function `B` of the input length is a Mathlib `TM2ComputableInTime` machine whose time function is at most
`C · (B n + n + 1)^d` (polynomial overhead). Input 8 consumes this form. -/
def OrdinaryToTM2InTime : Prop :=
  ∀ {α β : Type} (ea : α → List Bool) (eb : β → List Bool) (f : α → β) (budget : α → ℕ) (B : ℕ → ℕ),
    -- `app:short-pcp-proof`, "The exact Lean interface": "a fixed multitape implementation" (the ordinary machine, from `frame (ea a)` to `eb (f a)`)
    Nonempty (RepairOrdinary.WordFunction α ea (fun a => eb (f a)) budget) →
    -- `app:sources`, "Full-range amplification interface": the implementation's time bound, read as a function of the input length
    (∀ a, budget a ≤ B (ea a).length) →
    -- `app:sources`, "Full-range amplification interface": "The usual polynomial-overhead simulation into TM2 preserves this bound"
    ∃ C d : ℕ, ∃ M : Turing.TM2ComputableInTime ea eb f, ∀ n, M.time n ≤ C * (B n + n + 1) ^ d

/-- **X1, polynomial form** (`app:sources`, "Uniform three-query PCPP and code interfaces",, `app:short-pcp-proof`, "The exact Lean interface"). An ordinary word function whose budget is
at most `K · (L + 1)^e` in the input length `L` is a Mathlib `TM2ComputableInPolyTime` machine. Inputs 6 and 9
consume this form. -/
def OrdinaryToTM2PolyTime : Prop :=
  ∀ {α β : Type} (ea : α → List Bool) (eb : β → List Bool) (f : α → β) (budget : α → ℕ),
    -- `app:short-pcp-proof`, "The exact Lean interface": the ordinary implementation
    Nonempty (RepairOrdinary.WordFunction α ea (fun a => eb (f a)) budget) →
    -- `app:sources`, "Uniform three-query PCPP and code interfaces": "polynomial time", in the platform's cost-class form `K · (L + 1)^e`
    (∃ K e : ℕ, ∀ a, budget a ≤ K * ((ea a).length + 1) ^ e) →
    -- `app:short-pcp-proof`, "The exact Lean interface": "the Mathlib TM2 machine required by the interface"
    Nonempty (Turing.TM2ComputableInPolyTime ea eb f)

end NearCubicGates.Adapters.Joins
