import Proof.Gates.Worker.Decide
import Proof.Gates.Interfaces.Counter

set_option autoImplicit false

namespace NearCubicGates.Close.Worker

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation NearCubicGates.Close.Interfaces

/-- The verdict request: native width `q`, gadget count `M`, source length `N`, random bits `rb`, clause width `cl`,
and the `10M` terms in gadget-major order (term `t` of gadget `a` at index `10a + t`), each a flip bit and the raw
interval (a counter output or an exact parity mean); the term's interval is the raw one, complemented when the flip
is set (`flipI`, as in `Worker.Guess.intervalOf`). -/
structure VerdictReq where
  q : ℕ
  M : ℕ
  N : ℕ
  rb : ℕ
  cl : ℕ
  I : List (Bool × (ℚ × ℚ))
  hlen : I.length = 10 * M
  hden : ∀ x ∈ I, (x.2.1 * 2 ^ (q + 1)).den = 1 ∧ (x.2.2 * 2 ^ (q + 1)).den = 1

/-- The request word. -/
def verdictWord (r : VerdictReq) : List Bool :=
  natWord r.q ++ natWord r.M ++ natWord r.N ++ natWord r.rb ++ natWord r.cl ++
    listWord (fun x => bitWord x.1 ++ outputWord x.2) r.I

/-- The term interval: the raw interval, complemented when the flip is set. -/
def flipI (x : Bool × (ℚ × ℚ)) : ℚ × ℚ := if x.1 then (1 - x.2.1, x.2.2) else x.2

/-- `U` of eq:gadget-upper on the list form (`upperQ` on index `10a + t`). -/
def upperL (M : ℕ) (I : List (Bool × (ℚ × ℚ))) : ℚ :=
  1 + (((List.range I.length).map fun i => ((tenSigns ⟨i % 10, Nat.mod_lt _ (by norm_num)⟩ : ℚ) *
    (flipI (I.getD i (false, (0, 0)))).1 + (flipI (I.getD i (false, (0, 0)))).2)).sum) / (2 * M)

/-- The test bit (the guards and the test `eq:gadget-acceptance` of `sec:gadget-machine`, with the machine
threshold `εT`). -/
def verdictBit (γ εT : ℚ) (r : VerdictReq) : Bool :=
  decide (r.rb ≤ r.cl ∧ 2 ≤ r.q ∧ 1 ≤ r.N ∧ γ < εT * (r.N : ℚ) ^ 10 ∧ upperL r.M r.I < γ - εT)

structure VerdictMachine (γ εT : ℚ) where
  budget : VerdictReq → ℕ
  wf : WordFunction VerdictReq verdictWord (fun r => bitWord (verdictBit γ εT r)) budget
  cls : ∃ C e : ℕ, ∀ r : VerdictReq, budget r ≤ C * ((verdictWord r).length + 1) ^ e

end NearCubicGates.Close.Worker
