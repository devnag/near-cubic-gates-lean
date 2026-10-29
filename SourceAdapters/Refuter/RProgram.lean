import Proof.Amplification.RecoveryQueryCall
import Proof.MachineModel.OrdinaryOracleComposeReady

/-!
# The refuter program's oracle skeleton (input 7, R): a fixed three-node call graph

Paper anchor: `lem:multitape-refuter` Steps 3–4, proof of `lem:multitape-refuter` and `cor:framed-refuter` — `R_T` is an oracle machine whose
queries are adaptive ("Either way it makes `O(N)` adaptive queries", proof of `lem:multitape-refuter` and `cor:framed-refuter`) — and
`cor:framed-refuter` proof of `lem:multitape-refuter` and `cor:framed-refuter` (the queries are written in full, the oracle answers one bit).

The program is L's finite call graph (`OrdinaryOracleCompose.graph`) of three pieces on one tape set:

* piece `0` `INIT` (an ordinary machine): the loader;
* piece `1` `STEP` (an ordinary machine): one search round; it ends with all heads at `0` and the
  DONE cell (tape `done`, cell `0`) either set (the output is written) or clear (a query is written);
* piece `2` `ASK` (`RecoveryQueryAnswer.piece`): the literal oracle step, then the answer bit is
  written at cell `0` of tape `ans`.

Edges: `INIT → STEP`, `STEP → ASK` when DONE is clear, `STEP → stop` when DONE is set, `ASK → STEP`.

`runs_of_rounds` turns a loader run and a per-round contract into `OrdinaryOracleRuns`, charging every
machine step, every graph transition and the literal query length (`(RepairOrdinary.frame bits).length + 1`,
`Statement.lean` §14).
-/

namespace NearCubicGates.Adapters.Refuter.Loop

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairSource NearCubicWires.RepairSource.OrdinaryOracleCompose

set_option autoImplicit false

variable {t sI sS : ℕ}

/-- The three pieces. -/
noncomputable def pieces (MI : Machine t sI) (MS : Machine t sS) (ans : Fin t) : Fin 3 → Piece t
  | ⟨0, _⟩ => ordinary MI
  | ⟨1, _⟩ => ordinary MS
  | ⟨2, _⟩ => RecoveryQueryAnswer.piece ans
  | ⟨_ + 3, h⟩ => False.elim (by omega)

/-- The edges. -/
noncomputable def next (MI : Machine t sI) (MS : Machine t sS) (ans done : Fin t) (j : Fin 3)
    (_ : Fin (pieces MI MS ans j).states) (b : Fin t → Bool) : Option (Fin 3) :=
  if j.val = 1 then (if b done then none else some 2) else some 1

/-- **The refuter program skeleton.** -/
noncomputable def program (ports : Ports t) (MI : Machine t sI) (MS : Machine t sS) (ans done : Fin t) :
    OrdinaryOracleProgram :=
  ports.program (graph (pieces MI MS ans) 0 (next MI MS ans done))

/-- The configuration starting piece `j` on tapes `a` (all heads `0`). -/
noncomputable def startAt (MI : Machine t sI) (MS : Machine t sS) (ans : Fin t) (j : Fin 3)
    (a : Fin t → List Bool) :=
  controlConfig (RecoveryCalls.code (fun j => (pieces MI MS ans j).states) j)
    (initialConfiguration (pieces MI MS ans j).machine a)

/-- An ordinary run that returns every head to `0` is a `Ready` piece run. -/
theorem ready_of_run {o : ℕ → Bool} (ports : Ports t) {s : ℕ} (M : Machine t s) {n : ℕ}
    {a b : Fin t → List Bool} (h : ClockJoin.ReadyRun M n a b) :
    ∃ c ≤ n, Ready o (ports.program (ordinary M)) c a b := by
  obtain ⟨r, hr, ht, hh, hs⟩ := h
  have trace := ordinary_trace (o := o) ports M n _ r hr
  exact ⟨r.steps, hs, r.final, trace, (prefix_of_run M n _ r hr).2, hh, ht⟩

/-- The answer piece as a `Ready` run. -/
theorem ask_ready (o : ℕ → Bool) (ports : Ports t) (ans : Fin t) (a : Fin t → List Bool)
    (bits pad : List Bool) (hq : a ports.queryTape = RepairOrdinary.frame bits ++ pad) :
    Ready o (ports.program (RecoveryQueryAnswer.piece ans)) ((RepairOrdinary.frame bits).length + 2) a
      (RecoveryQueryAnswer.output ans a (o (CanonicalBinary.bitsValue bits))) :=
  ⟨_, RecoveryQueryAnswer.answer_trace ports ans o (fun _ => 0) a bits pad rfl rfl hq, rfl,
    fun _ => rfl, rfl⟩

/-- **The round loop.** `P k a`: the tapes `a` (all heads at `0`) start a `STEP` that finishes the
search within `k` rounds. Each round costs at most `B` machine steps, a query of framed length at
most `Q`, and four graph/oracle transitions. -/
theorem loop (o : ℕ → Bool) (ports : Ports t) (MI : Machine t sI) (MS : Machine t sS) (ans done : Fin t)
    (out : List Bool) (B Q : ℕ) (P : ℕ → (Fin t → List Bool) → Prop)
    (hstep : ∀ k a, P (k + 1) a →
      (∃ b, ClockJoin.ReadyRun MS B a b ∧ readTapeBit (b done) 0 = true ∧
          b ports.outputTape = RepairOrdinary.frame out) ∨
      (∃ b bits pad, ClockJoin.ReadyRun MS B a b ∧ readTapeBit (b done) 0 = false ∧
          b ports.queryTape = RepairOrdinary.frame bits ++ pad ∧ (RepairOrdinary.frame bits).length ≤ Q ∧
          P k (RecoveryQueryAnswer.output ans b (o (CanonicalBinary.bitsValue bits)))))
    (h0 : ∀ a, ¬ P 0 a) :
    ∀ k a, P k a → ∃ cost final, cost ≤ k * (B + Q + 4) ∧
      OrdinaryOracleTrace o (program ports MI MS ans done) cost (startAt MI MS ans 1 a) final ∧
      (program ports MI MS ans done).base.machine.halted final.control = true ∧
      final.tapes ports.outputTape = RepairOrdinary.frame out := by
  intro k
  induction k with
  | zero => intro a ha; exact absurd ha (h0 a)
  | succ k ih =>
    intro a ha
    rcases hstep k a ha with ⟨b, hb, hdone, hout⟩ | ⟨b, bits, pad, hb, hdone, hq, hQ, hP⟩
    · obtain ⟨c, hc, hr⟩ := ready_of_run (o := o) ports MS hb
      have hs := Ready.stop (o := o) ports (pieces MI MS ans) 0 (next MI MS ans done) 1 hr
        (fun _ => by simp [next, hdone])
      refine ⟨c + 1, _, by nlinarith, hs, ?_, by simpa [RecoveryCalls.stopped] using hout⟩
      simp [program, graph, RecoveryCalls.machine, RecoveryCalls.stopped]
    · obtain ⟨c, hc, hr⟩ := ready_of_run (o := o) ports MS hb
      have h1 := Ready.call (o := o) ports (pieces MI MS ans) 0 (next MI MS ans done) 1 2 hr
        (fun _ => by simp [next, hdone])
      have h2 := Ready.call (o := o) ports (pieces MI MS ans) 0 (next MI MS ans done) 2 1
        (ask_ready o ports ans b bits pad hq) (fun _ => by simp [next])
      obtain ⟨cost, final, hcost, htr, hh, hout⟩ := ih _ hP
      refine ⟨c + 1 + ((RepairOrdinary.frame bits).length + 2 + 1 + cost), final, ?_, ?_, hh, hout⟩
      · have : k * (B + Q + 4) + (B + Q + 4) = (k + 1) * (B + Q + 4) := by ring
        omega
      · exact trans h1 (trans h2 htr)

/-- **The whole program.** A loader run into a state finishing within `k` rounds gives
`OrdinaryOracleRuns` with budget `BI + 1 + k·(B + Q + 4)`. -/
theorem runs_of_rounds (o : ℕ → Bool) (ports : Ports t) (MI : Machine t sI) (MS : Machine t sS)
    (ans done : Fin t) (input out : List Bool) (BI B Q k : ℕ) (P : ℕ → (Fin t → List Bool) → Prop)
    (hstep : ∀ k a, P (k + 1) a →
      (∃ b, ClockJoin.ReadyRun MS B a b ∧ readTapeBit (b done) 0 = true ∧
          b ports.outputTape = RepairOrdinary.frame out) ∨
      (∃ b bits pad, ClockJoin.ReadyRun MS B a b ∧ readTapeBit (b done) 0 = false ∧
          b ports.queryTape = RepairOrdinary.frame bits ++ pad ∧ (RepairOrdinary.frame bits).length ≤ Q ∧
          P k (RecoveryQueryAnswer.output ans b (o (CanonicalBinary.bitsValue bits)))))
    (h0 : ∀ a, ¬ P 0 a)
    (hinit : ∃ a, ClockJoin.ReadyRun MI BI ((program ports MI MS ans done).base.inputTapes input) a ∧
      P k a) :
    OrdinaryOracleRuns o (program ports MI MS ans done) input out (BI + 1 + k * (B + Q + 4)) := by
  obtain ⟨a, ha, hP⟩ := hinit
  obtain ⟨c, hc, hr⟩ := ready_of_run (o := o) ports MI ha
  have h1 := Ready.call (o := o) ports (pieces MI MS ans) 0 (next MI MS ans done) 0 1 hr
    (fun _ => by simp [next])
  obtain ⟨cost, final, hcost, htr, hh, hout⟩ :=
    loop o ports MI MS ans done out B Q P hstep h0 k a hP
  exact ⟨c + 1 + cost, final, by omega, trans h1 htr, hh, hout⟩

end NearCubicGates.Adapters.Refuter.Loop
