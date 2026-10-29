import Proof.Gates.CheckedPCPP.WMXReady
import Proof.MachineModel.OrdinaryOracleComposeGraph
import Proof.MachineModel.OrdinaryOracleComposeTrace

/-!
# Single-run time, machine layer 2: ordinary oracle programs from re-entrant WMX programs

The consumer X5(a) (`Joins/ComputationToCircuit.lean`) compiles an `OrdinaryOracleProgram` run (proof of `thm:short-pcp-ours`, Step 4:
"consider the computation of V1 … its proof bits are read at addresses below L_π … replace each read of a proof bit
by an oracle gate"). WMX has no oracle instruction. This module supplies one generic seam: a WMX program `W` that is
*re-entrant* (every call starts with all heads and registers at `0` and decides what to do from its streams) becomes
an oracle program, the call graph (L `OrdinaryOracleCompose.graph`) of four pieces:
* `W` itself; when it halts, the first cell of the flag stream `FL` says "ask" (`true`) or "stop" (`false`);
* `ask`: one oracle query on the query stream `Qs` (which `W` left as `frame bits ++ padding`);
* `rec0` / `rec1`: write the answer into the first cell of the answer stream `AN`, then call `W` again.
`CoRuns` lists the calls of `W` (each a `WXExec` run with an exact post-state); `coRuns_runs` turns it into
`OrdinaryOracleRuns` on the framed input, with the cost of the calls plus `|frame bits| + 5` per query.
Since `V0` is non-adaptive (proof of `thm:short-pcp-ours`, Step 2, "The instance", "The queries of V0 are computed from the random string alone"), the
single-run program can recompute its query list at every call; the per-call cost is `poly`, and so is the number of
calls.
-/

set_option autoImplicit false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Adapters.ShortPCP.Machines

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairSource
open NearCubicWires.RepairSource.OrdinaryOracleCompose NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.CheckedPCPP
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicWires.WireExponent3_5 NearCubicWires.ExtDecompositionBatch

variable {ns nr : ℕ} (cap : ℕ)

/-! ## Banked tape vectors -/

/-- The tape vector `A` carries the word state `σ`: exact on the streams, read-equal everywhere. -/
def Banked (σ : WState ns nr) (A : Fin (ns + 2 + nr) → List Bool) : Prop :=
  (∀ j, RdEq ((wenc cap σ).A j) (A j)) ∧ ∀ i, A (sTape i) = σ.st i

/-- All stream heads and all registers at `0`. -/
def Rest (σ : WState ns nr) : Prop := (∀ i, σ.sh i = 0) ∧ ∀ r, σ.val r = 0

/-- **A WMX run on any banked tape vector.** -/
theorem runFrom_banked {P : WMX ns nr} {σ τ : WState ns nr} {n : ℕ} (h : WXExec cap P σ τ n) (hσ : Rest σ)
    (hτ : Rest τ) (A : Fin (ns + 2 + nr) → List Bool) (hA : Banked cap σ A) :
    ∃ r : ExecutionReceipt (ns + 2 + nr) P.size, runFrom P.compile n (initialConfiguration P.compile A) = some r ∧
      r.steps ≤ n ∧ (∀ j, r.final.heads j = 0) ∧ Banked cap τ r.final.tapes := by
  obtain ⟨r, hr, hh, ht, hs⟩ := WXExec.run cap h hσ.1 hσ.2
  let E : Fin (ns + 2 + nr) → Prop := fun j => ∃ i, j = sTape i
  have hrel : ConfRel E (initialConfiguration P.compile (wenc cap σ).A) (initialConfiguration P.compile A) := by
    refine ⟨rfl, rfl, fun j => hA.1 j, ?_⟩
    rintro j ⟨i, rfl⟩
    simp only [initialConfiguration]
    rw [wenc_A_s, hA.2]
  obtain ⟨r', hr', hrel', hst⟩ := runFrom_rel P.compile E n hrel r hr
  refine ⟨r', hr', by rw [hst]; exact hs, ?_, ?_, ?_⟩
  · intro j
    rw [← hrel'.heads, hh, wenc_H_zero cap τ hτ.1 hτ.2]
  · intro j
    rw [← ht]
    exact hrel'.read j
  · intro i
    rw [← hrel'.exact (sTape i) ⟨i, rfl⟩, ht, wenc_A_s]

/-! ## The pieces -/

/-- The query piece: state `0` asks; the answer `false`/`true` lands in the halting state `1`/`2`. -/
def askMachine (t : ℕ) : Machine t 3 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val ≠ 0
  rule := fun _ _ => none

/-- Write `b` into the scanned cell of tape `j`, then halt. -/
def recMachine (t : ℕ) (j : Fin t) (b : Bool) : Machine t 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val ≠ 0
  rule := fun q _ => if q.val = 0 then some ⟨1, fun i => if i = j then some b else none, fun _ => .stay⟩ else none

/-- The four pieces: `W`, ask, record `false`, record `true`. -/
noncomputable def coPieces (W : WMX ns nr) (AN : Fin (ns + 1)) : Fin 4 → Piece (ns + 2 + nr)
  | ⟨0, _⟩ => ordinary W.compile
  | ⟨1, _⟩ => ⟨3, askMachine (ns + 2 + nr), fun q => if q.val = 0 then some ⟨1, 2⟩ else none⟩
  | ⟨2, _⟩ => ordinary (recMachine (ns + 2 + nr) (sTape AN) false)
  | ⟨3, _⟩ => ordinary (recMachine (ns + 2 + nr) (sTape AN) true)

/-- The call graph: `W` asks or stops by the flag cell; the answer selects the recorder; recorders call `W`. -/
noncomputable def coNext (W : WMX ns nr) (AN FL : Fin (ns + 1)) :
    (j : Fin 4) → Fin (coPieces W AN j).states → (Fin (ns + 2 + nr) → Bool) → Option (Fin 4)
  | ⟨0, _⟩, _, bits => if bits (sTape FL) then some 1 else none
  | ⟨1, _⟩, q, _ => if q.val = 2 then some 3 else some 2
  | ⟨2, _⟩, _, _ => some 0
  | ⟨3, _⟩, _, _ => some 0

/-- The ports: output on `OUT`, queries on `Qs` (both not the input stream). -/
def coPorts (Qs OUT : Fin (ns + 1)) (hQ : Qs.val ≠ 0) (hO : OUT.val ≠ 0) : Ports (ns + 2 + nr) where
  twoTapes := by omega
  outputTape := sTape OUT
  outputFresh := by simp [sTape, hO]
  queryTape := sTape Qs
  queryFresh := by simp [sTape, hQ]

/-- **The oracle program of a re-entrant WMX program.** -/
noncomputable def coProgram (W : WMX ns nr) (Qs AN FL OUT : Fin (ns + 1)) (hQ : Qs.val ≠ 0) (hO : OUT.val ≠ 0) :
    OrdinaryOracleProgram :=
  (coPorts Qs OUT hQ hO).program (graph (coPieces W AN) 0 (coNext W AN FL))

/-! ## The calls of `W` -/

/-- The successive calls of `W` from `σ` until it stops with `output` on `OUT`, within `b` steps in all. -/
inductive CoRuns (o : ℕ → Bool) (W : WMX ns nr) (Qs AN FL OUT : Fin (ns + 1)) (output : List Bool) :
    WState ns nr → ℕ → Prop where
  | stop {σ τ : WState ns nr} {c : ℕ} : Rest σ → WXExec cap W σ τ c → Rest τ → readTapeBit (τ.st FL) 0 = false →
      τ.st OUT = RepairOrdinary.frame output → CoRuns o W Qs AN FL OUT output σ (c + 1)
  | ask {σ τ : WState ns nr} {c b : ℕ} (bits pad : List Bool) : Rest σ → WXExec cap W σ τ c → Rest τ →
      readTapeBit (τ.st FL) 0 = true → τ.st Qs = RepairOrdinary.frame bits ++ pad →
      CoRuns o W Qs AN FL OUT output
        (τ.sets AN (writeTapeBit (τ.st AN) 0 (o (CanonicalBinary.bitsValue bits)))) b →
      CoRuns o W Qs AN FL OUT output σ (c + (RepairOrdinary.frame bits).length + 5 + b)

/-! ## Traces of the pieces inside the graph -/

theorem rec_run (t : ℕ) (j : Fin t) (b : Bool) (heads : Fin t → ℕ) (A : Fin t → List Bool) :
    ∃ r : ExecutionReceipt t 2, runFrom (recMachine t j b) 1 ⟨0, heads, A⟩ = some r ∧ r.steps = 1 ∧
      r.final = ⟨1, heads, fun i => if i = j then writeTapeBit (A i) (heads i) b else A i⟩ := by
  refine ⟨_, rfl, rfl, ?_⟩
  simp only [applyAction]
  congr 1
  funext i
  by_cases h : i = j <;> simp [h]

/-- The control codes of the graph. -/
noncomputable abbrev coCode (W : WMX ns nr) (AN : Fin (ns + 1)) (j : Fin 4) :
    Fin (coPieces W AN j).states → Fin (Fintype.card (RecoveryCalls.Control (fun j => (coPieces W AN j).states))) :=
  RecoveryCalls.code (fun j => (coPieces W AN j).states) j

theorem wenc_sets_other (σ : WState ns nr) (i : Fin (ns + 1)) (l : List Bool) (j : Fin (ns + 2 + nr))
    (hj : j ≠ sTape i) : (wenc cap (σ.sets i l)).A j = (wenc cap σ).A j := by
  rcases PrimAsm.DockW.tape_cases j with ⟨i', rfl⟩ | rfl | ⟨q, rfl⟩
  · have : i' ≠ i := fun h => hj (by rw [h])
    rw [wenc_A_s, wenc_A_s]; simp [Function.update_of_ne this]
  · rw [PrimAsm.DockW.wenc_A_c, PrimAsm.DockW.wenc_A_c]; rfl
  · rw [wenc_A_r, wenc_A_r]; rfl

theorem banked_write {σ : WState ns nr} {A : Fin (ns + 2 + nr) → List Bool} (hA : Banked cap σ A)
    (AN : Fin (ns + 1)) (b : Bool) :
    Banked cap (σ.sets AN (writeTapeBit (σ.st AN) 0 b))
      (fun i => if i = sTape AN then writeTapeBit (A i) 0 b else A i) := by
  refine ⟨fun j => ?_, fun i => ?_⟩
  · by_cases hj : j = sTape AN
    · subst hj
      simp only [wenc_A_s, WState.sets_st, Function.update_self, if_true, hA.2]
      exact RdEq.refl _
    · simp only [hj, if_false]
      rw [wenc_sets_other cap σ AN _ j hj]; exact hA.1 j
  · by_cases hi : i = AN
    · subst hi; simp [hA.2]
    · have : sTape (nr := nr) i ≠ sTape AN := fun h => hi (PrimAsm.DockW.sTape_inj h)
      simp only [this, if_false, hA.2, WState.sets_st, Function.update_of_ne hi]

section Graph

variable {W : WMX ns nr} {Qs AN FL OUT : Fin (ns + 1)} {hQ : Qs.val ≠ 0} {hO : OUT.val ≠ 0}


/-- One call of `W` inside the graph. -/
theorem call_W (o : ℕ → Bool) {σ τ : WState ns nr} {c : ℕ} (h : WXExec cap W σ τ c) (hσ : Rest σ) (hτ : Rest τ)
    (A : Fin (ns + 2 + nr) → List Bool) (hA : Banked cap σ A) :
    ∃ r : ExecutionReceipt (ns + 2 + nr) W.size, r.steps ≤ c ∧ (∀ j, r.final.heads j = 0) ∧
      Banked cap τ r.final.tapes ∧ W.compile.halted r.final.control = true ∧
      OrdinaryOracleTrace o (coProgram W Qs AN FL OUT hQ hO) r.steps (controlConfig (coCode W AN 0) (initialConfiguration W.compile A))
        (controlConfig (coCode W AN 0) r.final) := by
  obtain ⟨r, hr, hs, hh, hb⟩ := runFrom_banked cap h hσ hτ A hA
  refine ⟨r, hs, hh, hb, (prefix_of_run _ _ _ r hr).2, ?_⟩
  have tr := ordinary_trace (o := o) (coPorts Qs OUT hQ hO) W.compile c _ r hr
  exact graph_trace (coPorts Qs OUT hQ hO) (coPieces W AN) 0 (coNext W AN FL) 0 tr

theorem scanned_zero {t s : ℕ} (c : Configuration t s) (hh : ∀ j, c.heads j = 0) (j : Fin t) :
    c.scanned j = readTapeBit (c.tapes j) 0 := by
  simp [Configuration.scanned, hh j]

/-- **The coroutine runs**: the calls of `CoRuns` are one trace of the graph program, ending halted with the
output on `OUT`. -/
theorem coRuns_trace (o : ℕ → Bool) {output : List Bool} {σ : WState ns nr} {b : ℕ}
    (h : CoRuns cap o W Qs AN FL OUT output σ b) :
    ∀ A, Banked cap σ A → ∃ cost final, cost ≤ b ∧
      OrdinaryOracleTrace o (coProgram W Qs AN FL OUT hQ hO) cost (controlConfig (coCode W AN 0) (initialConfiguration W.compile A)) final ∧
      (coProgram W Qs AN FL OUT hQ hO).base.machine.halted final.control = true ∧ final.tapes (sTape OUT) = RepairOrdinary.frame output := by
  induction h with
  | @stop σ τ c hσ hW hτ hfl hout =>
    intro A hA
    obtain ⟨r, hs, hh, hb, hhalt, tr⟩ := call_W cap (hQ := hQ) (hO := hO) (FL := FL) (AN := AN) o hW hσ hτ A hA
    have hn : coNext W AN FL 0 r.final.control r.final.scanned = none := by
      show (if r.final.scanned (sTape FL) then some 1 else none) = none
      rw [scanned_zero _ hh, hb.2, hfl]; rfl
    have st := graph_stop o (coPorts Qs OUT hQ hO) (coPieces W AN) 0 (coNext W AN FL) 0 r.final hhalt hn
    refine ⟨r.steps + 1, _, by omega, OrdinaryOracleCompose.trans tr st, ?_, ?_⟩
    · simp [coProgram, Ports.program, graph, RecoveryCalls.machine, RecoveryCalls.stopped]
    · show r.final.tapes (sTape OUT) = _
      rw [hb.2, hout]
  | @ask σ τ c b bits pad hσ hW hτ hfl hq _ ih =>
    intro A hA
    obtain ⟨r, hs, hh, hb, hhalt, tr⟩ := call_W cap (hQ := hQ) (hO := hO) (FL := FL) (AN := AN) o hW hσ hτ A hA
    -- `W` returns to the ask piece
    have hn : coNext W AN FL 0 r.final.control r.final.scanned = some 1 := by
      show (if r.final.scanned (sTape FL) then some 1 else none) = some 1
      rw [scanned_zero _ hh, hb.2, hfl]; rfl
    have ret1 := graph_return o (coPorts Qs OUT hQ hO) (coPieces W AN) 0 (coNext W AN FL) 0 1 r.final hhalt hn
    -- the query, the recorder, and the return to `W`
    have hqt : r.final.tapes (sTape Qs) = RepairOrdinary.frame bits ++ pad := by rw [hb.2, hq]
    have key : ∀ ans : Bool, o (CanonicalBinary.bitsValue bits) = ans →
        OrdinaryOracleTrace o (coProgram W Qs AN FL OUT hQ hO) ((RepairOrdinary.frame bits).length + 4)
          (controlConfig (coCode W AN 1) (RecoveryCalls.restarted (coPieces W AN 1).machine r.final.heads
            r.final.tapes))
          (controlConfig (coCode W AN 0) (initialConfiguration W.compile
            (fun i => if i = sTape AN then writeTapeBit (r.final.tapes i) 0 ans else r.final.tapes i))) := by
      intro ans hans
      have hask := OrdinaryOracleStep.ask (oracle := o)
        (program := (coPorts Qs OUT hQ hO).program (coPieces W AN 1))
        (⟨⟨0, by decide⟩, r.final.heads, r.final.tapes⟩ : Configuration (ns + 2 + nr) 3) bits pad
        (⟨⟨1, by decide⟩, ⟨2, by decide⟩⟩ : OracleReturn 3) rfl rfl (hh _) hqt
      rw [hans] at hask
      have hheads : (fun _ : Fin (ns + 2 + nr) => (0 : ℕ)) = r.final.heads := funext fun j => (hh j).symm
      cases ans
      · have hask' : OrdinaryOracleStep o ((coPorts Qs OUT hQ hO).program (coPieces W AN 1))
            ((RepairOrdinary.frame bits).length + 1)
            (⟨⟨0, by decide⟩, r.final.heads, r.final.tapes⟩ : Configuration (ns + 2 + nr) 3)
            (⟨⟨1, by decide⟩, r.final.heads, r.final.tapes⟩ : Configuration (ns + 2 + nr) 3) := hask
        have tr1 := graph_trace (coPorts Qs OUT hQ hO) (coPieces W AN) 0 (coNext W AN FL) 1 (single hask')
        obtain ⟨rr, hrr, hrs, hrf⟩ := rec_run (ns + 2 + nr) (sTape AN) false r.final.heads r.final.tapes
        have ret2 := graph_return o (coPorts Qs OUT hQ hO) (coPieces W AN) 0 (coNext W AN FL) 1 2
          (⟨⟨1, by decide⟩, r.final.heads, r.final.tapes⟩ : Configuration (ns + 2 + nr) 3) rfl rfl
        have trR := graph_trace (coPorts Qs OUT hQ hO) (coPieces W AN) 0 (coNext W AN FL) 2
          (ordinary_trace (o := o) (coPorts Qs OUT hQ hO) (recMachine (ns + 2 + nr) (sTape AN) false) 1 _ rr hrr)
        have ret3 := graph_return o (coPorts Qs OUT hQ hO) (coPieces W AN) 0 (coNext W AN FL) 2 0 rr.final
          (by rw [hrf]; rfl) (by rw [hrf]; rfl)
        rw [hrs] at trR
        have e3 : RecoveryCalls.restarted (coPieces W AN 0).machine rr.final.heads rr.final.tapes =
            initialConfiguration W.compile
              (fun i => if i = sTape AN then writeTapeBit (r.final.tapes i) 0 false else r.final.tapes i) := by
          rw [hrf]
          simp only [RecoveryCalls.restarted, initialConfiguration, ← hheads]
          first
            | rfl
            | (congr 1; funext i; split_ifs <;> rfl)
        rw [e3] at ret3
        have T := OrdinaryOracleCompose.trans tr1 (OrdinaryOracleCompose.trans ret2
          (OrdinaryOracleCompose.trans trR ret3))
        have hc : (RepairOrdinary.frame bits).length + 1 + (1 + (1 + 1)) =
            (RepairOrdinary.frame bits).length + 4 := by ring
        rw [hc] at T
        exact T
      · have hask' : OrdinaryOracleStep o ((coPorts Qs OUT hQ hO).program (coPieces W AN 1))
            ((RepairOrdinary.frame bits).length + 1)
            (⟨⟨0, by decide⟩, r.final.heads, r.final.tapes⟩ : Configuration (ns + 2 + nr) 3)
            (⟨⟨2, by decide⟩, r.final.heads, r.final.tapes⟩ : Configuration (ns + 2 + nr) 3) := hask
        have tr1 := graph_trace (coPorts Qs OUT hQ hO) (coPieces W AN) 0 (coNext W AN FL) 1 (single hask')
        obtain ⟨rr, hrr, hrs, hrf⟩ := rec_run (ns + 2 + nr) (sTape AN) true r.final.heads r.final.tapes
        have ret2 := graph_return o (coPorts Qs OUT hQ hO) (coPieces W AN) 0 (coNext W AN FL) 1 3
          (⟨⟨2, by decide⟩, r.final.heads, r.final.tapes⟩ : Configuration (ns + 2 + nr) 3) rfl rfl
        have trR := graph_trace (coPorts Qs OUT hQ hO) (coPieces W AN) 0 (coNext W AN FL) 3
          (ordinary_trace (o := o) (coPorts Qs OUT hQ hO) (recMachine (ns + 2 + nr) (sTape AN) true) 1 _ rr hrr)
        have ret3 := graph_return o (coPorts Qs OUT hQ hO) (coPieces W AN) 0 (coNext W AN FL) 3 0 rr.final
          (by rw [hrf]; rfl) (by rw [hrf]; rfl)
        rw [hrs] at trR
        have e3 : RecoveryCalls.restarted (coPieces W AN 0).machine rr.final.heads rr.final.tapes =
            initialConfiguration W.compile
              (fun i => if i = sTape AN then writeTapeBit (r.final.tapes i) 0 true else r.final.tapes i) := by
          rw [hrf]
          simp only [RecoveryCalls.restarted, initialConfiguration, ← hheads]
          first
            | rfl
            | (congr 1; funext i; split_ifs <;> rfl)
        rw [e3] at ret3
        have T := OrdinaryOracleCompose.trans tr1 (OrdinaryOracleCompose.trans ret2
          (OrdinaryOracleCompose.trans trR ret3))
        have hc : (RepairOrdinary.frame bits).length + 1 + (1 + (1 + 1)) =
            (RepairOrdinary.frame bits).length + 4 := by ring
        rw [hc] at T
        exact T
    have hk := key _ rfl
    obtain ⟨cost, final, hcost, trI, hhaltI, houtI⟩ := ih _ (banked_write cap hb AN _)
    exact ⟨r.steps + (1 + ((RepairOrdinary.frame bits).length + 4 + cost)), final, by omega,
      OrdinaryOracleCompose.trans tr (OrdinaryOracleCompose.trans ret1 (OrdinaryOracleCompose.trans hk trI)), hhaltI, houtI⟩

/-- The word state of the framed input word: stream `0` holds `frame input`, everything else is empty. -/
def inputState (input : List Bool) : WState ns nr :=
  ⟨fun _ => 0, fun i => if i.val = 0 then RepairOrdinary.frame input else [], fun _ => 0, false⟩

theorem banked_input (input : List Bool) (hQ : Qs.val ≠ 0) (hO : OUT.val ≠ 0) :
    Banked cap (inputState (ns := ns) (nr := nr) input)
      ((coProgram W Qs AN FL OUT hQ hO).base.inputTapes input) := by
  refine ⟨fun j => ?_, fun i => ?_⟩
  · rcases PrimAsm.DockW.tape_cases j with ⟨i, rfl⟩ | rfl | ⟨q, rfl⟩
    · rw [wenc_A_s]
      show RdEq _ (if (sTape (nr := nr) i).val = 0 then RepairOrdinary.frame input else [])
      simp only [inputState, sTape]
      by_cases hi : i.val = 0 <;> simp [hi] <;> exact RdEq.refl _
    · rw [PrimAsm.DockW.wenc_A_c]
      show RdEq _ (if (cTape (ns := ns) (nr := nr)).val = 0 then RepairOrdinary.frame input else [])
      simp only [cTape, inputState]
      exact rdEq_blank _ (by simp)
    · rw [wenc_A_r]
      show RdEq _ (if (rTape (ns := ns) q).val = 0 then RepairOrdinary.frame input else [])
      simp only [rTape, inputState, if_neg (show ns + 2 + q.val ≠ 0 by omega), regTape_zero]
      exact rdEq_blank _ (by simp)
  · show (if (sTape (nr := nr) i).val = 0 then RepairOrdinary.frame input else []) = _
    simp only [inputState, sTape]
    by_cases hi : i.val = 0 <;> simp [hi]

/-- **The oracle program runs** (proof of `thm:short-pcp-ours`): the calls `CoRuns` from the framed input are an
`OrdinaryOracleRuns` of `coProgram`, within their total cost. -/
theorem coRuns_runs (o : ℕ → Bool) {output input : List Bool} {b : ℕ} (hQ : Qs.val ≠ 0) (hO : OUT.val ≠ 0)
    (h : CoRuns cap o W Qs AN FL OUT output (inputState input) b) :
    OrdinaryOracleRuns o (coProgram W Qs AN FL OUT hQ hO) input output b := by
  obtain ⟨cost, final, hc, tr, hh, hout⟩ := coRuns_trace cap (hQ := hQ) (hO := hO) o h _
    (banked_input cap input hQ hO)
  exact ⟨cost, final, hc, tr, hh, hout⟩

end Graph

end NearCubicGates.Adapters.ShortPCP.Machines
