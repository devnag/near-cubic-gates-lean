import SourceAdapters.Proximity.TrimHonestFinish
import SourceAdapters.Proximity.TrimHonestLoop
import SourceAdapters.Proximity.HonestFullAllocationCost

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": one initialized program loads the original proof,
constructs every canonical auxiliary row and emits the exact restriction. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.TrimHonest
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicGates.Close.Cells
open NearCubicGates.Published.CW19Proximity NearCubicGates.Adapters.Joins

def fullProgram (q : ℕ) : St VV MM :=
  .seq (HonestPrepared.program q)
    (.seq (HonestCoinSetup.script q) (.seq (loopProgram q) outputProgram))

variable {q : ℕ} (V : (S : SourceCircuit) → NonadaptiveVerifier S.arity q)
    (proofSize : SourceCircuit → ℕ)
    (honest : (p : AcceptedSourceInput) → BitInput (proofSize p.1)) (K e a : ℕ)
    (P : WordFunction (ProofCall V) (proofCallInput V) (normalizedProofOutput V proofSize honest)
      (fun r => K * ((proofCallInput V r).length + 1) ^ e))

theorem full_run (p : AcceptedSourceInput) (Wd Lk Bk : ℕ)
    (H : HonestFullAllocation.AllBounds V proofSize honest K e a p Wd Lk Bk) :
    let C := SourceCallee.context V proofSize honest _ P Wd
      (LengthPrefix.wrapped (preparedHonestInput V p)) Lk Bk
    Hs C (fullProgram q) (a0 : DS VV MM) (HonestFullAllocation.cost V proofSize K e a p Lk Bk)
      (fun b => b.out = preparedHonestOutput V proofSize honest p) := by
  dsimp only
  rw [prepared_shape V p]
  let C := SourceCallee.context V proofSize honest _ P Wd
    (preparedPrefix V p ++ sourceCircuitWord p.1 ++ preparedTail V p) Lk Bk
  have initial := HonestPrepared.initial_run V proofSize honest _ P p Wd Lk Bk
    H.initial.1 H.initial.2.1 H.initial.2.2.1 H.initial.2.2.2.1 H.initial.2.2.2.2.1
    H.initial.2.2.2.2.2.1 H.initial.2.2.2.2.2.2
  rw [prepared_shape V p] at initial
  obtain ⟨b, nb, eb, hb, rb⟩ := initial
  have cb := initial_row_state (C := C) rb H.input_width H.initial.2.2.2.2.1
  have cursor_eq : preparedCursor V p = (preparedPrefix V p).length := rfl
  rw [cursor_eq] at cb
  have coin := HonestCoinSetup.run V proofSize honest _ P p.1 Wd Lk Bk
    (preparedPrefix V p) (preparedTail V p) b rb.constants H.coin.1 rb.source_length
    rb.cursor rb.kin H.coin.2.1 H.coin.2.2.1 H.coin.2.2.2.1 H.coin.2.2.2.2.1 H.coin.2.2.2.2.2
  obtain ⟨c, nc, ec, hc, rc⟩ := coin
  have cc := ready_after_coins cb rc
  have ac := auxiliary_after_coins (initial_auxiliary rb) rc
  have loop := loop_run V proofSize honest _ P p.1 p.2.val (honest p) Wd Lk Bk
    (HonestRowTable.rowWidth V K e a p) (preparedPrefix V p) (preparedTail V p) c
    cc ac rc.coins H.coin_width H.rows
    H.local_sum_width H.key_width H.auxiliary_count_width
  obtain ⟨d, nd, ed, hd, rd⟩ := loop
  have ready := rd.auxiliary.complete rd.ready.oracle H.auxiliary_count_width
  have run := finish_run (C := C) V proofSize honest p d rd.ready.source.constants ready
    (rd.schedule.trans ((congrFun rc.ram scheduleStore).trans rb.schedule_ram))
    ((rd.vars scheduleLength (by decide)).trans
      ((rc.vars scheduleLength (by decide)).trans rb.schedule_count))
    (rd.schedule_cursor.trans ((congrFun rc.rc scheduleStore).trans rb.schedule_cursor))
    (rd.out.trans (rc.out.trans rb.out)) H.schedule_value_width H.schedule_count_width
  obtain ⟨z, nz, ez, hz, rz⟩ := run
  refine ⟨z, _, Ex.seq eb (Ex.seq ec (Ex.seq ed ez)), ?_, rz⟩
  unfold HonestFullAllocation.cost HonestFullAllocation.outputCost finishCost at *
  rw [auxKeys_length]
  omega

end NearCubicGates.Adapters.Proximity.TrimHonest
