import Proof.CaseAnalysis.RowsSupportTermCalls

/-! The original one-step flag fold preserves the new support accumulator. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.Term
open LocalBitMultitape CloseoutWitness
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem flag_run (H : Fin 2532 → ℕ) (A : Fin 2532 → List Bool) (sh : ℕ) (st : List Bool)
    (hh : H 2527=0 ∧ H 719=0) :
    ∃ r,runFrom (TapeEmbedding.machine 1 TermRound.foldFlag) 1
      ⟨(TapeEmbedding.machine 1 TermRound.foldFlag).start,lift H sh,lift A st⟩=some r ∧
      r.steps=1 ∧ r.final.heads=lift H sh ∧ r.final.tapes=lift (TermRound.flagged A) st :=by
  obtain ⟨old,hr,rs,rh,rt⟩:=TermRound.flag_run H A hh
  let r:=TapeEmbedding.receipt (fun _ : Fin 1=>sh) (fun _=>st) old
  have run:=TapeEmbedding.run_embed TermRound.foldFlag (fun _ : Fin 1=>sh) (fun _=>st) 1 _ old hr
  refine ⟨r,run,rs,?_,?_⟩
  · change lift old.final.heads sh=lift H sh
    rw [rh]
  · change lift old.final.tapes st=lift (TermRound.flagged A) st
    rw [rt]

end NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.Term
