import Proof.MachineModel.OrdinaryMatrixScoreGateOrder

/-! The enclosing 2U-record traversal pays its final stream terminator and
returns exactly the existing gateRecords tape, ready for the sort handoff. -/
namespace NearCubicWires.RepairOrdinary.MatrixScoreGateStream
open LocalBitMultitape RecoveryExecution SignedSortKey MatrixScoreBatch MatrixScoreHalvesReset
open MatrixScoreLeftLoop (C State)
open MatrixScoreWeight (zeros)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def closeMachine : Machine 30 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==1
  rule := fun q _ => if q.val=0 then some ⟨1,fun i => if i=24 then some false else none,
    fun i => if i=24 then .right else .stay⟩ else none
noncomputable def machine := Composition.machine MatrixScoreBothHalves.machine closeMachine
def budget (r : Request) := MatrixScoreBothHalves.budget r+2

theorem close_run (source : List Bool) (d n c w x m id template U returnCap : ℕ)
    (work : Fin 12 → List Bool) (driver counter out : List Bool) (cols : List ℕ) :
    ∃ actual,runFrom closeMachine 1
      (RecoveryCalls.restarted closeMachine (heads out.length)
        (tapes source d n c w x m id template U returnCap work driver counter out cols))=some actual ∧
      actual.final.heads=heads (out++[false]).length ∧
      actual.final.tapes=tapes source d n c w x m id template U returnCap work driver counter (out++[false]) cols ∧
      actual.steps=1 := by
  let start := RecoveryCalls.restarted closeMachine (heads out.length)
    (tapes source d n c w x m id template U returnCap work driver counter out cols)
  let finish : Configuration 30 2 := ⟨1,heads (out++[false]).length,
    tapes source d n c w x m id template U returnCap work driver counter (out++[false]) cols⟩
  have he : step closeMachine start=some finish := by
    simp [step,closeMachine,start,RecoveryCalls.restarted]
    apply configuration_ext
    · rfl
    · funext i
      fin_cases i
      all_goals first
        | rfl
        | change out.length+1=(out++[false]).length
          simp
    · funext i
      fin_cases i
      all_goals first
        | rfl
        | change writeTapeBit out out.length false=out++[false]
          exact Streaming.write_append out false
  obtain ⟨actual,hr,hf,hs⟩ := (Timed.single (by rfl) he).run (by rfl)
  exact ⟨actual,hr,congrArg Configuration.heads hf,congrArg Configuration.tapes hf,hs⟩

theorem gate_run (r : Request) (gate : Fin r.Gates) (state : State r) (cap : ℕ) (driver counter out : List Bool)
    (hcap : cap≤C r+1) (hd : driver.length≤C r) (hc : counter.length≤C r) :
    ∃ final : State r,∃ actual,runFrom machine (budget r)
      (Composition.leftConfig 2 (MatrixScoreBothHalves.initial r gate state cap driver counter out))=some actual ∧
      actual.final.heads=heads (out++gateRecords r gate).length ∧
      actual.final.tapes=tapes (cutWord r.p (r.cuts.get gate)) r.width (r.phi (r.U-1))
        (C r) (r.S+1) (2^r.S) r.M (r.U+(r.U-1)) r.U r.U final.returnCap final.work
        (ZeroPadding.pad (C r) [true,true]) (zeros (C r)) (out++gateRecords r gate) r.cols ∧ actual.steps≤budget r := by
  obtain ⟨final,body,hb,bh,bt,bs⟩ := MatrixScoreBothHalves.both_run r gate state cap driver counter out hcap hd hc
  obtain ⟨last,hl,lh,lt,ls⟩ := close_run (cutWord r.p (r.cuts.get gate)) r.width (r.phi (r.U-1))
    (C r) (r.S+1) (2^r.S) r.M (r.U+(r.U-1)) r.U r.U final.returnCap final.work
    (ZeroPadding.pad (C r) [true,true]) (zeros (C r)) (out++MatrixScoreBothHalves.records r gate) r.cols
  have hi : Composition.restart body.final closeMachine.start=
      RecoveryCalls.restarted closeMachine (heads (out++MatrixScoreBothHalves.records r gate).length)
        (tapes (cutWord r.p (r.cuts.get gate)) r.width (r.phi (r.U-1)) (C r) (r.S+1) (2^r.S) r.M (r.U+(r.U-1))
          r.U r.U final.returnCap final.work (ZeroPadding.pad (C r) [true,true]) (zeros (C r))
          (out++MatrixScoreBothHalves.records r gate) r.cols) := by
    apply configuration_ext
    · rfl
    · exact bh
    · exact bt
  rw [← hi] at hl
  have joined := Composition.run_join MatrixScoreBothHalves.machine closeMachine _ 1 _ body last hb hl
  have he : (out++MatrixScoreBothHalves.records r gate)++[false]=out++gateRecords r gate := by
    rw [MatrixScoreGateOrder.records_eq]
    simp only [List.append_assoc,gateRecords,StablePartition.stream]
  rw [he] at lh lt
  refine ⟨final,Composition.joinedReceipt body last,?_,lh,lt,?_⟩
  · simpa only [budget,Nat.add_assoc,Nat.reduceAdd,machine] using joined
  · change body.steps+1+last.steps≤_
    unfold budget
    omega

end NearCubicWires.RepairOrdinary.MatrixScoreGateStream
