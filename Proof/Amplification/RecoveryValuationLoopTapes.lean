import Proof.Amplification.RecoveryValuationTableReturn

/-! Table repetition on the same ten tapes as its count producer. The
retained cap and both unary driver positions are literal configurations. -/
namespace NearCubicWires.RepairOrdinary.RecoveryValuationCount
open LocalBitMultitape RecoveryExecution RecoveryValuationStream
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable abbrev loopMachine := TapeEmbedding.machine 1 RecoveryValuationTable.machine

private theorem loop_input (x : RecoveryValuationTable.Cursor) (count cap : Nat) :
    TapeEmbedding.config (fun _ : Fin 1=>1) (fun _=>CompareMachine.word cap)
      (RepeatMachine.cfg 0 (RecoveryValuationTable.source x) count 1)=cfg x.data count cap loopMachine.start := by
  apply configuration_ext <;> rfl

private theorem loop_output (x : RecoveryValuationTable.Cursor) (count cap : Nat) :
    TapeEmbedding.config (fun _ : Fin 1=>1) (fun _=>CompareMachine.word cap)
      (RepeatMachine.cfg 3 (RecoveryValuationTable.source x) count 1)=
      cfg x.data count cap (RepeatMachine.phaseCode (Fintype.card (RecoveryCalls.Control sizes)) 3) := by
  apply configuration_ext <;> rfl

theorem loop_run (width count cap : Nat) (x : RecoveryValuationTable.Cursor)
    (hx : RecoveryValuationTable.Inv width x) :
    ∃ r,runFrom loopMachine (count*(budget width+3)+3) (cfg x.data count cap loopMachine.start)=some r ∧
      r.steps≤count*(budget width+3)+3 ∧ r.final.heads 7=0 ∧ (∃ old,r.final.tapes 7=[old]) ∧
      (r.final.control=RepeatMachine.phaseCode (Fintype.card (RecoveryCalls.Control sizes)) 3 ↔
        (readMany (readEntry x.data.width) count x.rest).isSome=true) ∧
      ((readMany (readEntry x.data.width) count x.rest).isSome=true →
        r.final=cfg (RepeatMachine.iterate RecoveryValuationTable.next count x).2.data count cap
          (RepeatMachine.phaseCode (Fintype.card (RecoveryCalls.Control sizes)) 3)) := by
  obtain ⟨base,hr,ht,hf,hh,hbad⟩ := RecoveryValuationTable.table_return width count x hx
  have hrun := TapeEmbedding.run_embed RecoveryValuationTable.machine (fun _ : Fin 1=>1)
    (fun _=>CompareMachine.word cap) _ _ base hr
  rw [loop_input x count cap] at hrun
  let r := TapeEmbedding.receipt (fun _ : Fin 1=>1) (fun _=>CompareMachine.word cap) base
  have hout : (readMany (readEntry x.data.width) count x.rest).isSome=true →
      r.final=cfg (RepeatMachine.iterate RecoveryValuationTable.next count x).2.data count cap
        (RepeatMachine.phaseCode (Fintype.card (RecoveryCalls.Control sizes)) 3) := by
    intro ha
    rw [←RecoveryValuationTable.iterate_accepts] at ha
    simp only [RepeatMachine.Result,ha,↓reduceIte] at hf
    change TapeEmbedding.config _ _ base.final=_
    rw [hf]
    exact loop_output _ count cap
  refine ⟨r,hrun,ht,?_,?_,?_,hout⟩
  · change base.final.heads 7=0
    exact hh
  · cases ha : (readMany (readEntry x.data.width) count x.rest).isSome with
    | false =>
      refine ⟨false,?_⟩
      change base.final.tapes 7=[false]
      exact hbad ha
    | true =>
      rw [hout ha]
      exact ⟨_,rfl⟩
  · exact RecoveryValuationTable.result_acceptance count x base.final hf

end NearCubicWires.RepairOrdinary.RecoveryValuationCount
