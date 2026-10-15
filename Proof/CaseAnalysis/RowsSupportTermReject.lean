import Proof.CaseAnalysis.RowsSupportTermFlag

/-! A false circuit verdict shares the reader/circuit prefix, folds into
the original term verdict, and stops through the existing false exit.
No mass update, coefficient append or outer circuit clear is executed. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.Term
open LocalBitMultitape RecoveryRootRound RecoveryExecution CloseoutWitness
open CloseoutWitness.TermRound (heads data flagOutput flag_bound)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
open private stopped_run from Proof.CaseAnalysis.WitnessTermRoundFinish

open private data_update from Proof.CaseAnalysis.WitnessTermRoundReject

theorem circuit_reject_run {s : ℕ} (circuit : Machine 1704 s) (readFuel circuitFuel : ℕ)
    (entry : Configuration 2533 (sizes s 0))
    (reader : ExecutionReceipt 2533 (sizes s 0)) (worker : ExecutionReceipt 2533 (sizes s 1))
    (hr : runFrom (programs circuit 0) readFuel entry=some reader)
    (hc : runFrom (programs circuit 1) circuitFuel
      (RecoveryCalls.restarted (programs circuit 1) reader.final.heads reader.final.tapes)=some worker)
    (hreader : reader.final.scanned 719=true)
    (P b position : ℕ) (source out : List Bool) (terms : Fin 725 → List Bool)
    (ambient : Fin 94 → List Bool) (extraHeads : Fin 1705 → ℕ) (extraTapes : Fin 1705 → List Bool)
    (supportHead : ℕ) (supportTape : List Bool)
    (wh : worker.final.heads=lift (heads position out extraHeads) supportHead)
    (wt : worker.final.tapes=lift (data P terms ambient out extraTapes) supportTape)
    (wch : heads position out extraHeads 2527=0)
    (wc : readTapeBit (data P terms ambient out extraTapes 2527) 0=false)
    (hP : 1 ≤ P) (hbound : ∀ i : Fin 719,(terms (TermRead.scratchSlots i)).length ≤ P)
    (hwidth : terms 149=ZeroPadding.pad P (List.replicate b true))
    (hextra : ∀ i,terms (i.natAdd 720)=TermRead.extra P source true i) :
    ∃ result,runFrom (machine circuit) (readFuel+circuitFuel+2*P+12)
        (controlConfig (RecoveryCalls.code (sizes s) 0) entry)=some result ∧
      result.steps ≤ readFuel+circuitFuel+2*P+12 ∧
      result.final.heads 724=0 ∧ result.final.tapes 724=[false] := by
  let left := data P terms ambient out extraTapes 2527
  let changed := Function.update terms 719 (flagOutput left (terms 719))
  have hlen : (terms 719).length ≤ P := by
    obtain ⟨i,hi⟩ := TermRead.scratch_covers 719 (by decide)
    have h:=hbound i
    rw [hi] at h
    exact h
  have bad : readTapeBit (changed 719) 0=false := by
    rw [show changed=Function.update terms 719 (flagOutput left (terms 719)) by rfl,Function.update_self]
    unfold flagOutput
    rw [wc,Bool.and_false]
    cases terms 719 <;> rfl
  obtain ⟨flag,hf,_fs,fh,ft⟩:=flag_run (heads position out extraHeads)
    (data P terms ambient out extraTapes) supportHead supportTape ⟨wch,rfl⟩
  have actualFlag:runFrom (programs circuit 2) 1
      (RecoveryCalls.restarted (programs circuit 2) worker.final.heads worker.final.tapes)=some flag:=by
    rw [wh,wt]
    exact hf
  have fheads:=fh
  have ftapes:flag.final.tapes=lift (data P changed ambient out extraTapes) supportTape:=by
    rw [ft]
    exact congrArg (fun A=>lift A supportTape)
      (data_update P terms ambient out (flagOutput left (terms 719)) extraTapes)
  obtain ⟨n,hn,ht⟩ := prefix_to_exit circuit readFuel circuitFuel entry reader worker flag hr hc actualFlag hreader
  rw [fheads,ftapes] at ht
  obtain ⟨last,hl,_ls,lh,lt⟩ := TermExit.reject_run P b position source out true changed ambient hP bad
    (by intro i
        by_cases hi : TermRead.scratchSlots i=719
        · rw [show changed=Function.update terms 719 (flagOutput left (terms 719)) by rfl,hi,Function.update_self]
          exact flag_bound P left (terms 719) hP hlen
        · rw [show changed=Function.update terms 719 (flagOutput left (terms 719)) by rfl,Function.update_of_ne hi]
          exact hbound i)
    (by rw [show changed=Function.update terms 719 (flagOutput left (terms 719)) by rfl,
          Function.update_of_ne (by decide)];exact hwidth)
    (by intro i
        rw [show changed=Function.update terms 719 (flagOutput left (terms 719)) by rfl,
          Function.update_of_ne (by apply Fin.ne_of_val_ne;change 720+i.val≠719;omega)]
        exact hextra i)
  let finalOld := TapeEmbedding.receipt extraHeads extraTapes last
  have finalOldRun := TapeEmbedding.run_embed TermExit.machine extraHeads extraTapes _ _ last hl
  have finalHeads : finalOld.final.heads=heads position out extraHeads := by
    change Fin.addCases (m:=827) (n:=1705) (motive:=fun _=>ℕ) last.final.heads extraHeads=_
    rw [lh];rfl
  have finalTapes : finalOld.final.tapes=data P (TermRead.data P b [] source false) ambient out extraTapes := by
    change Fin.addCases (m:=827) (n:=1705) (motive:=fun _=>List Bool) last.final.tapes extraTapes=_
    rw [lt];rfl
  let final:=TapeEmbedding.receipt (fun _ : Fin 1=>supportHead) (fun _=>supportTape) finalOld
  have finalRun:=TapeEmbedding.run_embed TermRound.ending (fun _ : Fin 1=>supportHead)
    (fun _=>supportTape) _ _ finalOld finalOldRun
  have finalFlag:final.final.scanned 724=false:=by
    change readTapeBit (finalOld.final.tapes 724) (finalOld.final.heads 724)=false
    rw [finalHeads,finalTapes];rfl
  obtain ⟨m,hm,tail⟩ := rejected_exit circuit (2*P+7) _ final finalRun finalFlag
  obtain ⟨r,run,rs,rh,rt⟩ := stopped_run (sizes s) (programs circuit) 0 next _
    final.final.heads final.final.tapes (ht.trans tail)
  have bound : n+m ≤ readFuel+circuitFuel+2*P+12 := by omega
  have more := runFrom_moreFuel (machine circuit) _ (readFuel+circuitFuel+2*P+12-(n+m)) _ r run
  rw [Nat.add_sub_of_le bound] at more
  refine ⟨r,more,rs.le.trans bound,?_,?_⟩
  · rw [rh]
    change finalOld.final.heads 724=0
    rw [finalHeads];rfl
  · rw [rt]
    change finalOld.final.tapes 724=[false]
    rw [finalTapes];rfl

end NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.Term
