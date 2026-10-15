import Proof.CaseAnalysis.RowsSupportTermCalls

/-! A successful literal term commits its original coefficient and clears
exactly the private circuit bank. This is the actual last two calls of the
fixed term controller; the failed exit never uses this clearing receipt. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.Term
open LocalBitMultitape RecoveryRootRound RecoveryExecution SignedSortKey CompetitorSumFold
open CloseoutWitness
open CloseoutWitness.TermRound (heads data)
open CompetitorValidity (Estimate)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

open private reset_external stopped_run from Proof.CaseAnalysis.WitnessTermRoundFinish

theorem commit_reset_run {s : ℕ} (circuit : Machine 1704 s)
    (P H B b position : ℕ) (q : ℚ) (a : Estimate)
    (bits source out : List Bool) (terms : Fin 725 → List Bool) (ambient : Fin 94 → List Bool)
    (extraHeads : Fin 1705 → ℕ) (extraTapes : Fin 1705 → List Bool)
    (supportHead : ℕ) (supportTape : List Bool)
    (htrue : readTapeBit (terms 719) 0=true) (hstore : Store B a [] ambient) (ha : a.Valid B)
    (hb : b ≤ B) (hn : q.num.natAbs < 2^b) (hd : q.den < 2^b)
    (hdecode : CanonicalWitnessCodec.decodeCanonicalRational (RadixSemantics.value bits)=some q)
    (hnum : terms 690=ZeroPadding.pad P (frame (binary b q.num.natAbs)))
    (hden : terms 693=ZeroPadding.pad P (frame (binary b q.den)))
    (hsign : terms 316=ZeroPadding.pad P (frame (RecoveryFixedUnpair.leftWord (RationalCold.numeratorWord bits))))
    (hwidth : terms 149=ZeroPadding.pad P (List.replicate b true))
    (hextra : ∀ i,terms (i.natAdd 720)=TermRead.extra P source true i)
    (hbound : ∀ i : Fin 719,(terms (TermRead.scratchSlots i)).length ≤ P)
    (hcap : MassStep.budget B+1 ≤ P) (hbits : 2*b+1 ≤ P)
    (hnative : CompetitorReusableDecision.capacity B+1 ≤ P)
    (hh : ∀ i,heads position out extraHeads (TermCircuitReset.slots i)=0)
    (hdr : extraTapes 1703=List.replicate H true)
    (hlog : extraTapes 1704=List.replicate (H+1) false)
    (hscratch : ∀ i,(extraTapes ((TermCircuitReset.privateSlot i).castAdd 2)).length ≤ H) :
    ∃ next nextExtra result,
      runFrom (machine circuit) (TermCommit.budget P B b+2*H+9)
        (controlConfig (RecoveryCalls.code (sizes s) 3)
          (RecoveryCalls.restarted (programs circuit 3) (lift (heads position out extraHeads) supportHead)
            (lift (data P terms ambient out extraTapes) supportTape)))=some result ∧
      result.steps ≤ TermCommit.budget P B b+2*H+9 ∧
      result.final.heads=lift (heads position (out++TermRecord.word b q) extraHeads) supportHead ∧
      result.final.tapes=lift (data P (TermRead.data P b [] source true) next
        (out++TermRecord.word b q) nextExtra) supportTape ∧
      Store B (CompetitorRationalNumerators.add a (Mass.magnitude q)) [] next ∧
      (∀ i,nextExtra ((TermCircuitReset.privateSlot i).castAdd 2)=List.replicate H false) ∧
      nextExtra 1703=List.replicate H true ∧ nextExtra 1704=List.replicate (H+1) false ∧
      (∀ i,(∀ j,TermCircuitReset.slots j≠i.natAdd 827) → nextExtra i=extraTapes i) := by
  let out' := out++TermRecord.word b q
  obtain ⟨next,last,hl,ls,lh,lt,store⟩ := TermExit.accept_run P B b position q a bits source out true
    terms ambient htrue hstore ha hb hn hd hdecode hnum hden hsign hwidth hextra hbound hcap hbits hnative
  let committedOld := TapeEmbedding.receipt extraHeads extraTapes last
  have committedOldRun := TapeEmbedding.run_embed TermExit.machine extraHeads extraTapes _ _ last hl
  have committedHeads : committedOld.final.heads=heads position out' extraHeads := by
    change Fin.addCases (m:=827) (n:=1705) (motive:=fun _=>ℕ) last.final.heads extraHeads=_
    rw [lh];rfl
  have committedTapes : committedOld.final.tapes=data P (TermRead.data P b [] source true) next out' extraTapes := by
    change Fin.addCases (m:=827) (n:=1705) (motive:=fun _=>List Bool) last.final.tapes extraTapes=_
    rw [lt];rfl
  obtain ⟨cleared,clearRun,cs,ch,ct,cd,cl,keep⟩ := TermCircuitReset.reset_run H
    (heads position out' extraHeads) (data P (TermRead.data P b [] source true) next out' extraTapes)
    (by intro i
        obtain ⟨j,hj⟩ := reset_external i
        have h:=hh i
        rw [hj] at h ⊢
        simpa only [TermRound.heads,Fin.addCases_right] using h)
    hdr hlog (by
      intro i
      have he : TermCircuitReset.scratch i=((TermCircuitReset.privateSlot i).castAdd 2).natAdd 827 := Fin.ext rfl
      rw [he]
      simpa only [TermRound.data,Fin.addCases_right] using hscratch i)
  let committed:=TapeEmbedding.receipt (fun _ : Fin 1=>supportHead) (fun _=>supportTape) committedOld
  let liftedClear:=TapeEmbedding.receipt (fun _ : Fin 1=>supportHead) (fun _=>supportTape) cleared
  have committedRun:=TapeEmbedding.run_embed TermRound.ending (fun _ : Fin 1=>supportHead)
    (fun _=>supportTape) _ _ committedOld committedOldRun
  have oldClear:runFrom TermCircuitReset.machine (2*H+4)
      (RecoveryCalls.restarted TermCircuitReset.machine committedOld.final.heads committedOld.final.tapes)=some cleared:=by
    rw [committedHeads,committedTapes]
    exact clearRun
  have hclear:runFrom (programs circuit 4) (2*H+4)
      (RecoveryCalls.restarted (programs circuit 4) committed.final.heads committed.final.tapes)=some liftedClear:=
    TapeEmbedding.run_embed TermCircuitReset.machine (fun _ : Fin 1=>supportHead) (fun _=>supportTape) _ _ cleared oldClear
  have accepted:committed.final.scanned 724=true:=by
    change readTapeBit (committedOld.final.tapes 724) (committedOld.final.heads 724)=true
    rw [committedHeads,committedTapes]
    rfl
  obtain ⟨n,hn,ht⟩ := accepted_exit circuit (TermCommit.budget P B b+3) (2*H+4) _ committed liftedClear
    committedRun hclear accepted
  obtain ⟨result,run,rs,finalHeads,finalTapes⟩ := stopped_run (sizes s) (programs circuit) 0 CloseoutRowsSupportStream.Term.next
    _ liftedClear.final.heads liftedClear.final.tapes ht
  have bound : n ≤ TermCommit.budget P B b+2*H+9 := by omega
  have more := runFrom_moreFuel (machine circuit) n (TermCommit.budget P B b+2*H+9-n) _ result run
  rw [Nat.add_sub_of_le bound] at more
  let nextExtra := fun i : Fin 1705=>cleared.final.tapes (i.natAdd 827)
  refine ⟨next,nextExtra,result,more,rs.le.trans bound,?_,?_,store,?_,cd,cl,?_⟩
  · rw [finalHeads]
    change lift cleared.final.heads supportHead=lift (heads position out' extraHeads) supportHead
    rw [ch]
  · rw [finalTapes]
    change lift cleared.final.tapes supportTape=lift (data P (TermRead.data P b [] source true) next out' nextExtra) supportTape
    congr 1
    funext i
    refine Fin.addCases (m:=827) (n:=1705) ?_ ?_ i
    · intro j
      simpa only [TermRound.data,Fin.addCases_left] using keep _ (TermCircuitReset.term_outside j)
    · intro j
      simp only [TermRound.data,Fin.addCases_right,nextExtra]
  · intro i
    exact ct i
  · intro i hi
    simpa only [nextExtra,TermRound.data,Fin.addCases_right] using keep _ hi

end NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.Term
