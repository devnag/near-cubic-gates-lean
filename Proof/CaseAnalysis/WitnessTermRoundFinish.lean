import Proof.CaseAnalysis.WitnessTermRoundCalls

/-! A successful literal term commits its original coefficient and clears
exactly the private circuit bank. This is the actual last two calls of the
fixed term controller; the failed exit never uses this clearing receipt. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.TermRound
open LocalBitMultitape RecoveryRootRound RecoveryExecution SignedSortKey CompetitorSumFold
open CompetitorValidity (Estimate)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

private theorem reset_external (j : Fin 1699) :
    ∃ i : Fin 1705,TermCircuitReset.slots j=i.natAdd 827 := by
  have hlow : 827 ≤ (TermCircuitReset.slots j).val := by
    unfold TermCircuitReset.slots
    split_ifs
    · change 827 ≤ 827+_
      omega
    · change 827 ≤ j.val+833
      omega
  refine ⟨⟨(TermCircuitReset.slots j).val-827,by have h:=(TermCircuitReset.slots j).isLt;omega⟩,?_⟩
  apply Fin.ext
  simp only [Fin.val_natAdd]
  omega

private theorem stopped_run {t k n : ℕ} (sizes : Fin k → ℕ)
    (programs : (j : Fin k) → Machine t (sizes j)) (entry : Fin k)
    (next : (j : Fin k) → Fin (sizes j) → (Fin t → Bool) → Option (Fin k))
    (input : Configuration t (Fintype.card (RecoveryCalls.Control sizes)))
    (heads : Fin t → ℕ) (tapes : Fin t → List Bool)
    (h : Timed (RecoveryCalls.machine sizes programs entry next) n input
      (RecoveryCalls.stopped sizes heads tapes)) :
    ∃ r,runFrom (RecoveryCalls.machine sizes programs entry next) n input=some r ∧
      r.steps=n ∧ r.final.heads=heads ∧ r.final.tapes=tapes := by
  obtain ⟨r,hr,rf,rs⟩ := h.run (by
    simp only [RecoveryCalls.machine,RecoveryCalls.stopped,Equiv.symm_apply_apply,Option.isNone_none])
  exact ⟨r,hr,rs,by rw [rf];rfl,by rw [rf];rfl⟩

theorem commit_reset_run {s : ℕ} (circuit : Machine 1703 s)
    (P H B b position : ℕ) (q : ℚ) (a : Estimate)
    (bits source out : List Bool) (terms : Fin 725 → List Bool) (ambient : Fin 94 → List Bool)
    (extraHeads : Fin 1705 → ℕ) (extraTapes : Fin 1705 → List Bool)
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
          (RecoveryCalls.restarted ending (heads position out extraHeads)
            (data P terms ambient out extraTapes)))=some result ∧
      result.steps ≤ TermCommit.budget P B b+2*H+9 ∧
      result.final.heads=heads position (out++TermRecord.word b q) extraHeads ∧
      result.final.tapes=data P (TermRead.data P b [] source true) next
        (out++TermRecord.word b q) nextExtra ∧
      Store B (CompetitorRationalNumerators.add a (Mass.magnitude q)) [] next ∧
      (∀ i,nextExtra ((TermCircuitReset.privateSlot i).castAdd 2)=List.replicate H false) ∧
      nextExtra 1703=List.replicate H true ∧ nextExtra 1704=List.replicate (H+1) false ∧
      (∀ i,(∀ j,TermCircuitReset.slots j≠i.natAdd 827) → nextExtra i=extraTapes i) := by
  let out' := out++TermRecord.word b q
  obtain ⟨next,last,hl,ls,lh,lt,store⟩ := TermExit.accept_run P B b position q a bits source out true
    terms ambient htrue hstore ha hb hn hd hdecode hnum hden hsign hwidth hextra hbound hcap hbits hnative
  let committed := TapeEmbedding.receipt extraHeads extraTapes last
  have committedRun := TapeEmbedding.run_embed TermExit.machine extraHeads extraTapes _ _ last hl
  have committedHeads : committed.final.heads=heads position out' extraHeads := by
    change Fin.addCases (m:=827) (n:=1705) (motive:=fun _=>ℕ) last.final.heads extraHeads=_
    rw [lh];rfl
  have committedTapes : committed.final.tapes=data P (TermRead.data P b [] source true) next out' extraTapes := by
    change Fin.addCases (m:=827) (n:=1705) (motive:=fun _=>List Bool) last.final.tapes extraTapes=_
    rw [lt];rfl
  obtain ⟨cleared,clearRun,cs,ch,ct,cd,cl,keep⟩ := TermCircuitReset.reset_run H
    (heads position out' extraHeads) (data P (TermRead.data P b [] source true) next out' extraTapes)
    (by intro i
        obtain ⟨j,hj⟩ := reset_external i
        have h:=hh i
        rw [hj] at h ⊢
        simpa only [heads,Fin.addCases_right] using h)
    hdr hlog (by
      intro i
      have he : TermCircuitReset.scratch i=((TermCircuitReset.privateSlot i).castAdd 2).natAdd 827 := Fin.ext rfl
      rw [he]
      simpa only [data,Fin.addCases_right] using hscratch i)
  have hclear : runFrom (programs circuit 4) (2*H+4)
      (RecoveryCalls.restarted (programs circuit 4) committed.final.heads committed.final.tapes)=some cleared := by
    rw [committedHeads,committedTapes]
    exact clearRun
  have accepted : committed.final.scanned 724=true := by
    change readTapeBit (committed.final.tapes 724) (committed.final.heads 724)=true
    rw [committedHeads,committedTapes]
    rfl
  obtain ⟨n,hn,ht⟩ := accepted_exit circuit (TermCommit.budget P B b+3) (2*H+4) _ committed cleared
    committedRun hclear accepted
  obtain ⟨result,run,rs,finalHeads,finalTapes⟩ := stopped_run (sizes s) (programs circuit) 0 TermRound.next
    _ cleared.final.heads cleared.final.tapes ht
  have bound : n ≤ TermCommit.budget P B b+2*H+9 := by omega
  have more := runFrom_moreFuel (machine circuit) n (TermCommit.budget P B b+2*H+9-n) _ result run
  rw [Nat.add_sub_of_le bound] at more
  let nextExtra := fun i : Fin 1705=>cleared.final.tapes (i.natAdd 827)
  refine ⟨next,nextExtra,result,more,rs.le.trans bound,?_,?_,store,?_,cd,cl,?_⟩
  · exact finalHeads.trans ch
  · rw [finalTapes]
    change cleared.final.tapes=data P (TermRead.data P b [] source true) next out' nextExtra
    funext i
    refine Fin.addCases (m:=827) (n:=1705) ?_ ?_ i
    · intro j
      simpa only [data,Fin.addCases_left] using keep _ (TermCircuitReset.term_outside j)
    · intro j
      simp only [data,Fin.addCases_right,nextExtra]
  · intro i
    exact ct i
  · intro i hi
    simpa only [nextExtra,data,Fin.addCases_right] using keep _ hi

end NearCubicWires.RepairOrdinary.CloseoutWitness.TermRound
