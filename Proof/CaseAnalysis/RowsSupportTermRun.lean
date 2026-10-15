import Proof.CaseAnalysis.RowsSupportTermFinish
import Proof.CaseAnalysis.RowsSupportTermFlag

/-! The retained-field reader and actual circuit receipt now join the
complete successful term controller. The circuit supplier is explicit;
its output is not decoded or copied a second time. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.Term
open LocalBitMultitape RecoveryRootRound RecoveryExecution SignedSortKey CompetitorSumFold
open CloseoutWitness
open CloseoutWitness.TermRound (heads data)
open CompetitorValidity (Estimate)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

open private continue_run from Proof.CaseAnalysis.WitnessTermRoundRun

theorem accepted_run {s : ℕ} (circuit : Machine 1704 s) (readFuel circuitFuel : ℕ)
    (entry : Configuration 2533 (sizes s 0))
    (reader : ExecutionReceipt 2533 (sizes s 0)) (worker : ExecutionReceipt 2533 (sizes s 1))
    (hr : runFrom (programs circuit 0) readFuel entry=some reader)
    (hc : runFrom (programs circuit 1) circuitFuel
      (RecoveryCalls.restarted (programs circuit 1) reader.final.heads reader.final.tapes)=some worker)
    (hreader : reader.final.scanned 719=true)
    (P H B b position : ℕ) (q : ℚ) (a : Estimate)
    (bits source out : List Bool) (terms : Fin 725 → List Bool) (ambient : Fin 94 → List Bool)
    (extraHeads : Fin 1705 → ℕ) (extraTapes : Fin 1705 → List Bool)
    (supportHead : ℕ) (supportTape : List Bool)
    (wh : worker.final.heads=lift (heads position out extraHeads) supportHead)
    (wt : worker.final.tapes=lift (data P terms ambient out extraTapes) supportTape)
    (wch : heads position out extraHeads 2527=0)
    (wc : readTapeBit (data P terms ambient out extraTapes 2527) 0=true)
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
      runFrom (machine circuit) (readFuel+circuitFuel+TermCommit.budget P B b+2*H+13)
        (controlConfig (RecoveryCalls.code (sizes s) 0) entry)=some result ∧
      result.steps ≤ readFuel+circuitFuel+TermCommit.budget P B b+2*H+13 ∧
      result.final.heads=lift (heads position (out++TermRecord.word b q) extraHeads) supportHead ∧
      result.final.tapes=lift (data P (TermRead.data P b [] source true) next
        (out++TermRecord.word b q) nextExtra) supportTape ∧
      Store B (CompetitorRationalNumerators.add a (Mass.magnitude q)) [] next ∧
      (∀ i,nextExtra ((TermCircuitReset.privateSlot i).castAdd 2)=List.replicate H false) ∧
      nextExtra 1703=List.replicate H true ∧ nextExtra 1704=List.replicate (H+1) false ∧
      (∀ i,(∀ j,TermCircuitReset.slots j≠i.natAdd 827) → nextExtra i=extraTapes i) := by
  obtain ⟨flag,hf,_fs,fh,ft⟩:=flag_run (heads position out extraHeads)
    (data P terms ambient out extraTapes) supportHead supportTape ⟨wch,rfl⟩
  have actualFlag:runFrom (programs circuit 2) 1
      (RecoveryCalls.restarted (programs circuit 2) worker.final.heads worker.final.tapes)=some flag:=by
    rw [wh,wt]
    exact hf
  have fheads:=fh
  have ftapes:flag.final.tapes=lift (data P terms ambient out extraTapes) supportTape:=by
    rw [ft,TermRound.flag_accepted _ htrue wc]
  obtain ⟨n,hsteps,ht⟩ := prefix_to_exit circuit readFuel circuitFuel entry reader worker flag hr hc actualFlag hreader
  rw [fheads,ftapes] at ht
  obtain ⟨next,nextExtra,last,hl,ls,lh,lt,store,scratch,driver,log,keep⟩ :=
    commit_reset_run circuit P H B b position q a bits source out terms ambient extraHeads extraTapes supportHead supportTape
      htrue hstore ha hb hn hd hdecode hnum hden hsign hwidth hextra hbound hcap hbits hnative
      hh hdr hlog hscratch
  obtain ⟨r,run,rs,rh,rt⟩ := continue_run (machine circuit) _ _ last ht hl
  have bound : n+(TermCommit.budget P B b+2*H+9) ≤
      readFuel+circuitFuel+TermCommit.budget P B b+2*H+13 := by omega
  have more := runFrom_moreFuel (machine circuit) _
    (readFuel+circuitFuel+TermCommit.budget P B b+2*H+13-(n+(TermCommit.budget P B b+2*H+9))) _ r run
  rw [Nat.add_sub_of_le bound] at more
  exact ⟨next,nextExtra,r,more,by rw [rs];omega,rh.trans lh,rt.trans lt,store,scratch,driver,log,keep⟩

end NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.Term
