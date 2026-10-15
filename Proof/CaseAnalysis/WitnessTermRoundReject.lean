import Proof.CaseAnalysis.WitnessTermRoundRun

/-! A false circuit verdict shares the reader/circuit prefix, folds into
the original term verdict, and stops through the existing false exit.
No mass update, coefficient append or outer circuit clear is executed. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.TermRound
open LocalBitMultitape RecoveryRootRound RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
open private stopped_run from Proof.CaseAnalysis.WitnessTermRoundFinish

private theorem data_update (P : ℕ) (terms : Fin 725 → List Bool) (ambient : Fin 94 → List Bool)
    (out bits : List Bool) (extra : Fin 1705 → List Bool) :
    Function.update (data P terms ambient out extra) 719 bits=
      data P (Function.update terms 719 bits) ambient out extra := by
  funext i
  refine Fin.addCases (m:=827) (n:=1705) ?_ ?_ i
  · intro j
    refine Fin.addCases (m:=826) (n:=1) ?_ ?_ j
    · intro k
      refine Fin.addCases (m:=725) (n:=101) ?_ ?_ k
      · intro l
        by_cases hl : l=719
        · subst l
          change Function.update (data P terms ambient out extra) (719 : Fin 2532) bits 719=
            Function.update terms (719 : Fin 725) bits 719
          rw [Function.update_self,Function.update_self]
        · have hi : (((l.castAdd 101).castAdd 1).castAdd 1705 : Fin 2532)≠719 := by
            intro h;apply hl;exact Fin.ext (congrArg (fun z : Fin 2532=>z.val) h)
          rw [Function.update_of_ne hi]
          simp only [data,Fin.addCases_left]
          change TermCommit.data _ _ _ _ (TermCommit.eraseSlots l)=TermCommit.data _ _ _ _ (TermCommit.eraseSlots l)
          rw [TermCommit.data_core,TermCommit.data_core,Function.update_of_ne hl]
      · intro l
        rw [Function.update_of_ne (by apply Fin.ne_of_val_ne;change 725+l.val≠719;omega)]
        simp only [data,TermCommit.data,Fin.addCases_left,TermMass.data,Fin.addCases_right]
    · intro k
      rw [Function.update_of_ne (by apply Fin.ne_of_val_ne;change 826+k.val≠719;omega)]
      simp only [data,Fin.addCases_left,TermCommit.data,Fin.addCases_right]
  · intro j
    rw [Function.update_of_ne (by apply Fin.ne_of_val_ne;change 827+j.val≠719;omega)]
    simp only [data,Fin.addCases_right]

theorem circuit_reject_run {s : ℕ} (circuit : Machine 1703 s) (readFuel circuitFuel : ℕ)
    (entry : Configuration 2532 (sizes s 0))
    (reader : ExecutionReceipt 2532 (sizes s 0)) (worker : ExecutionReceipt 2532 (sizes s 1))
    (hr : runFrom (programs circuit 0) readFuel entry=some reader)
    (hc : runFrom (programs circuit 1) circuitFuel
      (RecoveryCalls.restarted (programs circuit 1) reader.final.heads reader.final.tapes)=some worker)
    (hreader : reader.final.scanned 719=true)
    (P b position : ℕ) (source out : List Bool) (terms : Fin 725 → List Bool)
    (ambient : Fin 94 → List Bool) (extraHeads : Fin 1705 → ℕ) (extraTapes : Fin 1705 → List Bool)
    (wh : worker.final.heads=heads position out extraHeads)
    (wt : worker.final.tapes=data P terms ambient out extraTapes)
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
  obtain ⟨flag,hf,_fs,fh,ft⟩ := flag_run worker.final.heads worker.final.tapes (by rw [wh];exact ⟨wch,rfl⟩)
  have fheads : flag.final.heads=heads position out extraHeads := fh.trans wh
  have ftapes : flag.final.tapes=data P changed ambient out extraTapes := by
    rw [ft,wt]
    exact data_update P terms ambient out (flagOutput left (terms 719)) extraTapes
  obtain ⟨n,hn,ht⟩ := prefix_to_exit circuit readFuel circuitFuel entry reader worker flag hr hc hf hreader
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
  let final := TapeEmbedding.receipt extraHeads extraTapes last
  have finalRun := TapeEmbedding.run_embed TermExit.machine extraHeads extraTapes _ _ last hl
  have finalHeads : final.final.heads=heads position out extraHeads := by
    change Fin.addCases (m:=827) (n:=1705) (motive:=fun _=>ℕ) last.final.heads extraHeads=_
    rw [lh];rfl
  have finalTapes : final.final.tapes=data P (TermRead.data P b [] source false) ambient out extraTapes := by
    change Fin.addCases (m:=827) (n:=1705) (motive:=fun _=>List Bool) last.final.tapes extraTapes=_
    rw [lt];rfl
  have finalFlag : final.final.scanned 724=false := by
    change readTapeBit (final.final.tapes 724) (final.final.heads 724)=false
    rw [finalHeads,finalTapes];rfl
  obtain ⟨m,hm,tail⟩ := rejected_exit circuit (2*P+7) _ final finalRun finalFlag
  obtain ⟨r,run,rs,rh,rt⟩ := stopped_run (sizes s) (programs circuit) 0 next _
    final.final.heads final.final.tapes (ht.trans tail)
  have bound : n+m ≤ readFuel+circuitFuel+2*P+12 := by omega
  have more := runFrom_moreFuel (machine circuit) _ (readFuel+circuitFuel+2*P+12-(n+m)) _ r run
  rw [Nat.add_sub_of_le bound] at more
  refine ⟨r,more,rs.le.trans bound,?_,?_⟩
  · rw [rh,finalHeads];rfl
  · rw [rt,finalTapes];rfl

end NearCubicWires.RepairOrdinary.CloseoutWitness.TermRound
