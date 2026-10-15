import Proof.Amplification.RecoveryClauseEvaluationReturn

/-! Executed decoder and retained valuation calls in the common clause
layout. The lookup is charged again for every literal. -/
namespace NearCubicWires.RepairOrdinary.RecoveryClauseEvaluation
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryClauseState
open RepairSource.VerifierDecoding RecoveryValuationStream
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
open RepairSource.RecoveryOracle
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem decode_ready (s : State) (e : Extra) (which : Fin 3) (word : List Bool)
    (hv : s.Valid) (hw : word.length=s.bits.length) (hf : s.fields which=frame word) :
    ReadyRun (decodeMachine which) (RecoveryCheckedLiteral.time word) (tapes s e)
      (tapes (RecoveryCheckedLiteral.checkedState s which word) e) := by
  obtain ⟨base,hr,ht,hh,hs⟩ := RecoveryCheckedLiteral.state_ready s which word hv hw hf
  have h := TapeEmbedding.run_embed (RecoveryCheckedLiteral.machine which) (fun _ : Fin 14=>0)
    (e.tapes s) _ _ base hr
  have hin : TapeEmbedding.config (fun _ : Fin 14=>0) (e.tapes s)
      (initialConfiguration (RecoveryCheckedLiteral.machine which) s.tapes)=
      initialConfiguration (decodeMachine which) (tapes s e) := by
    apply configuration_ext
    · rfl
    · funext i
      refine Fin.addCases (fun j=>?_) (fun j=>?_) i <;>
        simp [TapeEmbedding.config,initialConfiguration]
    · rfl
  rw [hin] at h
  refine ⟨TapeEmbedding.receipt (fun _ : Fin 14=>0) (e.tapes s) base,h,?_,?_,hs⟩
  · change (Fin.addCases (m:=28) (n:=14) (motive:=fun _=>List Bool) base.final.tapes (e.tapes s))=_
    rw [ht]
    rfl
  · intro i
    change Fin.addCases base.final.heads (fun _ : Fin 14=>0) i=0
    refine Fin.addCases (fun j=>?_) (fun j=>?_) i
    · simpa using hh j
    · simp

def assignmentCost (s : State) (e : Extra) (index word : List Bool) : Nat :=
  2*RecoveryReusableUnpair.capacity s.bits+
    2*RecoveryAssignment.cost (assignmentData s e index word) e.cap e.binaryCount e.committed e.guard+11

theorem lookup_run (s : State) (e : Extra) (which : Fin 3) (index word : List Bool)
    (hf : s.fields which=frame index)
    (hsource : e.source=ZeroPadding.pad (2*e.prefixLimit+1) (frame (word.take e.prefixLimit)))
    (hi : index.length=s.bits.length) (hb : e.row.length ≤ 2*(s.bits.length+1)+1)
    (hw : e.binaryCount.length=index.length)
    (hc : 2*e.binaryCount.length+3 ≤ RecoveryReusableUnpair.capacity s.bits)
    (hbit : RecoveryCommittedBit.rawCost index e.committed ≤ RecoveryReusableUnpair.capacity s.bits)
    (hreset : RecoveryAssignment.cost (assignmentData s e index word) e.cap e.binaryCount e.committed e.guard+2 ≤ s.capacity)
    (hback : e.counter.length ≤ RecoveryReusableUnpair.capacity s.bits)
    (htotal : 1 ≤ RecoveryReusableUnpair.capacity s.bits)
    (herase : RecoveryReusableUnpair.capacity s.bits+1 ≤ s.capacity)
    (hprefix : e.cap*(s.bits.length+2)+1 ≤ e.prefixLimit) :
    ∃ r,run (assignmentMachine which) (assignmentCost s e index word) (tapes s e)=some r ∧
      r.steps ≤ assignmentCost s e index word ∧ (∀ i,r.final.heads i=0) ∧
      r.final.tapes 34=[(readList e.cap (readEntry s.bits.length) word).isSome] ∧
      ∀ table tail,readList e.cap (readEntry s.bits.length) word=some (table,tail) →
        ∃ count out guard,count ≤ e.cap ∧ out.width=s.bits.length ∧ out.index.length=index.length ∧
          out.row.length ≤ 2*(s.bits.length+1)+1 ∧ out.valid=true ∧
          out.value=FiniteValuation.assignment (RadixSemantics.value e.committed)
            (RadixSemantics.value e.binaryCount) table (RadixSemantics.value index) ∧
          r.final.tapes=tapes (assignedState s which out) (assignedExtra e s count out guard) := by
  obtain ⟨base,hbase,hsteps,hheads,hvalid,hout⟩ := RecoveryAssignment.retained_run
    (assignmentData s e index word) word e.cap e.prefixLimit e.binaryCount e.committed e.guard
    (RecoveryReusableUnpair.capacity s.bits) s.capacity e.counter rfl rfl hi hb hw hc hbit
    hreset hback htotal herase hprefix
  obtain ⟨r,hr,hfinal,hstep⟩ := RecoveryFocus.run_config (assignmentSlots which)
    (assignmentSlots_injective which) RecoveryAssignment.reusableMachine (fun _ : Fin 42=>0)
    (tapes s e) _ _ base hbase
  have hin : RecoveryFocus.config (assignmentSlots which) (fun _ : Fin 42=>0) (tapes s e)
      (initialConfiguration RecoveryAssignment.reusableMachine
        (RecoveryAssignment.reuseInput (assignmentData s e index word) e.cap e.binaryCount e.committed
          e.guard (2*e.prefixLimit+1) (RecoveryReusableUnpair.capacity s.bits) s.capacity e.counter))=
      initialConfiguration (assignmentMachine which) (tapes s e) := by
    apply configuration_ext
    · rfl
    · funext i; cases hp : RecoveryFocus.pick (assignmentSlots which) i <;>
        simp [RecoveryFocus.config,hp,initialConfiguration]
    · exact install_existing (assignmentSlots which) (tapes s e) _
        (assignment_input s e which index word hf hsource)
  rw [hin] at hr
  refine ⟨r,hr,hstep.trans_le hsteps,?_,?_,?_⟩
  · intro i
    rw [hfinal]
    cases hp : RecoveryFocus.pick (assignmentSlots which) i <;>
      simp [RecoveryFocus.config,hp,hheads]
  · rw [hfinal]
    change install (assignmentSlots which) (tapes s e) base.final.tapes (assignmentSlots which 7)=_
    rw [install_slot (assignmentSlots which) (assignmentSlots_injective which)]
    exact hvalid
  · intro table tail hparse
    obtain ⟨count,out,guard,hcount,hwidth,hindex,hsrc,hpos,hcap,hrow,hv,hvalue,htapes⟩ := hout table tail hparse
    refine ⟨count,out,guard,hcount,hwidth,hindex,hrow,hv,hvalue,?_⟩
    rw [hfinal]
    change install (assignmentSlots which) (tapes s e) base.final.tapes=_
    rw [htapes]
    exact assignment_output s e which word count out guard hsource hwidth hsrc hcap

end NearCubicWires.RepairOrdinary.RecoveryClauseEvaluation
