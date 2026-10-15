import Proof.Amplification.RecoveryFocusRetained

/-! The reusable physical invariant supplies every literal-lookup premise.
Failure retains the controller's result/accumulator tapes for the paid reject
node; success supplies the next literal's exact bounded workspace. -/
namespace NearCubicWires.RepairOrdinary.RecoveryClauseEvaluation
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryClauseState RadixSemantics
open RepairSource.VerifierDecoding RecoveryValuationStream
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
open RepairSource.RecoveryOracle
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem assignment_off_result (which : Fin 3) : ∀ j,assignmentSlots which j≠27 := by
  fin_cases which <;> decide
theorem assignment_off_aggregate (which : Fin 3) : ∀ j,assignmentSlots which j≠41 := by
  fin_cases which <;> decide

theorem lookup_ready (s : State) (e : Extra) (which : Fin 3) (index word : List Bool)
    (hs : s.Valid) (he : e.Valid s word) (hi : index.length=s.bits.length)
    (hf : s.fields which=frame index) :
    ∃ n output,n ≤ 32768*(s.bits.length+1)^2 ∧
      ReadyRun (assignmentMachine which) n (tapes s e) output ∧
      output 27=[s.result] ∧ output 41=[e.aggregate] ∧
      output 34=[(readList e.cap (readEntry s.bits.length) word).isSome] ∧
      ∀ table tail,readList e.cap (readEntry s.bits.length) word=some (table,tail) →
        ∃ count out guard,count ≤ e.cap ∧ out.index.length=s.bits.length ∧ out.valid=true ∧
          out.value=FiniteValuation.assignment (value e.committed) (value e.binaryCount) table (value index) ∧
          (assignedState s which out).Valid ∧
          (assignedExtra e s count out guard).Valid (assignedState s which out) word ∧
          output=tapes (assignedState s which out) (assignedExtra e s count out guard) := by
  have hfits := RecoveryAssignment.scratch_fits s.bits.length
  have hc : 2*e.binaryCount.length+3 ≤ RecoveryReusableUnpair.capacity s.bits := by
    rw [he.count]
    exact hfits.2.1
  have hbit : RecoveryCommittedBit.rawCost index e.committed ≤ RecoveryReusableUnpair.capacity s.bits := by
    have h := RecoveryAssignment.committed_budget index e.committed s.bits.length hi he.committed
    change RecoveryCommittedBit.rawCost index e.committed ≤ 8192*(s.bits.length+1)^2
    omega
  have hreset : RecoveryAssignment.cost (assignmentData s e index word) e.cap e.binaryCount e.committed e.guard+2 ≤ s.capacity := by
    have h := lookup_cost_bound s e index word he hi
    have hr := he.reset
    change 8192*(s.bits.length+1)^2+1 ≤ s.capacity at hr
    omega
  have htotal : 1 ≤ RecoveryReusableUnpair.capacity s.bits := by
    change 1 ≤ 8192*(s.bits.length+1)^2
    omega
  obtain ⟨r,hr,ht,hh,hvalid,hout⟩ := lookup_run s e which index word hf he.source hi he.row
    (he.count.trans hi.symm) hc hbit hreset he.counter htotal he.reset he.prefixBound
  have h27 := RecoveryFocus.run_other (assignmentSlots which) RecoveryAssignment.reusableMachine 27
    (assignment_off_result which) _ _ r hr
  have h41 := RecoveryFocus.run_other (assignmentSlots which) RecoveryAssignment.reusableMachine 41
    (assignment_off_aggregate which) _ _ r hr
  refine ⟨r.steps,r.final.tapes,ht.trans (assignment_cost_bound s e index word he hi),
    ready_of_run (assignmentMachine which) _ _ r hr hh,?_,?_,hvalid,?_⟩
  · exact h27.trans rfl
  · exact h41.trans rfl
  · intro table tail hp
    obtain ⟨count,out,guard,hcount,hwidth,hindex,hrow,hv,hvalue,hresult⟩ := hout table tail hp
    have hlen : out.index.length=s.bits.length := hindex.trans hi
    exact ⟨count,out,guard,hcount,hlen,hv,hvalue,assigned_valid s which out hs hlen,
      assigned_extra_valid s e which word count out guard he hcount hrow,hresult⟩

end NearCubicWires.RepairOrdinary.RecoveryClauseEvaluation
