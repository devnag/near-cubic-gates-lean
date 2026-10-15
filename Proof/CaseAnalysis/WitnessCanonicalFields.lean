import Proof.CaseAnalysis.WitnessCanonicalTest

/-! The canonical-list boundary exposes its physically produced field stream
and unary field count, so typed consumers do not traverse the same list again. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness
open LocalBitMultitape RecoveryExecution RecoveryRootRound RadixSemantics
open PCPPNativeCanonicalWalk PCPPNativeCanonicalTree CompetitorRationalProducts
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace Reencode
theorem list_run (bits : List Bool) : ∃ r,
    run machine (polynomialBudget bits) (input bits)=some r ∧ r.steps≤polynomialBudget bits ∧
      r.final.tapes 27=atomStream bits.length (tree (value bits)).atoms ∧
      r.final.tapes 38=RepairSource.VerifierDecoding.CompareMachine.word (tree (value bits)).atoms.length := by
  obtain ⟨raw,hr,_,hout,hcount,hsourceHead,hcountHead⟩:=TraversalCounted.counted_run bits
  obtain ⟨r,h,_,_,_,_,htapes,_,hsteps⟩:=PCPTraversalBank.producer_run
    (27 : Fin (36+1+3)) (38 : Fin (36+1+3)) (by decide) TraversalCounted.machine
    (TraversalCounted.budget bits) _ raw hr [] (fields bits) [] hsourceHead hcountHead
    (by simpa only [List.nil_append,List.append_nil,fields_stream] using hout)
    (by simpa only [fields,List.length_map,TraversalCounted.count] using hcount)
  rw [MatrixWilliamsProduct.initial_join] at h
  change run machine (budget bits) (input bits)=some r at h
  have more:=run_moreFuel machine (budget bits) (polynomialBudget bits-budget bits) (input bits) r h
  rw [Nat.add_sub_of_le (budget_bound bits)] at more
  exact ⟨r,more,hsteps.trans (budget_bound bits),(htapes 27).trans hout,(htapes 38).trans hcount⟩

theorem list_ready (bits : List Bool) : ∃ output,
    ClockJoin.ReadyRun readyMachine (readyBudget bits) (readyInput bits) output ∧
      output 117=ZeroPadding.pad (backing bits) (frame (canonical bits).bits) ∧
      output 27=atomStream bits.length (tree (value bits)).atoms ∧
      output 38=RepairSource.VerifierDecoding.CompareMachine.word (tree (value bits)).atoms.length := by
  obtain ⟨base,hb,hs,hframe,_⟩:=framed_run bits
  obtain ⟨list,hl,_,hout,hcount⟩:=list_run bits
  have he:list=base:=Option.some.inj (hl.symm.trans hb)
  subst list
  obtain ⟨r,hr,ht,_,hh,hsteps,_⟩:=Rewind.Workspace.reset_workspace machine _ _ base hb 0
  have hbound : 2*base.steps+2≤readyBudget bits := by unfold readyBudget;omega
  have more:=run_moreFuel readyMachine _ (readyBudget bits-(2*base.steps+2)) (readyInput bits) r hr
  rw [Nat.add_sub_of_le hbound] at more
  exact ⟨r.final.tapes,⟨r,more,rfl,hh,hsteps.le.trans hbound⟩,
    (ht 117).trans hframe,(ht 27).trans hout,(ht 38).trans hcount⟩
end Reencode

namespace CanonicalTest
theorem fields_run (bits : List Bool) : ∃ output,
    ClockJoin.ReadyRun machine (budget bits) (input bits) output ∧
      output 30=atomStream bits.length (tree (value bits)).atoms ∧
      output 41=RepairSource.VerifierDecoding.CompareMachine.word (tree (value bits)).atoms.length ∧
      (readTapeBit (output 172) 0=true ↔
        ∃ values,CanonicalBinary.encodeBalancedList values=value bits) := by
  obtain ⟨out,ho,hframe,hstream,hcount⟩:=Reencode.list_ready bits
  have hs:=ClockJoin.join copy boot _ _ _ _ _ (copy_ready bits) (boot_ready bits)
  have hw:=bounded_focus walkSlots walk_injective _ _ _ ho (primed bits) (walk_input bits)
  have hp:=ClockJoin.join start walk _ _ _ _ _ hs hw
  have he:=bounded_focus equalSlots equal_injective _ _ _ (comparison_ready bits)
    (walked bits out) (comparison_input bits out hframe)
  have h:=ClockJoin.join prefixMachine equality _ _ _ _ _ hp he
  have more:=ClockJoin.enlarge machine (time bits) (budget bits) _ _ h (time_bound bits)
  let final:=install equalSlots (walked bits out) (compareOutput bits)
  have h30:final 30=out 27:=by
    change install equalSlots (walked bits out) (compareOutput bits) 30=out 27
    rw [install_other _ _ _ _ (by decide)]
    change install walkSlots (primed bits) out (walkSlots 27)=out 27
    exact install_slot _ walk_injective _ _ _
  have h41:final 41=out 38:=by
    change install equalSlots (walked bits out) (compareOutput bits) 41=out 38
    rw [install_other _ _ _ _ (by decide)]
    change install walkSlots (primed bits) out (walkSlots 38)=out 38
    exact install_slot _ walk_injective _ _ _
  refine ⟨final,more,h30.trans hstream,h41.trans hcount,?_⟩
  change readTapeBit (install equalSlots (walked bits out) (compareOutput bits) (equalSlots 2)) 0=true ↔_
  rw [install_slot _ equal_injective]
  change decide (value bits=value (Reencode.canonical bits).bits)=true ↔_
  rw [decide_eq_true_eq,RecoveryUnpair.bits_value]
  exact eq_comm.trans (tree_canonical_iff (value bits))

end CanonicalTest
end NearCubicWires.RepairOrdinary.CloseoutWitness
