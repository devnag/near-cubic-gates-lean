import Proof.CaseAnalysis.WitnessReencode
import Proof.CaseAnalysis.WitnessNumericEquality

/-! Expose the serializer's actual framed output and pay its return scan.
The canonical-value comparison can consume this padded frame directly. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.Reencode
open LocalBitMultitape RecoveryExecution RecoveryRootRound RadixSemantics
open PCPPNativeCanonicalWalk PCPPNativeCanonicalTree CanonicalBinaryProgram
open RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def canonical (bits : List Bool) := CanonicalBinary.encodeBalancedList (tree (value bits)).atoms
def backing (bits : List Bool) := PCPPairReusable.capacity (PCPSerializerMass.mass (fields bits))

theorem framed_run (bits : List Bool) :
    ∃ r,run machine (polynomialBudget bits) (input bits)=some r ∧ r.steps≤polynomialBudget bits ∧
      r.final.tapes 117=ZeroPadding.pad (backing bits) (frame (canonical bits).bits) ∧
      r.final.tapes 118=(canonical bits).bits := by
  obtain ⟨raw,hr,_,hout,hcount,hsourceHead,hcountHead⟩:=TraversalCounted.counted_run bits
  obtain ⟨r,h,hframe,hraw,_,_,_,_,hsteps⟩:=PCPTraversalBank.producer_run
    (27 : Fin (36+1+3)) (38 : Fin (36+1+3)) (by decide) TraversalCounted.machine
    (TraversalCounted.budget bits) _ raw hr [] (fields bits) [] hsourceHead hcountHead
    (by simpa only [List.nil_append,List.append_nil,fields_stream] using hout)
    (by simpa only [fields,List.length_map,TraversalCounted.count] using hcount)
  rw [MatrixWilliamsProduct.initial_join] at h
  change run machine (budget bits) (input bits)=some r at h
  have more:=run_moreFuel machine (budget bits) (polynomialBudget bits-budget bits) (input bits) r h
  rw [Nat.add_sub_of_le (budget_bound bits)] at more
  have hf : (77 : Fin 128).natAdd (36+1+3) = (117 : Fin (36+1+3+128)) := by decide
  have hi : (78 : Fin 128).natAdd (36+1+3) = (118 : Fin (36+1+3+128)) := by decide
  rw [hf] at hframe
  rw [hi] at hraw
  refine ⟨r,more,hsteps.trans (budget_bound bits),?_,?_⟩
  · simpa only [PCPTraversal.code,fields_values,canonical,backing] using hframe
  · simpa only [PCPTraversal.code,fields_values,canonical] using hraw

noncomputable def readyMachine := Rewind.machine machine
def readyInput (bits : List Bool) : Fin (36+1+3+128+1)→List Bool :=
  Fin.addCases (m:=36+1+3+128) (n:=1) (motive:=fun _=>List Bool) (input bits) (fun _=>[])
def readyBudget (bits : List Bool) := 2*polynomialBudget bits+2

theorem reencode_ready (bits : List Bool) : ∃ output,
    ClockJoin.ReadyRun readyMachine (readyBudget bits) (readyInput bits) output ∧
      output 117=ZeroPadding.pad (backing bits) (frame (canonical bits).bits) ∧
      output 118=(canonical bits).bits := by
  obtain ⟨base,hb,hs,hframe,hraw⟩:=framed_run bits
  obtain ⟨r,hr,ht,_,hh,hsteps,_⟩:=Rewind.Workspace.reset_workspace machine _ _ base hb 0
  have hbound : 2*base.steps+2≤readyBudget bits := by unfold readyBudget; omega
  have more:=run_moreFuel readyMachine _ (readyBudget bits-(2*base.steps+2)) (readyInput bits) r hr
  rw [Nat.add_sub_of_le hbound] at more
  refine ⟨r.final.tapes,⟨r,more,rfl,hh,hsteps.le.trans hbound⟩,?_,?_⟩
  · exact (ht 117).trans hframe
  · exact (ht 118).trans hraw

end NearCubicWires.RepairOrdinary.CloseoutWitness.Reencode
