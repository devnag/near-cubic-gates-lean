import Proof.Hierarchy.CompetitorWitnessHeader
import Proof.Amplification.RecoveryRowLeafTapes
import Proof.Hierarchy.HierarchyBinaryMultiplyEntry

/-! The enclosing witness consumer retains the whole concrete output layout,
including the family-dispatch bit, for the two nested guarded parsers. -/
namespace NearCubicWires.RepairOrdinary.CompetitorWitnessHeader
open LocalBitMultitape RecoveryRootRound RecoveryExecution RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def time (bits : List Bool) := CompetitorWitnessTriple.time bits+1+(80*bits.length+142)

theorem header_ready (x bits : List Bool) : ReadyRun machine (time bits) (input x bits) (output x bits) := by
  have h := (CompetitorWitnessTriple.triple_ready x bits).embed (fun _ : Fin 26=>[])
  exact HierarchyMultiplyEntry.join_exact first guard _ _ _ _ _ h (guard_ready x bits)

theorem time_bound (bits : List Bool) : time bits ≤ budget bits := by
  have hb := CompetitorWitnessTriple.time_bound bits
  have hs : 0<(bits.length+1)^2 := by positivity
  unfold time CompetitorWitnessTriple.budget budget at *
  nlinarith

theorem header_output (x bits : List Bool) :
    ∃ r : ExecutionReceipt 148 _,run machine (budget bits) (input x bits)=some r ∧
      r.steps ≤ budget bits ∧ (∀ i,r.final.heads i=0) ∧ r.final.tapes=output x bits := by
  obtain ⟨r,hr,ht,hh,hs⟩ := header_ready x bits
  have hm := run_moreFuel machine (time bits) (budget bits-time bits) _ r hr
  rw [Nat.add_sub_of_le (time_bound bits)] at hm
  exact ⟨r,hm,hs.le.trans (time_bound bits),hh,ht⟩

theorem output_family (x bits : List Bool) : output x bits 142=[decide (CompetitorWitnessTriple.field bits 1=0)] := by
  rw [output,install_other gateSlots _ _ 142 (by intro j;fin_cases j <;> decide)]
  have h := before_output x bits 5 4 (by decide) (by rfl) 1
  change before x bits 5 (slots 4 1)=_
  rw [h]
  rfl

end NearCubicWires.RepairOrdinary.CompetitorWitnessHeader
