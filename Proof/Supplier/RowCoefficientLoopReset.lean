import Proof.Supplier.RowCoefficientField

/-! Execute the complete occurrence loop and physically rewind just its two
coefficient heads. The cache, index-stream cursor and loop counter survive;
the paid rewind log supplies real allocated normalization workspace. -/
namespace NearCubicWires.RepairOrdinary.RowCoefficientLoopReset
open LocalBitMultitape RepairRepresentation RecoveryExecution Streaming
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def selected (i : Fin 25) : Bool := decide (i=10 ∨ i=11)
noncomputable def machine := MaskedReset.machine RowOccurrenceLoop.machine selected
noncomputable def entry {n : ℕ} (gs : List (ExactThresholdGate n)) (j : ℕ)
    (pre tail : List Bool) (indices : List (Fin gs.length)) :=
  Rewind.recording (RowOccurrenceLoop.cfg gs j 0 (pre++RowOccurrenceLoop.word indices++tail)
    pre.length [] [] indices.length 1) 0
noncomputable def loopFinal {n : ℕ} (gs : List (ExactThresholdGate n)) (j : ℕ) (hj : j ≤ n)
    (pre tail : List Bool) (indices : List (Fin gs.length)) :=
  RowOccurrenceLoop.cfg gs j 3 (pre++RowOccurrenceLoop.word indices++tail)
    (pre.length+(RowOccurrenceLoop.word indices).length)
    (RowOccurrenceLoop.emitted gs j hj false indices) (RowOccurrenceLoop.emitted gs j hj true indices)
    indices.length 1
def finish {s : ℕ} (c : Configuration 25 s) (steps : ℕ) :=
  SelectiveReset.finished (s:=s) (fun i=>if selected i then 0 else c.heads i) c.tapes steps
noncomputable def output {n : ℕ} (gs : List (ExactThresholdGate n)) (j : ℕ) (hj : j ≤ n)
    (pre tail : List Bool) (indices : List (Fin gs.length)) :=
  finish (loopFinal gs j hj pre tail indices) (RowOccurrenceLoop.budget gs j hj indices)

theorem loop_run {n : ℕ} (gs : List (ExactThresholdGate n)) (j : ℕ) (hj : j ≤ n)
    (pre tail : List Bool) (indices : List (Fin gs.length)) :
    ∃ r,runFrom machine (2*RowOccurrenceLoop.budget gs j hj indices+2)
      (entry gs j pre tail indices)=some r ∧
      r.final=output gs j hj pre tail indices ∧ r.steps=2*RowOccurrenceLoop.budget gs j hj indices+2 := by
  obtain ⟨r,hr,rf,rs⟩ := RowOccurrenceLoop.list_run gs j hj pre tail [] [] indices
  have start := RowOccurrenceLoop.cfg_outputs gs j (pre++RowOccurrenceLoop.word indices++tail)
    pre.length [] [] indices.length 1 0
  have hh : ∀ i,selected i=true → r.final.heads i ≤ r.steps := by
    intro i hi
    have h := SelectiveReset.prefix_head (prefix_of_run RowOccurrenceLoop.machine _ _ r hr).1 i
    have hs : (RowOccurrenceLoop.cfg gs j 0 (pre++RowOccurrenceLoop.word indices++tail)
        pre.length [] [] indices.length 1).heads i=0 := by
      have ht : i=10 ∨ i=11 := by simpa only [selected,decide_eq_true_eq] using hi
      rcases ht with rfl | rfl
      · exact start.2.2.1
      · exact start.2.2.2
    simpa only [hs,zero_add] using h
  obtain ⟨a,ha,af,asteps,_⟩ := MaskedReset.reset_run RowOccurrenceLoop.machine selected _ _ r hr hh
  rw [rs] at ha asteps
  have hfinal : r.final=loopFinal gs j hj pre tail indices := by
    simpa only [loopFinal,List.nil_append] using rf
  rw [hfinal,rs] at af
  exact ⟨a,ha,af,asteps⟩

end NearCubicWires.RepairOrdinary.RowCoefficientLoopReset
