import Proof.Circuits.DecompositionCountReady

/-! Paid rewinding of one whole emitted stream. The existing selective
reset records the actual producer execution, then restores only its output. -/
namespace NearCubicWires.RepairOrdinary.DecompositionStreamReset
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem reset_output_run {t s : ℕ} (producer : Machine t s) (target : Fin t)
    (fuel : ℕ) (c : Configuration t s) (p : ExecutionReceipt t s)
    (hp : runFrom producer fuel c=some p) (hc : c.heads target=0) :
    ∃ r,runFrom (SelectiveReset.machine producer target) (2*fuel+2) (Rewind.recording c 0)=some r ∧
      (∀ i : Fin t,r.final.tapes (i.castAdd 1)=p.final.tapes i) ∧
      (∀ i : Fin t,r.final.heads (i.castAdd 1)=if i=target then 0 else p.final.heads i) ∧
      r.steps ≤ 2*fuel+2 := by
  have hhead : p.final.heads target ≤ p.steps := by
    have h := SelectiveReset.prefix_head (prefix_of_run producer fuel c p hp).1 target
    simpa only [hc,Nat.zero_add] using h
  obtain ⟨r,hr,rf,rs,_⟩ := SelectiveReset.reset_run producer target fuel c p hp hhead
  have hs := runFrom_steps_le producer fuel c p hp
  have hle : 2*p.steps+2 ≤ 2*fuel+2 := by omega
  have more := runFrom_moreFuel (SelectiveReset.machine producer target) (2*p.steps+2)
    ((2*fuel+2)-(2*p.steps+2)) _ r hr
  rw [Nat.add_sub_of_le hle] at more
  refine ⟨r,more,?_,?_,by omega⟩
  · intro i
    simp only [rf,SelectiveReset.finished,Rewind.config,Fin.addCases_left]
  · intro i
    simp only [rf,SelectiveReset.finished,Rewind.config,Fin.addCases_left]

end NearCubicWires.RepairOrdinary.DecompositionStreamReset
