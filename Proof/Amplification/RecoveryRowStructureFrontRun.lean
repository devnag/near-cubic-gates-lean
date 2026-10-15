import Proof.Amplification.RecoveryRowStructureFront

/-! Executable structural-tag front with its exact semantic acceptance,
retained parsed fields, and reusable streamed output configuration. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRowStructure
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryRowStream RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem tagAllowed_eq (tag : List Bool) : tagAllowed tag=decide (value tag≤2) := by
  apply Bool.eq_iff_iff.mpr
  simp only [tagAllowed,Bool.or_eq_true,decide_eq_true_eq]
  omega

theorem prepared_flag (d : Data) :
    (prepared d).flags 0=decide ((Nat.unpair (value d.code)).1=value d.kind) := by
  change decide (value (RecoveryFixedUnpair.leftWord d.code)=value d.kind)=_
  rw [(code_values d).1]

theorem front_answer (d : Data) :
    frontAnswer d=decide ((Nat.unpair (value d.code)).1=value d.kind ∧ value d.kind≤2) := by
  rw [frontAnswer,prepared_flag,tagAllowed_eq,(code_values d).1]
  by_cases he : (Nat.unpair (value d.code)).1=value d.kind
  · simp [he]
  · simp [he]

theorem front_output_answer (d : Data) : (frontOutput d).valid=frontAnswer d := by
  unfold frontOutput frontAnswer
  cases h : (prepared d).flags 0 <;> rfl

theorem front_retained (d : Data) :
    (frontOutput d).kind=d.kind ∧ (frontOutput d).code=d.code ∧
      (frontOutput d).count=d.count ∧ (frontOutput d).state.bits=d.state.bits ∧
      (frontOutput d).source=d.source ∧ (frontOutput d).pos=d.pos := by
  unfold frontOutput
  split <;> exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem front_output_valid (d : Data) (word : List Bool) (hd : d.Valid word)
    (hw : d.code.length=d.state.bits.length) : (frontOutput d).Valid word := by
  have hp : (prepared d).Valid word := decoded_valid (copied d) d.code word (copied_valid d word hd hw) hw
  unfold frontOutput
  split
  · exact classified_valid (prepared d) (RecoveryFixedUnpair.leftWord d.code) word hp
      ((RecoveryFixedUnpair.word_lengths d.code).1.trans hw)
  · exact hp

theorem front_run (d : Data) (capacity : Nat) (word : List Bool) (hd : d.Valid word)
    (hw : d.code.length=d.state.bits.length) (hk : d.kind.length=d.state.bits.length)
    (hc : 2*d.code.length+1≤capacity) (hr : 4*d.code.length+3≤d.state.capacity) :
    ∃ r,runFrom frontMachine (frontTime d) (cfg d capacity frontMachine.start)=some r ∧
      r.final=cfg (frontOutput d) capacity r.final.control ∧ r.steps≤frontTime d ∧
      (frontOutput d).Valid word ∧
      (frontOutput d).valid=decide ((Nat.unpair (value d.code)).1=value d.kind ∧ value d.kind≤2) := by
  obtain ⟨n,hn,h⟩ := front_trace d capacity word hd hw hk hc hr
  obtain ⟨r,hrun,hf,hs⟩ := h.run (by simp [frontMachine,frontStop,RecoveryCalls.machine,RecoveryCalls.stopped])
  have hm := runFrom_moreFuel frontMachine n (frontTime d-n) _ r hrun
  rw [Nat.add_sub_of_le hn] at hm
  refine ⟨r,hm,?_,hs.le.trans hn,front_output_valid d word hd hw,(front_output_answer d).trans (front_answer d)⟩
  rw [hf]
  rfl

end NearCubicWires.RepairOrdinary.RecoveryRowStructure
