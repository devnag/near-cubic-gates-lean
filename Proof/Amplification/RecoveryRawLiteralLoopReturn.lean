import Proof.Amplification.RecoveryRawLiteralLoop

/-! Both exits of the actual literal loop retain the physical result head;
a missing-cell rejection retains a literal false cell. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRawLiteralLoop
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open RepairSource.VerifierDecoding RecoveryRawLiteralBound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem supplier_tape (width : Nat) (x : State) (hx : Inv width x) :
    ∃ r,runFrom RecoveryRawLiteralBound.machine (bodyBudget width) (source x)=some r ∧
      r.steps ≤ bodyBudget width ∧ r.final.scanned 28=(next x).1 ∧
      ((next x).1=true → r.final.heads=(source (next x).2).heads ∧
        r.final.tapes=(source (next x).2).tapes ∧ Inv width (next x).2) ∧
      ((next x).1=false → r.final.heads 28=0 ∧ r.final.tapes 28=[false]) := by
  have hrun := RecoveryRawLiteralBound.body_run x hx.1
  obtain ⟨r,hr,hf,hb⟩ := hrun
  have hc : cost x ≤ bodyBudget width := by
    have h := RecoveryRawLiteralBound.cost_bound x hx.1
    rw [hx.2] at h
    exact h
  have hm := runFrom_moreFuel RecoveryRawLiteralBound.machine (cost x) (bodyBudget width-cost x) _ r hr
  rw [Nat.add_sub_of_le hc] at hm
  refine ⟨r,hm,hb.trans hc,?_,?_,?_⟩
  · rw [hf]
    change (output x).stream.data.present=(next x).1
    exact output_present x
  · intro _
    refine ⟨?_,?_,output_valid x hx.1,(output_width x).trans hx.2⟩
    · rw [hf]; rfl
    · rw [hf]; rfl
  · intro ha
    rw [hf]
    constructor
    · rfl
    · change [(output x).stream.data.present]=[false]
      rw [output_present]
      exact congrArg (fun b : Bool=>[b]) ha

theorem loop_return (width total : Nat) (x : State) (hx : Inv width x) :
    ∃ r,runFrom machine (budget width total) (RepeatMachine.cfg 0 (source x) total 1)=some r ∧
      r.steps ≤ budget width total ∧
      RepeatMachine.Result source total (RepeatMachine.iterate next total x) r.final ∧
      r.final.heads 28=0 ∧ (∃ bit,r.final.tapes 28=[bit]) ∧
      ((RepeatMachine.iterate next total x).1=false → r.final.tapes 28=[false]) := by
  have hrun := RepeatMachine.rejecting_repeat_tape RecoveryRawLiteralBound.machine (fun _ scanned=>scanned 28)
    source next (Inv width) (bodyBudget width) 28 (fun _ _=>rfl) (supplier_tape width) total x hx
  obtain ⟨r,hr,hb,hf,hbad⟩ := hrun
  cases ha : (RepeatMachine.iterate next total x).1
  · obtain ⟨hh,ht⟩ := hbad ha
    exact ⟨r,hr,hb,hf,hh,⟨false,ht⟩,fun _=>ht⟩
  · have he := hf
    simp only [RepeatMachine.Result,ha,ite_true] at he
    refine ⟨r,hr,hb,hf,?_,?_,?_⟩
    · rw [he]; rfl
    · refine ⟨(RepeatMachine.iterate next total x).2.stream.data.present,?_⟩
      rw [he]; rfl
    · simp only [Bool.true_eq_false,IsEmpty.forall_iff]

end NearCubicWires.RepairOrdinary.RecoveryRawLiteralLoop
