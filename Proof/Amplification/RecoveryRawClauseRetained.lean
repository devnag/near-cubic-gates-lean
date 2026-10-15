import Proof.Amplification.RecoveryRawClauseFlags

/-! The enclosing raw-view reader receives the same framed witness and
binary input-length bound, with the exact paid literal-field cursor advance. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRawClause
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open RepairSource.VerifierDecoding RecoveryRawLiteralBound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem out_stable (n : Nat) (x : State) :
    (out n x).2.bound=x.bound ∧ (out n x).2.stream.width=x.stream.width ∧
      (out n x).2.stream.source=x.stream.source := by
  induction n generalizing x with
  | zero=>exact ⟨rfl,rfl,rfl⟩
  | succ n ih=>
    have ho : (output x).bound=x.bound ∧ (output x).stream.width=x.stream.width ∧
        (output x).stream.source=x.stream.source := ⟨output_bound x,output_width x,output_source x⟩
    unfold out RepeatMachine.iterate
    split
    · obtain ⟨hb,hw,hs⟩ := ih (output x)
      exact ⟨hb.trans ho.1,hw.trans ho.2.1,hs.trans ho.2.2⟩
    · exact ho

theorem out_pos (n : Nat) (x : State) (ha : (out n x).1=true) :
    (out n x).2.stream.pos=x.stream.pos+4*n*x.stream.width := by
  induction n generalizing x with
  | zero=>simp only [out,RepeatMachine.iterate,Nat.mul_zero,Nat.zero_mul,Nat.add_zero]
  | succ n ih=>
    have hc : code x≠0 := by
      intro hz
      simp [out,RepeatMachine.iterate,RecoveryRawLiteralLoop.next,hz] at ha
    rw [out_succ n x hc] at ha ⊢
    rw [ih (output x) ha,output_pos,if_neg hc,output_width]
    ring

theorem final_stable (n : Nat) (x : State) :
    (inverted (output (out n x).2)).bound=x.bound ∧
      (inverted (output (out n x).2)).stream.width=x.stream.width ∧
      (inverted (output (out n x).2)).stream.source=x.stream.source := by
  obtain ⟨hb,hw,hs⟩ := out_stable n x
  exact ⟨(output_bound _).trans hb,(output_width _).trans hw,(output_source _).trans hs⟩

theorem final_pos (n : Nat) (x : State) (ha : answer n x=true) :
    (inverted (output (out n x).2)).stream.pos=x.stream.pos+4*n*x.stream.width := by
  rw [answer,Bool.and_eq_true,decide_eq_true_eq] at ha
  change (output (out n x).2).stream.pos=_
  rw [output_pos,if_pos ha.2]
  exact out_pos n x ha.1

theorem budget_bound (width total : Nat) (ht : total ≤ 3*(width+1)) :
    budget width total ≤ 16777216*(width+1)^3 := by
  have hl := RecoveryRawLiteralLoop.budget_bound width total ht
  unfold budget RecoveryRawLiteralLoop.bodyBudget
  nlinarith [show (width+1)^2 ≤ (width+1)^3 by
    calc
      _ ≤ (width+1)^2*(width+1) := by nlinarith [sq_nonneg (width:Nat)]
      _ = _ := by ring]

end NearCubicWires.RepairOrdinary.RecoveryRawClause
