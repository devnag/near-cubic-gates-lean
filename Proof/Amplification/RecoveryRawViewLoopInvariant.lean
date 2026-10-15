import Proof.Amplification.RecoveryRawViewEnd

/-! Successful outer iteration retains the exact next cursor and valid
workspace; rejected iteration needs only its physical false-result cell. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRawViewLoop
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryRawView
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def out (word : List Bool) (total : Nat) (x : Cursor) := RepeatMachine.iterate (next word) total x

theorem out_succ (word : List Bool) (total : Nat) (x : Cursor) (ha : (next word x).1=true) :
    out word (total+1) x=out word total (next word x).2 := by
  simp only [out,RepeatMachine.iterate,ha,ite_true]

theorem out_inv (width total : Nat) (word : List Bool) (x : Cursor) (hx : Inv width word x)
    (ha : (out word total x).1=true) : Inv width word (out word total x).2 := by
  induction total generalizing x with
  | zero=>exact hx
  | succ total ih=>
    have hn : (next word x).1=true := by
      by_cases hn : (next word x).1=true
      · exact hn
      · simp only [out,RepeatMachine.iterate,if_neg hn] at ha
        exact ha
    rw [out_succ word total x hn] at ha ⊢
    exact ih (next word x).2 (next_inv width word x hx hn) ha

theorem loop_return (width total : Nat) (word : List Bool) (x : Cursor) (hx : Inv width word x) :
    ∃ r,runFrom machine (budget width total) (RepeatMachine.cfg 0 (source x) total 1)=some r ∧
      r.steps ≤ budget width total ∧ RepeatMachine.Result source total (out word total x) r.final ∧
      r.final.heads 28=0 ∧ ((out word total x).1=false → r.final.tapes 28=[false]) := by
  obtain ⟨r,hr,hb,hf,hbad⟩ := loop_run width total word x hx
  cases ha : (out word total x).1
  · obtain ⟨hh,ht⟩ := hbad ha
    exact ⟨r,hr,hb,hf,hh,fun _=>ht⟩
  · have he := hf
    simp only [RepeatMachine.Result,show (RepeatMachine.iterate (next word) total x).1=true from ha,ite_true] at he
    refine ⟨r,hr,hb,hf,?_,?_⟩
    · rw [he]; rfl
    · simp only [Bool.true_eq_false,IsEmpty.forall_iff]

end NearCubicWires.RepairOrdinary.RecoveryRawViewLoop
