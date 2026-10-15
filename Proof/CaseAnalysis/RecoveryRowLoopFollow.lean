import Proof.CaseAnalysis.RecoveryRowLoopIncrement

/-! The original row's paid reusable tail. Every row clears its consumed
address batch; nonterminal rows then advance the same randomness field. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedRows
open LocalBitMultitape Composition SourceInterfaces RepairSource CanonicalRecoveryLanguage
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace Follow
variable {a b : ℕ}
def machine (first : Machine 115 a) (last : Machine 115 b):=Composition.machine first last
theorem join (first : Machine 115 a) (last : Machine 115 b) (H : Fin 115→ℕ) (A : Fin 115→List Bool)
    (u v : ℕ) (p : ExecutionReceipt 115 a) (q : ExecutionReceipt 115 b)
    (hp : runFrom first u ⟨first.start,H,A⟩=some p)
    (hq : runFrom last v (restart p.final last.start)=some q) :
    ∃ r,runFrom (machine first last) (u+1+v) ⟨(machine first last).start,H,A⟩=some r ∧
      r.steps=p.steps+1+q.steps ∧ r.final.heads=q.final.heads ∧ r.final.tapes=q.final.tapes := by
  exact ⟨joinedReceipt p q,Composition.run_join first last _ _ _ p q hp hq,rfl,rfl,rfl⟩
end Follow

noncomputable def finishMachine:=Follow.machine rowMachine clearMachine
noncomputable def bodyMachine:=Follow.machine finishMachine incrementMachine
def finishBudget (B : ℕ):=256*(B+2)
def bodyBudget (B : ℕ):=512*(B+2)

theorem finish_run (B : ℕ) (H0 : Fin 115→ℕ) (A0 : Fin 115→List Bool)
    (H : Fin 78→ℕ) (A : Fin 78→List Bool) (P : Fin 37→List Bool) (word : List Bool)
    (first : ExecutionReceipt 115 _)
    (fr : runFrom rowMachine (rowBudget B) ⟨rowMachine.start,H0,A0⟩=some first)
    (fs : first.steps≤rowBudget B) (fh : first.final.heads=heads H)
    (ft : first.final.tapes=data A (Function.update P 31 word))
    (h76 : H 76=0) (h77 : H 77=0)
    (d76 : A 76=List.replicate B true) (d77 : A 77=List.replicate (B+1) false)
    (hp : P 31=List.replicate B false) (hw : word.length≤B) :
    ∃ r,runFrom finishMachine (finishBudget B) ⟨finishMachine.start,H0,A0⟩=some r ∧
      r.steps≤finishBudget B ∧ r.final.heads=heads H ∧ r.final.tapes=data A P := by
  obtain ⟨last,lr,ls,lh,lt⟩:=clear_row_run H A P word B h76 h77 d76 d77 hp hw
  have lr' : runFrom clearMachine (2*B+4) (restart first.final clearMachine.start)=some last := by
    change runFrom _ _ ⟨_,first.final.heads,first.final.tapes⟩=some last
    rw [fh,ft]
    exact lr
  obtain ⟨r,rr,rs,rh,rt⟩:=Follow.join rowMachine clearMachine H0 A0 (rowBudget B) (2*B+4) first last fr lr'
  have hb : rowBudget B+1+(2*B+4)≤finishBudget B := by unfold rowBudget finishBudget;omega
  have more:=runFrom_moreFuel finishMachine _ (finishBudget B-(rowBudget B+1+(2*B+4))) _ r rr
  rw [Nat.add_sub_of_le hb] at more
  refine ⟨r,more,?_,rh.trans lh,rt.trans lt⟩
  rw [rs]
  omega

theorem body_run (p : RawProjectionPCP) (R Q k B : ℕ) (hk : k+1<2^R) (hR : R≤B)
    (H0 : Fin 115→ℕ) (A0 : Fin 115→List Bool) (H : Fin 78→ℕ) (A : Fin 78→List Bool)
    (first : ExecutionReceipt 115 _)
    (fr : runFrom finishMachine (finishBudget B) ⟨finishMachine.start,H0,A0⟩=some first)
    (fs : first.steps≤finishBudget B) (fh : first.final.heads=heads H)
    (ft : first.final.tapes=data A (RecoveryBoundedRowProjection.bank p R Q (bitInputOfCode R k) B)) :
    ∃ r,runFrom bodyMachine (bodyBudget B) ⟨bodyMachine.start,H0,A0⟩=some r ∧
      r.steps≤bodyBudget B ∧ r.final.heads=heads H ∧
      r.final.tapes=data A (RecoveryBoundedRowProjection.bank p R Q (bitInputOfCode R (k+1)) B) := by
  obtain ⟨last,lr,ls,lh,lt⟩:=increment_run p R Q k B hk H A
  have lr' : runFrom incrementMachine (4*R+2) (restart first.final incrementMachine.start)=some last := by
    change runFrom _ _ ⟨_,first.final.heads,first.final.tapes⟩=some last
    rw [fh,ft]
    exact lr
  obtain ⟨r,rr,rs,rh,rt⟩:=Follow.join finishMachine incrementMachine H0 A0 (finishBudget B) (4*R+2) first last fr lr'
  have hb : finishBudget B+1+(4*R+2)≤bodyBudget B := by unfold finishBudget bodyBudget;omega
  have more:=runFrom_moreFuel bodyMachine _ (bodyBudget B-(finishBudget B+1+(4*R+2))) _ r rr
  rw [Nat.add_sub_of_le hb] at more
  refine ⟨r,more,?_,rh.trans lh,rt.trans lt⟩
  rw [rs]
  omega

end NearCubicWires.RepairOrdinary.RecoveryBoundedRows
