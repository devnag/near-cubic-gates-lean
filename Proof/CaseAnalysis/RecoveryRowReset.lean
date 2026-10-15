import Proof.CaseAnalysis.RecoveryRowPosition

/-! The complete original row pays one coarse reset of every work cursor.
The graph append cursor and exact actual graph/count/output data survive. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedRowReuse
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def selected (i : Fin 73):=decide (i≠20)
noncomputable def machine:=MaskedReset.machine prepare selected
noncomputable def entry (out : List Bool) (A : Fin 73→List Bool) (B : ℕ):=
  ZeroPadding.config (Rewind.Workspace.capacities 73 B)
    (Rewind.recording (⟨prepare.start,heads out,A⟩ : Configuration 73 _) 0)
def resultHeads (graphPosition : ℕ) : Fin 74→ℕ:=
  Fin.addCases (m:=73) (n:=1) (motive:=fun _=>ℕ) (fun i=>if i=20 then graphPosition else 0) (fun _=>0)
def resultData (A : Fin 73→List Bool) (B : ℕ) : Fin 74→List Bool:=
  Fin.addCases (m:=73) (n:=1) (motive:=fun _=>List Bool) A (fun _=>List.replicate B false)

theorem original_heads_bound (out : List Bool) (S : ℕ) (ho : out.length ≤ S) (hS : 1 ≤ S) :
    ∀ i,RecoveryBoundedRow.heads out [] [] i ≤ S := by
  intro i
  fin_cases i <;> first | exact ho | exact hS | exact Nat.zero_le S

theorem reset_run (out : List Bool) (A : Fin 73→List Bool) (u S B : ℕ)
    (r : ExecutionReceipt 73 _)
    (hr : runFrom RecoveryBoundedRow.machine u ⟨RecoveryBoundedRow.machine.start,RecoveryBoundedRow.heads out [] [],A⟩=some r)
    (hs : r.steps ≤ u) (hS : 1 ≤ S) (ho : out.length ≤ S) (hA : ∀ i,(A i).length ≤ S)
    (hB : S+u+3 ≤ B) :
    ∃ q,runFrom machine (2*(u+2)+2) (entry out A B)=some q ∧
      q.steps ≤ 2*(u+2)+2 ∧ q.final.heads=resultHeads (r.final.heads 20) ∧
      q.final.tapes=resultData r.final.tapes B ∧ (∀ i,(r.final.tapes i).length ≤ B) := by
  obtain ⟨p,pr,ps,ph,pt⟩:=enter out A u r hr hs
  obtain ⟨q,qr,qf,qs,_⟩:=MaskedReset.workspace_run prepare selected _ B _ p pr
    (by intro i hi
        have hn : i≠20:=of_decide_eq_true hi
        simp only [heads,if_neg hn])
    (by omega)
  have hb : 2*p.steps+2 ≤ 2*(u+2)+2:=by omega
  have more:=runFrom_moreFuel machine _ (2*(u+2)+2-(2*p.steps+2)) _ q qr
  rw [Nat.add_sub_of_le hb] at more
  have hsupport:=RecoveryTapeSupport.run_support RecoveryBoundedRow.machine u _ r hr S S
    (original_heads_bound out S ho hS) (fun i=>(hA i).trans (Nat.le_max_left _ _))
  refine ⟨q,more,by omega,?_,?_,?_⟩
  · rw [qf]
    funext i
    refine Fin.addCases (m:=73) (n:=1) ?_ ?_ i
    · intro j
      simp only [SelectiveReset.finished,Rewind.config,resultHeads,Fin.addCases_left]
      by_cases hj : j=20
      · subst j
        simpa only [selected,ne_eq,not_true_eq_false,decide_false,Bool.false_eq_true,↓reduceIte] using congrFun ph 20
      · simp only [selected,if_neg hj,show decide (j≠20)=true from decide_eq_true hj,↓reduceIte]
    · intro j
      fin_cases j
      rfl
  · rw [qf]
    change resultData p.final.tapes B=resultData r.final.tapes B
    rw [pt]
  · intro i
    exact (hsupport i).trans (max_le (by omega) (by omega))

end NearCubicWires.RepairOrdinary.RecoveryBoundedRowReuse
