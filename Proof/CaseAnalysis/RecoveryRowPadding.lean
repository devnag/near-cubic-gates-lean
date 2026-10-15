import Proof.CaseAnalysis.RecoveryRowReset

/-! One paid coarse backing is reused by the complete original row. The
graph, actual node count and literal source retain their exact words. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedRowReuse
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def workCapacity (B : ℕ) (i : Fin 73):=if i=20 ∨ i=25 ∨ i=70 then 0 else B
def paddedData (B : ℕ) (A : Fin 73→List Bool) (i : Fin 73):=ZeroPadding.pad (workCapacity B i) (A i)
def paddedCapacity (B : ℕ) : Fin 74→ℕ:=
  Fin.addCases (m:=73) (n:=1) (motive:=fun _=>ℕ) (workCapacity B) (fun _=>0)

theorem padding_entry (out : List Bool) (A : Fin 73→List Bool) (B : ℕ) :
    ZeroPadding.config (paddedCapacity B) (entry out A B)=entry out (paddedData B A) B := by
  apply configuration_ext
  · rfl
  · rfl
  · funext i
    refine Fin.addCases (m:=73) (n:=1) ?_ ?_ i
    · intro j
      simp only [ZeroPadding.config,entry,paddedCapacity,Rewind.recording,Rewind.config,
        Rewind.Workspace.capacities,Fin.addCases_left,ZeroPadding.pad_zero,paddedData]
    · intro j
      fin_cases j
      exact ZeroPadding.pad_zero _

theorem padding_result (A : Fin 73→List Bool) (B : ℕ) :
    (fun i=>ZeroPadding.pad (paddedCapacity B i) (resultData A B i))=
      resultData (paddedData B A) B := by
  funext i
  refine Fin.addCases (m:=73) (n:=1) ?_ ?_ i
  · intro j
    simp only [paddedCapacity,resultData,Fin.addCases_left,paddedData]
  · intro j
    simp only [paddedCapacity,resultData,Fin.addCases_right,ZeroPadding.pad_zero]

theorem padded_reset_run (out : List Bool) (A : Fin 73→List Bool) (u S B : ℕ)
    (r : ExecutionReceipt 73 _)
    (hr : runFrom RecoveryBoundedRow.machine u ⟨RecoveryBoundedRow.machine.start,RecoveryBoundedRow.heads out [] [],A⟩=some r)
    (hs : r.steps ≤ u) (hS : 1 ≤ S) (ho : out.length ≤ S) (hA : ∀ i,(A i).length ≤ S)
    (hB : S+u+3 ≤ B) :
    ∃ q,runFrom machine (2*(u+2)+2) (entry out (paddedData B A) B)=some q ∧
      q.steps ≤ 2*(u+2)+2 ∧ q.final.heads=resultHeads (r.final.heads 20) ∧
      q.final.tapes=resultData (paddedData B r.final.tapes) B ∧
      (∀ i,(paddedData B r.final.tapes i).length ≤ B) := by
  obtain ⟨p,pr,ps,ph,pt,pb⟩:=reset_run out A u S B r hr hs hS ho hA hB
  obtain ⟨q,qr,qf,qs,_⟩:=ZeroPadding.run_config machine (paddedCapacity B) _ _ p pr
  rw [padding_entry] at qr
  refine ⟨q,qr,qs.le.trans ps,?_,?_,?_⟩
  · rw [qf]
    exact ph
  · rw [qf]
    change (fun i=>ZeroPadding.pad (paddedCapacity B i) (p.final.tapes i))=_
    rw [pt,padding_result]
  · intro i
    change (ZeroPadding.pad (workCapacity B i) (r.final.tapes i)).length ≤ B
    rw [ZeroPadding.pad_length]
    refine max_le ?_ (pb i)
    unfold workCapacity
    split <;> omega

end NearCubicWires.RepairOrdinary.RecoveryBoundedRowReuse
