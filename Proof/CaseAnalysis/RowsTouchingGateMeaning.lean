import Proof.CaseAnalysis.RowsTouchingGateMath
import Proof.CaseAnalysis.RowsTouchingSupportTyped
import Proof.CaseAnalysis.RowsTouchingComplement

/-! The paired physical accumulators are the exact complementary scores of
all original declared gate supports, including declared zero-weight wires. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsTouching.Gate
open SupportScan
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem states_exact (q k w P : ℕ) (records : List (List Cell)) (initial : Store)
    (j : ℕ) (hj:j≤records.length):
    (states q k w P records initial j).excluded=initial.excluded+
      ((records.take j).map (fun xs=>contribution false xs k)).sum ∧
    (states q k w P records initial j).included=initial.included+
      ((records.take j).map (fun xs=>contribution true xs k)).sum:=by
  induction j with
  | zero=>simp [states]
  | succ j ih=>
    have hj':j<records.length:=by omega
    have old:=ih (by omega)
    rw [states,after_excluded,after_included,old.1,old.2,List.take_succ_eq_append_getElem hj']
    simp only [List.map_append,List.map_cons,List.map_nil,List.sum_append,List.sum_cons,
      List.sum_nil,Nat.add_zero,List.getD_eq_getElem records [] hj',Nat.add_assoc,and_self]

def records {q G : ℕ} (support : Fin G→Finset (Fin q))
    (selected undecided : Finset (Fin q)) (coordinate : Fin q):List (List Cell):=
  List.ofFn (fun g=>cells (support g) selected undecided coordinate)

theorem contribution_excluded {q : ℕ} (support selected undecided : Finset (Fin q))
    (coordinate : Fin q) (k : ℕ):contribution false (cells support selected undecided coordinate) k=
      if Disjoint selected support then Nat.choose (undecided\support).card k else 0:=by
  classical
  simp [contribution,ScoreAdd.skip,cells_touched,cells_count,key]

theorem contribution_included {q : ℕ} (support selected undecided : Finset (Fin q))
    (coordinate : Fin q) (k : ℕ):contribution true (cells support selected undecided coordinate) k=
      if Disjoint (insert coordinate selected) support then Nat.choose (undecided\support).card (k-1) else 0:=by
  classical
  by_cases hs:Disjoint selected support <;> by_cases hc:coordinate∈support <;>
    simp [contribution,ScoreAdd.skip,cells_touched,cells_current,cells_count,key,hs,hc,Finset.disjoint_insert_left]

theorem records_scores {q G : ℕ} (support : Fin G→Finset (Fin q))
    (selected undecided : Finset (Fin q)) (coordinate : Fin q) (k w P : ℕ) (initial : Store):
    (states q k w P (records support selected undecided coordinate) initial G).excluded=
      initial.excluded+Complement.score support selected undecided k ∧
    (states q k w P (records support selected undecided coordinate) initial G).included=
      initial.included+Complement.score support (insert coordinate selected) undecided (k-1):=by
  have length:(records support selected undecided coordinate).length=G:=List.length_ofFn
  have exactScores:=states_exact q k w P (records support selected undecided coordinate) initial G (by omega)
  rw [List.take_of_length_le length.le] at exactScores
  simpa only [records,List.length_ofFn,List.map_ofFn,Function.comp_def,contribution_excluded,
    contribution_included,List.sum_ofFn,Complement.score] using exactScores

end NearCubicWires.RepairOrdinary.CloseoutRowsTouching.Gate
