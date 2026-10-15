import Proof.CaseAnalysis.RowsTouchingSupportFold

/-! Bind the physical support scan to the original declared support,
selected coordinates, current candidate, and undecided suffix. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsTouching.SupportScan
open LocalBitMultitape CloseoutRowsGateSupport
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def cells {q : ℕ} (support selected undecided : Finset (Fin q)) (coordinate : Fin q):List Cell:=
  List.ofFn (fun i=>(decide (i∈support),decide (i∈selected),decide (i=coordinate),decide (i∈undecided)))

theorem cells_length {q : ℕ} (support selected undecided : Finset (Fin q)) (coordinate : Fin q):
    (cells support selected undecided coordinate).length=q:=List.length_ofFn

theorem cells_support {q : ℕ} (support selected undecided : Finset (Fin q)) (coordinate : Fin q):
    (cells support selected undecided coordinate).map Prod.fst=gateMembers support:=by
  simp [cells,gateMembers,List.map_ofFn,Function.comp_def]

theorem cells_masks {q : ℕ} (support selected undecided : Finset (Fin q)) (coordinate : Fin q):
    masks (cells support selected undecided coordinate)=
      ![gateMembers selected,gateMembers {coordinate},gateMembers undecided]:=by
  funext i;fin_cases i <;> simp [masks,cells,gateMembers,List.map_ofFn,Function.comp_def]

theorem count_ones (xs : List Cell):count xs=CloseoutRowsSupportCount.ones (xs.map kept):=by
  induction xs with
  | nil=>rfl
  | cons e xs ih=>simp only [count,List.map_cons,CloseoutRowsSupportCount.ones,ih]

theorem cells_count {q : ℕ} (support selected undecided : Finset (Fin q)) (coordinate : Fin q):
    count (cells support selected undecided coordinate)=(undecided\support).card:=by
  rw [count_ones]
  have he:(cells support selected undecided coordinate).map kept=gateMembers (undecided\support):=by
    simp only [cells,List.map_ofFn,gateMembers]
    congr 1
    funext i
    by_cases hu:i∈undecided <;> by_cases hs:i∈support <;> simp [kept,hu,hs]
  rw [he]
  exact CloseoutRowsSupportCount.support_card _

theorem cells_touched {q : ℕ} (support selected undecided : Finset (Fin q)) (coordinate : Fin q):
    (cells support selected undecided coordinate).any touched=decide (¬Disjoint selected support):=by
  apply Bool.eq_iff_iff.mpr
  simp [List.any_eq_true,cells,touched,Finset.not_disjoint_iff,and_comm]

theorem cells_current {q : ℕ} (support selected undecided : Finset (Fin q)) (coordinate : Fin q):
    (cells support selected undecided coordinate).any current=decide (coordinate∈support):=by
  apply Bool.eq_iff_iff.mpr
  simp [List.any_eq_true,cells,current]

end NearCubicWires.RepairOrdinary.CloseoutRowsTouching.SupportScan
