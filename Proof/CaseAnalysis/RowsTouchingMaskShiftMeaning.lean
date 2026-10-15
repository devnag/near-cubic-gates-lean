import Proof.CaseAnalysis.RowsTouchingMaskShiftData

namespace NearCubicWires.RepairOrdinary.CloseoutRowsTouching.MaskShift
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def cells {q : ℕ} (selected : Finset (Fin q)) (j : ℕ):List Cell:=
  List.ofFn (fun i : Fin q=>(decide (i∈selected),decide (i.val=j),decide (j< i.val)))

theorem cells_length {q : ℕ} (selected : Finset (Fin q)) (j : ℕ):(cells selected j).length=q:=List.length_ofFn

theorem cells_get {q : ℕ} (selected : Finset (Fin q)) (j i : ℕ) (hi:i<q):
    (cells selected j).getD i (false,false,false)=
      (decide ((⟨i,hi⟩ : Fin q)∈selected),decide (i=j),decide (j< i)):=by
  rw [List.getD_eq_getElem _ _ (by rw [cells_length];exact hi)]
  simp only [cells,List.getElem_ofFn]

theorem carry_cells {q : ℕ} (selected : Finset (Fin q)) (j i : ℕ) (hi:i≤q):
    carry (cells selected j) i=decide (i=j+1):=by
  cases i with
  | zero=>simp [carry]
  | succ i=>
    rw [carry_succ,cells_get selected j i (by omega)]
    simp only [current,Nat.add_left_inj]

theorem transformed_cells {q : ℕ} (picked : Bool) (selected : Finset (Fin q)) (j : ℕ) (hj:j<q):
    transformed picked (cells selected j)=cells (if picked then insert ⟨j,hj⟩ selected else selected) (j+1):=by
  apply List.ext_getElem
  · simp only [transformed_length,cells_length]
  · intro i hi hi'
    have hqi:i<q:=by simpa only [transformed_length,cells_length] using hi
    rw [transformed_get picked (cells selected j) i (by rw [cells_length];exact hqi)]
    rw [carry_cells selected j i hqi.le,cells_get selected j i hqi]
    simp only [cells,List.getElem_ofFn]
    have remain:(decide (j< i)&& !decide (i=j+1))=decide (j+1< i):=by
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true',decide_eq_false_iff_not]
      omega
    cases picked <;> simp [update,live,current,remaining,remain,Fin.ext_iff,Bool.or_comm]

theorem carry_before_last {q : ℕ} (selected : Finset (Fin q)) (j : ℕ) (hj:j+1<q):
    carry (cells selected j) q=false:=by
  rw [carry_cells selected j q (by omega)]
  exact decide_eq_false (by omega)

end NearCubicWires.RepairOrdinary.CloseoutRowsTouching.MaskShift
