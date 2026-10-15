import Proof.CaseAnalysis.RowsTouchingCoordinateRun
import Proof.CaseAnalysis.RowsTouchingChoiceMeaning

namespace NearCubicWires.RepairOrdinary.CloseoutRowsTouching.Selector
open SupplierTouching
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def remaining (q j : ℕ):Finset (Fin q):=Finset.univ.filter (fun i=>j< i.val)

theorem remaining_eq_drop (q j : ℕ):remaining q j=((List.finRange q).drop (j+1)).toFinset:=by
  ext i
  simp only [remaining,Finset.mem_filter,Finset.mem_univ,true_and,List.mem_toFinset,List.mem_drop_iff_getElem]
  constructor
  · intro hi
    refine ⟨i.val-(j+1),by simp only [List.length_finRange];omega,?_⟩
    apply Fin.ext
    simp only [List.getElem_finRange,Fin.val_cast]
    omega
  · rintro ⟨n,hn,he⟩
    have hv:=congrArg (fun x : Fin q=>x.val) he
    simp only [List.getElem_finRange,Fin.val_cast] at hv
    omega

theorem remaining_card (q j : ℕ):(remaining q j).card=q-(j+1):=by
  rw [remaining_eq_drop,List.toFinset_card_of_nodup ((List.nodup_finRange q).drop)]
  simp

theorem coordinate_cons {q : ℕ} (j : ℕ) (hj:j<q):
    (List.finRange q).drop j=(⟨j,hj⟩ : Fin q)::(List.finRange q).drop (j+1):=by
  have hb:j<(List.finRange q).length:=by simpa only [List.length_finRange] using hj
  have he:(List.finRange q)[j]= (⟨j,hj⟩ : Fin q):=by
    apply Fin.ext
    simp only [List.getElem_finRange,Fin.val_cast]
  rw [List.drop_eq_getElem_cons hb,he]

theorem support_cells {q : ℕ} (selected : Finset (Fin q)) (j : ℕ) (hj:j<q):
    Coordinate.supportCells (MaskShift.cells selected j)=SupportScan.cells ∅ selected (remaining q j) ⟨j,hj⟩:=by
  simp only [Coordinate.supportCells,MaskShift.cells,List.map_ofFn,SupportScan.cells]
  congr 1
  funext i
  simp [remaining,Fin.ext_iff]

theorem aux_zero {q G : ℕ} (support : Fin G→Finset (Fin q)) (selected : Finset (Fin q)) (rest : List (Fin q)):
    touchingSelectAux support selected 0 rest=selected:=by
  cases rest <;> simp [touchingSelectAux]

theorem original_step {q G : ℕ} (support : Fin G→Finset (Fin q)) (selected : Finset (Fin q))
    (j k : ℕ) (hj:j<q) (hk:k≤q-j):
    let picked:=Choice.decision support selected (remaining q j) ⟨j,hj⟩ k
    touchingSelectAux support selected k ((List.finRange q).drop j)=
      touchingSelectAux support (if picked then insert ⟨j,hj⟩ selected else selected)
        (Coordinate.nextK k picked) ((List.finRange q).drop (j+1)):=by
  dsimp only
  by_cases hz:k=0
  · subst k
    simp [Choice.decision,Coordinate.nextK,aux_zero]
  have bound:k≤(remaining q j).card+1:=by rw [remaining_card];omega
  let comparison:=conditionalTouchNumerator support (insert ⟨j,hj⟩ selected) (remaining q j) (k-1)*Nat.choose (q-(j+1)) k≤
    conditionalTouchNumerator support selected (remaining q j) k*Nat.choose (q-(j+1)) (k-1)
  have pick:Choice.decision support selected (remaining q j) ⟨j,hj⟩ k=decide comparison:=by
    apply Bool.eq_iff_iff.mpr
    rw [Choice.decision_exact support selected (remaining q j) ⟨j,hj⟩ k bound]
    simp only [hz,ne_eq,not_false_eq_true,true_and,decide_eq_true_eq,remaining_card]
    rfl
  rw [pick,coordinate_cons j hj]
  simp only [touchingSelectAux,hz,↓reduceDIte]
  rw [←remaining_eq_drop]
  simp only [List.length_drop,List.length_finRange]
  by_cases hc:comparison
  all_goals simp only [comparison] at hc
  all_goals simp [comparison,hc,Coordinate.nextK]

end NearCubicWires.RepairOrdinary.CloseoutRowsTouching.Selector
