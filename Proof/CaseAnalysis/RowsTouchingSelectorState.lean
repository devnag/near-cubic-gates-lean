import Proof.CaseAnalysis.RowsTouchingSelectorMeaning

namespace NearCubicWires.RepairOrdinary.CloseoutRowsTouching.Selector
open SupplierTouching
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

structure State (q : ℕ) where
  selected : Finset (Fin q)
  k : ℕ
  h : ℕ
  store : Coordinate.Store

noncomputable def step {q G : ℕ} (support : Fin G→Finset (Fin q)) (w P j : ℕ) (st : State q):State q:=
  if hj:j<q then
    let records:=Gate.records support st.selected (remaining q j) ⟨j,hj⟩
    let picked:=Choice.decision support st.selected (remaining q j) ⟨j,hj⟩ st.k
    ⟨if picked then insert ⟨j,hj⟩ st.selected else st.selected,
      Coordinate.nextK st.k picked,Coordinate.nextH st.h picked,
      Coordinate.advanced q st.k st.h w P records (MaskShift.cells st.selected j) st.store⟩
  else st

noncomputable def states {q G : ℕ} (support : Fin G→Finset (Fin q)) (w P : ℕ) (initial : State q):ℕ→State q
  | 0=>initial
  | j+1=>step support w P j (states support w P initial j)

def Valid {q : ℕ} (w P j : ℕ) (st : State q):Prop:=
  st.k+st.h=q-j ∧ Coordinate.Valid q w P st.store ∧
  st.store.gate.excluded=0 ∧ st.store.gate.included=0 ∧ (j<q→st.store.carry=false)

theorem counts_next {q G : ℕ} (support : Fin G→Finset (Fin q)) (selected : Finset (Fin q))
    (j k h : ℕ) (hj:j<q) (count:k+h=q-j):
    let picked:=Choice.decision support selected (remaining q j) ⟨j,hj⟩ k
    Coordinate.nextK k picked+Coordinate.nextH h picked=q-(j+1):=by
  dsimp only
  let picked:=Choice.decision support selected (remaining q j) ⟨j,hj⟩ k
  have kp:picked=true→0<k:=by
    intro hp
    have hh:0<k ∧ k*Complement.score support selected (remaining q j) k≤
        ((remaining q j).card+1-k)*Complement.score support (insert ⟨j,hj⟩ selected) (remaining q j) (k-1):=by
      simpa only [picked,Choice.decision,Bool.and_eq_true,decide_eq_true_eq] using hp
    exact hh.1
  have hp:picked=false→0<h:=by
    intro hf
    by_contra hz
    have he:k=(remaining q j).card+1:=by rw [remaining_card];omega
    have forced:=Choice.forced_decision support selected (remaining q j) ⟨j,hj⟩
    rw [←he] at forced
    change picked=true at forced
    simp only [hf,Bool.false_eq_true] at forced
  change Coordinate.nextK k picked+Coordinate.nextH h picked=_
  cases he:picked
  · have hh:=hp he
    simp only [Coordinate.nextK,Coordinate.nextH,Bool.false_eq_true,↓reduceIte]
    omega
  · have hk:=kp he
    simp only [Coordinate.nextK,Coordinate.nextH,↓reduceIte]
    omega

theorem chosen_flag (w k h : ℕ) (store : Coordinate.Store):
    (Coordinate.chosen w k h store).flag=(decide (0<k)&&decide (k*store.gate.excluded≤h*store.gate.included)):=rfl

theorem picked_exact {q G : ℕ} (support : Fin G→Finset (Fin q)) (selected : Finset (Fin q))
    (j k h w P : ℕ) (store : Coordinate.Store) (hj:j<q) (count:k+h=q-j)
    (hz:store.gate.excluded=0 ∧ store.gate.included=0):
    (Coordinate.chosen w k h (Coordinate.folded q k w P
      (Gate.records support selected (remaining q j) ⟨j,hj⟩) store)).flag=
      Choice.decision support selected (remaining q j) ⟨j,hj⟩ k:=by
  have scores:=Gate.records_scores support selected (remaining q j) ⟨j,hj⟩ k w P store.gate
  simp only [hz.1,hz.2,Nat.zero_add] at scores
  have gap:h=(remaining q j).card+1-k:=by rw [remaining_card];omega
  have len:(Gate.records support selected (remaining q j) ⟨j,hj⟩).length=G:=List.length_ofFn
  rw [chosen_flag]
  simp only [Coordinate.folded,len]
  rw [scores.1,scores.2,gap]
  rfl

theorem step_valid {q G : ℕ} (support : Fin G→Finset (Fin q)) (w P j : ℕ) (st : State q)
    (hj:j<q) (hP:q+1≤P) (hv:Valid w P j st):Valid w P (j+1) (step support w P j st):=by
  have hq:∀ xs∈Gate.records support st.selected (remaining q j) ⟨j,hj⟩,xs.length=q:=by
    intro xs hxs
    rcases List.mem_ofFn.mp hxs with ⟨g,rfl⟩
    exact SupportScan.cells_length _ _ _ _
  have fv:=Gate.states_valid q st.k w P _ st.store.gate hq hP hv.2.1.1 _ (Nat.le_refl _)
  have cv:=Coordinate.chosen_valid q st.k st.h w P
    (Coordinate.folded q st.k w P (Gate.records support st.selected (remaining q j) ⟨j,hj⟩) st.store) fv
  simp only [Valid,step,dif_pos hj]
  refine ⟨?_,?_,?_,?_,?_⟩
  · exact counts_next support st.selected j st.k st.h hj hv.1
  · exact cv
  · rfl
  · rfl
  · intro hn
    change MaskShift.carry (MaskShift.cells st.selected j) (MaskShift.cells st.selected j).length=false
    rw [MaskShift.cells_length]
    exact MaskShift.carry_before_last st.selected j hn

theorem states_valid {q G : ℕ} (support : Fin G→Finset (Fin q)) (w P : ℕ) (initial : State q)
    (hP:q+1≤P) (hi:Valid w P 0 initial) (j : ℕ) (hj:j≤q):
    Valid w P j (states support w P initial j):=by
  induction j with
  | zero=>exact hi
  | succ j ih=>exact step_valid support w P j _ (by omega) hP (ih (by omega))

end NearCubicWires.RepairOrdinary.CloseoutRowsTouching.Selector
