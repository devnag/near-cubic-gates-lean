import Proof.Gates.Expand.PolyTabTail4a

set_option autoImplicit false

namespace NearCubicGates.Close.Expand.PolyTab

open NearCubicWires NearCubicWires.RepairRepresentation NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Tabulator NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.CounterMachine NearCubicGates.Close.TabMachine NearCubicGates.Close.WordPrograms

theorem occACost_mono (W n s k : ℕ) {p p' kd kd' : ℕ} (hp : p ≤ p') (hk : kd ≤ kd') :
    occACost W n s k p kd ≤ occACost W n s k p' kd' := by
  unfold occACost restrictCost; gcongr

theorem occBCost_mono (W s : ℕ) {K K' T T' M M' : ℕ} (hK : K ≤ K') (hT : T ≤ T') (hM : M ≤ M') :
    occBCost W s K T M ≤ occBCost W s K' T' M' := by
  unfold occBCost occB1Cost occB2Cost occB3Cost tupleCost tOuterCost tInnerCost copyStep; gcongr

theorem monoStepCost_mono (W s Wd CS B : ℕ) {p p' m m' F F' T T' : ℕ} (hp : p ≤ p') (hm : m ≤ m') (hF : F ≤ F')
    (hT : T ≤ T') : monoStepCost W s Wd CS B p m F T ≤ monoStepCost W s Wd CS B p' m' F' T' := by
  unfold monoStepCost monoPreCost monoStackCost stackAllCost stackOneCost baseCost sumBodyCost oneFieldCost
    fieldBodyCost
  gcongr

theorem foldr_max_le' (l : List ℕ) (b : ℕ) (h : ∀ x ∈ l, x ≤ b) : l.foldr max 0 ≤ b := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.foldr_cons]
    exact max_le (h a (List.mem_cons_self)) (ih (fun x hx => h x (List.mem_cons_of_mem _ hx)))

variable (E : ExpandMachine)

section Data
variable (r : TabReq)

/-- The bound of one occurrence step. -/
def SBf : ℕ :=
  occACost (Wk E r) (xsK E r).length r.s r.k (xsK E r).length (mTr r * (2 * ((r.s + 1) * (Wk E r + 1)) + 1)) + 1 +
    occBCost (Wk E r) r.s (mTr r) (Xr r ^ r.F.degree) (r.F.degree * (r.s + 1))

/-- The bound of the stacking parameter. -/
def BBf : ℕ := r.F.degree * (r.s + 1) + Xr r ^ r.F.degree + r.s + 1 + r.F.degree

/-- The bound of one monomial step. -/
def MBf : ℕ :=
  monoStepCost (Wk E r) r.s (Wdk E r) (CSk E r) (BBk E r) (xsK E r).length r.F.degree
    (Xr r ^ r.F.degree * (r.F.degree * (r.s + 1))) (Xr r ^ r.F.degree)

theorem oAt_mem (i i' : ℕ) (hi' : i' < (osAt E r i).length) : oAt E r i i' ∈ osAt E r i := by
  unfold oAt; rw [List.getD_eq_getElem _ _ hi']; exact List.getElem_mem hi'

theorem outW_of_os (i : ℕ) (hi : i < (tsK E r).length) (o : Occ) (ho : o ∈ osAt E r i) : o.outW.length = r.s := by
  obtain ⟨t, -, e⟩ := os_eq E r i hi
  rw [e, List.mem_reverse] at ho
  obtain ⟨v, -, rfl⟩ := List.mem_map.mp ho
  exact occ_outW_length E r v

theorem CSk_le : CSk E r ≤ SBf E r := by
  unfold CSk
  refine foldr_max_le' _ _ (fun y hy => ?_)
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
  simp only [idx3, List.mem_flatMap, List.mem_map, List.mem_range] at hx
  obtain ⟨j, hj, i, hi, i', hi', rfl⟩ := hx
  have ho := oAt_mem E r i i' hi'
  have hc := cAt_lt E r j hj
  have hK := kids_le E r i hi _ ho (cAt E r j) hc
  have hout := outW_of_os E r i hi _ ho
  have hT := (tup_le E r i hi (cAt E r j) hc ((osAt E r i).take i') (List.take_sublist _ _)).1
  have hM : i' * (r.s + 1) ≤ r.F.degree * (r.s + 1) :=
    Nat.mul_le_mul_right _ ((Nat.le_of_lt hi').trans (os_len_le E r i hi))
  unfold stepCost occStepCost SBf
  simp only
  rw [compRecs_len, hout]
  have h1 := occACost_mono (Wk E r) (xsK E r).length r.s r.k (pAt_le E r i hi i' hi')
    (Nat.mul_le_mul_right (2 * ((r.s + 1) * (Wk E r + 1)) + 1) hK)
  have h2 := occBCost_mono (Wk E r) r.s hK hT hM
  unfold tfAt
  omega

theorem BBk_le' : BBk E r ≤ BBf r := by
  unfold BBk
  refine foldr_max_le' _ _ (fun y hy => ?_)
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
  simp only [idx2, List.mem_flatMap, List.mem_map, List.mem_range] at hx
  obtain ⟨j, hj, i, hi, rfl⟩ := hx
  have hc := cAt_lt E r j hj
  have hos := os_len_le E r i hi
  have hT := (tup_le E r i hi (cAt E r j) hc (osAt E r i) (List.Sublist.refl _)).2
  unfold bbAt BBf
  have : (osAt E r i).length * (r.s + 1) ≤ r.F.degree * (r.s + 1) := Nat.mul_le_mul_right _ hos
  simp only
  omega

theorem CMk_le : CMk E r ≤ MBf E r := by
  unfold CMk
  refine foldr_max_le' _ _ (fun y hy => ?_)
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
  simp only [idx2, List.mem_flatMap, List.mem_map, List.mem_range] at hx
  obtain ⟨j, hj, i, hi, rfl⟩ := hx
  have hc := cAt_lt E r j hj
  have hos := os_len_le E r i hi
  have hT := (tup_le E r i hi (cAt E r j) hc (osAt E r i) (List.Sublist.refl _)).2
  have hF := fieldNums_len r (cAt E r j) (osAt E r i) (fun o ho => outW_of_os E r i hi o ho)
  have hF' : (monoTuples (cAt E r j) (osAt E r i)).length * ((osAt E r i).length * (r.s + 1)) ≤
      Xr r ^ r.F.degree * (r.F.degree * (r.s + 1)) :=
    Nat.mul_le_mul hT (Nat.mul_le_mul_right _ hos)
  unfold monoCost MBf
  simp only
  exact monoStepCost_mono _ _ _ _ _ (termStart_le E r i hi) hos (hF.trans hF') hT

end Data

end NearCubicGates.Close.Expand.PolyTab
