import Proof.Gates.Expand.PolyTabCls3
import Proof.Gates.Expand.PolyTabTail3

set_option autoImplicit false

namespace NearCubicGates.Close.Expand.PolyTab

open NearCubicWires NearCubicWires.RepairRepresentation NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)
open NearCubicGates.Close.Tabulator NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.CounterMachine NearCubicGates.Close.TabMachine

variable (E : ExpandMachine)

/-- Tuples of children: at most `m^{|os|}` when every occurrence has at most `m` children. -/
theorem tupF_len_le (c m : ℕ) : ∀ os : List Occ, (∀ o ∈ os, (o.kids c).length ≤ m) →
    (tupF c os).length ≤ m ^ os.length := by
  intro os
  induction os using List.reverseRecOn with
  | nil => intro _; simp [tupF]
  | append_singleton os o ih =>
    intro h
    rw [tupF_length, List.length_append, List.length_singleton, pow_succ]
    have h1 := ih (fun o' ho' => h o' (List.mem_append_left _ ho'))
    have h2 := h o (List.mem_append_right _ (List.mem_singleton_self o))
    calc (o.kids c).length * (tupF c os).length ≤ m * m ^ os.length := Nat.mul_le_mul h2 h1
      _ = m ^ os.length * m := by ring

theorem monoTuples_len_le (c m : ℕ) (os : List Occ) (h : ∀ o ∈ os, (o.kids c).length ≤ m) :
    (monoTuples c os).length ≤ m ^ os.length := by
  unfold monoTuples
  rw [tuples_length, List.map_map]
  have := List.prod_le_pow_card ((os.reverse).map (List.length ∘ fun o => o.kids c)) m (by
    intro a ha
    obtain ⟨o, ho, rfl⟩ := List.mem_map.mp ha
    exact h o (List.mem_reverse.mp ho))
  simpa using this

section Data
variable (r : TabReq)

theorem tsK_len : (tsK E r).length = (E.expand ⟨r.V, r.F⟩).length := by rw [tsK_eq]; simp

theorem hsK_len_le : (hsK E r).length ≤ 2 ^ r.k := by
  unfold hsK hList
  exact (List.length_filter_le _ _).trans (by simp [code])

/-- The occurrences of monomial `i`. -/
theorem os_eq (i : ℕ) (hi : i < (tsK E r).length) :
    ∃ t ∈ E.expand ⟨r.V, r.F⟩, osAt E r i = ((mvars t).map (occ (tabT E r))).reverse := by
  have hi' : i < (E.expand ⟨r.V, r.F⟩).length := by rw [← tsK_len]; exact hi
  refine ⟨(E.expand ⟨r.V, r.F⟩)[i], List.getElem_mem hi', ?_⟩
  unfold osAt
  rw [List.getD_eq_getElem _ _ hi]
  simp [tsK_eq]

theorem os_len_le (i : ℕ) (hi : i < (tsK E r).length) : (osAt E r i).length ≤ r.F.degree := by
  obtain ⟨t, ht, e⟩ := os_eq E r i hi
  rw [e, List.length_reverse, List.length_map]
  unfold mvars
  rw [Finset.length_sort]
  exact (E.ok ⟨r.V, r.F⟩).degree t.1 (by unfold Terms.keys; exact List.mem_map.mpr ⟨t, ht, rfl⟩)

theorem kids_le (i : ℕ) (hi : i < (tsK E r).length) (o : Occ) (ho : o ∈ osAt E r i) (c : ℕ) (hc : c < 2 ^ r.k) :
    (o.kids c).length ≤ mTr r := by
  obtain ⟨t, -, e⟩ := os_eq E r i hi
  rw [e, List.mem_reverse] at ho
  obtain ⟨v, -, rfl⟩ := List.mem_map.mp ho
  have h := occ_kids (tabT E r) ⟨c, hc⟩ v
  simp only at h
  rw [h, List.length_map]
  unfold Tabulation.kids
  rw [List.length_map]
  exact exactChildren_length_le _ _ (restrict_bits r.B _ (tabT E r).layout _ (r.hB _))

theorem V_pos_of_os (i : ℕ) (hi : i < (tsK E r).length) (hne : (osAt E r i) ≠ []) : 1 ≤ r.V := by
  obtain ⟨t, -, e⟩ := os_eq E r i hi
  rw [e] at hne
  rcases Nat.eq_zero_or_pos r.V with h0 | h0
  · exfalso
    apply hne
    have : mvars t = [] := by
      unfold mvars
      rw [List.eq_nil_iff_forall_not_mem]
      intro v _
      have hv : (v : ℕ) < r.V := v.isLt
      omega
    simp [this]
  · exact h0

theorem mTr_le_Xr (h : 1 ≤ r.V) : mTr r ≤ Xr r := by unfold Xr; nlinarith

/-- **Tuples are at most `X_r^D`.** -/
theorem tup_le (i : ℕ) (hi : i < (tsK E r).length) (c : ℕ) (hc : c < 2 ^ r.k) (os : List Occ)
    (hos : os.Sublist (osAt E r i)) :
    (tupF c os).length ≤ Xr r ^ r.F.degree ∧ (monoTuples c os).length ≤ Xr r ^ r.F.degree := by
  have hlen : os.length ≤ r.F.degree := (hos.length_le).trans (os_len_le E r i hi)
  by_cases h0 : os = []
  · subst h0
    have : 1 ≤ Xr r ^ r.F.degree := Nat.one_le_pow _ _ (Xr_pos r)
    simp [tupF, monoTuples, tuples]; exact this
  have hV : 1 ≤ r.V := V_pos_of_os E r i hi (fun e => h0 (List.eq_nil_of_sublist_nil (e ▸ hos)))
  have hk : ∀ o ∈ os, (o.kids c).length ≤ Xr r := fun o ho =>
    (kids_le E r i hi o (hos.subset ho) c hc).trans (mTr_le_Xr r hV)
  have hX := Xr_pos r
  exact ⟨(tupF_len_le c _ os hk).trans (Nat.pow_le_pow_right hX hlen),
    (monoTuples_len_le c _ os hk).trans (Nat.pow_le_pow_right hX hlen)⟩

theorem cAt_lt (j : ℕ) (hj : j < (hsK E r).length) : cAt E r j < 2 ^ r.k := by
  unfold cAt; rw [List.getD_eq_getElem _ _ hj]; exact hs_lt E r j hj

theorem termStart_le (i : ℕ) (hi : i < (tsK E r).length) : termStart (tsK E r) i ≤ (xsK E r).length :=
  (code_count (tsK E r) i hi).1.le

theorem pAt_le (i : ℕ) (hi : i < (tsK E r).length) (i' : ℕ) (hi' : i' < (osAt E r i).length) :
    pAt E r i i' ≤ (xsK E r).length := by
  have hos : osAt E r i = (tsK E r)[i].1 := by unfold osAt; rw [List.getD_eq_getElem _ _ hi]
  have hi'' : i' < (tsK E r)[i].1.length := by rw [← hos]; exact hi'
  have hb := blk_at (tsK E r) i hi i' hi''
  have hl := congrArg List.length hb
  rw [List.length_take, List.length_drop, occRecs_length] at hl
  have : 1 ≤ occLen (tsK E r)[i].1[i'] := by unfold occLen; omega
  unfold pAt xsK; rw [hos]
  omega

/-- A compiled child record of an occurrence at inner point `c`. -/
theorem compRecs_len (o : Occ) (c W : ℕ) :
    (compRecs W o.outW (rTarget o c)).length = (o.kids c).length * (2 * ((o.outW.length + 1) * (W + 1)) + 1) := by
  unfold compRecs
  have e : o.kids c = compileL o.outW (rTarget o c) := rfl
  rw [← e]
  refine flatMap_len_const _ _ _ (fun kid hk => ?_)
  rw [frame_length]
  unfold recBits
  rw [flatMap_len_const _ _ (W + 1) (fun z _ => binary_length _ _), kids_length o c kid hk]

theorem fieldNums_len (c : ℕ) (os : List Occ) (hs : ∀ o ∈ os, o.outW.length = r.s) :
    (fieldNums ((monoTuples c os).map List.flatten)).length ≤ (monoTuples c os).length * (os.length * (r.s + 1)) := by
  unfold fieldNums
  rw [List.length_map, List.length_flatten, List.map_map]
  refine sum_le_len_mul _ _ _ (fun ls hls => ?_)
  simp only [Function.comp_apply]
  rw [List.length_flatten]
  unfold monoTuples at hls
  have hl := mem_tuples_length _ ls hls
  rw [List.length_map, List.length_reverse] at hl
  have hm := mem_tuples_mem _ ls hls
  calc (ls.map List.length).sum ≤ ls.length * (r.s + 1) := sum_le_len_mul _ _ _ (fun e he => by
        obtain ⟨L, hL, heL⟩ := hm e he
        obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hL
        rw [kids_length o c e heL, hs o (List.mem_reverse.mp ho)])
    _ = os.length * (r.s + 1) := by rw [hl]

end Data

end NearCubicGates.Close.Expand.PolyTab
