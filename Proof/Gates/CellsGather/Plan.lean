import Proof.Gates.CellsGather.Rows

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.Cells.GatherPhase

open NearCubicGates.Close.Cells
open NearCubicWires NearCubicGates
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Counter

section L
variable (c : Call) (p : Params) (wt : Wit c.n) (i : ℕ)

/-- The table: (key, value) of every block record, then the padding entries. -/
noncomputable def tabT : List (ℕ × ℕ) :=
  (blk c p wt i).map (fun x => (x / 2 ^ valueWidth c p % 2 ^ keyW c p, x % 2 ^ valueWidth c p)) ++
    List.replicate (CounterMachine.cellN c p wt).length (2 ^ keyW c p, 0)

/-- The queries: (key, tag). -/
noncomputable def qryQ : List (ℕ × ℕ) := (rowKeys c p wt (cellOf wt.I i)).zipIdx

/-- The input of `gather_eq`. -/
noncomputable def gIn : List ℕ :=
  (tabT c p wt i).map (fun e => tRec (gZ c p) e.1 e.2) ++ (qryQ c p wt i).map (fun q => qRec (gZ c p) q.1 q.2)

/-- The real records (all but the padding). -/
noncomputable def realL : List ℕ :=
  (blk c p wt i).map (tabRec c p) ++ (qryQ c p wt i).map (fun q => qRec (gZ c p) q.1 q.2)

/-- The sorted real records. -/
noncomputable def realS : List ℕ := (realL c p wt i).insertionSort (· ≤ ·)

theorem emitL_eq : emitL c p wt i = realL c p wt i ++
    List.replicate (CounterMachine.cellN c p wt).length (padRec c p) := by
  unfold emitL realL qryQ; rfl

theorem emitL_perm : (emitL c p wt i).Perm (gIn c p wt i) := by
  unfold emitL gIn tabT qryQ
  simp only [List.map_append, List.map_map, List.map_replicate]
  have e : ((fun e : ℕ × ℕ => tRec (gZ c p) e.1 e.2) ∘ fun x =>
      (x / 2 ^ valueWidth c p % 2 ^ keyW c p, x % 2 ^ valueWidth c p)) = tabRec c p := rfl
  rw [e, List.append_assoc, List.append_assoc]
  refine List.Perm.append_left _ ?_
  unfold padRec
  exact List.perm_append_comm

theorem gWork_eq : (emitL c p wt i).length = gWork c p wt (cellOf wt.I i) := by
  unfold emitL gWork
  simp [blk_length, rowKeys_length]; omega

theorem qryQ_length : (qryQ c p wt i).length = (rowVals c p wt (cellOf wt.I i)).length := by
  unfold qryQ; rw [List.length_zipIdx, rowKeys_length]

theorem realL_length : (realL c p wt i).length = (reqIds c p).length + (rowVals c p wt (cellOf wt.I i)).length := by
  unfold realL; simp [blk_length, qryQ_length]

theorem realS_length : (realS c p wt i).length = (reqIds c p).length + (rowVals c p wt (cellOf wt.I i)).length := by
  unfold realS; rw [List.length_insertionSort, realL_length]

/-! ## Widths -/

theorem tRec_lt_pad (k v : ℕ) (hk : k < 2 ^ keyW c p) (hv : v < 2 ^ gZ c p) : tRec (gZ c p) k v < padRec c p := by
  unfold tRec padRec tRec
  have h1 : (2 * k + 1) * 2 ^ gZ c p ≤ 2 * 2 ^ keyW c p * 2 ^ gZ c p := Nat.mul_le_mul_right _ (by omega)
  have h2 : (2 * k + 1) * 2 ^ gZ c p = 2 * k * 2 ^ gZ c p + 2 ^ gZ c p := by ring
  omega

theorem qRec_lt_pad (k t : ℕ) (hk : k < 2 ^ keyW c p) (ht : t < 2 ^ gZ c p) : qRec (gZ c p) k t < padRec c p := by
  unfold qRec padRec tRec
  have h1 : (2 * k + 2) * 2 ^ gZ c p ≤ 2 * 2 ^ keyW c p * 2 ^ gZ c p := Nat.mul_le_mul_right _ (by omega)
  have h2 : (2 * k + 2) * 2 ^ gZ c p = (2 * k + 1) * 2 ^ gZ c p + 2 ^ gZ c p := by ring
  omega

theorem VW_le_gZ : 2 ^ valueWidth c p ≤ 2 ^ gZ c p := Nat.pow_le_pow_right (by norm_num) (by unfold gZ; omega)
theorem KW_le_gZ : 2 ^ keyW c p ≤ 2 ^ gZ c p := Nat.pow_le_pow_right (by norm_num) (by unfold gZ; omega)

theorem qryQ_mem {cT : ℕ} (hs : Spec cT (header c) p) (q : ℕ × ℕ) (hq : q ∈ qryQ c p wt i) :
    q.2 < 2 ^ keyW c p ∧ ∃ id ∈ reqIds c p, reqKey c p id = q.1 := by
  unfold qryQ at hq
  obtain ⟨h1, h2⟩ := List.mem_zipIdx' (x := q.1) (i := q.2) hq
  refine ⟨lt_trans h1 (rowKeys_lt c p wt (cellOf wt.I i) hs), rowKeys_mem c p wt (cellOf wt.I i) hs q.1 ?_⟩
  rw [h2]; exact List.getElem_mem _

theorem realL_lt {cT : ℕ} (hs : Spec cT (header c) p) : ∀ x ∈ realL c p wt i, x < padRec c p := by
  intro x hx
  unfold realL at hx
  rcases List.mem_append.mp hx with hx | hx
  · obtain ⟨z, _, rfl⟩ := List.mem_map.mp hx
    unfold tabRec
    exact tRec_lt_pad c p _ _ (Nat.mod_lt _ (by positivity))
      (lt_of_lt_of_le (Nat.mod_lt _ (by positivity)) (VW_le_gZ c p))
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
    obtain ⟨ht, id, hid, hk⟩ := qryQ_mem c p wt i hs q hq
    rw [← hk]
    exact qRec_lt_pad c p _ _ (reqKey_lt c p hs id hid) (lt_of_lt_of_le ht (KW_le_gZ c p))

/-- **After the sort:** the sorted real records, then the padding. -/
theorem sorted_split {cT : ℕ} (hs : Spec cT (header c) p) (L : List ℕ) (hL : L.Perm (emitL c p wt i)) :
    L.insertionSort (· ≤ ·) = realS c p wt i ++
      List.replicate (CounterMachine.cellN c p wt).length (padRec c p) := by
  refine List.Perm.eq_of_pairwise' (List.pairwise_insertionSort _ _) ?_ ?_
  · rw [List.pairwise_append]
    refine ⟨List.pairwise_insertionSort _ _, List.pairwise_replicate_of_refl, fun x hx y hy => ?_⟩
    rw [List.eq_of_mem_replicate hy]
    have := realL_lt c p wt i hs x ((List.perm_insertionSort _ _).mem_iff.mp hx)
    omega
  · refine (List.perm_insertionSort _ _).trans (hL.trans ?_)
    rw [emitL_eq]
    exact (List.perm_insertionSort _ _).symm.append_right _

theorem sweep_pads (Z' l : ℕ) (n : ℕ) : sweep (gZ c p) Z' (List.replicate n (padRec c p)) l = [] := by
  induction n generalizing l with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, sweep, if_pos (by unfold padRec; exact tRec_flag _ _ _ (by positivity))]
    exact ih _

theorem sweep_split {cT : ℕ} (hs : Spec cT (header c) p) (L : List ℕ) (hL : L.Perm (emitL c p wt i)) (Z' : ℕ) :
    sweep (gZ c p) Z' (L.insertionSort (· ≤ ·)) 0 = sweep (gZ c p) Z' (realS c p wt i) 0 := by
  rw [sorted_split c p wt i hs L hL, sweep_append, sweep_pads, List.append_nil]

/-! ## The gathering lemma, instantiated -/

theorem tabT_mem {cT : ℕ} (hs : Spec cT (header c) p) (w : List Bool) (hw : decodeWitness c p w = some wt)
    (e : ℕ × ℕ) (he : e ∈ tabT c p wt i) :
    e.2 < 2 ^ gZ c p ∧ e.2 = F c p wt (cellOf wt.I i) e.1 := by
  unfold tabT at he
  rcases List.mem_append.mp he with he | he
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp he
    obtain ⟨id, hid, rfl⟩ := mem_blk c p wt hx
    simp only
    rw [rec_key c p wt hs w hw i id hid, rec_val c p wt hs w hw i id hid, Nat.add_comm, Nat.add_mul_mod_self_right,
      Nat.mod_eq_of_lt (reqKey_lt c p hs id hid)]
    exact ⟨lt_of_lt_of_le (reqValue_lt c p wt hs w hw _ id hid) (VW_le_gZ c p), (F_key c p wt hs _ id hid).symm⟩
  · rw [List.eq_of_mem_replicate he]
    exact ⟨by positivity, (F_pad c p wt hs _).symm⟩

theorem gather_main {cT : ℕ} (hs : Spec cT (header c) p) (w : List Bool) (hw : decodeWitness c p w = some wt) :
    (sweep (gZ c p) (valueWidth c p) ((gIn c p wt i).insertionSort (· ≤ ·)) 0).insertionSort (· ≤ ·) =
      (qryQ c p wt i).map (aRec (valueWidth c p) (F c p wt (cellOf wt.I i))) := by
  unfold gIn
  refine gather_eq (gZ c p) (valueWidth c p) (F c p wt (cellOf wt.I i)) (F_lt c p wt hs w hw _) _ _ 0
    (tabT_mem c p wt i hs w hw) (fun q hq => ?_) ?_
  · obtain ⟨ht, id, hid, hk⟩ := qryQ_mem c p wt i hs q hq
    refine ⟨lt_of_lt_of_le ht (KW_le_gZ c p), (reqKey c p id, reqValue c p wt (cellOf wt.I i) id), ?_, hk⟩
    unfold tabT
    refine List.mem_append_left _ (List.mem_map.mpr ⟨cellRec c p wt i id, cellRec_mem_blk c p wt i id hid, ?_⟩)
    rw [rec_key c p wt hs w hw i id hid, rec_val c p wt hs w hw i id hid, Nat.add_comm, Nat.add_mul_mod_self_right,
      Nat.mod_eq_of_lt (reqKey_lt c p hs id hid)]
  · unfold qryQ
    rw [List.zipIdx_map_snd]
    exact List.pairwise_lt_range'

/-- **The answers after the second sort**, from the program's sweep of `realS`. -/
theorem answers_eq {cT : ℕ} (hs : Spec cT (header c) p) (w : List Bool) (hw : decodeWitness c p w = some wt) :
    (sweep (gZ c p) (valueWidth c p) (realS c p wt i) 0).insertionSort (· ≤ ·) =
      (qryQ c p wt i).map (aRec (valueWidth c p) (F c p wt (cellOf wt.I i))) := by
  rw [← sweep_split c p wt i hs (emitL c p wt i) (List.Perm.refl _),
    show (emitL c p wt i).insertionSort (· ≤ ·) = (gIn c p wt i).insertionSort (· ≤ ·) from
      List.Perm.eq_of_pairwise' (List.pairwise_insertionSort _ _) (List.pairwise_insertionSort _ _)
        ((List.perm_insertionSort _ _).trans ((emitL_perm c p wt i).trans (List.perm_insertionSort _ _).symm))]
  exact gather_main c p wt i hs w hw

theorem answers_length {cT : ℕ} (hs : Spec cT (header c) p) (w : List Bool) (hw : decodeWitness c p w = some wt) :
    (sweep (gZ c p) (valueWidth c p) (realS c p wt i) 0).length = (rowVals c p wt (cellOf wt.I i)).length := by
  have := congrArg List.length (answers_eq c p wt i hs w hw)
  rw [List.length_insertionSort, List.length_map, qryQ_length] at this
  exact this

/-- **Stripping the tags gives `rowVals`.** -/
theorem strip_main {cT : ℕ} (hs : Spec cT (header c) p) (w : List Bool) (hw : decodeWitness c p w = some wt) :
    ((qryQ c p wt i).map (aRec (valueWidth c p) (F c p wt (cellOf wt.I i)))).map (· % 2 ^ valueWidth c p) =
      rowVals c p wt (cellOf wt.I i) := by
  rw [List.map_map, ← rowKeys_map_F c p wt _ hs]
  unfold qryQ
  have e : ∀ (l : List ℕ) (k : ℕ), (l.zipIdx k).map ((· % 2 ^ valueWidth c p) ∘
      aRec (valueWidth c p) (F c p wt (cellOf wt.I i))) = l.map (F c p wt (cellOf wt.I i)) := by
    intro l
    induction l with
    | nil => intro k; rfl
    | cons x l ih =>
      intro k
      rw [List.zipIdx_cons, List.map_cons, List.map_cons, ih]
      simp only [Function.comp, aRec]
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (F_lt c p wt hs w hw _ _)]
  exact e _ 0

end L

end NearCubicGates.Close.Cells.GatherPhase
