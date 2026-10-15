import Proof.Gates.Cells.InputLen

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace NearCubicGates.Close.Cells

open NearCubicWires NearCubicGates
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Counter

section Recs
variable {cT : ℕ} (c : Call) (p : Params) (wt : Wit c.n)

/-! ## Values -/

theorem card_pts (hk : wt.I.card = p.k) : Fintype.card (Points wt.I) = 2 ^ p.k := by simp [Points, hk]

theorem jointCount_le' (hk : wt.I.card = p.k) (q : ℕ) (part : Option Bool) (y : Cells wt.I)
    (κ : Role c × Fin p.J → ℤ) (σ : Role c → ℤ) : jointCount c p wt q part y κ σ ≤ 2 ^ p.k := by
  unfold jointCount
  exact (Finset.card_filter_le _ _).trans (by rw [Finset.card_univ, card_pts c p wt hk])

theorem even_pow_nonneg (x : ℤ) (k : ℕ) : 0 ≤ x ^ (2 * k) := by rw [pow_mul]; positivity

theorem pow_le_of_abs (x : ℤ) (d : ℕ) (k : ℕ) (h : |x| ≤ d) : x ^ (2 * k) ≤ (d : ℤ) ^ (2 * k) := by
  rw [show x ^ (2 * k) = |x| ^ (2 * k) by rw [pow_mul, pow_mul, sq_abs]]
  exact pow_le_pow_left₀ (abs_nonneg x) h _

theorem moment_sum_le (hk : wt.I.card = p.k) (f : Points wt.I → ℤ) (d : ℕ) (hf : ∀ x, |f x| ≤ d) :
    0 ≤ ∑ x : Points wt.I, f x ^ (2 * p.k) ∧
      ∑ x : Points wt.I, f x ^ (2 * p.k) ≤ (2 ^ p.k : ℤ) * (d : ℤ) ^ (2 * p.k) := by
  refine ⟨Finset.sum_nonneg (fun x _ => even_pow_nonneg _ _), ?_⟩
  calc ∑ x : Points wt.I, f x ^ (2 * p.k) ≤ ∑ _x : Points wt.I, (d : ℤ) ^ (2 * p.k) :=
        Finset.sum_le_sum (fun x _ => pow_le_of_abs _ _ _ (hf x))
    _ = (2 ^ p.k : ℤ) * (d : ℤ) ^ (2 * p.k) := by
        rw [Finset.sum_const, Finset.card_univ, card_pts c p wt hk]; simp

theorem bound_lt_two_pow (k d : ℕ) : 2 ^ k * d ^ (2 * k) < 2 ^ (k + 2 * k * Nat.size d + 1) := by
  have h1 : d ^ (2 * k) ≤ (2 ^ Nat.size d) ^ (2 * k) := Nat.pow_le_pow_left (Nat.lt_size_self d).le _
  have h2 : (2 ^ Nat.size d) ^ (2 * k) = 2 ^ (2 * k * Nat.size d) := by rw [← pow_mul]; ring_nf
  have h3 : 2 ^ k * d ^ (2 * k) ≤ 2 ^ (k + 2 * k * Nat.size d) := by
    rw [pow_add]; exact Nat.mul_le_mul_left _ (h1.trans h2.le)
  have h4 : 2 ^ (k + 2 * k * Nat.size d) < 2 ^ (k + 2 * k * Nat.size d + 1) :=
    Nat.pow_lt_pow_right (by norm_num) (by omega)
  omega

theorem toNat_lt_of (z : ℤ) (B : ℕ) (h0 : 0 ≤ z) (h : z ≤ (B : ℤ)) (hB : B < 2 ^ valueWidth c p) :
    z.toNat < 2 ^ valueWidth c p := by omega

theorem mem_reqIds_moment {r j : ℕ} (h : ReqId.digitMoment r j ∈ reqIds c p) : r < roleCount c.kind ∧ j < p.J := by
  unfold reqIds at h
  simp only [List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range, List.mem_singleton] at h
  rcases h with ⟨_, _, _, _, _, _, _, _, h⟩ | ⟨r', hr', (⟨j', hj', h⟩ | h)⟩
  · cases h
  · cases h; exact ⟨hr', hj'⟩
  · cases h

theorem mem_reqIds_phi {r : ℕ} (h : ReqId.phiMoment r ∈ reqIds c p) : r < roleCount c.kind := by
  unfold reqIds at h
  simp only [List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range, List.mem_singleton] at h
  rcases h with ⟨_, _, _, _, _, _, _, _, h⟩ | ⟨r', hr', (⟨j', hj', h⟩ | h)⟩
  · cases h
  · cases h
  · cases h; exact hr'

/-- **Every cell-table value fits its field.** -/
theorem reqValue_lt (hs : Spec cT (header c) p) (w : List Bool) (hw : decodeWitness c p w = some wt)
    (y : Cells wt.I) (id : ReqId) (hid : id ∈ reqIds c p) : reqValue c p wt y id < 2 ^ valueWidth c p := by
  have hk := decodeWitness_card c p w wt hw
  have hb := bound_lt_two_pow p.k (deltaBound c p)
  unfold valueWidth
  cases id with
  | residue part q κ σ =>
    have := jointCount_le' c p wt hk q part y (fun rj => (κ.getD (rj.1.val * p.J + rj.2.val) 0 : ℤ))
      (fun r => (σ.getD r.val 0 : ℤ))
    have : 1 ≤ deltaBound c p ^ (2 * p.k) := Nat.one_le_pow _ _ (by unfold deltaBound; positivity)
    simp only [reqValue]
    calc _ ≤ 2 ^ p.k := by assumption
      _ ≤ 2 ^ p.k * deltaBound c p ^ (2 * p.k) := Nat.le_mul_of_pos_right _ (by omega)
      _ < _ := hb
  | digitMoment r j =>
    obtain ⟨hr, hj⟩ := mem_reqIds_moment c p hid
    have hm := moment_sum_le c p wt hk (fun x => digit c p wt r j (extend wt.I y x) -
      digit c p wt r j (extend wt.I y (zeroPoint wt.I))) (deltaBound c p)
      (fun x => digit_diff c p wt w hw r j hj hr _ _)
    simp only [reqValue, digitMoment]
    have hc : ((2 ^ p.k * deltaBound c p ^ (2 * p.k) : ℕ) : ℤ) = (2 ^ p.k : ℤ) * (deltaBound c p : ℤ) ^ (2 * p.k) := by
      push_cast; ring
    have := hm.2; rw [← hc] at this
    have h1 := Int.toNat_le_toNat this
    simp only [Int.toNat_natCast] at h1
    omega
  | phiMoment r =>
    have hr := mem_reqIds_phi c p hid
    have hJ := hs.J_pos
    have hm := moment_sum_le c p wt hk (fun x => phi c p wt r (extend wt.I y x) -
      phi c p wt r (extend wt.I y (zeroPoint wt.I))) (deltaBound c p)
      (fun x => phi_diff c p wt w hw r hJ hr _ _)
    simp only [reqValue, phiMoment]
    have hc : ((2 ^ p.k * deltaBound c p ^ (2 * p.k) : ℕ) : ℤ) = (2 ^ p.k : ℤ) * (deltaBound c p : ℤ) ^ (2 * p.k) := by
      push_cast; ring
    have := hm.2; rw [← hc] at this
    have h1 := Int.toNat_le_toNat this
    simp only [Int.toNat_natCast] at h1
    omega

end Recs

/-! ## Cell blocks -/

section Blocks
variable {cT : ℕ} (c : Call) (p : Params) (wt : Wit c.n)

/-- The key width `K = keyBits·keyLen`. -/
abbrev keyW : ℕ := keyBits p * keyLen c p

/-- The sorted records of cell `i`. -/
def blk (i : ℕ) : List ℕ := ((reqIds c p).map (cellRec c p wt i)).insertionSort (· ≤ ·)

theorem cellRec_bounds (hs : Spec cT (header c) p) (w : List Bool) (hw : decodeWitness c p w = some wt) (i : ℕ)
    (id : ReqId) (hid : id ∈ reqIds c p) :
    i * 2 ^ (keyW c p + valueWidth c p) ≤ cellRec c p wt i id ∧
      cellRec c p wt i id < (i + 1) * 2 ^ (keyW c p + valueWidth c p) := by
  have hk := reqKey_lt c p hs id hid
  have hv := reqValue_lt c p wt hs w hw (cellOf wt.I i) id hid
  unfold cellRec
  set K := keyBits p * keyLen c p
  set vw := valueWidth c p
  rw [pow_add]
  constructor
  · calc i * (2 ^ K * 2 ^ vw) = (i * 2 ^ K) * 2 ^ vw := by ring
      _ ≤ (i * 2 ^ K + reqKey c p id) * 2 ^ vw := Nat.mul_le_mul_right _ (by omega)
      _ ≤ _ := by omega
  · calc (i * 2 ^ K + reqKey c p id) * 2 ^ vw + reqValue c p wt (cellOf wt.I i) id
        < (i * 2 ^ K + reqKey c p id) * 2 ^ vw + 2 ^ vw := by omega
      _ = (i * 2 ^ K + reqKey c p id + 1) * 2 ^ vw := by ring
      _ ≤ (i * 2 ^ K + 2 ^ K) * 2 ^ vw := Nat.mul_le_mul_right _ (by omega)
      _ = (i + 1) * (2 ^ K * 2 ^ vw) := by ring

theorem sorted_flat_blk (hs : Spec cT (header c) p) (w : List Bool) (hw : decodeWitness c p w = some wt) :
    ∀ N, List.Pairwise (· ≤ ·) ((List.range N).flatMap (blk c p wt)) := by
  intro N
  induction N with
  | zero => simp
  | succ N ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.pairwise_append]
    refine ⟨ih, List.pairwise_insertionSort _ _, ?_⟩
    intro a ha b hb
    simp only [List.mem_flatMap, List.mem_range] at ha
    obtain ⟨i, hi, ha⟩ := ha
    unfold blk at ha hb
    rw [(List.perm_insertionSort _ _).mem_iff, List.mem_map] at ha hb
    obtain ⟨id, hid, rfl⟩ := ha
    obtain ⟨id', hid', rfl⟩ := hb
    have h1 := (cellRec_bounds c p wt hs w hw i id hid).2
    have h2 := (cellRec_bounds c p wt hs w hw N id' hid').1
    have : (i + 1) * 2 ^ (keyW c p + valueWidth c p) ≤ N * 2 ^ (keyW c p + valueWidth c p) :=
      Nat.mul_le_mul_right _ hi
    omega

theorem sorted_blocks (hs : Spec cT (header c) p) (w : List Bool) (hw : decodeWitness c p w = some wt) (N : ℕ) :
    (((List.range N).flatMap fun i => (reqIds c p).map (cellRec c p wt i)).insertionSort (· ≤ ·)) =
      (List.range N).flatMap (blk c p wt) := by
  refine List.Perm.eq_of_pairwise' (List.pairwise_insertionSort _ _) (sorted_flat_blk c p wt hs w hw N) ?_
  refine (List.perm_insertionSort _ _).trans ?_
  apply List.Perm.flatMap_left
  intro i _
  exact (List.perm_insertionSort _ _).symm

theorem blk_length (i : ℕ) : (blk c p wt i).length = (reqIds c p).length := by
  unfold blk; rw [(List.perm_insertionSort _ _).length_eq, List.length_map]

theorem mem_blk {i x : ℕ} (h : x ∈ blk c p wt i) : ∃ id ∈ reqIds c p, x = cellRec c p wt i id := by
  unfold blk at h
  rw [(List.perm_insertionSort _ _).mem_iff, List.mem_map] at h
  obtain ⟨id, hid, rfl⟩ := h
  exact ⟨id, hid, rfl⟩

theorem cellRec_mem_blk (i : ℕ) (id : ReqId) (hid : id ∈ reqIds c p) : cellRec c p wt i id ∈ blk c p wt i := by
  unfold blk; rw [(List.perm_insertionSort _ _).mem_iff]; exact List.mem_map_of_mem hid

/-! ## Record fields -/

theorem rec_val (hs : Spec cT (header c) p) (w : List Bool) (hw : decodeWitness c p w = some wt) (i : ℕ)
    (id : ReqId) (hid : id ∈ reqIds c p) :
    cellRec c p wt i id % 2 ^ valueWidth c p = reqValue c p wt (cellOf wt.I i) id := by
  have hv := reqValue_lt c p wt hs w hw (cellOf wt.I i) id hid
  unfold cellRec
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hv]

theorem rec_key (hs : Spec cT (header c) p) (w : List Bool) (hw : decodeWitness c p w = some wt) (i : ℕ)
    (id : ReqId) (hid : id ∈ reqIds c p) :
    cellRec c p wt i id / 2 ^ valueWidth c p = i * 2 ^ keyW c p + reqKey c p id := by
  have hv := reqValue_lt c p wt hs w hw (cellOf wt.I i) id hid
  unfold cellRec
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt hv, zero_add]

/-- The kind of a request: `0` table (a), `1` digit moment, `2` `Φ` moment (the first key field). -/
def kindOf : ReqId → ℕ
  | .residue .. => 0
  | .digitMoment .. => 1
  | .phiMoment .. => 2

theorem rk_cons (b x : ℕ) (l : List ℕ) : rk b (x :: l) = x * 2 ^ (b * l.length) + rk b l := by
  unfold rk; simp only [List.foldl_cons]; rw [rk_foldl]; simp [rk]

theorem keyFields_head (id : ReqId) : ∃ rest, keyFields id = kindOf id :: rest := by
  cases id <;> simp [keyFields, kindOf]

theorem keyLen_pos : 1 ≤ keyLen c p := by unfold keyLen; omega

theorem reqKey_kind (hs : Spec cT (header c) p) (id : ReqId) (hid : id ∈ reqIds c p) :
    reqKey c p id / 2 ^ (keyW c p - keyBits p) = kindOf id := by
  obtain ⟨rest, hr⟩ := keyFields_head id
  have hlen := keyFields_length_le c p id hid
  have hlt := keyFields_lt c p hs id hid
  unfold reqKey
  rw [radixKey_eq, hr, List.cons_append, rk_cons]
  set L := rest ++ List.replicate (keyLen c p - (kindOf id :: rest).length) 0 with hL
  have hLlen : L.length = keyLen c p - 1 := by
    rw [hL, hr] at *; simp only [List.length_append, List.length_replicate, List.length_cons] at hlen ⊢; omega
  have hLlt : rk (keyBits p) L < 2 ^ (keyBits p * L.length) := by
    apply rk_lt
    intro x hx
    rw [hL] at hx
    simp only [List.mem_append, List.mem_replicate] at hx
    rcases hx with hx | ⟨_, rfl⟩
    · exact hlt x (by rw [hr]; exact List.mem_cons_of_mem _ hx)
    · positivity
  have hK : keyW c p - keyBits p = keyBits p * L.length := by
    rw [hLlen]; unfold keyW; rw [Nat.mul_sub, mul_one]
  rw [hK, Nat.add_comm, Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt hLlt, zero_add]

theorem rec_kind (hs : Spec cT (header c) p) (w : List Bool) (hw : decodeWitness c p w = some wt) (i : ℕ)
    (id : ReqId) (hid : id ∈ reqIds c p) :
    cellRec c p wt i id / 2 ^ valueWidth c p % 2 ^ keyW c p / 2 ^ (keyW c p - keyBits p) = kindOf id := by
  rw [rec_key c p wt hs w hw i id hid, Nat.add_comm, Nat.add_mul_mod_self_right,
    Nat.mod_eq_of_lt (reqKey_lt c p hs id hid)]
  exact reqKey_kind c p hs id hid

/-! ## The tests from the records -/

/-- A record passes: a digit-moment value is below `hb`, a `Φ`-moment value below `lb`. -/
def recOK (hb lb rec : ℕ) : Prop :=
  (rec / 2 ^ valueWidth c p % 2 ^ keyW c p / 2 ^ (keyW c p - keyBits p) = 1 → rec % 2 ^ valueWidth c p < hb) ∧
    (rec / 2 ^ valueWidth c p % 2 ^ keyW c p / 2 ^ (keyW c p - keyBits p) = 2 → rec % 2 ^ valueWidth c p < lb)

theorem digitMoment_nonneg (r j : ℕ) (y : Cells wt.I) : 0 ≤ digitMoment c p wt r j y :=
  Finset.sum_nonneg (fun _ _ => even_pow_nonneg _ _)

theorem phiMoment_nonneg (r : ℕ) (y : Cells wt.I) : 0 ≤ phiMoment c p wt r y :=
  Finset.sum_nonneg (fun _ _ => even_pow_nonneg _ _)

/-- **The strict tests eq:tests from the cell's records.** -/
theorem tests_iff (hs : Spec cT (header c) p) (w : List Bool) (hw : decodeWitness c p w = some wt) (i : ℕ) :
    (∀ rec ∈ blk c p wt i, recOK c p (p.hE ^ (2 * p.k)) (p.Lambda ^ (2 * p.k)) rec) ↔
      CellTests c p wt (cellOf wt.I i) := by
  constructor
  · intro h
    refine ⟨fun r j => ?_, fun r => ?_⟩
    · have hid : ReqId.digitMoment r.val j.val ∈ reqIds c p := by
        unfold reqIds
        simp only [List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range, List.mem_singleton]
        exact Or.inr ⟨r.val, r.isLt, Or.inl ⟨j.val, j.isLt, rfl⟩⟩
      have h1 := (h _ (cellRec_mem_blk c p wt i _ hid)).1 (by rw [rec_kind c p wt hs w hw i _ hid]; rfl)
      rw [rec_val c p wt hs w hw i _ hid] at h1
      simp only [reqValue] at h1
      have h0 := digitMoment_nonneg c p wt r.val j.val (cellOf wt.I i)
      have : ((digitMoment c p wt r.val j.val (cellOf wt.I i)).toNat : ℤ) < ((p.hE ^ (2 * p.k) : ℕ) : ℤ) := by
        exact_mod_cast h1
      rw [Int.toNat_of_nonneg h0] at this
      exact_mod_cast this
    · have hid : ReqId.phiMoment r.val ∈ reqIds c p := by
        unfold reqIds
        simp only [List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range, List.mem_singleton]
        exact Or.inr ⟨r.val, r.isLt, Or.inr rfl⟩
      have h1 := (h _ (cellRec_mem_blk c p wt i _ hid)).2 (by rw [rec_kind c p wt hs w hw i _ hid]; rfl)
      rw [rec_val c p wt hs w hw i _ hid] at h1
      simp only [reqValue] at h1
      have h0 := phiMoment_nonneg c p wt r.val (cellOf wt.I i)
      have : ((phiMoment c p wt r.val (cellOf wt.I i)).toNat : ℤ) < ((p.Lambda ^ (2 * p.k) : ℕ) : ℤ) := by
        exact_mod_cast h1
      rw [Int.toNat_of_nonneg h0] at this
      exact_mod_cast this
  · intro ht rec hrec
    obtain ⟨id, hid, rfl⟩ := mem_blk c p wt hrec
    unfold recOK
    rw [rec_kind c p wt hs w hw i id hid, rec_val c p wt hs w hw i id hid]
    cases id with
    | residue part q κ σ => exact ⟨fun h => absurd h (by simp [kindOf]), fun h => absurd h (by simp [kindOf])⟩
    | digitMoment r j =>
      obtain ⟨hr, hj⟩ := mem_reqIds_moment c p hid
      refine ⟨fun _ => ?_, fun h => absurd h (by simp [kindOf])⟩
      have h1 := ht.1 ⟨r, hr⟩ ⟨j, hj⟩
      have h0 := digitMoment_nonneg c p wt r j (cellOf wt.I i)
      simp only [reqValue]
      have : ((digitMoment c p wt r j (cellOf wt.I i)).toNat : ℤ) < ((p.hE ^ (2 * p.k) : ℕ) : ℤ) := by
        rw [Int.toNat_of_nonneg h0]; exact_mod_cast h1
      exact_mod_cast this
    | phiMoment r =>
      have hr := mem_reqIds_phi c p hid
      refine ⟨fun h => absurd h (by simp [kindOf]), fun _ => ?_⟩
      have h1 := ht.2 ⟨r, hr⟩
      have h0 := phiMoment_nonneg c p wt r (cellOf wt.I i)
      simp only [reqValue]
      have : ((phiMoment c p wt r (cellOf wt.I i)).toNat : ℤ) < ((p.Lambda ^ (2 * p.k) : ℕ) : ℤ) := by
        rw [Int.toNat_of_nonneg h0]; exact_mod_cast h1
      exact_mod_cast this

end Blocks

end NearCubicGates.Close.Cells
