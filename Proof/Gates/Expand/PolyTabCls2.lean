import Proof.Gates.Expand.PolyTabCls1

/-! # PolyTab cost classes: the head's word and list atoms -/

set_option autoImplicit false

namespace NearCubicGates.Close.Expand.PolyTab

open NearCubicWires NearCubicWires.RepairRepresentation NearCubicGates.Close.Tabulator NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.CounterMachine NearCubicGates.Close.TabMachine

variable (E : ExpandMachine)

theorem natWord_len (x : ℕ) : (natWord x).length = 2 * natBitLength x + 1 :=
  NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.natWord_length x

theorem flatMap_natWord_le (L : List ℕ) (b : ℕ) (h : ∀ x ∈ L, natBitLength x ≤ b) :
    (L.flatMap natWord).length ≤ L.length * (2 * b + 1) := by
  induction L with
  | nil => simp
  | cons x L ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons, natWord_len]
    have := h x (by simp)
    have := ih (fun y hy => h y (by simp [hy]))
    nlinarith

theorem sum_le_len_mul {α : Type} (L : List α) (f : α → ℕ) (b : ℕ) (h : ∀ x ∈ L, f x ≤ b) :
    (L.map f).sum ≤ L.length * b := by
  induction L with
  | nil => simp
  | cons x L ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have := h x (by simp); have := ih (fun y hy => h y (by simp [hy])); nlinarith

/-- Every field of the request word is below `2^(B + k + tabSz + 1)`. -/
theorem preN_lt (r : TabReq) (x : ℕ) (hx : x ∈ preN r) : x < 2 ^ (r.B + r.k + tabSz r + 1) := by
  have hT : ∀ y, y ≤ tabSz r → y < 2 ^ (r.B + r.k + tabSz r + 1) := fun y hy =>
    lt_of_le_of_lt hy (lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_right (by norm_num) (by omega)))
  have hB : ∀ y, y < 2 ^ r.B → y < 2 ^ (r.B + r.k + tabSz r + 1) := fun y hy =>
    lt_of_lt_of_le hy (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hn := le_tabSz_n r
  have hG := le_tabSz_G r
  unfold preN at hx
  simp only [List.mem_append] at hx
  rcases hx with (((((((((hA | hB') | hC) | hD) | hE) | hF) | hG') | hH) | hI) | hJ)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hA
    rcases hA with h | h | h | h | h <;> subst h
    · exact hT _ hn
    · exact hT _ (le_tabSz_k r)
    · exact hT _ (le_tabSz_s r)
    · exact hT _ (le_tabSz_B r)
    · exact hT _ hG
  · obtain ⟨g, hg1, hg⟩ := List.mem_flatMap.mp hB'
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hg1
    have hb := r.hB i
    simp only [gateN, List.mem_cons, List.mem_append] at hg
    rcases hg with h | hz | hz
    · subst h; exact hT _ hn
    · obtain ⟨z, hz1, hz2⟩ := List.mem_flatMap.mp hz
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hz1
      simp only [intN, List.mem_cons, List.not_mem_nil, or_false] at hz2
      rcases hz2 with h | h <;> subst h
      · split_ifs <;> exact hT _ (by have := tabSz_pos r; omega)
      · exact hB _ (hb.1 j)
    · simp only [intN, List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with h | h <;> subst h
      · split_ifs <;> exact hT _ (by have := tabSz_pos r; omega)
      · exact hB _ hb.2
  · simp only [List.mem_singleton] at hC; subst hC; exact hT _ (le_tabSz_k r)
  · obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hD
    exact hT _ (by have := (r.layout.symm (.inl j)).isLt; omega)
  · simp only [List.mem_singleton] at hE; subst hE; exact hT _ (le_tabSz_s r)
  · obtain ⟨t, rfl⟩ := List.mem_ofFn.mp hF
    exact hT _ (by have := (r.layout.symm (.inr t)).isLt; omega)
  · simp only [List.mem_singleton] at hG'; subst hG'
    exact lt_of_lt_of_le (Nat.pow_lt_pow_right (by norm_num) (show r.k < r.k + 1 by omega))
      (Nat.pow_le_pow_right (by norm_num) (by omega))
  · obtain ⟨c, rfl⟩ := List.mem_ofFn.mp hH
    split_ifs <;> exact hT _ (by have := tabSz_pos r; omega)
  · simp only [List.mem_singleton] at hI; subst hI; exact hT _ (le_tabSz_V r)
  · obtain ⟨ρ, hρ1, hρ⟩ := List.mem_flatMap.mp hJ
    obtain ⟨v, rfl⟩ := List.mem_ofFn.mp hρ1
    simp only [roleN, List.mem_cons, List.not_mem_nil, or_false] at hρ
    rcases hρ with h | h <;> subst h
    · exact hT _ (by have := (r.role v).gate.isLt; omega)
    · split_ifs <;> exact hT _ (by have := tabSz_pos r; omega)

theorem preN_nbl_le (r : TabReq) (x : ℕ) (hx : x ∈ preN r) : natBitLength x ≤ 3 * tabSz r + 2 := by
  have := nbl_le_of_lt x _ (preN_lt r x hx)
  have := le_tabSz_B r; have := le_tabSz_k r; omega

theorem lc_n : LCls 0 (fun r : TabReq => r.n) := lc_le_tabSz le_tabSz_n
theorem lc_k : LCls 0 (fun r : TabReq => r.k) := lc_le_tabSz le_tabSz_k
theorem lc_s : LCls 0 (fun r : TabReq => r.s) := lc_le_tabSz le_tabSz_s
theorem lc_B : LCls 0 (fun r : TabReq => r.B) := lc_le_tabSz le_tabSz_B
theorem lc_G : LCls 0 (fun r : TabReq => r.G) := lc_le_tabSz le_tabSz_G
theorem lc_V : LCls 0 (fun r : TabReq => r.V) := lc_le_tabSz le_tabSz_V
theorem lc_w : LCls 0 (fun r : TabReq => r.F.weight) := lc_le_tabSz le_tabSz_w
theorem lc_fw : LCls 0 (fun r : TabReq => (formulaWord ⟨r.V, r.F⟩).length) := lc_le_tabSz le_tabSz_fw

theorem lc_preN : LCls 1 (fun r => (preN r).length) := by
  refine lc_mono (f := fun r : TabReq => 5 + r.G * (2 * r.n + 3) + r.k + 1 + r.s + 1 + 2 ^ r.k + 1 + 1 + 2 * r.V) ?_
    (fun r => by rw [preN_length]; unfold pV pN ps pk; omega)
  have := lc_n; have := lc_k; have := lc_s; have := lc_G; have := lc_V; have := lc_two_pow_k
  lcs_to

theorem lc_nblmax : LCls 0 (fun r => ((preN r).map natBitLength).foldr max 0) := by
  refine lc_mono (f := fun r => 3 * tabSz r + 2) ?_ (fun r => foldr_max_le _ _ (fun x hx => by
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx; exact preN_nbl_le r y hy))
  have := lc_tabSz; lcs_to

theorem lc_tabWord : LCls 1 (fun r => (tabWord r).length) := by
  refine lc_mono (f := fun r => (preN r).length * (2 * (3 * tabSz r + 2) + 1) + tabSz r) ?_ (fun r => ?_)
  · have := lc_preN; have := lc_tabSz; lcs_to
  rw [tabWord_eq, List.length_append]
  have := flatMap_natWord_le (preN r) _ (preN_nbl_le r)
  have := le_tabSz_fw r
  omega

theorem lc_Lt : LCls 1 Lt := lc_tabWord

theorem lc_ts9 : LCls 1 (fun r => (ts9 E r).length) := by
  refine lc_mono (lc_P E) (fun r => by simp [ts9])

theorem coef_nbl (r : TabReq) (t : Finset (Fin r.V) × ℤ) (ht : t ∈ E.expand ⟨r.V, r.F⟩) :
    natBitLength t.2.natAbs ≤ r.F.weight + 2 := by
  have h1 : t.2.natAbs ≤ 2 ^ r.F.weight := tabT_coeff E r t ht
  have h2 : t.2.natAbs < 2 ^ (r.F.weight + 1) := by rw [pow_succ]; have := Nat.two_pow_pos r.F.weight; omega
  exact nbl_le_of_lt _ _ h2

theorem termsN_nbl_le (r : TabReq) (x : ℕ) (hx : x ∈ termsN (E.expand ⟨r.V, r.F⟩)) :
    natBitLength x ≤ r.V + r.F.weight + 3 := by
  simp only [termsN, List.mem_cons, List.mem_flatMap] at hx
  rcases hx with rfl | ⟨t, ht, hx⟩
  · have h1 := Q_length E r
    have h2 : (E.expand ⟨r.V, r.F⟩).length < 2 ^ (r.V + 1) := by
      rw [pow_succ]; have : (tabT E r).Q = E.expand ⟨r.V, r.F⟩ := rfl
      rw [this] at h1; have := Nat.two_pow_pos r.V; omega
    have := nbl_le_of_lt _ _ h2
    omega
  · simp only [monoN, List.mem_cons, List.mem_append, intN, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | hv | rfl | rfl
    · have := mvars_len t
      have := nbl_le_of_lt (((t.1.sort (· ≤ ·)).map Fin.val).length) r.V
        (lt_of_le_of_lt (by simpa [mvars] using this) Nat.lt_two_pow_self)
      omega
    · obtain ⟨v, _, rfl⟩ := List.mem_map.mp hv
      have := nbl_le_of_lt v.val r.V (lt_trans v.isLt Nat.lt_two_pow_self); omega
    · split_ifs <;> simp [natBitLength]
    · have := coef_nbl E r t ht; omega

theorem termsN_len (r : TabReq) : (termsN (E.expand ⟨r.V, r.F⟩)).length ≤ 1 + (E.expand ⟨r.V, r.F⟩).length * (r.V + 3) := by
  have h := sum_le_len_mul (E.expand ⟨r.V, r.F⟩) (fun t => (monoN t).length) (r.V + 3) (fun t _ => by
    simp only [monoN, List.length_cons, List.length_append, intN, List.length_map]
    have := mvars_len t; simp [mvars] at this; simp; omega)
  rw [termsN, List.length_cons, List.length_flatMap]
  omega

theorem lc_terms : LCls 1 (fun r => (termsWord (E.expand ⟨r.V, r.F⟩)).length) := by
  refine lc_mono (f := fun r => (1 + (E.expand ⟨r.V, r.F⟩).length * (r.V + 3)) * (2 * (r.V + r.F.weight + 3) + 1))
    ?_ (fun r => ?_)
  · have := lc_P E; have := lc_V; have := lc_w; lcs_to
  rw [termsWord_eq]
  have h1 := flatMap_natWord_le _ _ (termsN_nbl_le E r)
  have h2 := termsN_len E r
  calc ((termsN (E.expand ⟨r.V, r.F⟩)).flatMap natWord).length
      ≤ (termsN (E.expand ⟨r.V, r.F⟩)).length * (2 * (r.V + r.F.weight + 3) + 1) := h1
    _ ≤ (1 + (E.expand ⟨r.V, r.F⟩).length * (r.V + 3)) * (2 * (r.V + r.F.weight + 3) + 1) := by gcongr

theorem lc_lk : LCls 1 (ℓk E) := lc_terms E

theorem Cm_le' (r : TabReq) : Cm E r ≤ r.F.weight + 2 := by
  unfold Cm
  exact foldr_max_le _ _ (fun x hx => by
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx; exact coef_nbl E r t ht)

theorem lc_Wk : LCls 0 (Wk E) := by
  refine lc_mono (f := fun r : TabReq => (r.V + 2) * (3 * r.B + 2 * r.n + 6 * r.s + r.k + 20 + r.V * (r.s + 1)) +
      (r.F.weight + 2) + r.G) ?_ (fun r => by have := Cm_le' E r; unfold Wk Dm; omega)
  have := lc_V; have := lc_B; have := lc_n; have := lc_s; have := lc_k; have := lc_w; have := lc_G; lcs_to

theorem lc_Wdk : LCls 0 (Wdk E) := by
  refine lc_mono (f := fun r : TabReq => (r.s + 1) * (Wk E r + 1)) ?_ (fun r => by unfold Wdk; omega)
  have := lc_s; have := lc_Wk E; lcs_to

theorem lc_VTn : LCls 0 (fun r => (VTn E r).length) := by
  refine lc_mono (f := fun r : TabReq => r.V * (r.k + r.s + 2)) ?_ (fun r => by rw [VTn_length])
  have := lc_V; have := lc_k; have := lc_s; lcs_to

end NearCubicGates.Close.Expand.PolyTab
