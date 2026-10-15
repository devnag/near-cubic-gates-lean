import Proof.Gates.Expand.PolyTabVal
import Proof.Gates.TabMachine.CutM

set_option autoImplicit false

namespace NearCubicGates.Close.Expand.PolyTab

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicGates.Close.Tabulator NearCubicGates.Close.TabMachine
open NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Expand

variable (E : ExpandMachine)

/-- lem:exact's parameter bit bound after restriction. -/
def Bg (r : TabReq) : ℕ := r.B + Nat.clog 2 (r.n + 1)
/-- lem:exact's child bound. -/
def CB (r : TabReq) : ℕ := childBound r.s (Bg r)
theorem le_foldr_max (l : List ℕ) (x : ℕ) (hx : x ∈ l) : x ≤ l.foldr max 0 := by
  induction l with
  | nil => simp at hx
  | cons a l ih =>
    simp only [List.foldr_cons]
    rcases List.mem_cons.mp hx with rfl | hx
    · exact le_max_left _ _
    · exact le_trans (ih hx) (le_max_right _ _)

/-- A bound on the number of occurrences in a monomial: the number of variables. -/
def Dm (r : TabReq) : ℕ := r.V
/-- The largest bit length of a coefficient of the expansion (the machine measures it on the terms word). -/
def Cm (r : TabReq) : ℕ := ((E.expand ⟨r.V, r.F⟩).map fun t => natBitLength t.2.natAbs).foldr max 0
/-- The cut machine's word width parameter (computable from `n, k, s, B, V, G` and `Cm`; `G` so that gate indices
fit a word). -/
def Wk (r : TabReq) : ℕ :=
  (Dm r + 2) * (3 * r.B + 2 * r.n + 6 * r.s + r.k + 20 + Dm r * (r.s + 1)) + Cm E r + r.G
/-- The stacked field width. -/
def Wdk (r : TabReq) : ℕ := (r.s + 1) * (Wk E r + 1) - 1

theorem Wdk_succ (r : TabReq) : Wdk E r + 1 = (r.s + 1) * (Wk E r + 1) := by
  unfold Wdk; have : 1 ≤ (r.s + 1) * (Wk E r + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity); omega

theorem Wk_dm (r : TabReq) :
    (Dm r + 2) * (3 * r.B + 2 * r.n + 6 * r.s + r.k + 20 + Dm r * (r.s + 1)) ≤ Wk E r := by
  unfold Wk; omega

theorem Wk_ge0 (r : TabReq) : 3 * r.B + 2 * r.n + 6 * r.s + r.k + 20 + Dm r * (r.s + 1) ≤ Wk E r :=
  le_trans (Nat.le_mul_of_pos_left _ (by omega)) (Wk_dm E r)

theorem Wk_ge (r : TabReq) : r.B + r.k + r.s + 10 ≤ Wk E r := by have := Wk_ge0 E r; omega

theorem two_pow_ge (a : ℕ) : a + 1 ≤ 2 ^ a := Nat.lt_two_pow_self

/-- The occurrences of the encoding are the roles' gates split by the layout. -/
theorem mem_terms_occ (r : TabReq) (t : List Occ × ℤ) (ht : t ∈ (code (tabT E r)).terms) (o : Occ) (ho : o ∈ t.1) :
    ∃ v, o = occ (tabT E r) v := by
  simp only [code, List.mem_map] at ht
  obtain ⟨u, _, rfl⟩ := ht
  simp only [List.mem_reverse, List.mem_map] at ho
  obtain ⟨v, _, rfl⟩ := ho
  exact ⟨v, rfl⟩

theorem occ_inW_length (r : TabReq) (v : Fin r.V) : (occ (tabT E r) v).inW.length = r.k := by simp [occ]
theorem occ_outW_length (r : TabReq) (v : Fin r.V) : (occ (tabT E r) v).outW.length = r.s := by simp [occ]

theorem sum_natAbs_ofFn_le {m : ℕ} (f : Fin m → ℤ) (b : ℕ) (h : ∀ i, (f i).natAbs < b) :
    ((List.ofFn f).map Int.natAbs).sum ≤ m * b := by
  have : ∀ x ∈ (List.ofFn f).map Int.natAbs, x ≤ b := by
    intro x hx
    simp only [List.mem_map, List.mem_ofFn] at hx
    obtain ⟨_, ⟨i, rfl⟩, rfl⟩ := hx
    exact (h i).le
  have := List.sum_le_card_nsmul _ _ this
  simpa using this

theorem occ_inW_sum (r : TabReq) (v : Fin r.V) : ((occ (tabT E r) v).inW.map Int.natAbs).sum ≤ r.k * 2 ^ r.B := by
  unfold occ; exact sum_natAbs_ofFn_le _ _ (fun i => ((r.hB _).1 _))

theorem occ_outW_sum (r : TabReq) (v : Fin r.V) : totalL (occ (tabT E r) v).outW ≤ r.s * 2 ^ r.B := by
  unfold occ totalL; exact sum_natAbs_ofFn_le _ _ (fun i => ((r.hB _).1 _))

theorem occ_thr (r : TabReq) (v : Fin r.V) : (occ (tabT E r) v).thr.natAbs < 2 ^ r.B := (r.hB _).2

theorem pow_le_Wk (r : TabReq) (a : ℕ) (ha : a ≤ r.B + r.k + r.s + 10) : 2 ^ a ≤ 2 ^ Wk E r :=
  Nat.pow_le_pow_right (by norm_num) (ha.trans (Wk_ge E r))

/-- `StepOK.bound`. -/
theorem occ_bound (r : TabReq) (v : Fin r.V) :
    ((occ (tabT E r) v).inW.map Int.natAbs).sum + (occ (tabT E r) v).thr.natAbs + 1 < 2 ^ Wk E r := by
  have h1 := occ_inW_sum E r v
  have h2 := occ_thr E r v
  have h3 : (r.k + 2) * 2 ^ r.B ≤ 2 ^ (r.B + r.k + 2) := by
    rw [pow_add, pow_add, mul_comm]; have := two_pow_ge (r.k + 1)
    rw [show r.k + 2 = r.k + 1 + 1 by ring, pow_succ] at *; nlinarith [Nat.one_le_two_pow (n := r.B)]
  have h4 := pow_le_Wk E r (r.B + r.k + 2) (by omega)
  have : 1 ≤ 2 ^ r.B := Nat.one_le_two_pow
  nlinarith

/-- `StepOK.hB`. -/
theorem occ_hB (r : TabReq) (v : Fin r.V) : 4 * totalL (occ (tabT E r) v).outW + 2 * r.s + 4 ≤ 2 ^ Wk E r := by
  have h1 := occ_outW_sum E r v
  set X := 2 ^ r.B with hX
  have hX1 : 1 ≤ X := Nat.one_le_two_pow
  have h2 : 6 * r.s + 6 ≤ 2 ^ (r.s + 3) := by
    have : 2 ^ (r.s + 3) = 8 * 2 ^ r.s := by rw [pow_add]; ring
    have := two_pow_ge r.s; omega
  have h3 : (6 * r.s + 6) * X ≤ 2 ^ (r.B + r.s + 3) := by
    rw [show r.B + r.s + 3 = r.B + (r.s + 3) by ring, pow_add, mul_comm]
    exact Nat.mul_le_mul_left _ h2
  have h4 := pow_le_Wk E r (r.B + r.s + 3) (by omega)
  have e : (6 * r.s + 6) * X = 6 * (r.s * X) + 6 * X := by ring
  have h5 : r.s ≤ r.s * X := Nat.le_mul_of_pos_right _ hX1
  omega

/-- `StepOK.ht`. -/
theorem occ_ht (r : TabReq) (v : Fin r.V) (c : ℕ) :
    (rTarget (occ (tabT E r) v) c).natAbs + totalL (occ (tabT E r) v).outW < 2 ^ Wk E r := by
  have h1 := occ_outW_sum E r v
  have h2 := occ_thr E r v
  have h3 := occ_inW_sum E r v
  set X := 2 ^ r.B with hX
  have hX1 : 1 ≤ X := Nat.one_le_two_pow
  have h5 : (rTarget (occ (tabT E r) v) c).natAbs ≤ (occ (tabT E r) v).thr.natAbs +
      ((occ (tabT E r) v).inW.map Int.natAbs).sum + 1 := by
    unfold rTarget
    have := innerDot_bound (occ (tabT E r) v).inW c
    split_ifs <;> omega
  have h2' : r.k + r.s + 3 ≤ 2 ^ (r.k + r.s + 3) := (two_pow_ge _).trans' (by omega)
  have h6 : (r.k + r.s + 3) * X ≤ 2 ^ (r.B + r.k + r.s + 3) := by
    rw [show r.B + r.k + r.s + 3 = r.B + (r.k + r.s + 3) by ring, pow_add, mul_comm]
    exact Nat.mul_le_mul_left _ h2'
  have h4 := pow_le_Wk E r (r.B + r.k + r.s + 3) (by omega)
  have e : (r.k + r.s + 3) * X = r.k * X + r.s * X + 3 * X := by ring
  omega

theorem clog_le (x : ℕ) : Nat.clog 2 (x + 1) ≤ x := by
  rw [Nat.clog_le_iff_le_pow (by norm_num)]; exact Nat.lt_two_pow_self

theorem CB_lt (r : TabReq) : CB r < 2 ^ (2 * r.B + 2 * r.n + 4 * r.s + 10) := by
  unfold CB childBound Bg blockBits
  set bb := r.B + Nat.clog 2 (r.n + 1) + Nat.clog 2 (r.s + 1) + 1 with hbb
  have h1 : bb ≤ r.B + r.n + r.s + 1 := by have := clog_le r.n; have := clog_le r.s; omega
  have hs : r.s < 2 ^ r.s := Nat.lt_two_pow_self
  have hb : bb < 2 ^ bb := Nat.lt_two_pow_self
  have h2 : 2 * r.s * r.s * (r.B + Nat.clog 2 (r.n + 1) + Nat.clog 2 (r.s + 1) + 1) + r.s + 5 <
      2 ^ (2 * r.s + bb + 4) := by
    rw [← hbb]
    have e : 2 ^ (2 * r.s + bb + 4) = 16 * (2 ^ r.s * 2 ^ r.s * 2 ^ bb) := by rw [pow_add, pow_add, two_mul, pow_add]; ring
    have m1 : r.s * r.s * bb ≤ 2 ^ r.s * 2 ^ r.s * 2 ^ bb := Nat.mul_le_mul (Nat.mul_le_mul hs.le hs.le) hb.le
    have m2 : 1 ≤ 2 ^ r.s * 2 ^ r.s * 2 ^ bb := Nat.one_le_iff_ne_zero.mpr (by positivity)
    have m3 : r.s ≤ 2 ^ r.s * 2 ^ r.s * 2 ^ bb := le_trans hs.le (by
      calc 2 ^ r.s = 2 ^ r.s * 1 * 1 := by ring
        _ ≤ 2 ^ r.s * 2 ^ r.s * 2 ^ bb := by gcongr <;> exact Nat.one_le_two_pow)
    have e2 : 2 * r.s * r.s * bb = 2 * (r.s * r.s * bb) := by ring
    omega
  calc (2 * r.s * r.s * (r.B + Nat.clog 2 (r.n + 1) + Nat.clog 2 (r.s + 1) + 1) + r.s + 5) * 2 ^ bb
      < 2 ^ (2 * r.s + bb + 4) * 2 ^ bb := Nat.mul_lt_mul_of_pos_right h2 (Nat.two_pow_pos _)
    _ = 2 ^ (2 * r.s + bb + 4 + bb) := (pow_add 2 _ _).symm
    _ ≤ 2 ^ (2 * r.B + 2 * r.n + 4 * r.s + 10) := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem CB_lt_Wk (r : TabReq) : CB r < 2 ^ Wk E r :=
  lt_of_lt_of_le (CB_lt r) (Nat.pow_le_pow_right (by norm_num) (by have := Wk_ge0 E r; omega))

/-- `StepOK.fit`: the children's numbers fit `W`. -/
theorem occ_fit (r : TabReq) (v : Fin r.V) (c : ℕ) (hc : c < 2 ^ r.k) :
    ∀ kid ∈ (occ (tabT E r) v).kids c, ∀ y ∈ kid, y.natAbs ≤ CB r := by
  intro kid hkid y hy
  have e := occ_kids (tabT E r) ⟨c, hc⟩ v
  simp only at e
  rw [e] at hkid
  obtain ⟨eq, heq, rfl⟩ := List.mem_map.mp hkid
  have hp := (tabT E r).kids_params r.B r.hB _ v eq heq
  unfold eqF at hy
  rcases List.mem_append.mp hy with hy | hy
  · obtain ⟨t, rfl⟩ := List.mem_ofFn.mp hy; exact hp.1 _
  · simp at hy; subst hy; exact hp.2

theorem mem_tuples_mem {α : Type} : ∀ (Ls : List (List α)) (ls : List α), ls ∈ tuples Ls →
    ∀ l ∈ ls, ∃ L ∈ Ls, l ∈ L
  | [], ls, h, l, hl => by simp [tuples] at h; subst h; simp at hl
  | L :: Ls, ls, h, l, hl => by
      simp only [tuples, List.mem_flatMap, List.mem_map] at h
      obtain ⟨a, ha, t, ht, rfl⟩ := h
      rcases List.mem_cons.mp hl with rfl | hl
      · exact ⟨L, List.mem_cons_self, ha⟩
      · obtain ⟨L', hL', hl'⟩ := mem_tuples_mem Ls t ht l hl
        exact ⟨L', List.mem_cons_of_mem _ hL', hl'⟩

/-- A monomial's occurrences number at most the degree. -/
theorem terms_length (r : TabReq) (t : List Occ × ℤ) (ht : t ∈ (code (tabT E r)).terms) : t.1.length ≤ Dm r := by
  simp only [code, List.mem_map] at ht
  obtain ⟨u, _, rfl⟩ := ht
  simp only [List.length_reverse, List.length_map, Finset.length_sort, Dm]
  exact (Finset.card_le_univ _).trans (by simp)

theorem magL_le (r : TabReq) (c : ℕ) (hc : c < 2 ^ r.k) (t : List Occ × ℤ) (ht : t ∈ (code (tabT E r)).terms)
    (ls : List (List ℤ)) (hls : ls ∈ monoTuples c t.1) : magL ls ≤ Dm r * ((r.s + 1) * CB r) := by
  have hlen : ls.length = t.1.length := by
    have := mem_tuples_length _ _ hls; simpa using this
  have hall : ∀ l ∈ ls, (l.map Int.natAbs).sum ≤ (r.s + 1) * CB r := by
    intro l hl
    obtain ⟨L, hL, hlL⟩ := mem_tuples_mem _ _ hls l hl
    simp only [List.mem_map, List.mem_reverse] at hL
    obtain ⟨o, ho, rfl⟩ := hL
    obtain ⟨v, rfl⟩ := mem_terms_occ E r t ht o ho
    have hl1 : l.length = r.s + 1 := by rw [kids_length _ c l hlL, occ_outW_length]
    have hb := occ_fit E r v c hc l hlL
    have := List.sum_le_card_nsmul (l.map Int.natAbs) (CB r) (by
      intro x hx; obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx; exact hb y hy)
    simpa [hl1] using this
  unfold magL
  have := List.sum_le_card_nsmul (ls.map fun l => (l.map Int.natAbs).sum) ((r.s + 1) * CB r) (by
    intro x hx; obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hx; exact hall l hl)
  simp only [List.length_map, smul_eq_mul] at this
  have h2 := terms_length E r t ht
  calc _ ≤ ls.length * ((r.s + 1) * CB r) := this
    _ ≤ Dm r * ((r.s + 1) * CB r) := Nat.mul_le_mul_right _ (by omega)

theorem mul_succ_le_two_pow (x y a b : ℕ) (hx : x < 2 ^ a) (hy : y < 2 ^ b) : x * y + 1 ≤ 2 ^ (a + b) := by
  rw [pow_add]
  have : x * y ≤ (2 ^ a - 1) * (2 ^ b - 1) := Nat.mul_le_mul (by omega) (by omega)
  have h1 : 1 ≤ 2 ^ a := Nat.one_le_two_pow
  have h2 : 1 ≤ 2 ^ b := Nat.one_le_two_pow
  have e : (2 ^ a - 1) * (2 ^ b - 1) + 1 ≤ 2 ^ a * 2 ^ b := by
    zify [h1, h2]; nlinarith
  omega

/-- `MonoOK.bound`: the stacking base fits `Wd`. -/
theorem mono_bound (r : TabReq) (c : ℕ) (hc : c < 2 ^ r.k) (t : List Occ × ℤ) (ht : t ∈ (code (tabT E r)).terms) :
    ∀ ls ∈ monoTuples c t.1, (magL ls + 1) ^ (t.1.length + 1) < 2 ^ Wdk E r := by
  intro ls hls
  have h1 := magL_le E r c hc t ht ls hls
  have h2 := terms_length E r t ht
  set a := Dm r * (r.s + 1) with ha
  set b := 2 * r.B + 2 * r.n + 4 * r.s + 10 with hb
  have h3 : magL ls + 1 ≤ 2 ^ (a + b) := by
    have := mul_succ_le_two_pow (Dm r * (r.s + 1)) (CB r) a b Nat.lt_two_pow_self (CB_lt r)
    rw [mul_assoc] at this; omega
  have h4 : (magL ls + 1) ^ (t.1.length + 1) ≤ (2 ^ (a + b)) ^ (Dm r + 1) :=
    le_trans (Nat.pow_le_pow_left h3 _) (Nat.pow_le_pow_right (Nat.one_le_two_pow) (by omega))
  rw [← pow_mul] at h4
  refine lt_of_le_of_lt h4 (Nat.pow_lt_pow_right (by norm_num) ?_)
  have hW : (a + b) * (Dm r + 2) ≤ Wk E r := by
    refine le_trans ?_ (Wk_dm E r); rw [mul_comm]; exact Nat.mul_le_mul_left _ (by omega)
  have hWk : Wk E r ≤ Wdk E r := by have := Wdk_succ E r; nlinarith
  have h10 := Wk_ge E r
  rcases Nat.eq_zero_or_pos (a + b) with h0 | h0
  · rw [h0]; omega
  · have : (a + b) * (Dm r + 1) < (a + b) * (Dm r + 2) := Nat.mul_lt_mul_of_pos_left (by omega) h0
    omega

end NearCubicGates.Close.Expand.PolyTab
