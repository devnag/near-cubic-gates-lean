import Proof.Wire_3_5.PrimTC4Geo

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.PrimT.C4Geo
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.SupplierPipeline NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.CompilerMachine

/-! ## The pulled-back point, bit by bit -/

theorem pointList_getD (aL aR : ℕ) : ∀ (cs : List (Bool × Bool)) (kL kR i : ℕ) (h : i < cs.length),
    (Pool.pointList aL aR cs kL kR).getD i false =
      xor (if cs[i].1 then aL.testBit (kL + ((cs.take i).filter (fun c => c.1)).length)
        else aR.testBit (kR + ((cs.take i).filter (fun c => !c.1)).length)) cs[i].2
  | [], _, _, _, h => by simp at h
  | c :: cs, kL, kR, 0, _ => by
    obtain ⟨s, f⟩ := c
    cases s <;> simp [Pool.pointList]
  | c :: cs, kL, kR, i + 1, h => by
    obtain ⟨s, f⟩ := c
    have hi : i < cs.length := by simpa using h
    cases s
    · have ih := pointList_getD aL aR cs kL (kR + 1) i hi
      show (Pool.pointList aL aR cs kL (kR + 1)).getD i false = _
      rw [ih]
      simp only [List.getElem_cons_succ, List.take_succ_cons, List.filter_cons, Bool.not_false, if_true,
        Bool.false_eq_true, if_false, List.length_cons]
      have e : kR + 1 + (List.filter (fun c : Bool × Bool => !c.1) (List.take i cs)).length =
          kR + ((List.filter (fun c : Bool × Bool => !c.1) (List.take i cs)).length + 1) := by omega
      rw [e]
    · have ih := pointList_getD aL aR cs (kL + 1) kR i hi
      show (Pool.pointList aL aR cs (kL + 1) kR).getD i false = _
      rw [ih]
      simp only [List.getElem_cons_succ, List.take_succ_cons, List.filter_cons, Bool.not_true, if_true,
        Bool.false_eq_true, if_false, List.length_cons]
      have e : kL + 1 + (List.filter (fun c : Bool × Bool => c.1) (List.take i cs)).length =
          kL + ((List.filter (fun c : Bool × Bool => c.1) (List.take i cs)).length + 1) := by omega
      rw [e]

/-- A count below `x`. -/
def cnt (p : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | x + 1 => cnt p x + if p x then 1 else 0

theorem take_filter_length {n : ℕ} (g : Fin n → Bool × Bool) (p : Bool × Bool → Bool) :
    ∀ x, x ≤ n → (((List.ofFn g).take x).filter p).length =
      cnt (fun y => if h : y < n then p (g ⟨y, h⟩) else false) x
  | 0, _ => by simp [cnt]
  | x + 1, hx => by
    have ih := take_filter_length g p x (by omega)
    rw [List.take_add_one, List.filter_append, List.length_append, ih]
    have hx' : x < (List.ofFn g).length := by simp; omega
    rw [List.getElem?_eq_getElem hx']
    simp only [cnt, List.getElem_ofFn, dif_pos (show x < n by omega), Option.toList_some, List.filter_cons,
      List.filter_nil]
    split_ifs <;> simp

variable (P : StarParams)

/-- The left count below `x`: the left coordinates before `x` (`centerSide`). -/
def cntL (x : ℕ) : ℕ := min x (P.r / 2 * P.b) + (min x (P.r * P.b + hL P) - P.r * P.b)

theorem rb_eq : P.r * P.b = 2 * (P.r / 2 * P.b) := by
  have h := P.r_half_add
  calc P.r * P.b = (P.r / 2 + P.r / 2) * P.b := by rw [h]
    _ = 2 * (P.r / 2 * P.b) := by ring

theorem hL_le : P.r * P.b + hL P ≤ P.n := by
  have := P.r_mul_b_le; unfold hL; omega

theorem cnt_side : ∀ x, cnt (fun y => if h : y < P.n then P.centerSide ⟨y, h⟩ else false) x = cntL P x
  | 0 => by simp [cnt, cntL]
  | x + 1 => by
    rw [cnt, cnt_side x]
    have h1 := rb_eq P
    have h2 := hL_le P
    unfold cntL
    by_cases hx : x < P.n
    · rw [dif_pos hx]
      unfold StarParams.centerSide
      unfold hL at h2 ⊢
      by_cases hc : (x < P.r / 2 * P.b ∨ (P.r * P.b ≤ x ∧ x < P.r * P.b + (P.n - P.r * P.b + 1) / 2))
      · rw [decide_eq_true hc]; simp only [if_true]; omega
      · rw [decide_eq_false hc]; simp only [Bool.false_eq_true, if_false]; omega
    · rw [dif_neg hx]; simp only [Bool.false_eq_true, if_false]; unfold hL at h2 ⊢; omega

theorem side_getD (j : ℕ) (hj : j < P.n) : (side P).getD j false = P.centerSide ⟨j, hj⟩ := by
  unfold side
  rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_ofFn]

/-- **The pulled-back point, bit by bit**: a left coordinate `x` reads bit `cntL x` of `a_L`, a right one bit
`x − cntL x` of `a_R`, each xored with the flip's bit. -/
theorem pull_bit (f : List Bool) (aL aR : ℕ) (x : Fin P.n) :
    Pool.pullPoint (side P) f aL aR x =
      xor (if P.centerSide x then aL.testBit (cntL P x) else aR.testBit (x.val - cntL P x)) (f.getD x false) := by
  unfold Pool.pullPoint
  have hx : x.val < (List.ofFn fun j : Fin P.n => ((side P).getD j false, f.getD j false)).length := by simp
  rw [pointList_getD aL aR _ 0 0 x.val hx]
  simp only [List.getElem_ofFn, Nat.zero_add]
  have hs : (side P).getD x.val false = P.centerSide x := side_getD P x.val x.isLt
  rw [hs]
  have hT := take_filter_length (fun j : Fin P.n => ((side P).getD j false, f.getD j false)) (fun c => c.1) x.val
    (le_of_lt x.isLt)
  have hF := take_filter_length (fun j : Fin P.n => ((side P).getD j false, f.getD j false)) (fun c => !c.1) x.val
    (le_of_lt x.isLt)
  have hsum := List.length_eq_length_filter_add
    (l := (List.ofFn fun j : Fin P.n => ((side P).getD j false, f.getD j false)).take x.val) (fun c : Bool × Bool => c.1)
  have hlen : ((List.ofFn fun j : Fin P.n => ((side P).getD j false, f.getD j false)).take x.val).length = x.val := by
    simp
    all_goals omega
  have hc : cnt (fun y => if h : y < P.n then ((fun j : Fin P.n => ((side P).getD j false, f.getD j false)) ⟨y, h⟩).1
      else false) x.val = cntL P x.val := by
    rw [← cnt_side P x.val]
    congr 1
    funext y
    by_cases hy : y < P.n
    · rw [dif_pos hy, dif_pos hy]; exact side_getD P y hy
    · rw [dif_neg hy, dif_neg hy]
  rw [hc] at hT
  cases hcs : P.centerSide x
  · simp only [Bool.false_eq_true, if_false]
    congr 2
    all_goals omega
  · simp only [if_true]
    congr 2
    all_goals omega

/-! ## XOR over a range, and the bits of `φ` -/

/-- The XOR of `f 0, …, f (N−1)`. -/
def xr (f : ℕ → Bool) : ℕ → Bool
  | 0 => false
  | N + 1 => xor (xr f N) (f N)

theorem xr_congr (f g : ℕ → Bool) : ∀ N, (∀ j < N, f j = g j) → xr f N = xr g N
  | 0, _ => rfl
  | N + 1, h => by
    simp only [xr]
    rw [xr_congr f g N (fun j hj => h j (by omega)), h N (by omega)]

theorem xr_zero (f : ℕ → Bool) : ∀ N, (∀ j < N, f j = false) → xr f N = false
  | 0, _ => rfl
  | N + 1, h => by
    simp only [xr]
    rw [xr_zero f N (fun j hj => h j (by omega)), h N (by omega)]
    rfl

/-- A window: outside `[lo, lo + len)` every term is `false`. -/
theorem xr_window (f : ℕ → Bool) (lo len : ℕ) :
    ∀ N, lo + len ≤ N → (∀ j < N, (j < lo ∨ lo + len ≤ j) → f j = false) →
      xr f N = xr (fun m => f (lo + m)) len := by
  intro N hN hf
  have key : ∀ M, M ≤ N → xr f M = xr (fun m => f (lo + m)) (min (M - lo) len) := by
    intro M
    induction M with
    | zero => intro _; simp [xr]
    | succ M ih =>
      intro hM
      simp only [xr]
      rw [ih (by omega)]
      by_cases h1 : M < lo
      · rw [hf M (by omega) (Or.inl h1)]
        have e : min (M + 1 - lo) len = min (M - lo) len := by omega
        rw [e]; simp
      · by_cases h2 : lo + len ≤ M
        · rw [hf M (by omega) (Or.inr h2)]
          have e : min (M + 1 - lo) len = min (M - lo) len := by omega
          rw [e]; simp
        · have e : min (M + 1 - lo) len = min (M - lo) len + 1 := by omega
          rw [e]
          simp only [xr]
          congr 2
          omega
  rw [key N le_rfl]
  congr 1
  omega

theorem xr_single (f : ℕ → Bool) (j0 N : ℕ) (hj0 : j0 < N) (hf : ∀ j < N, j ≠ j0 → f j = false) :
    xr f N = f j0 := by
  rw [xr_window f j0 1 N (by omega) (fun j hj h => hf j hj (by omega))]
  simp [xr]

theorem testBit_bitsValue : ∀ (bs : List Bool) (p : ℕ), (CanonicalBinary.bitsValue bs).testBit p = bs.getD p false
  | [], p => by simp [CanonicalBinary.bitsValue]
  | b :: bs, p => by
    have e : CanonicalBinary.bitsValue (b :: bs) = Nat.bit b (CanonicalBinary.bitsValue bs) := by
      show b.toNat + 2 * CanonicalBinary.bitsValue bs = _
      cases b <;> simp [Nat.bit] <;> ring
    rw [e]
    cases p with
    | zero => simp [Nat.testBit_bit_zero]
    | succ p => rw [Nat.testBit_bit_succ, testBit_bitsValue bs p]; simp

theorem foldl_xor_testBit (z p : ℕ) : ∀ (l : List (ℕ × ℕ)) (acc : ℕ),
    (l.foldl (fun acc cj => if z.testBit cj.2 then acc ^^^ cj.1 else acc) acc).testBit p =
      xor (acc.testBit p) (l.foldr (fun cj b => xor (z.testBit cj.2 && cj.1.testBit p) b) false)
  | [], acc => by simp
  | cj :: l, acc => by
    rw [List.foldl_cons, foldl_xor_testBit z p l, List.foldr_cons]
    split_ifs with h
    · rw [Nat.testBit_xor, h]; simp [Bool.xor_assoc]
    · simp [h]

theorem foldr_zipIdx (z p : ℕ) : ∀ (cols : List ℕ) (k : ℕ),
    (cols.zipIdx k).foldr (fun cj b => xor (z.testBit cj.2 && cj.1.testBit p) b) false =
      xr (fun j => z.testBit (k + j) && (cols.getD j 0).testBit p) cols.length
  | [], k => by simp [xr]
  | c :: cols, k => by
    rw [List.zipIdx_cons, List.foldr_cons, foldr_zipIdx z p cols (k + 1)]
    have key : ∀ N (g : ℕ → Bool), xr g (N + 1) = xor (g 0) (xr (fun j => g (j + 1)) N) := by
      intro N g
      induction N with
      | zero => simp [xr]
      | succ N ih => simp only [xr] at ih ⊢; rw [ih]; simp [Bool.xor_assoc]
    rw [List.length_cons, key]
    simp only [Nat.add_zero, List.getD_cons_zero, List.getD_cons_succ]
    congr 1
    apply xr_congr
    intro j _
    congr 2
    omega

/-- **The bits of `φ`**: bit `p` of `value cols z` is the XOR of the columns' bits `p` selected by `z`. -/
theorem value_testBit (cols : List ℕ) (z p : ℕ) :
    (MatrixScorePhi.value cols z).testBit p = xr (fun j => z.testBit j && (cols.getD j 0).testBit p) cols.length := by
  unfold MatrixScorePhi.value
  rw [foldl_xor_testBit, Nat.zero_testBit, Bool.false_xor]
  have := foldr_zipIdx z p cols 0
  simp only [Nat.zero_add] at this
  exact this

variable (P : StarParams)

theorem cols_length : (cols P).length = dRow P := by simp [cols]

theorem cols_getD (j : ℕ) (hj : j < dRow P) : (cols P).getD j 0 = CanonicalBinary.bitsValue (colBits P j) := by
  unfold cols
  rw [List.getD_eq_getElem _ _ (by simpa using hj)]
  simp

theorem colBits_getD (j p : ℕ) : (colBits P j).getD p false = (decide (p < width P) && colBit P j p) := by
  unfold colBits
  by_cases hp : p < width P
  · rw [List.getD_eq_getElem _ _ (by simpa using hp)]; simp [hp]
  · rw [List.getD_eq_default _ _ (by simp; omega)]; simp [hp]

/-- The bits of `φ z` through the columns' bit function. -/
theorem phi_testBit (z p : ℕ) : (MatrixScorePhi.value (cols P) z).testBit p =
    xr (fun j => z.testBit j && (decide (p < width P) && colBit P j p)) (dRow P) := by
  rw [value_testBit, cols_length]
  apply xr_congr
  intro j hj
  rw [cols_getD P j hj, testBit_bitsValue, colBits_getD]

/-! ## The block code's data positions -/

theorem two_le_s : 2 ≤ P.s := by
  unfold StarParams.s
  have h4 : 4 ≤ P.n / P.r := (Nat.le_div_iff_mul_le P.r_pos).mpr (by have := P.four_r_le_n; omega)
  exact Nat.le_log_of_pow_le (by norm_num) (by omega)

theorem s_add_two_le : P.s + 2 ≤ 2 ^ P.s := by
  have h2 := two_le_s P
  have key : ∀ t, 2 ≤ t → t + 2 ≤ 2 ^ t := by
    intro t ht
    induction t with
    | zero => omega
    | succ t ih =>
      rcases Nat.lt_or_ge t 2 with h | h
      · interval_cases t <;> simp_all
      · have := ih h; rw [pow_succ]; omega
  exact key P.s h2

theorem dB_pos : 1 ≤ dB P := by
  unfold dB; have := s_add_two_le P; have := P.b_succ; omega

theorem isPar_iff (i : ℕ) : isPar P i = true ↔ ∃ t < P.s, i + 1 = 2 ^ t := by
  unfold isPar
  simp [List.any_eq_true]

theorem par_length_le : ((List.range P.b).filter fun i => isPar P i).length ≤ P.s := by
  have hsub : ((List.range P.b).filter fun i => isPar P i) ⊆ (List.range P.s).map fun t => 2 ^ t - 1 := by
    intro i hi
    rw [List.mem_filter] at hi
    obtain ⟨t, ht, he⟩ := (isPar_iff P i).mp hi.2
    exact List.mem_map.mpr ⟨t, List.mem_range.mpr ht, by omega⟩
  have hnd : ((List.range P.b).filter fun i => isPar P i).Nodup := (List.nodup_range).filter _
  have := (hnd.subperm hsub).length_le
  simpa using this

theorem dataPos_length : dB P ≤ (dataPos P).length := by
  have h := List.length_eq_length_filter_add (l := List.range P.b) (fun i => isPar P i)
  have h2 := par_length_le P
  unfold dataPos dB
  simp only [List.length_range] at h
  omega

theorem dpos_mem (m : ℕ) (hm : m < dB P) : dpos P m < P.b ∧ isPar P (dpos P m) = false := by
  have hl := dataPos_length P
  unfold dpos
  rw [List.getD_eq_getElem _ _ (by omega)]
  have hmem0 := List.getElem_mem (show m < (dataPos P).length by omega)
  have hmem : (dataPos P)[m] ∈ (List.range P.b).filter (fun i => !isPar P i) := hmem0
  rw [List.mem_filter, List.mem_range] at hmem
  exact ⟨hmem.1, by simpa using hmem.2⟩

theorem dpos_inj (m m' : ℕ) (hm : m < dB P) (hm' : m' < dB P) (h : dpos P m = dpos P m') : m = m' := by
  have hl := dataPos_length P
  have hnd : (dataPos P).Nodup := (List.nodup_range).filter _
  unfold dpos at h
  rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)] at h
  exact (hnd.getElem_inj_iff).mp h

theorem not_par_pow (i : ℕ) (hi : i < P.b) (hp : isPar P i = false) (t : ℕ) : i + 1 ≠ 2 ^ t := by
  intro h
  have hb := P.b_succ
  rcases Nat.lt_or_ge t P.s with ht | ht
  · have : isPar P i = true := (isPar_iff P i).mpr ⟨t, ht, h⟩
    rw [hp] at this; exact absurd this (by decide)
  · have : 2 ^ P.s ≤ 2 ^ t := Nat.pow_le_pow_right (by norm_num) ht
    omega

/-- The basis vectors at the data positions: `cwBit (dpos m') (dpos m) = [m' = m]`. -/
theorem cwBit_data (m m' : ℕ) (hm : m < dB P) (hm' : m' < dB P) :
    cwBit P (dpos P m') (dpos P m) = decide (m' = m) := by
  have ⟨h1, h2⟩ := dpos_mem P m hm
  unfold cwBit
  have hpar : ((List.range P.s).any fun t => (dpos P m' + 1).testBit t && dpos P m + 1 == 2 ^ t) = false := by
    rw [List.any_eq_false]
    intro t _
    have := not_par_pow P (dpos P m) h1 h2 t
    simp [this]
  rw [hpar, Bool.or_false]
  by_cases he : m' = m
  · subst he; simp
  · have : dpos P m ≠ dpos P m' := fun h => he (dpos_inj P m m' hm hm' h).symm
    simp [this, he]

def encB (zb : ℕ → Bool) (i : ℕ) : Bool := xr (fun m => zb m && cwBit P (dpos P m) i) (dB P)

/-- The encoding reads its bits back at the data positions. -/
theorem encB_data (zb : ℕ → Bool) (m : ℕ) (hm : m < dB P) : encB P zb (dpos P m) = zb m := by
  unfold encB
  rw [xr_single _ m (dB P) hm (fun j hj hne => by rw [cwBit_data P m j hm hj]; simp [hne])]
  rw [cwBit_data P m m hm hm]; simp

/-! ## The bits of `φ` on the two parts of a half -/

theorem phi_block (z p : ℕ) (hp : p < P.r / 2 * P.b) :
    (MatrixScorePhi.value (cols P) z).testBit p = encB P (fun m => z.testBit (p / P.b * dB P + m)) (p % P.b) := by
  have hd := dB_pos P
  have hbp := P.b_pos
  have hq : p / P.b < P.r / 2 := (Nat.div_lt_iff_lt_mul hbp).mpr hp
  have hwin : p / P.b * dB P + dB P ≤ P.r / 2 * dB P := by
    have := Nat.mul_le_mul_right (dB P) (show p / P.b + 1 ≤ P.r / 2 by omega); rw [Nat.add_mul, Nat.one_mul] at this
    exact this
  have hdrow : P.r / 2 * dB P ≤ dRow P := by unfold dRow StarParams.leftCenterBits dB; omega
  have hwidth : p < width P := by unfold width; omega
  rw [phi_testBit, xr_window _ (p / P.b * dB P) (dB P) (dRow P) (by omega)]
  · unfold encB
    apply xr_congr
    intro m hm
    have hj : p / P.b * dB P + m < P.r / 2 * dB P := by omega
    have hdiv : (p / P.b * dB P + m) / dB P = p / P.b := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hm, Nat.zero_add]
    have hmod : (p / P.b * dB P + m) % dB P = m := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hm]
    unfold colBit
    rw [if_pos hj, hdiv, hmod]
    simp [hwidth, hp]
  · intro j _ hj
    unfold colBit
    split_ifs with h1
    · have hne : (p / P.b == j / dB P) = false := by
        rcases hj with hj | hj
        · have : j / dB P < p / P.b := (Nat.div_lt_iff_lt_mul (by omega)).mpr hj
          simp; omega
        · have : p / P.b + 1 ≤ j / dB P := (Nat.le_div_iff_mul_le (by omega)).mpr (by rw [Nat.add_mul, Nat.one_mul]; omega)
          simp; omega
      simp [hne]
    · have : (p == P.r / 2 * P.b + (j - P.r / 2 * dB P)) = false := by simp; omega
      simp [this]

theorem phi_free (z p : ℕ) (hp1 : P.r / 2 * P.b ≤ p) (hp2 : p < width P) :
    (MatrixScorePhi.value (cols P) z).testBit p = z.testBit (P.r / 2 * dB P + (p - P.r / 2 * P.b)) := by
  have hdrow : dRow P = P.r / 2 * dB P + hL P := by unfold dRow StarParams.leftCenterBits dB hL; rfl
  have hw : width P = P.r / 2 * P.b + hL P := rfl
  rw [phi_testBit, xr_single _ (P.r / 2 * dB P + (p - P.r / 2 * P.b)) (dRow P) (by omega)]
  · unfold colBit
    rw [if_neg (by omega)]
    simp [hp2]
    all_goals (intro _; omega)
  · intro j _ hne
    unfold colBit
    split_ifs with h1
    · have : decide (p < P.r / 2 * P.b) = false := by simp; omega
      simp [this]
    · have : (p == P.r / 2 * P.b + (j - P.r / 2 * dB P)) = false := by simp; omega
      simp [this]

/-! ## The center at a table position, bit by bit -/

/-- **The center bits of table position `(row, col)`** (before the offset): the left blocks encode `row`'s code bits,
the right blocks `col`'s, then `row`'s and `col`'s free bits on the unblocked coordinates. -/
def ctrBit (row col x : ℕ) : Bool :=
  if x < P.r / 2 * P.b then encB P (fun m => row.testBit (x / P.b * dB P + m)) (x % P.b)
  else if x < P.r * P.b then
    encB P (fun m => col.testBit ((x - P.r / 2 * P.b) / P.b * dB P + m)) ((x - P.r / 2 * P.b) % P.b)
  else if x < P.r * P.b + hL P then row.testBit (P.r / 2 * dB P + (x - P.r * P.b))
  else col.testBit (P.r / 2 * dB P + (x - P.r * P.b - hL P))

variable (σ : P.Translation)

theorem ofFn_getD {n : ℕ} (g : Fin n → Bool) (x : Fin n) : (List.ofFn g).getD x false = g x := by
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]

theorem centerAt_bit (row col : ℕ) (x : Fin P.n) :
    centerAt P σ row col x = xor (ctrBit P row col x) (offset P σ x) := by
  unfold centerAt
  rw [pull_bit, ofFn_getD]
  congr 1
  have h1 := rb_eq P
  have h2 := hL_le P
  have hxn := x.isLt
  unfold ctrBit
  cases hcs : P.centerSide x
  · have hc : ¬ (x.val < P.r / 2 * P.b ∨ (P.r * P.b ≤ x.val ∧ x.val < P.r * P.b + hL P)) := by
      unfold StarParams.centerSide at hcs; unfold hL; simpa using hcs
    simp only [Bool.false_eq_true, if_false]
    rw [if_neg (by omega)]
    by_cases hx : x.val < P.r * P.b
    · rw [if_pos hx]
      have e : x.val - cntL P x.val = x.val - P.r / 2 * P.b := by unfold cntL; omega
      rw [e, phi_block P col _ (by omega)]
    · rw [if_neg hx, if_neg (by omega)]
      have e : x.val - cntL P x.val = x.val - P.r / 2 * P.b - hL P := by unfold cntL; omega
      have hw : width P = P.r / 2 * P.b + hL P := rfl
      rw [e, phi_free P col _ (by unfold hL at *; omega) (by unfold hL at *; omega)]
      congr 2
      omega
  · have hc : x.val < P.r / 2 * P.b ∨ (P.r * P.b ≤ x.val ∧ x.val < P.r * P.b + hL P) := by
      unfold StarParams.centerSide at hcs; unfold hL; simpa using hcs
    simp only [if_true]
    by_cases hx : x.val < P.r / 2 * P.b
    · rw [if_pos hx]
      have e : cntL P x.val = x.val := by unfold cntL; omega
      rw [e, phi_block P row _ hx]
    · rw [if_neg hx, if_neg (by omega), if_pos (by omega)]
      have e : cntL P x.val = P.r / 2 * P.b + (x.val - P.r * P.b) := by unfold cntL; omega
      have hw : width P = P.r / 2 * P.b + hL P := rfl
      rw [e, phi_free P row _ (by omega) (by omega)]
      congr 2
      omega

theorem bc_val (j : Fin P.r) (i : Fin P.b) : (P.blockCoord j i).val = j.val * P.b + i.val := rfl

theorem blockCoord_inj (j j' : Fin P.r) (i i' : Fin P.b) (h : P.blockCoord j i = P.blockCoord j' i') :
    j = j' ∧ i = i' := by
  have hv := congrArg Fin.val h
  rw [bc_val P, bc_val P] at hv
  have hb := P.b_pos
  have hi := i.isLt; have hi' := i'.isLt
  have hj : j.val = j'.val := by
    have e1 : (j.val * P.b + i.val) / P.b = j.val := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hb, Nat.div_eq_of_lt hi, Nat.zero_add]
    have e2 : (j'.val * P.b + i'.val) / P.b = j'.val := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hb, Nat.div_eq_of_lt hi', Nat.zero_add]
    rw [← e1, ← e2, hv]
  refine ⟨Fin.ext hj, Fin.ext ?_⟩
  rw [hj] at hv; omega

theorem offset_block (j : Fin P.r) (i : Fin P.b) : offset P σ (P.blockCoord j i) = offBlock P σ j i := by
  unfold offset
  by_cases h : offBlock P σ j i = true
  · rw [h]; exact decide_eq_true ⟨j, i, rfl, h⟩
  · rw [Bool.not_eq_true] at h; rw [h]
    apply decide_eq_false
    rintro ⟨j', i', he, h'⟩
    obtain ⟨rfl, rfl⟩ := blockCoord_inj P j' j i' i he
    rw [h] at h'; exact absurd h' (by decide)

theorem offset_free (x : Fin P.n) (hx : P.r * P.b ≤ x.val) : offset P σ x = false := by
  unfold offset
  apply decide_eq_false
  rintro ⟨j, i, he, _⟩
  have hv := congrArg Fin.val he
  rw [bc_val P] at hv
  have hj := j.isLt; have hi := i.isLt
  have : j.val * P.b + i.val < P.r * P.b := by
    calc j.val * P.b + i.val < (j.val + 1) * P.b := by rw [Nat.add_mul, Nat.one_mul]; omega
      _ ≤ P.r * P.b := Nat.mul_le_mul_right _ hj
  omega

theorem column_apply (q : Fin P.b) (t : Fin P.s) :
    P.column q t = if (q.val + 1).testBit t.val then 1 else 0 := by
  apply Fin.ext
  have hv : (P.column q t).val = (q.val + 1) / 2 ^ t.val % 2 := by
    unfold StarParams.column
    rw [finFunctionFinEquiv_symm_apply_val]
  rw [hv, Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one ((q.val + 1) / 2 ^ t.val) with h | h <;> simp [h]

theorem cw_term (i : ℕ) (hi : i < P.b) (hp : isPar P i = false) (q : Fin P.b) (t0 : Fin P.s) :
    (if cwBit P i q then P.column q t0 else 0) =
      (if q.val = i then P.column q t0 else 0) +
        (if q.val + 1 = 2 ^ t0.val ∧ (i + 1).testBit t0.val = true then 1 else 0) := by
  have hnp := not_par_pow P i hi hp
  unfold cwBit
  by_cases hq : q.val = i
  · have h2 : ¬ (q.val + 1 = 2 ^ t0.val ∧ (i + 1).testBit t0.val = true) := fun h => hnp t0.val (hq ▸ h.1)
    have h1 : (q.val == i) = true := by simp [hq]
    rw [h1, Bool.true_or, if_pos rfl, if_pos hq, if_neg h2, add_zero]
  · have h1 : (q.val == i) = false := by simp [hq]
    rw [h1, Bool.false_or, if_neg hq, zero_add]
    by_cases hex : ∃ t < P.s, (i + 1).testBit t = true ∧ q.val + 1 = 2 ^ t
    · obtain ⟨t, ht, hbit, hqt⟩ := hex
      have hany : ((List.range P.s).any fun t => (i + 1).testBit t && q.val + 1 == 2 ^ t) = true := by
        rw [List.any_eq_true]; exact ⟨t, List.mem_range.mpr ht, by simp [hbit, hqt]⟩
      rw [if_pos hany, column_apply, hqt, Nat.testBit_two_pow]
      by_cases htt : t = t0.val
      · subst htt; simp [hbit]
      · have : ¬ (2 ^ t = 2 ^ t0.val ∧ (i + 1).testBit t0.val = true) := by
          rintro ⟨he, _⟩; exact htt (Nat.pow_right_injective (le_refl 2) he)
        rw [if_neg this]; simp [htt]
    · have hany : ((List.range P.s).any fun t => (i + 1).testBit t && q.val + 1 == 2 ^ t) = false := by
        rw [List.any_eq_false]
        intro t ht h
        apply hex
        simp at h
        exact ⟨t, List.mem_range.mp ht, h.1, h.2⟩
      have : ¬ (q.val + 1 = 2 ^ t0.val ∧ (i + 1).testBit t0.val = true) := by
        rintro ⟨h1, h2⟩; exact hex ⟨t0.val, t0.isLt, h2, h1⟩
      rw [if_neg (by rw [hany]; decide), if_neg this]

theorem syndrome_cw (i : ℕ) (hi : i < P.b) (hp : isPar P i = false) : P.syndrome (fun q => cwBit P i q) = 0 := by
  funext t0
  unfold StarParams.syndrome
  rw [Finset.sum_apply]
  simp only [ite_apply, Pi.zero_apply]
  rw [Finset.sum_congr rfl (fun q _ => cw_term P i hi hp q t0), Finset.sum_add_distrib]
  have hs1 : (∑ q : Fin P.b, if q.val = i then P.column q t0 else 0) = P.column ⟨i, hi⟩ t0 := by
    rw [Finset.sum_eq_single ⟨i, hi⟩]
    · simp
    · intro q _ hq; rw [if_neg (fun h => hq (Fin.ext h))]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hlt : 2 ^ t0.val - 1 < P.b := by
    have := P.b_succ
    have : 2 ^ t0.val < 2 ^ P.s := Nat.pow_lt_pow_right (by norm_num) t0.isLt
    have := Nat.one_le_two_pow (n := t0.val)
    omega
  have hs2 : (∑ q : Fin P.b, if q.val + 1 = 2 ^ t0.val ∧ (i + 1).testBit t0.val = true then (1 : Fin 2) else 0) =
      if (i + 1).testBit t0.val then 1 else 0 := by
    rw [Finset.sum_eq_single ⟨2 ^ t0.val - 1, hlt⟩]
    · have := Nat.one_le_two_pow (n := t0.val)
      by_cases hb : (i + 1).testBit t0.val = true
      · rw [if_pos ⟨by simp; omega, hb⟩, if_pos hb]
      · rw [if_neg (fun h => hb h.2), if_neg hb]
    · intro q _ hq
      rw [if_neg]
      rintro ⟨h1, _⟩
      exact hq (Fin.ext (by simp; omega))
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [hs1, hs2, column_apply]
  exact fin2_add_self _

theorem syndrome_false : P.syndrome (fun _ => false) = 0 := by
  unfold StarParams.syndrome; simp

/-- **Every encoding is a codeword**: `H·encB zb = 0`. -/
theorem syndrome_encB (zb : ℕ → Bool) : P.syndrome (fun q : Fin P.b => encB P zb q) = 0 := by
  have key : ∀ N, N ≤ dB P → P.syndrome (fun q : Fin P.b => xr (fun m => zb m && cwBit P (dpos P m) q) N) = 0 := by
    intro N
    induction N with
    | zero => intro _; exact syndrome_false P
    | succ N ih =>
      intro hN
      have e : (fun q : Fin P.b => xr (fun m => zb m && cwBit P (dpos P m) q) (N + 1)) =
          fun q : Fin P.b => xor (xr (fun m => zb m && cwBit P (dpos P m) q) N) (zb N && cwBit P (dpos P N) q) := rfl
      rw [e, P.syndrome_xor, ih (by omega)]
      obtain ⟨h1, h2⟩ := dpos_mem P N (by omega)
      cases hz : zb N
      · simp only [Bool.false_and]; rw [syndrome_false]; simp
      · simp only [Bool.true_and]; rw [syndrome_cw P _ h1 h2]; simp
  exact key (dB P) le_rfl

theorem syndrome_offBlock (j : Fin P.r) : P.syndrome (offBlock P σ j) = σ j := by
  have h := P.syndrome_errorOf (σ j) (fun _ => false)
  simp only [Bool.false_xor] at h
  exact h

/-! ## V1: every table position is a cell center -/

theorem blockBits_centerAt (row col : ℕ) (j : Fin P.r) : ∃ zb : ℕ → Bool,
    P.blockBits (centerAt P σ row col) j = fun i : Fin P.b => xor (encB P zb i) (offBlock P σ j i) := by
  have hb := P.b_pos
  have h1 := rb_eq P
  by_cases hj : j.val < P.r / 2
  · refine ⟨fun m => row.testBit (j.val * dB P + m), ?_⟩
    funext i
    unfold StarParams.blockBits
    rw [centerAt_bit, offset_block]
    congr 1
    have hx : (P.blockCoord j i).val < P.r / 2 * P.b := by
      rw [bc_val]
      calc j.val * P.b + i.val < (j.val + 1) * P.b := by rw [Nat.add_mul, Nat.one_mul]; omega
        _ ≤ P.r / 2 * P.b := Nat.mul_le_mul_right _ hj
    unfold ctrBit
    rw [if_pos hx, bc_val]
    have hd : (j.val * P.b + i.val) / P.b = j.val := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hb, Nat.div_eq_of_lt i.isLt, Nat.zero_add]
    have hm : (j.val * P.b + i.val) % P.b = i.val := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt i.isLt]
    rw [hd, hm]
  · refine ⟨fun m => col.testBit ((j.val - P.r / 2) * dB P + m), ?_⟩
    funext i
    unfold StarParams.blockBits
    rw [centerAt_bit, offset_block]
    congr 1
    have hjr := j.isLt
    have hx1 : ¬ (P.blockCoord j i).val < P.r / 2 * P.b := by
      rw [bc_val]
      have : P.r / 2 * P.b ≤ j.val * P.b := Nat.mul_le_mul_right _ (by omega)
      omega
    have hx2 : (P.blockCoord j i).val < P.r * P.b := by
      rw [bc_val]
      calc j.val * P.b + i.val < (j.val + 1) * P.b := by rw [Nat.add_mul, Nat.one_mul]; omega
        _ ≤ P.r * P.b := Nat.mul_le_mul_right _ hjr
    unfold ctrBit
    rw [if_neg hx1, if_pos hx2, bc_val]
    have he : j.val * P.b + i.val - P.r / 2 * P.b = (j.val - P.r / 2) * P.b + i.val := by
      rw [Nat.sub_mul]
      have : P.r / 2 * P.b ≤ j.val * P.b := Nat.mul_le_mul_right _ (by omega)
      omega
    have hd : ((j.val - P.r / 2) * P.b + i.val) / P.b = j.val - P.r / 2 := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hb, Nat.div_eq_of_lt i.isLt, Nat.zero_add]
    have hm : ((j.val - P.r / 2) * P.b + i.val) % P.b = i.val := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt i.isLt]
    rw [he, hd, hm]

theorem centerAt_isCenter (row col : ℕ) : P.IsCenter σ (centerAt P σ row col) := by
  intro j
  obtain ⟨zb, hz⟩ := blockBits_centerAt P σ row col j
  rw [hz, P.syndrome_xor, syndrome_encB, syndrome_offBlock, zero_add]

/-! ## V2: the pool atoms are the corners at the center -/

theorem pull_flip (row col : ℕ) (u v : BitInput P.n) (k : Fin 4) :
    Pool.pullPoint (side P) (List.ofFn (cornerPt (offset P σ) u v k)) (MatrixScorePhi.value (cols P) row)
      (MatrixScorePhi.value (cols P) col) = cornerPt (centerAt P σ row col) u v k := by
  funext y
  have hl := pull_bit P (List.ofFn (cornerPt (offset P σ) u v k)) (MatrixScorePhi.value (cols P) row)
    (MatrixScorePhi.value (cols P) col) y
  have hr := pull_bit P (List.ofFn (offset P σ)) (MatrixScorePhi.value (cols P) row)
    (MatrixScorePhi.value (cols P) col) y
  rw [ofFn_getD] at hl hr
  rw [hl]
  unfold centerAt
  fin_cases k <;> simp [cornerPt, xorInput, hr, Bool.xor_assoc]

theorem errAt_fst (x : Fin (2 ^ SeedFix.callKh P) × Fin (2 ^ SeedFix.callKh P)) :
    errAt P (SeedFix.cellNumC x / 2 ^ SeedFix.callKh P) = (SeedFix.callEqv P).symm x.1 := by
  unfold errAt
  congr 1
  apply Fin.ext
  show SeedFix.cellNumC x / 2 ^ SeedFix.callKh P % 2 ^ SeedFix.callKh P = x.1.val
  unfold SeedFix.cellNumC
  rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt x.2.isLt, Nat.zero_add,
    Nat.mod_eq_of_lt x.1.isLt]

theorem errAt_snd (x : Fin (2 ^ SeedFix.callKh P) × Fin (2 ^ SeedFix.callKh P)) :
    errAt P (SeedFix.cellNumC x % 2 ^ SeedFix.callKh P) = (SeedFix.callEqv P).symm x.2 := by
  unfold errAt
  congr 1
  apply Fin.ext
  show SeedFix.cellNumC x % 2 ^ SeedFix.callKh P % 2 ^ SeedFix.callKh P = x.2.val
  unfold SeedFix.cellNumC
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt x.2.isLt, Nat.mod_eq_of_lt x.2.isLt]

theorem cellNumC_lt (x : Fin (2 ^ SeedFix.callKh P) × Fin (2 ^ SeedFix.callKh P)) :
    SeedFix.cellNumC x < 2 ^ SeedFix.callKh P * 2 ^ SeedFix.callKh P := by
  unfold SeedFix.cellNumC
  have h1 := x.1.isLt; have h2 := x.2.isLt
  calc x.2.val + 2 ^ SeedFix.callKh P * x.1.val < 2 ^ SeedFix.callKh P + 2 ^ SeedFix.callKh P * x.1.val := by omega
    _ = 2 ^ SeedFix.callKh P * (x.1.val + 1) := by ring
    _ ≤ 2 ^ SeedFix.callKh P * 2 ^ SeedFix.callKh P := Nat.mul_le_mul_left _ h1

theorem atomVal_center (pool : List (NormalizedThresholdGate P.n)) (h Q psi row col : ℕ)
    (x : Fin (2 ^ SeedFix.callKh P) × Fin (2 ^ SeedFix.callKh P)) (gi : ℕ) (hgi : gi < pool.length) (k : Fin 4) :
    Req.atomVal (poolReq P σ pool h Q psi) (MatrixScorePhi.value (cols P) row) (MatrixScorePhi.value (cols P) col)
        (Pool.poolIndex pool.length (SeedFix.cellNumC x) k gi) =
      Stars.corners (pool.getD gi PrimAsm.Records.dGate).eval (centerAt P σ row col)
        (P.errorVector P.leftBlock ((SeedFix.callEqv P).symm x.1))
        (P.errorVector P.rightBlock ((SeedFix.callEqv P).symm x.2)) k := by
  have hcn := cellNumC_lt P x
  have hk := k.isLt
  have hG : 0 < pool.length := by omega
  have hidx : Pool.poolIndex pool.length (SeedFix.cellNumC x) k gi =
      (4 * SeedFix.cellNumC x + k.val) * pool.length + gi := rfl
  have hfl : (poolReq P σ pool h Q psi).flips.length = 4 * (2 ^ SeedFix.callKh P * 2 ^ SeedFix.callKh P) := by
    simp [poolReq, flips]
  have hgl : (poolReq P σ pool h Q psi).gates.length = pool.length := by simp [poolReq]
  have hlt : Pool.poolIndex pool.length (SeedFix.cellNumC x) k gi < (poolReq P σ pool h Q psi).flips.length *
      (poolReq P σ pool h Q psi).gates.length := by
    rw [hidx, hfl, hgl]
    have : 4 * SeedFix.cellNumC x + k.val + 1 ≤ 4 * (2 ^ SeedFix.callKh P * 2 ^ SeedFix.callKh P) := by omega
    calc (4 * SeedFix.cellNumC x + k.val) * pool.length + gi
        < (4 * SeedFix.cellNumC x + k.val) * pool.length + pool.length := by omega
      _ = (4 * SeedFix.cellNumC x + k.val + 1) * pool.length := by ring
      _ ≤ 4 * (2 ^ SeedFix.callKh P * 2 ^ SeedFix.callKh P) * pool.length := Nat.mul_le_mul_right _ this
  have hmod : Pool.poolIndex pool.length (SeedFix.cellNumC x) k gi % pool.length = gi := by
    rw [hidx, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hgi]
  have hdiv : Pool.poolIndex pool.length (SeedFix.cellNumC x) k gi / pool.length = 4 * SeedFix.cellNumC x + k.val := by
    rw [hidx, Nat.add_comm, Nat.add_mul_div_right _ _ hG, Nat.div_eq_of_lt hgi, Nat.zero_add]
  unfold Req.atomVal
  rw [dif_pos hlt]
  have hg : ((poolReq P σ pool h Q psi).gates[Pool.poolIndex pool.length (SeedFix.cellNumC x) k gi %
      (poolReq P σ pool h Q psi).gates.length]'(Nat.mod_lt _ (Req.gates_pos _ _ _ hlt))).gate =
      pool.getD gi PrimAsm.Records.dGate := by
    simp only [poolReq, List.getElem_map, suppG]
    rw [List.getD_eq_getElem _ _ hgi]
    congr 1
    simp only [List.length_map]
    exact hmod
  have hf : (poolReq P σ pool h Q psi).flips[Pool.poolIndex pool.length (SeedFix.cellNumC x) k gi /
      (poolReq P σ pool h Q psi).gates.length]'((Nat.div_lt_iff_lt_mul (Req.gates_pos _ _ _ hlt)).mpr hlt) =
      List.ofFn (cornerPt (offset P σ) (P.errorVector P.leftBlock ((SeedFix.callEqv P).symm x.1))
        (P.errorVector P.rightBlock ((SeedFix.callEqv P).symm x.2)) k) := by
    simp only [poolReq, flips, List.getElem_ofFn]
    unfold flipAt
    have e1 : (Pool.poolIndex pool.length (SeedFix.cellNumC x) k gi / (List.map suppG pool).length) / 4 =
        SeedFix.cellNumC x := by
      rw [List.length_map, hdiv]; omega
    have e2 : (Pool.poolIndex pool.length (SeedFix.cellNumC x) k gi / (List.map suppG pool).length) % 4 = k.val := by
      rw [List.length_map, hdiv]; omega
    rw [e1, e2, errAt_fst, errAt_snd]
    congr 2
    apply Fin.ext
    simp [Nat.mod_eq_of_lt hk]
  rw [hg, hf]
  change (pool.getD gi PrimAsm.Records.dGate).eval (Pool.pullPoint (n := P.n) (side P)
    (List.ofFn (cornerPt (offset P σ) (P.errorVector P.leftBlock ((SeedFix.callEqv P).symm x.1))
      (P.errorVector P.rightBlock ((SeedFix.callEqv P).symm x.2)) k))
    (MatrixScorePhi.value (cols P) row) (MatrixScorePhi.value (cols P) col)) = _
  rw [pull_flip, corners_eq]

/-! ## V3: the table enumerates the centers, `mult` times each -/

/-- The right half's center bits, `rightCenterBits`. -/
abbrev dR : ℕ := P.rightCenterBits

theorem dRow_eq : dRow P = P.r / 2 * dB P + hL P := rfl

theorem dR_eq : dR P = P.r / 2 * dB P + (P.n - P.r * P.b) / 2 := rfl

theorem encB_congr (zb zb' : ℕ → Bool) (h : ∀ m < dB P, zb m = zb' m) (i : ℕ) : encB P zb i = encB P zb' i := by
  unfold encB
  apply xr_congr
  intro m hm
  rw [h m hm]

theorem block_split (j : ℕ) (hj : j < P.r / 2 * dB P) :
    j / dB P < P.r / 2 ∧ j / dB P * dB P + j % dB P = j ∧ j % dB P < dB P := by
  have hd := dB_pos P
  refine ⟨(Nat.div_lt_iff_lt_mul (by omega)).mpr hj, ?_, Nat.mod_lt _ (by omega)⟩
  have := Nat.div_add_mod j (dB P)
  rw [Nat.mul_comm] at this
  exact this

theorem bpos_lt (jb i : ℕ) (hjb : jb < P.r / 2) (hi : i < P.b) : jb * P.b + i < P.r / 2 * P.b := by
  calc jb * P.b + i < (jb + 1) * P.b := by rw [Nat.add_mul, Nat.one_mul]; omega
    _ ≤ P.r / 2 * P.b := Nat.mul_le_mul_right _ hjb

theorem bpos_div (jb i : ℕ) (hi : i < P.b) : (jb * P.b + i) / P.b = jb := by
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ P.b_pos, Nat.div_eq_of_lt hi, Nat.zero_add]

theorem bpos_mod (jb i : ℕ) (hi : i < P.b) : (jb * P.b + i) % P.b = i := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hi]

/-- The coordinate carrying row bit `j`. -/
def rowPos (j : ℕ) : ℕ :=
  if j < P.r / 2 * dB P then j / dB P * P.b + dpos P (j % dB P) else P.r * P.b + (j - P.r / 2 * dB P)

/-- The coordinate carrying column bit `j`. -/
def colPos (j : ℕ) : ℕ :=
  if j < P.r / 2 * dB P then P.r / 2 * P.b + (j / dB P * P.b + dpos P (j % dB P))
  else P.r * P.b + hL P + (j - P.r / 2 * dB P)

theorem rowPos_lt (j : ℕ) (hj : j < dRow P) : rowPos P j < P.n := by
  have h1 := rb_eq P
  have h2 := hL_le P
  unfold rowPos
  split_ifs with hjb
  · obtain ⟨hq, _, hm⟩ := block_split P j hjb
    have hx := bpos_lt P (j / dB P) (dpos P (j % dB P)) hq (dpos_mem P _ hm).1
    omega
  · rw [dRow_eq] at hj; omega

theorem colPos_lt (j : ℕ) (hj : j < dR P) : colPos P j < P.n := by
  have h1 := rb_eq P
  have h2 := hL_le P
  unfold colPos
  split_ifs with hjb
  · obtain ⟨hq, _, hm⟩ := block_split P j hjb
    have hx := bpos_lt P (j / dB P) (dpos P (j % dB P)) hq (dpos_mem P _ hm).1
    omega
  · rw [dR_eq] at hj; unfold hL; omega

/-- The row's bits are read back from the center bits. -/
theorem ctrBit_rowPos (row col j : ℕ) (hj : j < dRow P) : ctrBit P row col (rowPos P j) = row.testBit j := by
  have h1 := rb_eq P
  have h2 := hL_le P
  unfold rowPos
  by_cases hjb : j < P.r / 2 * dB P
  · obtain ⟨hq, hsplit, hm⟩ := block_split P j hjb
    obtain ⟨hd1, _⟩ := dpos_mem P (j % dB P) hm
    have hx := bpos_lt P (j / dB P) (dpos P (j % dB P)) hq hd1
    rw [if_pos hjb]
    unfold ctrBit
    rw [if_pos hx, bpos_div P _ _ hd1, bpos_mod P _ _ hd1, encB_data P _ _ hm, hsplit]
  · rw [if_neg hjb]
    rw [dRow_eq] at hj
    unfold ctrBit
    rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]
    congr 1
    omega

/-- The column's low `dR` bits are read back from the center bits. -/
theorem ctrBit_colPos (row col j : ℕ) (_hj : j < dR P) : ctrBit P row col (colPos P j) = col.testBit j := by
  have h1 := rb_eq P
  have h2 := hL_le P
  unfold colPos
  by_cases hjb : j < P.r / 2 * dB P
  · obtain ⟨hq, hsplit, hm⟩ := block_split P j hjb
    obtain ⟨hd1, _⟩ := dpos_mem P (j % dB P) hm
    have hx := bpos_lt P (j / dB P) (dpos P (j % dB P)) hq hd1
    rw [if_pos hjb]
    unfold ctrBit
    rw [if_neg (by omega), if_pos (by omega), Nat.add_sub_cancel_left, bpos_div P _ _ hd1, bpos_mod P _ _ hd1,
      encB_data P _ _ hm, hsplit]
  · rw [if_neg hjb]
    unfold ctrBit
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    congr 1
    omega

theorem ctrBit_eq_of (row col row' col' : ℕ) (h : centerAt P σ row col = centerAt P σ row' col') (x : Fin P.n) :
    ctrBit P row col x = ctrBit P row' col' x := by
  have hx := congrFun h x
  rw [centerAt_bit, centerAt_bit] at hx
  cases h1 : ctrBit P row col x <;> cases h2 : ctrBit P row' col' x <;> simp_all

theorem eq_of_bits (a b w : ℕ) (ha : a < 2 ^ w) (hb : b < 2 ^ w) (h : ∀ j < w, a.testBit j = b.testBit j) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < w
  · exact h j hj
  · have h2 : 2 ^ w ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.testBit_eq_false_of_lt (by omega), Nat.testBit_eq_false_of_lt (by omega)]

/-- **The table positions are distinct centers** (rows below `2^dRow`, columns below `2^dR`). -/
theorem centerAt_inj (row col row' col' : ℕ) (hr : row < 2 ^ dRow P) (hr' : row' < 2 ^ dRow P)
    (hc : col < 2 ^ dR P) (hc' : col' < 2 ^ dR P) (h : centerAt P σ row col = centerAt P σ row' col') :
    row = row' ∧ col = col' := by
  refine ⟨eq_of_bits row row' (dRow P) hr hr' fun j hj => ?_, eq_of_bits col col' (dR P) hc hc' fun j hj => ?_⟩
  · have e := ctrBit_eq_of P σ row col row' col' h ⟨rowPos P j, rowPos_lt P j hj⟩
    simp only at e
    rw [ctrBit_rowPos P row col j hj, ctrBit_rowPos P row' col' j hj] at e
    exact e
  · have e := ctrBit_eq_of P σ row col row' col' h ⟨colPos P j, colPos_lt P j hj⟩
    simp only at e
    rw [ctrBit_colPos P row col j hj, ctrBit_colPos P row' col' j hj] at e
    exact e

/-- The column is read only through its low `dR` bits. -/
theorem ctrBit_mod (row col : ℕ) (x : Fin P.n) : ctrBit P row col x = ctrBit P row (col % 2 ^ dR P) x := by
  have h1 := rb_eq P
  have h2 := hL_le P
  have hxn := x.isLt
  unfold ctrBit
  split_ifs with hx1 hx2 hx3
  · rfl
  · apply encB_congr
    intro m hm
    rw [Nat.testBit_mod_two_pow]
    have hq : (x.val - P.r / 2 * P.b) / P.b < P.r / 2 := (Nat.div_lt_iff_lt_mul P.b_pos).mpr (by omega)
    have hlt : (x.val - P.r / 2 * P.b) / P.b * dB P + m < dR P := by
      have : ((x.val - P.r / 2 * P.b) / P.b + 1) * dB P ≤ P.r / 2 * dB P := Nat.mul_le_mul_right _ hq
      rw [dR_eq]; rw [Nat.add_mul, Nat.one_mul] at this; omega
    simp [hlt]
  · rfl
  · rw [Nat.testBit_mod_two_pow]
    have hlt : P.r / 2 * dB P + (x.val - P.r * P.b - hL P) < dR P := by rw [dR_eq]; unfold hL at *; omega
    simp [hlt]

theorem centerAt_mod (row col : ℕ) : centerAt P σ row col = centerAt P σ row (col % 2 ^ dR P) := by
  funext x
  rw [centerAt_bit, centerAt_bit, ctrBit_mod]

theorem dRow_dR : dRow P = dR P + (if (P.n - P.r * P.b) % 2 = 1 then 1 else 0) := by
  rw [dRow_eq, dR_eq]; unfold hL; split_ifs <;> omega

theorem sum_range_mod {M : Type} [AddCommMonoid M] (g : ℕ → M) (K : ℕ) :
    ∀ a : ℕ, ∑ c ∈ Finset.range (a * K), g (c % K) = a • ∑ c ∈ Finset.range K, g c
  | 0 => by simp
  | a + 1 => by
    rw [Nat.add_mul, Nat.one_mul, Finset.sum_range_add, sum_range_mod g K a, succ_nsmul]
    congr 1
    apply Finset.sum_congr rfl
    intro c hc
    rw [Finset.mem_range] at hc
    rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hc]

theorem sum_table {M : Type} [AddCommMonoid M] (F : BitInput P.n → M) :
    ∑ row ∈ Finset.range (2 ^ dRow P), ∑ col ∈ Finset.range (2 ^ dRow P), F (centerAt P σ row col) =
      mult P • ∑ c : {c // P.IsCenter σ c}, F c.1 := by
  have hm : 2 ^ dRow P = mult P * 2 ^ dR P := by
    rw [dRow_dR, pow_add]; unfold mult; split_ifs <;> simp [Nat.mul_comm]
  have hcol : ∀ row, ∑ col ∈ Finset.range (2 ^ dRow P), F (centerAt P σ row col) =
      mult P • ∑ col ∈ Finset.range (2 ^ dR P), F (centerAt P σ row col) := by
    intro row
    rw [hm]
    rw [Finset.sum_congr rfl (fun col _ => congrArg F (centerAt_mod P σ row col))]
    exact sum_range_mod (fun c => F (centerAt P σ row c)) (2 ^ dR P) (mult P)
  rw [Finset.sum_congr rfl (fun row _ => hcol row), ← Finset.smul_sum]
  congr 1
  -- the bijection with the centers
  let e : Fin (2 ^ dRow P) × Fin (2 ^ dR P) → {c // P.IsCenter σ c} :=
    fun p => ⟨centerAt P σ p.1 p.2, centerAt_isCenter P σ p.1 p.2⟩
  have hinj : Function.Injective e := by
    intro p p' h
    have h' := congrArg Subtype.val h
    obtain ⟨h1, h2⟩ := centerAt_inj P σ p.1 p.2 p'.1 p'.2 p.1.isLt p'.1.isLt p.2.isLt p'.2.isLt h'
    exact Prod.ext (Fin.ext h1) (Fin.ext h2)
  have hcard : Fintype.card (Fin (2 ^ dRow P) × Fin (2 ^ dR P)) = Fintype.card {c // P.IsCenter σ c} := by
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, P.card_centers σ, ← pow_add]
    congr 1
    exact P.centerBits_sum
  have hbij : Function.Bijective e := (Fintype.bijective_iff_injective_and_card e).mpr ⟨hinj, hcard⟩
  have hs := hbij.sum_comp (fun c : {c // P.IsCenter σ c} => F c.1)
  rw [← hs, Fintype.sum_prod_type]
  rw [← Fin.sum_univ_eq_sum_range (fun row => ∑ col ∈ Finset.range (2 ^ dR P), F (centerAt P σ row col))]
  apply Finset.sum_congr rfl
  intro row _
  rw [← Fin.sum_univ_eq_sum_range (fun col => F (centerAt P σ row col))]

end NearCubicWires.WireExponent3_5.PrimT.C4Geo
