import SourceAdapters.RAMTrace.RowComplete

/-!
# One sorted vertex: the equations (S1)–(S5)

`app:event-trace` Sorted-vertex equations and `lem:trace-sorted` (the local part). For a Boolean sorted vertex with routed record
`rec` and predecessor copy `prev`:
- `SortOK`: the semantic content of (S1)–(S5) — activity is non-increasing, two active neighbours have strictly
  increasing keys (`key(PREV) < key`), a memory load reads its predecessor's value if the predecessor is the same
  cell and `0` otherwise, and a tape-A read has a same-cell phase-`0` predecessor with the same value;
- `sorted_sound`: a vertex satisfying (S1)–(S5) is `sortCanon rec prev` on its slots and `SortOK rec prev` holds;
- `sorted_complete`: if `SortOK rec prev`, `sortCanon rec prev` satisfies (S1)–(S5).
`natOf` reads a key as a number; `key_split` writes it as `ts + 2^τ (ph + 2 (ad + 2^w rgn))`.
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.RAMTrace

open NearCubicGates.Adapters.ACSP Expr BitVec

/-! ## Numbers from bits -/

/-- The number with bits `f 0, …, f (n−1)` (least significant first). -/
def natOf : (ℕ → Bool) → ℕ → ℕ
  | _, 0 => 0
  | f, n + 1 => (f 0).toNat + 2 * natOf (fun l => f (l + 1)) n

theorem natOf_lt (f : ℕ → Bool) (n : ℕ) : natOf f n < 2 ^ n := by
  induction n generalizing f with
  | zero => simp [natOf]
  | succ n ih =>
    have := ih (fun l => f (l + 1))
    have hb : (f 0).toNat ≤ 1 := Bool.toNat_le _
    simp only [natOf, pow_succ]; omega

theorem natOf_congr (f g : ℕ → Bool) (n : ℕ) (h : ∀ l < n, f l = g l) : natOf f n = natOf g n := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih =>
    simp only [natOf]
    rw [h 0 (by omega), ih (fun l => f (l + 1)) (fun l => g (l + 1)) (fun l hl => h (l + 1) (by omega))]

theorem natOf_add (f : ℕ → Bool) (n m : ℕ) :
    natOf f (n + m) = natOf f n + 2 ^ n * natOf (fun l => f (n + l)) m := by
  induction n generalizing f with
  | zero => simp [natOf]
  | succ n ih =>
    rw [show n + 1 + m = (n + m) + 1 by omega]
    simp only [natOf]
    rw [ih (fun l => f (l + 1))]
    have : (fun l => f (n + l + 1)) = (fun l => f (n + 1 + l)) := by funext l; congr 1; omega
    rw [this, pow_succ]; ring

theorem natOf_one (f : ℕ → Bool) : natOf f 1 = (f 0).toNat := by simp [natOf]

theorem toNat_bvOf (n : ℕ) (f : ℕ → Bool) : (bvOf n f).toNat = natOf f n := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [← BitVec.getLsbD, getLsbD_bvOf]
  induction n generalizing f i with
  | zero => simp [natOf]
  | succ n ih =>
    simp only [natOf]
    rcases i with _ | i
    · simp only [Nat.testBit_zero, Nat.zero_lt_succ, decide_true, Bool.true_and]
      cases f 0 <;> simp [Nat.add_mod]
    · rw [show (f 0).toNat + 2 * natOf (fun l => f (l + 1)) n = 2 * natOf (fun l => f (l + 1)) n + (f 0).toNat
        by ring, Nat.testBit_succ, Nat.mul_add_div (by norm_num),
        show (f 0).toNat / 2 = 0 by cases f 0 <;> rfl, Nat.add_zero (natOf _ n), ← ih (fun l => f (l + 1)) i]
      simp

theorem bvOf_toNat_lt_iff (n : ℕ) (f g : ℕ → Bool) :
    (bvOf n f).toNat < (bvOf n g).toNat ↔ natOf f n < natOf g n := by
  rw [toNat_bvOf, toNat_bvOf]

/-! ## Keys -/

section Keys

variable (d : Dims)

/-- The key of a record given by its bits: `ts + 2^τ·ph + 2^{τ+1}·ad + 2^{τ+1+w}·rgn` (the record convention of `app:event-trace`). -/
def keyOf (r : RecField → ℕ → Bool) : ℕ := natOf (fun l => r (keySlot d l).1 (keySlot d l).2) d.κ

/-- The key, field by field. -/
theorem key_split (r : RecField → ℕ → Bool) :
    keyOf d r = natOf (r .ts) d.τ + 2 ^ d.τ * ((r .ph 0).toNat + 2 * (natOf (r .ad) d.w + 2 ^ d.w *
      (r .rgn 0).toNat)) := by
  unfold keyOf Dims.κ
  rw [show d.w + d.τ + 2 = d.τ + (1 + (d.w + 1)) by omega, natOf_add, natOf_add, natOf_add, natOf_one,
    natOf_one]
  have h1 : natOf (fun l => r (keySlot d l).1 (keySlot d l).2) d.τ = natOf (r .ts) d.τ :=
    natOf_congr _ _ _ fun l hl => by simp [keySlot, hl]
  have h2 : r (keySlot d (d.τ + 0)).1 (keySlot d (d.τ + 0)).2 = r .ph 0 := by simp [keySlot]
  have h3 : natOf (fun l => r (keySlot d (d.τ + (1 + l))).1 (keySlot d (d.τ + (1 + l))).2) d.w =
      natOf (r .ad) d.w := natOf_congr _ _ _ fun l hl => by
        simp only [keySlot]
        rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]
        congr 1; omega
  have h4 : r (keySlot d (d.τ + (1 + (d.w + 0)))).1 (keySlot d (d.τ + (1 + (d.w + 0)))).2 = r .rgn 0 := by
    simp only [keySlot]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  rw [h1, h2, h3, h4]
  ring

end Keys

/-! ## The sorted vertex -/

section Vertex

variable (d : Dims)

/-- Key bit `l` of a record. -/
def keyBits (r : RecField → ℕ → Bool) (l : ℕ) : Bool := r (keySlot d l).1 (keySlot d l).2

/-- The differences `d_0 = prgn + rgn`, `d_{1+j} = pad[j] + ad[j]` of (S3). -/
def cellDiff (r p : RecField → ℕ → Bool) : ℕ → Bool
  | 0 => Bool.xor (p .rgn 0) (r .rgn 0)
  | l + 1 => Bool.xor (p .ad l) (r .ad l)

/-- `so_w = 0`: the record and its predecessor name the same region and address. -/
def sameCell (r p : RecField → ℕ → Bool) : Bool := !prefixOr (cellDiff r p) d.w

/-- The canonical sorted vertex with record `r` and predecessor copy `p`. -/
def sortCanon (r p : RecField → ℕ → Bool) : SVar → Bool
  | .inl (.prev f k) => p f k
  | .inl (.ob l) => !carry (l + 1) (bvOf d.κ (keyBits d p)) (~~~(bvOf d.κ (keyBits d r))) true
  | .inl .both => r .act 0 && p .act 0
  | .inl (.so l) => prefixOr (cellDiff r p) l
  | .inl .u => r .act 0 && !r .rgn 0
  | .inl .g => (r .act 0 && !r .rgn 0) && !r .st 0
  | .inl (.ev j) => (!prefixOr (cellDiff r p) d.w) && p .va j
  | .inl .gA1 => r .act 0 && r .rgn 0
  | .inl .gA => (r .act 0 && r .rgn 0) && r .ph 0
  | .inr (f, k) => r f k

/-- **The semantic content of (S1)–(S5).** -/
def SortOK (r p : RecField → ℕ → Bool) : Prop :=
  (r .act 0 = true → p .act 0 = true) ∧
  (r .act 0 = true → p .act 0 = true → keyOf d p < keyOf d r) ∧
  (r .act 0 = true → r .rgn 0 = false → r .st 0 = false →
    ∀ j < d.w, r .va j = (sameCell d r p && p .va j)) ∧
  (r .act 0 = true → r .rgn 0 = true → r .ph 0 = true →
    sameCell d r p = true ∧ p .ph 0 = false ∧ ∀ j < d.w, r .va j = p .va j)

/-- The record of a sorted vertex. -/
def recB (v : SVar → Bool) (f : RecField) (k : ℕ) : Bool := v (.inr (f, k))

/-- The predecessor copy of a sorted vertex. -/
def prevB (v : SVar → Bool) (f : RecField) (k : ℕ) : Bool := v (.inl (.prev f k))

theorem evalB_keyE (v : SVar → Bool) (l : ℕ) : (keyE d l).evalB v = keyBits d (recB v) l := rfl

theorem evalB_pkeyE (v : SVar → Bool) (l : ℕ) : (pkeyE d l).evalB v = keyBits d (prevB v) l := rfl

theorem evalB_obE (v : SVar → Bool) (l : ℕ) : (obE l).evalB v = cin (fun i => v (.inl (.ob i))) false l := by
  unfold obE cin; split_ifs <;> simp

/-- The borrow chain of (S2) is the comparison of the keys. -/
theorem key_chain_iff (P K : BitVec d.κ) (ob : ℕ → Bool) :
    (∀ l < d.κ, ob l = Bool.xor ((!P.getLsbD l) && Bool.xor (K.getLsbD l) (cin ob false l))
        (K.getLsbD l && cin ob false l)) ↔
      ∀ l < d.κ, ob l = !carry (l + 1) P (~~~K) true := by
  have h := subtractor_iff P K (fun l => Bool.xor (Bool.xor (P.getLsbD l) (K.getLsbD l)) (cin ob false l)) ob
  constructor
  · intro hob
    exact (h.mp ⟨fun _ _ => rfl, hob⟩).2
  · intro hob
    have hs := (subtractor_iff P K (fun l => (P - K).getLsbD l) ob).mpr ⟨fun _ _ => rfl, hob⟩
    exact hs.2

/-- **(S1)–(S5), soundness.** -/
theorem sorted_sound (hw : 1 ≤ d.w) (v : SVar → Bool)
    (h : ∀ q : SEq, q.Active d → (sortEq d q).evalB v = false) :
    (∀ s : SVar, s.Active d → v s = sortCanon d (recB v) (prevB v) s) ∧ SortOK d (recB v) (prevB v) := by
  have hκ : 1 ≤ d.κ := by unfold Dims.κ; omega
  set P := bvOf d.κ (keyBits d (prevB v)) with hP
  set K := bvOf d.κ (keyBits d (recB v)) with hK
  have hPl : ∀ l < d.κ, keyBits d (prevB v) l = P.getLsbD l := by intro l hl; simp [hP, hl]
  have hKl : ∀ l < d.κ, keyBits d (recB v) l = K.getLsbD l := by intro l hl; simp [hK, hl]
  have hob : ∀ l < d.κ, v (.inl (.ob l)) = !carry (l + 1) P (~~~K) true := by
    apply (key_chain_iff d P K (fun l => v (.inl (.ob l)))).mp
    intro l hl
    have := h (.borrow l) hl
    simp only [sortEq, evalB_add, evalB_var, evalB_mul, evalB_compl, evalB_keyE, evalB_pkeyE, evalB_obE] at this
    rw [xor2_false, hPl l hl, hKl l hl] at this
    exact this
  have hso : ∀ l ≤ d.w, v (.inl (.so l)) = prefixOr (cellDiff (recB v) (prevB v)) l := by
    have hc := (prefixOr_chain_iff (cellDiff (recB v) (prevB v)) (fun l => v (.inl (.so l))) (d.w + 1)).mp
      ⟨?_, ?_⟩
    · intro l hl
      rcases Nat.eq_zero_or_pos l with h0 | h0
      · subst h0; rw [hc.1, prefixOr_zero]
      · exact hc.2 l h0 (by omega)
    · have := h .soFirst trivial
      simp only [sortEq, evalB_add, evalB_var] at this
      rw [xor2_false] at this; exact this
    · intro l hl1 hl
      have := h (.soNext (l - 1)) (by show l - 1 < d.w; omega)
      simp only [sortEq, evalB_add, evalB_var, evalB_mul] at this
      rw [xor2_false, Nat.sub_add_cancel hl1] at this
      rw [this]
      have : cellDiff (recB v) (prevB v) l = Bool.xor (prevB v .ad (l - 1)) (recB v .ad (l - 1)) := by
        obtain ⟨l', rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
        rfl
      rw [this]; rfl
  have hboth : v (.inl .both) = (recB v .act 0 && prevB v .act 0) := by
    have := h .both trivial
    simp only [sortEq, evalB_add, evalB_var, evalB_mul] at this
    rw [xor2_false] at this; exact this
  have hu : v (.inl .u) = (recB v .act 0 && !recB v .rgn 0) := by
    have := h .u trivial
    simp only [sortEq, evalB_add, evalB_var, evalB_mul, evalB_compl] at this
    rw [xor2_false] at this; exact this
  have hg : v (.inl .g) = ((recB v .act 0 && !recB v .rgn 0) && !recB v .st 0) := by
    have := h .g trivial
    simp only [sortEq, evalB_add, evalB_var, evalB_mul, evalB_compl] at this
    rw [xor2_false, hu] at this; exact this
  have hev : ∀ j < d.w, v (.inl (.ev j)) = ((!prefixOr (cellDiff (recB v) (prevB v)) d.w) && prevB v .va j) := by
    intro j hj
    have := h (.ev j) hj
    simp only [sortEq, evalB_add, evalB_var, evalB_mul, evalB_compl] at this
    rw [xor2_false, hso d.w le_rfl] at this; exact this
  have hgA1 : v (.inl .gA1) = (recB v .act 0 && recB v .rgn 0) := by
    have := h .gA1 trivial
    simp only [sortEq, evalB_add, evalB_var, evalB_mul] at this
    rw [xor2_false] at this; exact this
  have hgA : v (.inl .gA) = ((recB v .act 0 && recB v .rgn 0) && recB v .ph 0) := by
    have := h .gA trivial
    simp only [sortEq, evalB_add, evalB_var, evalB_mul] at this
    rw [xor2_false, hgA1] at this; exact this
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rintro (s | ⟨f, k⟩) hs
    · cases s with
      | prev f k => rfl
      | ob l => exact hob l hs
      | both => exact hboth
      | so l => exact hso l hs
      | u => exact hu
      | g => exact hg
      | ev j => exact hev j hs
      | gA1 => exact hgA1
      | gA => exact hgA
    · rfl
  · intro ha
    have := h .act trivial
    simp only [sortEq, evalB_mul, evalB_var, evalB_compl] at this
    unfold recB at ha; unfold prevB
    rw [ha] at this; simpa using this
  · intro ha hpa
    have := h .strict trivial
    simp only [sortEq, evalB_mul, evalB_var, evalB_compl, evalB_obE] at this
    rw [hboth] at this
    unfold recB at ha; unfold prevB at hpa
    simp only [recB, prevB, ha, hpa, Bool.true_and] at this
    have hc : cin (fun i => v (.inl (.ob i))) false d.κ = decide (P.toNat < K.toNat) := by
      simp only [cin, show d.κ ≠ 0 by omega, if_false]
      rw [hob (d.κ - 1) (by omega)]
      exact final_borrow P K hκ
    rw [hc] at this
    simp only [Bool.not_eq_false', decide_eq_true_eq] at this
    rw [hP, hK, bvOf_toNat_lt_iff] at this
    exact this
  · intro ha hr hst j hj
    have := h (.load j) hj
    simp only [sortEq, evalB_mul, evalB_var, evalB_add] at this
    rw [hg, hev j hj] at this
    unfold recB at ha hr hst
    simp only [recB, ha, hr, hst, Bool.not_false, Bool.and_self, Bool.true_and] at this
    rw [xor2_false] at this
    exact this
  · intro ha hr hph
    unfold recB at ha hr hph
    have hgA' : v (.inl .gA) = true := by rw [hgA]; simp [recB, ha, hr, hph]
    have h1 := h .same trivial
    have h2 := h .phase trivial
    simp only [sortEq, evalB_mul, evalB_var, hgA', Bool.true_and] at h1 h2
    refine ⟨?_, h2, ?_⟩
    · unfold sameCell; rw [← hso d.w le_rfl, h1]; rfl
    · intro j hj
      have := h (.value j) hj
      simp only [sortEq, evalB_mul, evalB_var, evalB_add, hgA', Bool.true_and] at this
      exact (xor2_false _ _).mp this

/-- **(S1)–(S5), existence.** If the record and its predecessor satisfy `SortOK`, the canonical vertex satisfies
(S1)–(S5). -/
theorem sorted_complete (hw : 1 ≤ d.w) (r p : RecField → ℕ → Bool) (hok : SortOK d r p) :
    ∀ q : SEq, q.Active d → (sortEq d q).evalB (sortCanon d r p) = false := by
  obtain ⟨h1, h2, h3, h4⟩ := hok
  have hκ : 1 ≤ d.κ := by unfold Dims.κ; omega
  set P := bvOf d.κ (keyBits d p) with hP
  set K := bvOf d.κ (keyBits d r) with hK
  have hchain := (key_chain_iff d P K (fun l => !carry (l + 1) P (~~~K) true)).mpr (fun _ _ => rfl)
  have hsoc := (prefixOr_chain_iff (cellDiff r p) (fun l => prefixOr (cellDiff r p) l) (d.w + 1)).mpr
    ⟨prefixOr_zero _, fun _ _ _ => rfl⟩
  intro q hq
  cases q with
  | act =>
    simp only [sortEq, evalB_mul, evalB_var, evalB_compl, sortCanon]
    cases hr : r .act 0
    · simp
    · simp [h1 hr]
  | both =>
    simp only [sortEq, evalB_add, evalB_var, evalB_mul, sortCanon]
    simp
  | borrow l =>
    simp only [sortEq, evalB_add, evalB_var, evalB_mul, evalB_compl, evalB_keyE, evalB_pkeyE, evalB_obE]
    rw [xor2_false]
    have hl : l < d.κ := hq
    have e1 : keyBits d (recB (sortCanon d r p)) l = K.getLsbD l := by
      simp [hK, hl, recB, sortCanon, keyBits]
    have e2 : keyBits d (prevB (sortCanon d r p)) l = P.getLsbD l := by
      simp [hP, hl, prevB, sortCanon, keyBits]
    rw [e1, e2]
    exact hchain l hl
  | strict =>
    simp only [sortEq, evalB_mul, evalB_var, evalB_compl, evalB_obE, sortCanon]
    cases hr : r .act 0
    · simp
    · cases hp : p .act 0
      · simp
      · have hlt := h2 hr hp
        have hcin : cin (fun i => !carry (i + 1) (bvOf d.κ (keyBits d p)) (~~~bvOf d.κ (keyBits d r)) true)
            false d.κ = decide (P.toNat < K.toNat) := by
          simp only [cin, show d.κ ≠ 0 by omega, if_false]
          exact final_borrow P K hκ
        rw [hcin]
        have : P.toNat < K.toNat := by
          rw [hP, hK, bvOf_toNat_lt_iff]; unfold keyOf at hlt; exact hlt
        simp [this]
  | soFirst =>
    simp only [sortEq, evalB_add, evalB_var, sortCanon]
    rw [xor2_false, prefixOr_zero]; rfl
  | soNext j =>
    simp only [sortEq, evalB_add, evalB_var, evalB_mul, sortCanon]
    rw [xor2_false]
    exact hsoc.2 (j + 1) (by omega) (by have : j < d.w := hq; omega)
  | u => simp [sortEq, sortCanon]
  | g => simp [sortEq, sortCanon]
  | ev j => simp [sortEq, sortCanon]
  | load j =>
    simp only [sortEq, evalB_mul, evalB_var, evalB_add, sortCanon]
    cases ha : r .act 0
    · simp
    · cases hr : r .rgn 0
      · cases hs : r .st 0
        · simp only [Bool.not_false, Bool.and_self, Bool.true_and]
          rw [xor2_false, h3 ha hr hs j hq]; rfl
        · simp
      · simp
  | gA1 => simp [sortEq, sortCanon]
  | gA => simp [sortEq, sortCanon]
  | same =>
    simp only [sortEq, evalB_mul, evalB_var, sortCanon]
    cases ha : r .act 0
    · simp
    · cases hr : r .rgn 0
      · simp
      · cases hph : r .ph 0
        · simp
        · have := (h4 ha hr hph).1
          unfold sameCell at this
          simp at this; simp [this]
  | phase =>
    simp only [sortEq, evalB_mul, evalB_var, sortCanon]
    cases ha : r .act 0
    · simp
    · cases hr : r .rgn 0
      · simp
      · cases hph : r .ph 0
        · simp
        · simp [(h4 ha hr hph).2.1]
  | value j =>
    simp only [sortEq, evalB_mul, evalB_var, evalB_add, sortCanon]
    cases ha : r .act 0
    · simp
    · cases hr : r .rgn 0
      · simp
      · cases hph : r .ph 0
        · simp
        · simp [(h4 ha hr hph).2.2 j hq]

end Vertex

end NearCubicGates.Adapters.RAMTrace
