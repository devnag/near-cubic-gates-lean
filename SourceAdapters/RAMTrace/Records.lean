import SourceAdapters.RAMTrace.Global

/-!
# Records, cells and keys (the record convention of `app:event-trace`; `lem:trace-memory`'s order)

The key of a record is `low + 2^{τ+1}·cell` with `low = ts + 2^τ·ph < 2^{τ+1}` and `cell = ad + 2^w·rgn`; keys compare
lexicographically by cell, then by phase and time stamp (`key_lt_iff`). `sameCell` of (S3) is equality of cells
(`sameCell_iff`). `SortOK` depends on the predecessor only through its slots of `def:event-trace` (`sortOK_congr`).
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.RAMTrace

open NearCubicGates.Adapters.ACSP

variable (d : Dims)

/-- The cell `ad + 2^w·rgn` of a record. -/
def cellN (r : RecField → ℕ → Bool) : ℕ := natOf (r .ad) d.w + 2 ^ d.w * (r .rgn 0).toNat

/-- The low part `ts + 2^τ·ph` of a key. -/
def lowN (r : RecField → ℕ → Bool) : ℕ := natOf (r .ts) d.τ + 2 ^ d.τ * (r .ph 0).toNat

theorem lowN_lt (r : RecField → ℕ → Bool) : lowN d r < 2 ^ (d.τ + 1) := by
  have h1 := natOf_lt (r .ts) d.τ
  have h2 : (r .ph 0).toNat ≤ 1 := Bool.toNat_le _
  unfold lowN; rw [pow_succ]
  have : 2 ^ d.τ * (r .ph 0).toNat ≤ 2 ^ d.τ * 1 := Nat.mul_le_mul_left _ h2
  omega

theorem key_eq (r : RecField → ℕ → Bool) : keyOf d r = lowN d r + 2 ^ (d.τ + 1) * cellN d r := by
  rw [key_split, lowN, cellN, pow_succ]; ring

theorem key_lt_iff (r r' : RecField → ℕ → Bool) :
    keyOf d r < keyOf d r' ↔ cellN d r < cellN d r' ∨ (cellN d r = cellN d r' ∧ lowN d r < lowN d r') := by
  rw [key_eq, key_eq]
  exact lex_lt (lowN_lt d r) (lowN_lt d r')

theorem natOf_inj (f g : ℕ → Bool) (n : ℕ) : natOf f n = natOf g n ↔ ∀ l < n, f l = g l := by
  constructor
  · intro h l hl
    have hb : bvOf n f = bvOf n g := BitVec.eq_of_toNat_eq (by rw [toNat_bvOf, toNat_bvOf]; exact h)
    have := congrArg (fun x => BitVec.getLsbD x l) hb
    simpa [hl] using this
  · intro h; rw [natOf_congr f g n h]

theorem sameCell_iff (r p : RecField → ℕ → Bool) : sameCell d r p = true ↔ cellN d r = cellN d p := by
  unfold sameCell
  rw [Bool.not_eq_true', ← Bool.not_eq_true, prefixOr_iff]
  have hc : cellN d r = cellN d p ↔ (natOf (r .ad) d.w = natOf (p .ad) d.w ∧ r .rgn 0 = p .rgn 0) := by
    unfold cellN
    have h1 := natOf_lt (r .ad) d.w
    have h2 := natOf_lt (p .ad) d.w
    constructor
    · intro h
      have n1 := (lex_lt (a := (r .rgn 0).toNat) (b := (p .rgn 0).toNat) h1 h2).not.mp (by omega)
      have n2 := (lex_lt (a := (p .rgn 0).toNat) (b := (r .rgn 0).toNat) h2 h1).not.mp (by omega)
      have hrg : (r .rgn 0).toNat = (p .rgn 0).toNat := by omega
      refine ⟨by omega, ?_⟩
      cases hr : r .rgn 0 <;> cases hp : p .rgn 0 <;> simp [hr, hp] at hrg ⊢
    · rintro ⟨h, h'⟩; rw [h, h']
  rw [hc, natOf_inj]
  constructor
  · intro h
    refine ⟨fun l hl => ?_, ?_⟩
    · by_contra hne
      exact h ⟨l + 1, by omega, by simp only [cellDiff]; cases hr : r .ad l <;> cases hp : p .ad l <;> simp_all⟩
    · by_contra hne
      exact h ⟨0, Nat.zero_le _, by simp only [cellDiff]; cases hr : r .rgn 0 <;> cases hp : p .rgn 0 <;> simp_all⟩
  · rintro ⟨had, hrg⟩ ⟨l, hl, hd⟩
    rcases l with _ | l
    · simp only [cellDiff, hrg, Bool.xor_self] at hd; exact absurd hd (by simp)
    · simp only [cellDiff, had l (by omega), Bool.xor_self] at hd; exact absurd hd (by simp)

/-- Two records agree on the slots of `def:event-trace` other than `st`. -/
def AgreeP (p p' : RecField → ℕ → Bool) : Prop := ∀ f k, f ≠ .st → k < f.width d.w d.τ → p f k = p' f k

/-- Two records agree on all slots of `def:event-trace`. -/
def AgreeR (r r' : RecField → ℕ → Bool) : Prop := ∀ f k, k < f.width d.w d.τ → r f k = r' f k

theorem keyOf_congr (p p' : RecField → ℕ → Bool) (h : AgreeP d p p') : keyOf d p = keyOf d p' := by
  unfold keyOf
  apply natOf_congr
  intro l hl
  unfold keySlot Dims.κ at *
  split_ifs with h1 h2 h3
  · exact h _ _ (by simp) (by simpa [RecField.width] using h1)
  · exact h _ _ (by simp) (by simp [RecField.width])
  · exact h _ _ (by simp) (by simp only [RecField.width]; omega)
  · exact h _ _ (by simp) (by simp [RecField.width])

theorem cellN_congr (p p' : RecField → ℕ → Bool) (h : AgreeP d p p') : cellN d p = cellN d p' := by
  unfold cellN
  rw [natOf_congr _ _ _ fun l hl => h .ad l (by decide) (by simpa [RecField.width] using hl),
    h .rgn 0 (by decide) (by simp [RecField.width])]

theorem sameCell_congr (r p p' : RecField → ℕ → Bool) (h : AgreeP d p p') :
    sameCell d r p = sameCell d r p' := by
  rw [Bool.eq_iff_iff, sameCell_iff, sameCell_iff, cellN_congr d p p' h]

theorem sortOK_congr (r r' p p' : RecField → ℕ → Bool) (hr : AgreeR d r r') (hp : AgreeP d p p')
    (h : SortOK d r p) : SortOK d r' p' := by
  have hrp : AgreeP d r r' := fun f k _ hk => hr f k hk
  have ra := hr .act 0 (by simp [RecField.width])
  have rg := hr .rgn 0 (by simp [RecField.width])
  have rs := hr .st 0 (by simp [RecField.width])
  have rph := hr .ph 0 (by simp [RecField.width])
  have pa := hp .act 0 (by decide) (by simp [RecField.width])
  have pph := hp .ph 0 (by decide) (by simp [RecField.width])
  have hsc : sameCell d r p = sameCell d r' p' := by
    rw [Bool.eq_iff_iff, sameCell_iff, sameCell_iff, cellN_congr d p p' hp, cellN_congr d r r' hrp]
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ha; rw [← pa]; exact h1 (by rw [ra]; exact ha)
  · intro ha hpa
    rw [← keyOf_congr d p p' hp, ← keyOf_congr d r r' hrp]
    exact h2 (by rw [ra]; exact ha) (by rw [pa]; exact hpa)
  · intro ha hrg hst j hj
    rw [← hr .va j (by simpa [RecField.width] using hj), ← hp .va j (by decide) (by simpa [RecField.width] using hj),
      ← hsc]
    exact h3 (by rw [ra]; exact ha) (by rw [rg]; exact hrg) (by rw [rs]; exact hst) j hj
  · intro ha hrg hph
    obtain ⟨a1, a2, a3⟩ := h4 (by rw [ra]; exact ha) (by rw [rg]; exact hrg) (by rw [rph]; exact hph)
    refine ⟨by rw [← hsc]; exact a1, by rw [← pph]; exact a2, fun j hj => ?_⟩
    rw [← hr .va j (by simpa [RecField.width] using hj), ← hp .va j (by decide) (by simpa [RecField.width] using hj)]
    exact a3 j hj

/-! ## The sorted list (`lem:trace-sorted`, first part) -/

/-- The sentinel `(1, 0, 0, 0, 0, 0)`. -/
def sentinelR (f : RecField) (_ : ℕ) : Bool := decide (f = .act)

/-- The predecessor of sorted position `j`: the sentinel at `0`. -/
def predR (R : ℕ → RecField → ℕ → Bool) (j : ℕ) : RecField → ℕ → Bool :=
  if j = 0 then sentinelR else R (j - 1)

/-- The order part of `SortOK` ((S1), (S2)). -/
def OrdOK (r p : RecField → ℕ → Bool) : Prop :=
  (r .act 0 = true → p .act 0 = true) ∧ (r .act 0 = true → p .act 0 = true → keyOf d p < keyOf d r)

theorem SortOK.ord {r p : RecField → ℕ → Bool} (h : SortOK d r p) : OrdOK d r p := ⟨h.1, h.2.1⟩

section SortedList

variable (N : ℕ) (R : ℕ → RecField → ℕ → Bool) (hok : ∀ j < N, OrdOK d (R j) (predR R j))
include hok

/-- Activity is non-increasing: the active vertices are a prefix. -/
theorem active_prefix (j : ℕ) (hj : j < N) (ha : R j .act 0 = true) (j' : ℕ) (hj' : j' ≤ j) :
    R j' .act 0 = true := by
  induction j, hj' using Nat.le_induction with
  | base => exact ha
  | succ m _ ih =>
    exact ih (by omega) (by have := (hok (m + 1) hj).1 ha; simpa [predR] using this)

/-- Keys strictly increase along the active prefix. -/
theorem key_mono (j : ℕ) (hj : j < N) (ha : R j .act 0 = true) (j' : ℕ) (hj' : j' < j) :
    keyOf d (R j') < keyOf d (R j) := by
  induction j, hj' using Nat.le_induction with
  | base =>
    have h := hok (j' + 1) hj
    have hp : predR R (j' + 1) = R j' := by simp [predR]
    rw [hp] at h
    exact h.2 ha (h.1 ha)
  | succ m hm ih =>
    have h := hok (m + 1) hj
    have hp : predR R (m + 1) = R m := by simp [predR]
    rw [hp] at h
    exact lt_trans (ih (by omega) (h.1 ha)) (h.2 ha (h.1 ha))

/-- An active vertex with a smaller key comes earlier. -/
theorem key_pos (j j' : ℕ) (hj : j < N) (hj' : j' < N) (ha : R j .act 0 = true) (ha' : R j' .act 0 = true)
    (hk : keyOf d (R j') < keyOf d (R j)) : j' < j := by
  rcases Nat.lt_trichotomy j' j with h | h | h
  · exact h
  · subst h; omega
  · have := key_mono d N R hok j' hj' ha' j h; omega

/-- No active key lies strictly between a vertex and its predecessor. -/
theorem key_gap (j j' : ℕ) (hj : j < N) (hj1 : 1 ≤ j) (hj' : j' < N) (ha : R j .act 0 = true)
    (ha' : R j' .act 0 = true) (hk : keyOf d (R j') < keyOf d (R j)) : keyOf d (R j') ≤ keyOf d (R (j - 1)) := by
  have hlt := key_pos d N R hok j j' hj hj' ha ha' hk
  rcases Nat.eq_or_lt_of_le (show j' ≤ j - 1 by omega) with h | h
  · rw [h]
  · exact le_of_lt (key_mono d N R hok (j - 1) (by omega)
      (active_prefix d N R hok j hj ha (j - 1) (by omega)) j' h)

end SortedList

/-- A key between two keys of one cell lies in that cell. -/
theorem cell_sandwich (r1 r2 r3 : RecField → ℕ → Bool) (h12 : keyOf d r1 ≤ keyOf d r2)
    (h23 : keyOf d r2 < keyOf d r3) (h13 : cellN d r1 = cellN d r3) : cellN d r2 = cellN d r1 := by
  rcases Nat.lt_trichotomy (cellN d r2) (cellN d r1) with h | h | h
  · have := (key_lt_iff d r2 r1).mpr (Or.inl h); omega
  · exact h
  · have := (key_lt_iff d r3 r2).mpr (Or.inl (by omega)); omega

end NearCubicGates.Adapters.RAMTrace
