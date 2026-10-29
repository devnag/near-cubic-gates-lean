import SourceAdapters.ShortPCP.Machines.FLang

/-!
# Single-run time, machine layer 8: reasoning about `FL` programs, and the frame reader

Rules for the semantics `evalS` (`FLang.lean`): counted loops by an invariant over the pass number (`loop_inv`),
bounded while loops by an invariant and a measure below the pass bound (`whl_inv`), and frames (which variables a
program writes, `Wr`). The first routine is the reader of a framed word (`frame u` = the bits of `u`, each after a
`1`, then `0`): `rdFrame` leaves `bitsValue u` (least significant bit first) and `|u|` in two variables (proof of `thm:short-pcp-ours`: the program input is `frame data ++ frame R`).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false

namespace NearCubicGates.Adapters.ShortPCP.Machines.FL

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.CanonicalBinary
open NearCubicGates.Close.Cells (natWord_one natWord_zero natWord_bit natWord_length lt_natBitLength)
open NearCubicWires.RepairRepresentation (natWord)

variable (G : Glob)

/-! ## Equations of the semantics -/

@[simp] theorem evalS_skip (s : FS) : evalS G .skip s = s := rfl
@[simp] theorem evalS_set (i : Var) (e : E) (s : FS) : evalS G (.set i e) s = s.setv i (evalE G s e) := rfl
@[simp] theorem evalS_seq (a b : S) (s : FS) : evalS G (.seq a b) s = evalS G b (evalS G a s) := rfl
theorem evalS_ite (c : E) (a b : S) (s : FS) :
    evalS G (.ite c a b) s = if evalE G s c = 0 then evalS G b s else evalS G a s := rfl
@[simp] theorem evalS_emit (e : E) (s : FS) : evalS G (.emit e) s = { s with out := s.out ++ [evalE G s e != 0] } := rfl
theorem evalS_rd (i : Var) (s : FS) (h : s.ip < G.inp.length) :
    evalS G (.rd i) s = { s.setv i (G.inp.getD s.ip false).toNat with ip := s.ip + 1 } := by
  simp [evalS, h]

/-- **Counted loops**: an invariant over the pass number. -/
theorem loop_inv {i : Var} {n : E} {body : S} {s : FS} (P : ℕ → FS → Prop) (h0 : P 0 s)
    (hstep : ∀ j < min (evalE G s n) G.N, ∀ t, P j t → P (j + 1) (evalS G body (t.setv i j))) :
    P (min (evalE G s n) G.N) (evalS G (.loop i n body) s) := by
  show P _ ((List.range (min (evalE G s n) G.N)).foldl (fun s' j => evalS G body (s'.setv i j)) s)
  generalize min (evalE G s n) G.N = m at *
  suffices h : ∀ k ≤ m, P k ((List.range k).foldl (fun s' j => evalS G body (s'.setv i j)) s) from h m le_rfl
  intro k hk
  induction k with
  | zero => simpa using h0
  | succ k ih =>
    rw [List.range_succ, List.foldl_append]
    exact hstep k (by omega) _ (ih (by omega))

/-- **Bounded while loops**: an invariant and a measure (at most `N`) that every pass lowers. -/
theorem whl_inv {c : E} {body : S} (P : FS → Prop) (μ : FS → ℕ) (s : FS) (hs : P s) (hμ : μ s ≤ G.N)
    (hstep : ∀ t, P t → evalE G t c ≠ 0 → P (evalS G body t) ∧ μ (evalS G body t) < μ t) :
    P (evalS G (.whl c body) s) ∧ evalE G (evalS G (.whl c body) s) c = 0 := by
  show P (whileN _ _ G.N s) ∧ evalE G (whileN _ _ G.N s) c = 0
  suffices h : ∀ k t, P t → μ t ≤ k → P (whileN (fun s' => evalE G s' c != 0) (evalS G body) k t) ∧
      evalE G (whileN (fun s' => evalE G s' c != 0) (evalS G body) k t) c = 0 from h _ s hs hμ
  intro k
  induction k with
  | zero =>
    intro t ht hμt
    refine ⟨ht, ?_⟩
    by_contra hc
    have := (hstep t ht hc).2; omega
  | succ k ih =>
    intro t ht hμt
    by_cases hc : evalE G t c = 0
    · simp only [whileN, hc, bne_self_eq_false, if_false]; exact ⟨ht, hc⟩
    · have h2 := hstep t ht hc
      simp only [whileN, show (evalE G t c != 0) = true by simpa using hc, if_true]
      exact ih _ h2.1 (by omega)

/-! ## Frames -/

/-- `p` changes only the variables `W`, keeps the output, the field, and the out-of-input flag. -/
structure Wr (W : List Var) (s t : FS) : Prop where
  env : ∀ j, j ∉ W → t.env j = s.env j
  out : t.out = s.out
  fl : t.fl = s.fl
  fp : t.fp = s.fp
  bad : t.bad = s.bad

theorem Wr.refl (W : List Var) (s : FS) : Wr W s s := ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl⟩

theorem Wr.trans {W : List Var} {s t u : FS} (h1 : Wr W s t) (h2 : Wr W t u) : Wr W s u :=
  ⟨fun j hj => (h2.env j hj).trans (h1.env j hj), h2.out.trans h1.out, h2.fl.trans h1.fl, h2.fp.trans h1.fp,
    h2.bad.trans h1.bad⟩

theorem Wr.setv {W : List Var} (s : FS) {i : Var} (hi : i ∈ W) (v : ℕ) : Wr W s (s.setv i v) :=
  ⟨fun j hj => by simp [Function.update_of_ne (show j ≠ i from fun h => hj (h ▸ hi))], rfl, rfl, rfl, rfl⟩

/-! ## Framed words -/

theorem frame_getD_even : ∀ (u : List Bool) (k : ℕ), (frame u).getD (2 * k) false = decide (k < u.length)
  | [], k => by cases k <;> simp [frame]
  | b :: u, 0 => by simp [frame]
  | b :: u, k + 1 => by
    rw [show 2 * (k + 1) = 2 * k + 2 by ring]
    show (true :: b :: frame u).getD (2 * k + 2) false = _
    rw [List.getD_cons_succ, List.getD_cons_succ, frame_getD_even u k]; simp

theorem frame_getD_odd : ∀ (u : List Bool) (k : ℕ), k < u.length → (frame u).getD (2 * k + 1) false = u.getD k false
  | [], k, h => by simp at h
  | b :: u, 0, _ => by simp [frame]
  | b :: u, k + 1, h => by
    rw [show 2 * (k + 1) + 1 = 2 * k + 1 + 2 by ring]
    show (true :: b :: frame u).getD (2 * k + 1 + 2) false = _
    rw [List.getD_cons_succ, List.getD_cons_succ, frame_getD_odd u k (by simpa using h)]; simp

theorem frame_len (u : List Bool) : (frame u).length = 2 * u.length + 1 := by
  induction u with
  | nil => rfl
  | cons b u ih => simp [frame, ih]; ring

theorem bitsValue_take_succ (u : List Bool) (k : ℕ) (hk : k < u.length) :
    bitsValue (u.take (k + 1)) = bitsValue (u.take k) + (u.getD k false).toNat * 2 ^ k := by
  induction u generalizing k with
  | nil => simp at hk
  | cons b u ih =>
    cases k with
    | zero => cases b <;> simp [bitsValue]
    | succ k =>
      simp only [List.take_succ_cons, List.getD_cons_succ, bitsValue]
      rw [ih k (by simp at hk; omega)]; ring

theorem bv_lt (u : List Bool) : bitsValue u < 2 ^ u.length := by
  induction u with
  | nil => simp [bitsValue]
  | cons b u ih => cases b <;> simp [bitsValue, pow_succ] <;> omega

/-! ## The frame reader -/

/-- Read `frame u` from the input: variable `0 := bitsValue u`, `1 := |u|` (scratch `2, 3, 4`). -/
def rdFrame : S :=
  .seq (.set 0 (.k 0)) (.seq (.set 1 (.k 0)) (.seq (.set 2 (.k 1)) (.seq (.rd 3)
    (.whl (.v 3) (.seq (.rd 4) (.seq (.set 0 (.add (.v 0) (.mul (.v 4) (.v 2))))
      (.seq (.set 2 (.add (.v 2) (.v 2))) (.seq (.set 1 (.add (.v 1) (.k 1))) (.rd 3)))))))))

/-- The variables of `rdFrame`. -/
def rdFrameW : List Var := [0, 1, 2, 3, 4]

theorem bool_toNat_le (c : Bool) : c.toNat ≤ 1 := by cases c <;> simp

/-- **The frame reader.** -/
theorem rdFrame_spec (s : FS) (u rest : List Bool)
    (hin : G.inp.drop s.ip = frame u ++ rest) (hcap : 2 * 2 ^ u.length ≤ G.cap) (hN : u.length + 1 ≤ G.N) :
    let t := evalS G rdFrame s
    t.env 0 = bitsValue u ∧ t.env 1 = u.length ∧ t.ip = s.ip + 2 * u.length + 1 ∧ Wr rdFrameW s t := by
  intro t
  have hlen : s.ip + 2 * u.length + 1 ≤ G.inp.length := by
    have := congrArg List.length hin; simp [frame_len] at this; omega
  have bit : ∀ j, j < 2 * u.length + 1 → G.inp.getD (s.ip + j) false = (frame u).getD j false := by
    intro j hj
    have h1 : (G.inp.drop s.ip).getD j false = G.inp.getD (s.ip + j) false := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_drop]
    rw [← h1, hin, List.getD_append _ _ _ _ (by rw [frame_len]; omega)]
  have hcap1 : 1 ≤ G.cap := by have := Nat.one_le_two_pow (n := u.length); omega
  have hm1 : min 1 G.cap = 1 := by omega
  set s1 := ((s.setv 0 (min 0 G.cap)).setv 1 (min 0 G.cap)).setv 2 (min 1 G.cap) with hs1
  have hr1 : s1.ip < G.inp.length := by simp [s1]; omega
  -- the loop invariant
  let P : FS → Prop := fun w => ∃ k ≤ u.length, w.env 0 = bitsValue (u.take k) ∧ w.env 1 = k ∧ w.env 2 = 2 ^ k ∧
    w.env 3 = (decide (k < u.length)).toNat ∧ w.ip = s.ip + 2 * k + 1 ∧ Wr rdFrameW s w
  let μ : FS → ℕ := fun w => u.length - w.env 1
  have hP0 : P (evalS G (.rd 3) s1) := by
    rw [evalS_rd G 3 s1 hr1]
    have b0 := bit 0 (by omega); simp only [Nat.add_zero] at b0
    refine ⟨0, Nat.zero_le _, ?_, ?_, ?_, ?_, by simp [s1], ?_⟩
    · simp (config := { decide := true }) [s1, Function.update_apply, bitsValue]
    · simp (config := { decide := true }) [s1, Function.update_apply]
    · simp (config := { decide := true }) [s1, Function.update_apply, hm1]
    · simp only [FS.setv_env, Function.update_self]
      rw [show s1.ip = s.ip from rfl, b0, show (0 : ℕ) = 2 * 0 by rfl, frame_getD_even]
    · refine ⟨fun j hj => ?_, rfl, rfl, rfl, rfl⟩
      simp only [rdFrameW, List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
      simp [s1, Function.update_apply, hj.1, hj.2.1, hj.2.2.1, hj.2.2.2.1]
  have hw := whl_inv G (c := .v 3) (body := .seq (.rd 4) (.seq (.set 0 (.add (.v 0) (.mul (.v 4) (.v 2))))
      (.seq (.set 2 (.add (.v 2) (.v 2))) (.seq (.set 1 (.add (.v 1) (.k 1))) (.rd 3))))) P μ _ hP0
    (by simp only [μ]; omega) (by
      rintro w ⟨k, hk, wx, wn, wp, wm, wi, wW⟩ hc
      have hk' : k < u.length := by
        by_contra h; simp only [evalE, wm, show ¬ k < u.length from h, decide_false, Bool.toNat_false] at hc
        exact hc rfl
      have hb1 : w.ip < G.inp.length := by omega
      have hbit : G.inp.getD w.ip false = u.getD k false := by
        rw [wi, show s.ip + 2 * k + 1 = s.ip + (2 * k + 1) by ring, bit _ (by omega), frame_getD_odd u k hk']
      have hbit2 : G.inp.getD (w.ip + 1) false = decide (k + 1 < u.length) := by
        rw [wi, show s.ip + 2 * k + 1 + 1 = s.ip + 2 * (k + 1) by ring, bit _ (by omega), frame_getD_even]
      have hpow : 2 ^ (k + 1) ≤ 2 ^ u.length := Nat.pow_le_pow_right (by norm_num) hk'
      have hxlt : bitsValue (u.take k) < 2 ^ k := by
        have := bv_lt (u.take k); simp only [List.length_take] at this
        rwa [min_eq_left hk] at this
      have hb01 := bool_toNat_le (u.getD k false)
      have hmul : (u.getD k false).toNat * 2 ^ k ≤ 2 ^ k := by
        have := Nat.mul_le_mul_right (2 ^ k) hb01; simpa using this
      have e1 : min ((u.getD k false).toNat * 2 ^ k) G.cap = (u.getD k false).toNat * 2 ^ k := by
        rw [pow_succ] at hpow; omega
      have e2 : min (bitsValue (u.take k) + (u.getD k false).toNat * 2 ^ k) G.cap =
          bitsValue (u.take k) + (u.getD k false).toNat * 2 ^ k := by rw [pow_succ] at hpow; omega
      have e3 : min (2 ^ k + 2 ^ k) G.cap = 2 ^ (k + 1) := by rw [pow_succ] at hpow ⊢; omega
      have e4 : min (k + min 1 G.cap) G.cap = k + 1 := by
        rw [hm1]; have : k + 1 < 2 ^ (k + 1) := Nat.lt_two_pow_self
        rw [pow_succ] at hpow this; omega
      rw [evalS_seq, evalS_rd G 4 w hb1]
      simp (config := { decide := true }) only [evalS_seq, evalS_set, evalE, FS.setv_env, Function.update_apply,
        if_true, if_false, wx, wn, wp, hbit, e1, e2, e3, e4, FS.setv_ip]
      rw [evalS_rd G 3 _ (by simp; omega)]
      refine ⟨⟨k + 1, hk', ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
      · simp (config := { decide := true }) [Function.update_apply, bitsValue_take_succ u k hk']
      · simp (config := { decide := true }) [Function.update_apply]
      · simp (config := { decide := true }) [Function.update_apply]
      · have h2 := hbit2
        simp only [FS.setv_env, Function.update_self, FS.setv_ip]
        rw [h2]
      · simp [wi]; ring
      · refine wW.trans ⟨fun j hj => ?_, rfl, rfl, rfl, rfl⟩
        simp only [rdFrameW, List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
        simp [Function.update_apply, hj.1, hj.2.1, hj.2.2.1, hj.2.2.2.1, hj.2.2.2.2]
      · simp (config := { decide := true }) [μ, Function.update_apply, wn]; omega)
  have ht : t = evalS G (.whl (.v 3) (.seq (.rd 4) (.seq (.set 0 (.add (.v 0) (.mul (.v 4) (.v 2))))
      (.seq (.set 2 (.add (.v 2) (.v 2))) (.seq (.set 1 (.add (.v 1) (.k 1))) (.rd 3)))))) (evalS G (.rd 3) s1) := rfl
  rw [ht]
  obtain ⟨⟨k, hk, wx, wn, wp, wm, wi, wW⟩, hc⟩ := hw
  have hku : k = u.length := by
    by_contra h; simp only [evalE, wm, show k < u.length by omega, decide_true, Bool.toNat_true] at hc
    exact absurd hc one_ne_zero
  subst hku
  exact ⟨by rw [wx, List.take_length], wn, wi, wW⟩

/-! ## Bits of a packed word, and the reader of `natWord` -/

/-- The word `w` sits at bit position `p` of the number `D` (bit `i` of `D` is `D / 2^i % 2`). -/
def At (D p : ℕ) (w : List Bool) : Prop := ∀ j < w.length, D / 2 ^ (p + j) % 2 = (w.getD j false).toNat

theorem At.append {D p : ℕ} {w1 w2 : List Bool} (h : At D p (w1 ++ w2)) : At D p w1 ∧ At D (p + w1.length) w2 := by
  constructor
  · intro j hj
    have := h j (by simp; omega)
    rwa [List.getD_append _ _ _ _ hj] at this
  · intro j hj
    have := h (w1.length + j) (by simp; omega)
    rwa [List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left, ← Nat.add_assoc] at this

theorem testBit_bitsValue : ∀ (u : List Bool) (j : ℕ), bitsValue u / 2 ^ j % 2 = (u.getD j false).toNat
  | [], j => by simp [bitsValue]
  | b :: u, 0 => by cases b <;> simp [bitsValue] <;> omega
  | b :: u, j + 1 => by
    rw [pow_succ', ← Nat.div_div_eq_div_mul]
    have : (b.toNat + 2 * bitsValue u) / 2 = bitsValue u := by cases b <;> simp <;> omega
    simp only [bitsValue, List.getD_cons_succ]
    rw [this, testBit_bitsValue u j]

/-- A word sits at position `0` of its own value. -/
theorem At.self (u : List Bool) : At (bitsValue u) 0 u := fun j _ => by rw [Nat.zero_add]; exact testBit_bitsValue u j

/-- The bit of `D` at the cursor (`D` in variable `10`, the cursor in `14`). -/
def bitE : E := .md (.shr (.v 10) (.v 14)) (.k 2)

/-- The leading ones of `natWord v`: count them in `6`. -/
def pNatOnes : S := .whl (.eq bitE (.k 1)) (.seq (.set 6 (.add (.v 6) (.k 1))) (.set 14 (.add (.v 14) (.k 1))))

/-- The `ℓ` value bits: accumulate in `5` (place value in `8`). -/
def pNatBits : S :=
  .loop 9 (.v 6) (.seq (.set 5 (.add (.v 5) (.mul bitE (.v 8)))) (.seq (.set 8 (.add (.v 8) (.v 8)))
    (.set 14 (.add (.v 14) (.k 1)))))

/-- Read `natWord v` at the cursor: variable `5 := v`, the cursor moves past it (scratch `6, 8, 9`). -/
def pNat : S :=
  .seq (.set 5 (.k 0)) (.seq (.set 6 (.k 0)) (.seq pNatOnes (.seq (.set 14 (.add (.v 14) (.k 1)))
    (.seq (.set 8 (.k 1)) pNatBits))))

def pNatW : List Var := [5, 6, 8, 9, 14]

theorem mod_two_pow_succ' (v j : ℕ) : v % 2 ^ (j + 1) = v % 2 ^ j + (v.testBit j).toNat * 2 ^ j := by
  rw [Nat.mod_pow_succ, Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (v / 2 ^ j) with h | h <;> simp [h] <;> ring

/-- **The reader of `natWord`.** -/
theorem pNat_spec (s : FS) (v p : ℕ) (hat : At (s.env 10) p (natWord v)) (hp : s.env 14 = p)
    (hcap : p + (natWord v).length + 2 * 2 ^ natBitLength v ≤ G.cap) (hN : natBitLength v + 1 ≤ G.N) :
    let t := evalS G pNat s
    t.env 5 = v ∧ t.env 14 = p + (natWord v).length ∧ Wr pNatW s t := by
  intro t
  set ℓ := natBitLength v with hℓ
  have hlw := natWord_length v
  have hvl : v < 2 ^ ℓ := lt_natBitLength v
  have hc2 : min 2 G.cap = 2 := by have := Nat.one_le_two_pow (n := ℓ); omega
  have hc1 : min 1 G.cap = 1 := by omega
  have hc0 : min 0 G.cap = 0 := by omega
  -- the bit at position `p + j` of the word
  have hbit : ∀ (w : FS) (j : ℕ), w.env 10 = s.env 10 → w.env 14 = p + j → j < (natWord v).length →
      evalE G w bitE = ((natWord v).getD j false).toNat := by
    intro w j h10 h14 hj
    simp only [bitE, evalE, h10, h14, hc2]
    exact hat j hj
  -- phase 1: the leading ones
  set s1 := (s.setv 5 (min 0 G.cap)).setv 6 (min 0 G.cap) with hs1
  let P : FS → Prop := fun w => ∃ k ≤ ℓ, w.env 6 = k ∧ w.env 14 = p + k ∧ w.env 5 = 0 ∧ Wr pNatW s w
  have hP0 : P s1 := ⟨0, Nat.zero_le _, by simp [s1, hc0], by simp [s1, hp], by
    simp (config := { decide := true }) [s1, Function.update_apply, hc0],
    (Wr.setv s (by decide) _).trans (Wr.setv _ (by decide) _)⟩
  have hw := whl_inv G (c := .eq bitE (.k 1)) (body := .seq (.set 6 (.add (.v 6) (.k 1)))
      (.set 14 (.add (.v 14) (.k 1)))) P (fun w => ℓ - w.env 6) s1 hP0 (by omega) (by
    rintro w ⟨k, hk, w6, w14, w5, wW⟩ hc
    have h10 : w.env 10 = s.env 10 := wW.env 10 (by decide)
    have hk' : k < ℓ := by
      rcases Nat.lt_or_ge k ℓ with h | h
      · exact h
      · have hkl : k = ℓ := by omega
        have := hbit w k h10 w14 (by omega)
        rw [hkl, natWord_zero] at this
        simp only [evalE, this, hc1] at hc; simp at hc
    have e6 : min (k + 1) G.cap = k + 1 := by omega
    have e14 : min (p + k + 1) G.cap = p + k + 1 := by omega
    simp (config := { decide := true }) only [evalS_seq, evalS_set, evalE, FS.setv_env, Function.update_apply,
      if_true, if_false, w6, w14, hc1, e6, e14]
    refine ⟨⟨k + 1, hk', by simp, by simp; ring, by simp [w5], wW.trans ((Wr.setv _ (by decide) _).trans
      (Wr.setv _ (by decide) _))⟩, by omega⟩)
  obtain ⟨⟨k, hk, w6, w14, w5, wW⟩, hc⟩ := hw
  set s2 := evalS G (.whl (.eq bitE (.k 1)) (.seq (.set 6 (.add (.v 6) (.k 1)))
      (.set 14 (.add (.v 14) (.k 1))))) s1 with hs2
  have h10 : s2.env 10 = s.env 10 := wW.env 10 (by decide)
  have hkl : k = ℓ := by
    by_contra h
    have := hbit s2 k h10 w14 (by omega)
    rw [natWord_one v k (by omega)] at this
    simp only [evalE, this, hc1] at hc; simp at hc
  subst hkl
  -- phase 2: skip the `0`, then the bits
  set s3 := (s2.setv 14 (min (s2.env 14 + min 1 G.cap) G.cap)).setv 8 (min 1 G.cap) with hs3
  have s3_14 : s3.env 14 = p + ℓ + 1 := by simp (config := { decide := true }) [s3, Function.update_apply, w14, hc1]; omega
  have s3_8 : s3.env 8 = 1 := by simp [s3, hc1]
  have s3_6 : s3.env 6 = ℓ := by simp (config := { decide := true }) [s3, Function.update_apply, w6]
  have s3_5 : s3.env 5 = 0 := by simp (config := { decide := true }) [s3, Function.update_apply, w5]
  have s3W : Wr pNatW s s3 := wW.trans ((Wr.setv _ (by decide) _).trans (Wr.setv _ (by decide) _))
  have hmin : min (evalE G s3 (.v 6)) G.N = ℓ := by simp only [evalE, s3_6]; omega
  have hl := loop_inv G (i := 9) (n := .v 6) (body := .seq (.set 5 (.add (.v 5) (.mul bitE (.v 8))))
      (.seq (.set 8 (.add (.v 8) (.v 8))) (.set 14 (.add (.v 14) (.k 1)))))
    (s := s3) (fun j w => w.env 5 = v % 2 ^ j ∧ w.env 8 = 2 ^ j ∧ w.env 14 = p + ℓ + 1 + j ∧ Wr pNatW s w)
    ⟨by rw [s3_5, pow_zero, Nat.mod_one], by rw [s3_8, pow_zero], by rw [s3_14, Nat.add_zero], s3W⟩ (by
      rw [hmin]
      rintro j hj w ⟨w5, w8, w14, wW⟩
      have h10 : (w.setv 9 j).env 10 = s.env 10 := by simp; exact wW.env 10 (by decide)
      have hb := hbit (w.setv 9 j) (ℓ + 1 + j) h10 (by simp [w14]; ring) (by omega)
      rw [natWord_bit v j (by omega)] at hb
      have hpow : 2 ^ (j + 1) ≤ 2 ^ ℓ := Nat.pow_le_pow_right (by norm_num) hj
      have hb01 := bool_toNat_le (v.testBit j)
      have hmul : (v.testBit j).toNat * 2 ^ j ≤ 2 ^ j := by
        have := Nat.mul_le_mul_right (2 ^ j) hb01; simpa using this
      have hvj : v % 2 ^ j < 2 ^ j := Nat.mod_lt _ (by positivity)
      rw [pow_succ] at hpow
      have e1 : min ((v.testBit j).toNat * 2 ^ j) G.cap = (v.testBit j).toNat * 2 ^ j := by omega
      have e2 : min (v % 2 ^ j + (v.testBit j).toNat * 2 ^ j) G.cap = v % 2 ^ j + (v.testBit j).toNat * 2 ^ j := by
        omega
      have e3 : min (2 ^ j + 2 ^ j) G.cap = 2 ^ (j + 1) := by rw [pow_succ]; omega
      have e4 : min (p + ℓ + 1 + j + 1) G.cap = p + ℓ + 1 + (j + 1) := by omega
      have hb' : evalE G (w.setv 9 j) bitE = (v.testBit j).toNat := hb
      simp only [evalS_seq, evalS_set]
      simp (config := { decide := true }) only [evalE, hb', FS.setv_env, Function.update_apply, if_true, if_false]
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp (config := { decide := true }) only [Function.update_apply, if_true, if_false, w5, w8, hb', e1, e2]
        rw [mod_two_pow_succ']
      · simp (config := { decide := true }) only [Function.update_apply, if_true, if_false, w8, e3]
      · simp (config := { decide := true }) only [Function.update_apply, if_true, if_false, w14, hc1, e4]
      · exact (wW.trans (Wr.setv _ (by decide) _)).trans (((Wr.setv _ (by decide) _).trans (Wr.setv _ (by decide) _)).trans
          (Wr.setv _ (by decide) _)))
  rw [hmin] at hl
  obtain ⟨t5, -, t14, tW⟩ := hl
  have ht : t = evalS G (.loop 9 (.v 6) (.seq (.set 5 (.add (.v 5) (.mul bitE (.v 8))))
      (.seq (.set 8 (.add (.v 8) (.v 8))) (.set 14 (.add (.v 14) (.k 1)))))) s3 := rfl
  rw [ht]
  exact ⟨t5.trans (Nat.mod_eq_of_lt hvl), by rw [t14, hlw]; ring, tW⟩

end NearCubicGates.Adapters.ShortPCP.Machines.FL
