import Proof.Gates.CheckedPCPP.EmitNat
import Proof.Gates.WordPrograms.RegArith
import Proof.MachineModel.OrdinaryRadixSemantics
import Proof.Gates.PublishedSources.PCPP

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicGates.Close.CheckedPCPP.LitDecode

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicWires.RepairOrdinary.RadixSemantics (value value_append value_lt)
open NearCubicWires.SourceInterfaces

/-! ## Pure facts -/

theorem value_bits (n : ℕ) : value n.bits = n := by
  refine Nat.binaryRec' (by simp [value]) (fun b m hm ih => ?_) n
  rw [Nat.bits_append_bit m b hm]
  simp only [value, ih]
  cases b
  · simp [Nat.bit]
  · simp [Nat.bit]; omega

theorem two_pow_bits_pos (n : ℕ) : 0 < n → 2 ^ n.bits.length ≤ 2 * n := by
  refine Nat.binaryRec' (by simp) (fun b m hm ih => ?_) n
  intro hpos
  rw [Nat.bits_append_bit m b hm, List.length_cons, pow_succ]
  rcases Nat.eq_zero_or_pos m with h0 | h0
  · subst h0; have := hm rfl; subst this; simp [Nat.bit]
  · have := ih h0
    cases b <;> simp [Nat.bit] <;> omega

theorem two_pow_bits_le (n : ℕ) : 2 ^ n.bits.length ≤ 2 * n + 1 := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp
  · have := two_pow_bits_pos n h; omega

/-- The variable index of a literal. -/
def litVar {a : ℕ} : Literal a → ℕ
  | .positive i => i.val
  | .negative i => i.val

/-- The sign of a literal (`1` for a negated literal). -/
def litNeg {a : ℕ} : Literal a → ℕ
  | .positive _ => 0
  | .negative _ => 1

theorem literalCode_eq {a : ℕ} (l : Literal a) : RepairSource.literalCode l = 2 * litVar l + litNeg l := by
  cases l <;> simp [RepairSource.literalCode, litVar, litNeg]

theorem frame_cons (b : Bool) (w : List Bool) : frame (b :: w) = true :: b :: frame w := rfl

theorem frame_length' (w : List Bool) : (frame w).length = 2 * w.length + 1 := by
  induction w with
  | nil => rfl
  | cons b w ih => rw [frame_cons]; simp [ih]; ring

theorem rtb_off (pre r : List Bool) (k : ℕ) : readTapeBit (pre ++ r) (pre.length + k) = readTapeBit r k := by
  induction pre with
  | nil => simp
  | cons a pre ih =>
    rw [List.cons_append, List.length_cons, show pre.length + 1 + k = (pre.length + k) + 1 by omega]
    exact ih

theorem rtb_off0 (pre r : List Bool) : readTapeBit (pre ++ r) pre.length = readTapeBit r 0 := by
  simpa using rtb_off pre r 0

variable {ns nr : ℕ} {cap : ℕ}

/-! ## One marked bit -/

/-- One marked bit `[true, b]` at the head of `s`: `X += b·P`, `P := 2P`, head `+ 2` (`Q`, `T` scratch). -/
def binBody (s : Fin (ns + 1)) (X P Q T : Fin nr) : WMX ns nr :=
  .seq (WMX.fwd s) (.seq (.ifs s (addR P X T) WMX.skip) (.seq (WMX.fwd s) (.seq (addR P Q T) (.wm (WM.move Q P)))))

theorem binBody_exec (s : Fin (ns + 1)) {X P Q T : Fin nr} (hR : [X, P, Q, T].Nodup) (σ : WState ns nr) (b : Bool)
    (hb : readTapeBit (σ.st s) (σ.sh s + 1) = b) (hQ : σ.val Q = 0) (hT : σ.val T = 0)
    (hc1 : σ.val X + b.toNat * σ.val P ≤ cap) (hc2 : 2 * σ.val P ≤ cap) :
    WXExec cap (binBody s X P Q T) σ
      (((σ.seth s (σ.sh s + 2)).setv X (σ.val X + b.toNat * σ.val P)).setv P (2 * σ.val P)) (50 * σ.val P + 20) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true,
    not_false_eq_true] at hR
  obtain ⟨⟨xp, xq, xt⟩, ⟨pq, pt⟩, qt⟩ := hR
  have e1 := WXExec.fwd (cap := cap) s σ
  set σ1 := σ.seth s (σ.sh s + 1) with hσ1
  set σ2 := σ1.setv X (σ.val X + b.toNat * σ.val P) with hσ2
  have e2 : WXExec cap (.ifs s (addR P X T) WMX.skip) σ1 σ2 (18 * σ.val P + 4) := by
    have hw : wbit σ1 s = b := by simp [wbit, hσ1, hb]
    cases b
    · have := WXExec.ifsF (cap := cap) (P := addR P X T) hw (WXExec.skip cap σ1)
      refine WXExec.mono (WXExec.cast cap this ?_ le_rfl) (by omega)
      apply WState.eq <;> try rfl
      funext j; simp [hσ2, hσ1, Function.update_apply]; intro hj; subst hj; rfl
    · have ha := addR_spec cap (Ne.symm xp) pt xt σ1 (by simp [hσ1, hT]) (by simp [hσ1]; simp at hc1; omega)
      have := WXExec.ifsT (cap := cap) (Q := WMX.skip) hw ha
      refine WXExec.mono (WXExec.cast cap this ?_ le_rfl) (by simp [hσ1])
      apply WState.eq <;> try rfl
      funext j; simp [hσ2, hσ1, Function.update_apply, add_comm]
  have e3 := WXExec.fwd (cap := cap) s σ2
  set σ3 := σ2.seth s (σ2.sh s + 1) with hσ3
  have e4 := addR_spec cap pq pt qt σ3 (by simp [hσ3, hσ2, hσ1, Function.update_apply, Ne.symm xt, hT])
    (by simp [hσ3, hσ2, hσ1, Function.update_apply, Ne.symm xq, Ne.symm pq, hQ, xp, Ne.symm xp]; omega)
  set σ4 := σ3.setv Q (σ3.val Q + σ3.val P) with hσ4
  have hP3 : σ3.val P = σ.val P := by simp [hσ3, hσ2, hσ1, Function.update_apply, Ne.symm xp]
  have hQ3 : σ3.val Q = 0 := by simp [hσ3, hσ2, hσ1, Function.update_apply, Ne.symm xq, hQ]
  have e5 := wmove_spec (cap := cap) Q P (Ne.symm pq) (σ.val P) σ4
    (by simp [hσ4, hP3, hQ3]) (by simp [hσ4, hP3, hQ3]; omega)
    (by simp [hσ4, hP3, hQ3, Function.update_apply, pq]; omega)
  have := WXExec.seq e1 (WXExec.seq e2 (WXExec.seq e3 (WXExec.seq e4 (WXExec.wm e5))))
  refine WXExec.mono (WXExec.cast cap this ?_ le_rfl) (by rw [hP3]; omega)
  apply WState.eq
  · funext j; by_cases hj : j = s
    · subst hj; simp [hσ4, hσ3, hσ2, hσ1]; try omega
    · simp [hσ4, hσ3, hσ2, hσ1, Function.update_apply, hj]
  · rfl
  · funext j
    by_cases jP : j = P
    · simp [jP, hσ4, Function.update_apply, Ne.symm pq, pq, hP3, hQ3]; omega
    · by_cases jQ : j = Q
      · simp [jQ, hσ4, Ne.symm xq, pq, Ne.symm pq, hQ]
      · simp [hσ4, hσ3, hσ2, hσ1, Function.update_apply, jP, jQ]
  · rfl

theorem setv_setv (σ : WState ns nr) (r : Fin nr) (a b : ℕ) : (σ.setv r a).setv r b = σ.setv r b := by
  apply WState.eq <;> try rfl
  funext q; simp only [WState.setv_val, Function.update_apply]; split_ifs <;> rfl

/-- `binBody`, then `SC += 2` (the head of `s` moved two cells). -/
def binBodyC (s : Fin (ns + 1)) (X P Q T SC : Fin nr) : WMX ns nr :=
  .seq (binBody s X P Q T) (.seq (WMX.inc SC) (WMX.inc SC))

theorem binBodyC_exec (s : Fin (ns + 1)) {X P Q T SC : Fin nr} (hR : [X, P, Q, T, SC].Nodup) (σ : WState ns nr)
    (b : Bool) (hb : readTapeBit (σ.st s) (σ.sh s + 1) = b) (hQ : σ.val Q = 0) (hT : σ.val T = 0)
    (hc1 : σ.val X + b.toNat * σ.val P ≤ cap) (hc2 : 2 * σ.val P ≤ cap) (hc3 : σ.val SC + 2 ≤ cap) :
    WXExec cap (binBodyC s X P Q T SC) σ
      ((((σ.seth s (σ.sh s + 2)).setv X (σ.val X + b.toNat * σ.val P)).setv P (2 * σ.val P)).setv SC
        (σ.val SC + 2)) (50 * σ.val P + 28) := by
  have hR' := hR
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true,
    not_false_eq_true] at hR'
  obtain ⟨⟨xp, xq, xt, xs⟩, ⟨pq, pt, ps⟩, ⟨qt, qs⟩, ts⟩ := hR'
  have e1 := binBody_exec (cap := cap) s (X := X) (P := P) (Q := Q) (T := T) (by simp [xp, xq, xt, pq, pt, qt]) σ b
    hb hQ hT hc1 hc2
  set σ1 := ((σ.seth s (σ.sh s + 2)).setv X (σ.val X + b.toNat * σ.val P)).setv P (2 * σ.val P) with hσ1
  have h1 : σ1.val SC = σ.val SC := by simp [hσ1, Function.update_apply, Ne.symm xs, Ne.symm ps]
  have e2 := WXExec.inc (cap := cap) SC σ1 (by omega)
  have e3 := WXExec.inc (cap := cap) SC (σ1.setv SC (σ1.val SC + 1)) (by simp; omega)
  refine WXExec.cast cap (WXExec.seq e1 (WXExec.seq e2 e3)) ?_ (by omega)
  simp only [WState.setv_val, Function.update_self, setv_setv, h1]

/-! ## Framed words -/

/-- Read the bits of a frame, low bit first: `X += P · value w`, `P := P · 2^|w|`. -/
def binLoop (s : Fin (ns + 1)) (X P Q T SC : Fin nr) : WMX ns nr := .whs s (binBodyC s X P Q T SC)

theorem binLoop_exec (s : Fin (ns + 1)) {X P Q T SC : Fin nr} (hR : [X, P, Q, T, SC].Nodup) (rest : List Bool)
    (Pm : ℕ) : ∀ (w pre : List Bool) (σ : WState ns nr), RdEq (σ.st s) (pre ++ frame w ++ rest) →
      σ.sh s = pre.length →
      σ.val Q = 0 → σ.val T = 0 → σ.val P * 2 ^ w.length ≤ Pm → σ.val X + σ.val P * value w ≤ cap → 2 * Pm ≤ cap →
      σ.val SC + 2 * w.length ≤ cap →
      WXExec cap (binLoop s X P Q T SC) σ
        ((((σ.seth s (pre.length + 2 * w.length)).setv X (σ.val X + σ.val P * value w)).setv P
          (σ.val P * 2 ^ w.length)).setv SC (σ.val SC + 2 * w.length)) (w.length * (50 * Pm + 30) + 1)
  | [], pre, σ, hst, hsh, _, _, _, _, _, _ => by
    have hw : wbit σ s = false := by
      unfold wbit; rw [hst, hsh]; simp [frame, rtb_off0]; rfl
    have e : (((σ.seth s (pre.length + 2 * ([] : List Bool).length)).setv X (σ.val X + σ.val P * value [])).setv P
        (σ.val P * 2 ^ ([] : List Bool).length)).setv SC (σ.val SC + 2 * ([] : List Bool).length) = σ := by
      simp only [List.length_nil, Nat.mul_zero, Nat.add_zero, value, pow_zero, Nat.mul_one]
      rw [← hsh, wseth_same, wsetv_same, wsetv_same, wsetv_same]
    rw [e]
    unfold binLoop
    exact WXExec.mono (WXExec.whsF hw) (by simp)
  | b :: w, pre, σ, hst, hsh, hQ, hT, hPm, hX, hcap, hSC => by
    have hlen : (b :: w).length = w.length + 1 := rfl
    have hP1 : σ.val P * 2 ^ w.length ≤ Pm := by
      rw [hlen, pow_succ] at hPm; nlinarith [Nat.one_le_two_pow (n := w.length)]
    have hPle : σ.val P ≤ Pm := by
      have := Nat.one_le_two_pow (n := w.length); nlinarith
    have hw : wbit σ s = true := by
      unfold wbit; rw [hst, hsh]; simp [frame, rtb_off0]; rfl
    have hb : readTapeBit (σ.st s) (σ.sh s + 1) = b := by
      rw [hst, hsh]
      rw [show pre ++ frame (b :: w) ++ rest = pre ++ (true :: b :: (frame w ++ rest)) by simp [frame]]
      rw [rtb_off pre _ 1]; rfl
    have hv : value (b :: w) = b.toNat + 2 * value w := rfl
    have hid : σ.val P * value (b :: w) = b.toNat * σ.val P + 2 * (σ.val P * value w) := by rw [hv]; ring
    have hR' := hR
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true,
      not_false_eq_true] at hR'
    obtain ⟨⟨xp, xq, xt, xs⟩, ⟨pq, pt, ps⟩, ⟨qt, qs⟩, ts⟩ := hR'
    have e1 := binBodyC_exec (cap := cap) s hR σ b hb hQ hT (by omega) (by omega) (by rw [hlen] at hSC; omega)
    set σ1 := (((σ.seth s (σ.sh s + 2)).setv X (σ.val X + b.toNat * σ.val P)).setv P (2 * σ.val P)).setv SC
      (σ.val SC + 2) with hσ1
    have ih := binLoop_exec s hR rest Pm w (pre ++ [true, b]) σ1
      (by rw [frame_cons] at hst; simpa [hσ1, Function.update_apply] using hst)
      (by simp [hσ1, hsh])
      (by simp [hσ1, Function.update_apply, Ne.symm pq, Ne.symm xq, qs, hQ])
      (by simp [hσ1, Function.update_apply, Ne.symm pt, Ne.symm xt, ts, hT])
      (by simp [hσ1, Function.update_apply, ps]; rw [hlen, pow_succ] at hPm; nlinarith)
      (by simp [hσ1, Function.update_apply, Ne.symm xp, xp, xs, ps]; nlinarith [hid, hX])
      hcap
      (by simp [hσ1]; rw [hlen] at hSC; omega)
    refine WXExec.mono (WXExec.cast cap (WXExec.whsT hw (WXExec.mono e1 (show 50 * σ.val P + 28 ≤ 50 * Pm + 28 by
      omega)) ih) ?_ le_rfl) (by rw [hlen]; ring_nf; omega)
    apply WState.eq
    · funext j; by_cases hj : j = s
      · simp [hj, hσ1, hsh]; ring
      · simp [hσ1, Function.update_apply, hj]
    · rfl
    · funext j
      by_cases jS : j = SC
      · simp [jS, hσ1, Ne.symm xs, Ne.symm ps]; ring
      · by_cases jP : j = P
        · simp [jP, hσ1, Ne.symm xp, ps, pow_succ]; ring
        · by_cases jX : j = X
          · simp [jX, hσ1, xp, xs, hv, Function.update_apply, ps, Ne.symm ps]; ring
          · simp [hσ1, Function.update_apply, jP, jX, jS]
    · rfl

/-- Read `frame w`: `P := 1`, the loop, skip the end marker, clear `P`; `SC` counts the cells read. -/
def binW (s : Fin (ns + 1)) (X P Q T SC : Fin nr) : WMX ns nr :=
  .seq (WMX.inc P) (.seq (binLoop s X P Q T SC) (.seq (.wm (WM.fwdC s SC)) (.wm (WM.clear P))))

/-- The cost bound of `binW` for a frame of `L` bits. -/
def binCost (L : ℕ) : ℕ := L * (50 * 2 ^ L + 30) + 3 * 2 ^ L + 14

theorem binW_exec (s : Fin (ns + 1)) {X P Q T SC : Fin nr} (hR : [X, P, Q, T, SC].Nodup) (w pre rest : List Bool)
    (σ : WState ns nr) (hst : RdEq (σ.st s) (pre ++ frame w ++ rest)) (hsh : σ.sh s = pre.length)
    (hP : σ.val P = 0) (hQ : σ.val Q = 0) (hT : σ.val T = 0) (hcap : σ.val X + 2 * 2 ^ w.length ≤ cap)
    (hSC : σ.val SC + (frame w).length ≤ cap) :
    WXExec cap (binW s X P Q T SC) σ
      (((σ.seth s (pre.length + (frame w).length)).setv X (σ.val X + value w)).setv SC (σ.val SC + (frame w).length))
      (binCost w.length) := by
  have hR' := hR
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true,
    not_false_eq_true] at hR'
  obtain ⟨⟨xp, xq, xt, xs⟩, ⟨pq, pt, ps⟩, ⟨qt, qs⟩, ts⟩ := hR'
  have hvl := value_lt w
  have h2 := Nat.one_le_two_pow (n := w.length)
  have hfl := frame_length' w
  have e1 := WXExec.inc (cap := cap) P σ (by omega)
  set σ1 := σ.setv P (σ.val P + 1) with hσ1
  have e2 := binLoop_exec (cap := cap) s hR rest (2 ^ w.length) w pre σ1 (by simpa [hσ1] using hst)
    (by simp [hσ1, hsh]) (by simp [hσ1, Function.update_apply, Ne.symm pq, hQ])
    (by simp [hσ1, Function.update_apply, Ne.symm pt, hT]) (by simp [hσ1, hP])
    (by simp [hσ1, hP, Function.update_apply, Ne.symm xp, xp]; omega) (by omega)
    (by simp [hσ1, Function.update_apply, Ne.symm ps]; omega)
  set σ2 := (((σ1.seth s (pre.length + 2 * w.length)).setv X (σ1.val X + σ1.val P * value w)).setv P
    (σ1.val P * 2 ^ w.length)).setv SC (σ1.val SC + 2 * w.length) with hσ2
  have e3 := wfwdC_spec cap s SC σ2 (by simp [hσ2, hσ1, Function.update_apply, Ne.symm ps]; omega)
  set σ3 := (σ2.seth s (σ2.sh s + 1)).setv SC (σ2.val SC + 1) with hσ3
  have e4 := wclear_spec (cap := cap) P (2 ^ w.length) σ3 (by simp [hσ3, hσ2, hσ1, hP, ps])
    (by simp [hσ3, hσ2, hσ1, hP, ps]; omega)
  have := WXExec.seq e1 (WXExec.seq e2 (WXExec.seq (WXExec.wm e3) (WXExec.wm e4)))
  refine WXExec.mono (WXExec.cast cap this ?_ le_rfl) (by unfold binCost; omega)
  apply WState.eq
  · funext j; by_cases hj : j = s
    · simp [hj, hσ3, hσ2, hσ1, frame_length']; omega
    · simp [hσ3, hσ2, hσ1, Function.update_apply, hj]
  · rfl
  · funext j
    by_cases jP : j = P
    · simp [jP, hσ3, hσ2, hσ1, Ne.symm xp, ps, hP]
    · by_cases jS : j = SC
      · simp [jS, hσ3, hσ2, hσ1, Ne.symm xs, Ne.symm ps, frame_length']; omega
      · by_cases jX : j = X
        · simp [jX, hσ3, hσ2, hσ1, xp, xs, hP, Function.update_apply, Ne.symm xp]
        · simp [hσ3, hσ2, hσ1, Function.update_apply, jP, jX, jS]
  · rfl

/-! ## A counted run of marked bits -/

/-- Read `K` marked bits, low bit first: `X += P · value w`, `P := P · 2^|w|`, `K := 0`, `SC += 2|w|`. -/
def binKLoop (s : Fin (ns + 1)) (K X P Q T SC : Fin nr) : WMX ns nr :=
  .whr K (.seq (WMX.dec K) (binBodyC s X P Q T SC))

theorem binKLoop_exec (s : Fin (ns + 1)) {K X P Q T SC : Fin nr} (hR : [K, X, P, Q, T, SC].Nodup) (rest : List Bool)
    (Pm : ℕ) : ∀ (w pre : List Bool) (σ : WState ns nr), RdEq (σ.st s) (pre ++ Streaming.marks w ++ rest) →
      σ.sh s = pre.length → σ.val K = w.length → w.length ≤ cap →
      σ.val Q = 0 → σ.val T = 0 → σ.val P * 2 ^ w.length ≤ Pm → σ.val X + σ.val P * value w ≤ cap → 2 * Pm ≤ cap →
      σ.val SC + 2 * w.length ≤ cap →
      WXExec cap (binKLoop s K X P Q T SC) σ
        (((((σ.seth s (pre.length + 2 * w.length)).setv X (σ.val X + σ.val P * value w)).setv P
          (σ.val P * 2 ^ w.length)).setv SC (σ.val SC + 2 * w.length)).setv K 0) (w.length * (50 * Pm + 32) + 1)
  | [], pre, σ, hst, hsh, hK, _, _, _, _, _, _, _ => by
    have e : ((((σ.seth s (pre.length + 2 * ([] : List Bool).length)).setv X (σ.val X + σ.val P * value [])).setv P
        (σ.val P * 2 ^ ([] : List Bool).length)).setv SC (σ.val SC + 2 * ([] : List Bool).length)).setv K 0 = σ := by
      simp only [List.length_nil, Nat.mul_zero, Nat.add_zero, value, pow_zero, Nat.mul_one]
      rw [← hsh, wseth_same, wsetv_same, wsetv_same, wsetv_same]
      have hK0 : σ.val K = 0 := by simpa using hK
      rw [← hK0]; exact wsetv_same σ K
    rw [e]
    unfold binKLoop
    exact WXExec.mono (WXExec.whrF (by simpa using hK)) (by simp)
  | b :: w, pre, σ, hst, hsh, hK, hKc, hQ, hT, hPm, hX, hcap, hSC => by
    have hR' := hR
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true,
      not_false_eq_true] at hR'
    obtain ⟨⟨kx, kp, kq, kt, ks⟩, ⟨xp, xq, xt, xs⟩, ⟨pq, pt, ps⟩, ⟨qt, qs⟩, ts⟩ := hR'
    have hlen : (b :: w).length = w.length + 1 := rfl
    have hP1 : σ.val P * 2 ^ w.length ≤ Pm := by
      rw [hlen, pow_succ] at hPm; nlinarith [Nat.one_le_two_pow (n := w.length)]
    have hPle : σ.val P ≤ Pm := by
      have := Nat.one_le_two_pow (n := w.length); nlinarith
    have hv : value (b :: w) = b.toNat + 2 * value w := rfl
    have hid : σ.val P * value (b :: w) = b.toNat * σ.val P + 2 * (σ.val P * value w) := by rw [hv]; ring
    have e0 := WXExec.dec (cap := cap) K σ (by omega)
    set σ0 := σ.setv K (σ.val K - 1) with hσ0
    have hb : readTapeBit (σ0.st s) (σ0.sh s + 1) = b := by
      simp only [hσ0, WState.setv_st, WState.setv_sh]
      rw [hst, hsh]
      rw [show pre ++ Streaming.marks (b :: w) ++ rest = pre ++ (true :: b :: (Streaming.marks w ++ rest)) by
        simp [Streaming.marks]]
      rw [rtb_off pre _ 1]; rfl
    have hP0 : σ0.val P = σ.val P := by simp [hσ0, Function.update_apply, Ne.symm kp]
    have hX0 : σ0.val X = σ.val X := by simp [hσ0, Function.update_apply, Ne.symm kx]
    have hS0 : σ0.val SC = σ.val SC := by simp [hσ0, Function.update_apply, Ne.symm ks]
    have e1 := binBodyC_exec (cap := cap) s (X := X) (P := P) (Q := Q) (T := T) (SC := SC)
      (by simp [xp, xq, xt, xs, pq, pt, ps, qt, qs, ts])
      σ0 b hb (by simp [hσ0, Function.update_apply, Ne.symm kq, hQ]) (by simp [hσ0, Function.update_apply, Ne.symm kt, hT])
      (by rw [hX0, hP0]; omega) (by rw [hP0]; omega) (by rw [hS0]; rw [hlen] at hSC; omega)
    set σ1 := (((σ0.seth s (σ0.sh s + 2)).setv X (σ0.val X + b.toNat * σ0.val P)).setv P (2 * σ0.val P)).setv SC
      (σ0.val SC + 2) with hσ1
    have ih := binKLoop_exec s hR rest Pm w (pre ++ [true, b]) σ1
      (by simp only [hσ1, hσ0, WState.setv_st, WState.seth_st, Function.update_self]
          have : pre ++ Streaming.marks (b :: w) ++ rest = (pre ++ [true, b]) ++ Streaming.marks w ++ rest := by
            simp [Streaming.marks]
          rw [this] at hst; simpa using hst)
      (by simp [hσ1, hσ0, hsh])
      (by simp [hσ1, hσ0, Function.update_apply, kx, kp, ks, hK])
      (by omega)
      (by simp [hσ1, hσ0, Function.update_apply, Ne.symm pq, Ne.symm xq, Ne.symm kq, qs, hQ])
      (by simp [hσ1, hσ0, Function.update_apply, Ne.symm pt, Ne.symm xt, Ne.symm kt, ts, hT])
      (by simp [hσ1, Function.update_apply, ps, hP0]; rw [hlen, pow_succ] at hPm; nlinarith)
      (by simp [hσ1, Function.update_apply, Ne.symm xp, xp, xs, ps, hP0, hX0]; nlinarith [hid, hX])
      hcap
      (by simp [hσ1, hS0]; rw [hlen] at hSC; omega)
    refine WXExec.mono (WXExec.cast cap (WXExec.whrT (by omega) (WXExec.seq e0 (WXExec.mono e1
      (show 50 * σ0.val P + 28 ≤ 50 * Pm + 28 by omega))) ih) ?_ le_rfl) (by rw [hlen]; ring_nf; omega)
    apply WState.eq
    · funext j; by_cases hj : j = s
      · simp [hj, hσ1, hσ0, hsh]; ring
      · simp [hσ1, hσ0, Function.update_apply, hj]
    · rfl
    · funext j
      by_cases jK : j = K
      · simp [jK, hσ1, hσ0, kx, kp, ks]
      · by_cases jS : j = SC
        · simp [jS, hσ1, hσ0, Ne.symm xs, Ne.symm ps, Ne.symm ks, Function.update_apply]; ring
        · by_cases jP : j = P
          · simp [jP, hσ1, hσ0, Ne.symm xp, Ne.symm kp, kp, ps, pow_succ, Function.update_apply]; ring
          · by_cases jX : j = X
            · simp [jX, hσ1, hσ0, xp, kx, xs, Ne.symm kx, hv, Function.update_apply, Ne.symm kp, ps]; ring
            · simp [hσ1, hσ0, Function.update_apply, jP, jX, jK, jS]
    · rfl

/-- Read `K` marked bits: `P := 1`, the loop, clear `P`. -/
def binK (s : Fin (ns + 1)) (K X P Q T SC : Fin nr) : WMX ns nr :=
  .seq (WMX.inc P) (.seq (binKLoop s K X P Q T SC) (.wm (WM.clear P)))

/-- The cost bound of `binK` for `L` bits. -/
def binKCost (L : ℕ) : ℕ := L * (50 * 2 ^ L + 32) + 3 * 2 ^ L + 10

/-- **`binK`**: from `marks w` at the head of `s` and `K = |w|`: `X += value w`, the head past `marks w`, `K := 0`,
`SC += 2|w|`. -/
theorem binK_exec (s : Fin (ns + 1)) {K X P Q T SC : Fin nr} (hR : [K, X, P, Q, T, SC].Nodup)
    (w pre rest : List Bool)
    (σ : WState ns nr) (hst : RdEq (σ.st s) (pre ++ Streaming.marks w ++ rest)) (hsh : σ.sh s = pre.length)
    (hK : σ.val K = w.length) (hP : σ.val P = 0) (hQ : σ.val Q = 0) (hT : σ.val T = 0)
    (hcap : σ.val X + 2 * 2 ^ w.length ≤ cap) (hSC : σ.val SC + 2 * w.length ≤ cap) :
    WXExec cap (binK s K X P Q T SC) σ
      ((((σ.seth s (pre.length + 2 * w.length)).setv X (σ.val X + value w)).setv SC (σ.val SC + 2 * w.length)).setv
        K 0) (binKCost w.length) := by
  have hR' := hR
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true,
    not_false_eq_true] at hR'
  obtain ⟨⟨kx, kp, kq, kt, ks⟩, ⟨xp, xq, xt, xs⟩, ⟨pq, pt, ps⟩, ⟨qt, qs⟩, ts⟩ := hR'
  have hvl := value_lt w
  have h2 := Nat.one_le_two_pow (n := w.length)
  have hwl : w.length < 2 ^ w.length := Nat.lt_two_pow_self
  have e1 := WXExec.inc (cap := cap) P σ (by omega)
  set σ1 := σ.setv P (σ.val P + 1) with hσ1
  have e2 := binKLoop_exec (cap := cap) s hR rest (2 ^ w.length) w pre σ1 (by simpa [hσ1] using hst)
    (by simp [hσ1, hsh]) (by simp [hσ1, Function.update_apply, kp, hK]) (by omega)
    (by simp [hσ1, Function.update_apply, Ne.symm pq, hQ])
    (by simp [hσ1, Function.update_apply, Ne.symm pt, hT]) (by simp [hσ1, hP])
    (by simp [hσ1, hP, Function.update_apply, Ne.symm xp, xp]; omega) (by omega)
    (by simp [hσ1, Function.update_apply, Ne.symm ps]; omega)
  set σ2 := ((((σ1.seth s (pre.length + 2 * w.length)).setv X (σ1.val X + σ1.val P * value w)).setv P
    (σ1.val P * 2 ^ w.length)).setv SC (σ1.val SC + 2 * w.length)).setv K 0 with hσ2
  have e4 := wclear_spec (cap := cap) P (2 ^ w.length) σ2 (by simp [hσ2, hσ1, hP, Ne.symm kp, ps])
    (by simp [hσ2, hσ1, hP, Ne.symm kp, ps]; omega)
  have := WXExec.seq e1 (WXExec.seq e2 (WXExec.wm e4))
  refine WXExec.mono (WXExec.cast cap this ?_ le_rfl) (by unfold binKCost; omega)
  apply WState.eq
  · funext j; by_cases hj : j = s
    · simp [hj, hσ2, hσ1]
    · simp [hσ2, hσ1, Function.update_apply, hj]
  · rfl
  · funext j
    by_cases jP : j = P
    · simp [jP, hσ2, hσ1, Ne.symm xp, kp, Ne.symm kp, ps, hP]
    · by_cases jK : j = K
      · simp [jK, hσ2, hσ1, kp, kx, ks]
      · by_cases jS : j = SC
        · simp [jS, hσ2, hσ1, Ne.symm ps, Ne.symm ks, Ne.symm xs, Function.update_apply]
        · by_cases jX : j = X
          · simp [jX, hσ2, hσ1, xp, xs, hP, Function.update_apply, Ne.symm xp, kx, Ne.symm kx]
          · simp [hσ2, hσ1, Function.update_apply, jP, jX, jK, jS]
  · rfl

/-! ## The literal decoder -/

/-- Decode `frame (literalCode l).bits`: `V += (literalVar l).val`, `NEG := [l negative]` (`X` the code, scratch;
`SC` counts the cells read). -/
def litW (s : Fin (ns + 1)) (X P Q T SC V NEG : Fin nr) : WMX ns nr :=
  .seq (binW s X P Q T SC) (EmitNat.halve X V NEG)

/-- The cost bound of `litW` for a code `c`. -/
def litCost (c : ℕ) : ℕ := binCost c.bits.length + 1 + (5 * c + 9)

theorem litW_exec (s : Fin (ns + 1)) {X P Q T SC V NEG : Fin nr} (hR : [X, P, Q, T, SC, V, NEG].Nodup) {a : ℕ}
    (l : Literal a) (pre rest : List Bool) (σ : WState ns nr)
    (hst : RdEq (σ.st s) (pre ++ frame (RepairSource.literalCode l).bits ++ rest)) (hsh : σ.sh s = pre.length)
    (hX : σ.val X = 0) (hP : σ.val P = 0) (hQ : σ.val Q = 0) (hT : σ.val T = 0) (hV : σ.val V = 0)
    (hN : σ.val NEG = 0) (hcap : 4 * RepairSource.literalCode l + 4 ≤ cap)
    (hSC : σ.val SC + (frame (RepairSource.literalCode l).bits).length ≤ cap) :
    WXExec cap (litW s X P Q T SC V NEG) σ
      ((((σ.seth s (pre.length + (frame (RepairSource.literalCode l).bits).length)).setv SC
        (σ.val SC + (frame (RepairSource.literalCode l).bits).length)).setv V (litVar l)).setv NEG
        (litNeg l)) (litCost (RepairSource.literalCode l)) := by
  have hR' := hR
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true,
    not_false_eq_true] at hR'
  obtain ⟨⟨xp, xq, xt, xs, xv, xn⟩, ⟨pq, pt, ps, pv, pn⟩, ⟨qt, qs, qv, qn⟩, ⟨ts, tv, tn⟩, ⟨sv, sn⟩, vn⟩ := hR'
  set c := RepairSource.literalCode l with hc
  have hb := two_pow_bits_le c
  have e1 := binW_exec (cap := cap) s (X := X) (P := P) (Q := Q) (T := T) (SC := SC)
    (by simp [xp, xq, xt, xs, pq, pt, ps, qt, qs, ts]) c.bits pre rest σ hst hsh hP hQ hT (by rw [hX]; omega) hSC
  rw [value_bits, hX, Nat.zero_add] at e1
  set σ1 := ((σ.seth s (pre.length + (frame c.bits).length)).setv X c).setv SC (σ.val SC + (frame c.bits).length)
    with hσ1
  have e2 := EmitNat.halve_exec (cap := cap) X V NEG xv xn vn c σ1 (by simp [hσ1, Function.update_apply, xs])
    (by simp [hσ1, Function.update_apply, Ne.symm xn, Ne.symm sn, hN])
    (by simp [hσ1, Function.update_apply, Ne.symm xv, Ne.symm sv, hV]; omega)
    (by omega) (by omega)
  refine WXExec.cast cap (WXExec.seq e1 e2) ?_ (by unfold litCost; rfl)
  have hc2 : c = 2 * litVar l + litNeg l := literalCode_eq l
  have hn : litNeg l ≤ 1 := by cases l <;> simp [litNeg]
  apply WState.eq
  · rfl
  · rfl
  · funext j
    simp only [hσ1, WState.setv_val, WState.seth_val, Function.update_apply]
    by_cases jN : j = NEG
    · subst jN; simp [hc2, Ne.symm sn, Ne.symm vn]; omega
    · by_cases jV : j = V
      · subst jV; simp [jN, Ne.symm xv, Ne.symm sv, hV, hc2]; omega
      · by_cases jX : j = X
        · subst jX; simp [jN, jV, hX, xs]
        · by_cases jS : j = SC
          · subst jS; simp [jN, jV, jX]
          · simp [jN, jV, jX, jS]
  · rfl

theorem bits_len_le (n : ℕ) : n.bits.length ≤ n := by
  rw [Nat.size_eq_bits_len, Nat.size_le]; exact Nat.lt_two_pow_self

theorem binCost_le (n : ℕ) : binCost n.bits.length ≤ 200 * (n + 1) ^ 2 := by
  have hL := bits_len_le n
  have h2 := two_pow_bits_le n
  unfold binCost
  have := Nat.mul_le_mul hL (Nat.add_le_add_right (Nat.mul_le_mul_left 50 h2) 30)
  nlinarith

theorem litCost_le (c : ℕ) : litCost c ≤ 300 * (c + 1) ^ 2 := by
  have := binCost_le c
  unfold litCost
  nlinarith

end NearCubicGates.Close.CheckedPCPP.LitDecode
