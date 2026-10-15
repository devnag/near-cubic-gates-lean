import Proof.Wire_3_5.FinalPassWordLib
import Proof.Wire_3_5.FinalPassHashTable
import Proof.Wire_3_5.UnionMachineRoundParse
import Proof.Wire_3_5.UnionCodec
import Proof.Foundations.OrdinaryStreaming

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.PrimAsm.ParseNat
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.RepairOrdinary.Streaming (marks)

/-! ## Reading inside a framed word -/

theorem read_pre (pre T : List Bool) (j : ℕ) : readTapeBit (pre ++ T) (pre.length + j) = readTapeBit T j := by
  unfold readTapeBit
  rw [List.getD_append_right _ _ _ _ (by omega)]
  congr 1
  omega

theorem marks_cons (b : Bool) (w : List Bool) : marks (b :: w) = true :: b :: marks w := by
  simp [marks]

/-- The payload cell of the `k`-th logical bit. -/
theorem read_marks_bit (rest : List Bool) :
    ∀ (w : List Bool) (k : ℕ), k < w.length → readTapeBit (marks w ++ rest) (2 * k + 1) = w.getD k false
  | [], k, hk => absurd hk (by simp)
  | b :: w, 0, _ => by simp [marks_cons, readTapeBit]
  | b :: w, k + 1, hk => by
    have ih := read_marks_bit rest w k (by simp at hk; omega)
    rw [marks_cons]
    unfold readTapeBit at ih ⊢
    have e : 2 * (k + 1) + 1 = (2 * k + 1) + 2 := by ring
    rw [e]
    simpa using ih

/-- The marker cell of the `k`-th logical bit. -/
theorem read_marks_mark (rest : List Bool) :
    ∀ (w : List Bool) (k : ℕ), k < w.length → readTapeBit (marks w ++ rest) (2 * k) = true
  | [], k, hk => absurd hk (by simp)
  | b :: w, 0, _ => by simp [marks_cons, readTapeBit]
  | b :: w, k + 1, hk => by
    have ih := read_marks_mark rest w k (by simp at hk; omega)
    rw [marks_cons]
    unfold readTapeBit at ih ⊢
    have e : 2 * (k + 1) = 2 * k + 2 := by ring
    rw [e]
    simpa using ih

/-! ## The bits of `natWord x` -/

theorem natWord_eq (x : ℕ) : RepairRepresentation.natWord x =
    List.replicate (natBitLength x) true ++ false ::
      WilliamsPublishedForm.fixedWidthNatBits (natBitLength x) x := rfl

theorem natWord_length (x : ℕ) : (RepairRepresentation.natWord x).length = 2 * natBitLength x + 1 := by
  rw [natWord_eq]
  simp [WilliamsPublishedForm.fixedWidthNatBits]
  ring

theorem natWord_getD_one (x k : ℕ) (hk : k < natBitLength x) :
    (RepairRepresentation.natWord x).getD k false = true := by
  rw [natWord_eq, List.getD_append _ _ _ _ (by simpa using hk)]
  simp [hk]

theorem natWord_getD_zero (x : ℕ) : (RepairRepresentation.natWord x).getD (natBitLength x) false = false := by
  rw [natWord_eq, List.getD_append_right _ _ _ _ (by simp)]
  simp

/-! ## Framed and raw words

A field sits on its stream either FRAMED (`marks w`: a marker cell `true` before each bit; the estimator's input tape and
the union machine's tables) or RAW (`w`: a word function's output tape). A logical bit takes `stp ε` cells, its payload
cell is at offset `off ε`. -/

/-- The cells per logical bit: `2` framed, `1` raw. -/
def stp (ε : Bool) : ℕ := if ε then 2 else 1

/-- The offset of a logical bit's payload cell: `1` framed (after its marker), `0` raw. -/
def off (ε : Bool) : ℕ := if ε then 1 else 0

theorem stp_eq (ε : Bool) : stp ε = off ε + 1 := by cases ε <;> rfl
theorem off_le (ε : Bool) : off ε ≤ 1 := by cases ε <;> simp [off]

/-- A word as it sits on a stream: framed (`marks w`) or raw (`w`). -/
def enc (ε : Bool) (w : List Bool) : List Bool := if ε then marks w else w

theorem enc_length (ε : Bool) (w : List Bool) : (enc ε w).length = stp ε * w.length := by
  cases ε <;> simp [enc, stp, marks] <;> ring

theorem read_enc_bit (ε : Bool) (rest w : List Bool) (k : ℕ) (hk : k < w.length) :
    readTapeBit (enc ε w ++ rest) (stp ε * k + off ε) = w.getD k false := by
  cases ε with
  | true => exact read_marks_bit rest w k hk
  | false =>
    simp only [enc, stp, off, if_false, Nat.one_mul, Nat.add_zero, Bool.false_eq_true]
    unfold readTapeBit
    exact List.getD_append _ _ _ _ hk

/-! ## Skipping one field -/

variable {ns nr : ℕ} (cap : ℕ)

/-- Step to the payload cell of the current logical bit (framed: past its marker; raw: stay). -/
def preE (ε : Bool) (i : Fin (ns + 1)) : WM ns nr := if ε then .fwd i else .skip

theorem preE_spec (ε : Bool) (i : Fin (ns + 1)) (σ : WState ns nr) :
    WExec cap (preE ε i) σ (σ.seth i (σ.sh i + off ε)) (off ε) := by
  cases ε with
  | true => exact WExec.fwd i σ
  | false =>
    have e : σ.seth i (σ.sh i + off false) = σ := WState.eq (by simp [off]) rfl rfl rfl
    rw [e]
    exact WExec.skip σ

/-- One logical bit of the unary prefix: step to its payload cell; on `1` count it in `c`, on `0` clear the flag `f`;
step to the next logical bit. -/
def unaryBody (ε : Bool) (i : Fin (ns + 1)) (f c : Fin nr) : WM ns nr :=
  .seq (preE ε i) (.ifs i (.seq (.inc c) (.fwd i)) (.seq (.dec f) (.fwd i)))

/-- Skip `c` logical bits, clearing `c`. -/
def skipPairs (ε : Bool) (i : Fin (ns + 1)) (c : Fin nr) : WM ns nr :=
  .whr c (.seq (.dec c) (.seq (preE ε i) (.fwd i)))

/-- **Skip one field** `enc ε (natWord x)`: read its unary prefix into `c` (flag `f`), skip the `0`, then skip the `L`
payload bits. Both registers are `0` again at the end. -/
def skipNatM (ε : Bool) (i : Fin (ns + 1)) (f c : Fin nr) : WM ns nr :=
  .seq (.inc f) (.seq (.whr f (unaryBody ε i f c)) (skipPairs ε i c))

theorem unary_loop (ε : Bool) (i : Fin (ns + 1)) (f c : Fin nr) (hfc : f ≠ c) (hcap1 : 1 ≤ cap) :
    ∀ (r : ℕ) (σ : WState ns nr), σ.val f = 1 →
      (∀ k < r, readTapeBit (σ.st i) (σ.sh i + stp ε * k + off ε) = true) →
      readTapeBit (σ.st i) (σ.sh i + stp ε * r + off ε) = false → σ.val c + r ≤ cap →
      WExec cap (.whr f (unaryBody ε i f c)) σ
        (((σ.seth i (σ.sh i + stp ε * r + stp ε)).setv c (σ.val c + r)).setv f 0) (10 * r + 9)
  | 0, σ, hf, _, hend, _ => by
    have hs := stp_eq ε
    have ho := off_le ε
    have h1 := preE_spec cap ε i σ
    have hb : wbit (σ.seth i (σ.sh i + off ε)) i = false := by
      simpa [wbit] using hend
    have h2 := WExec.dec (cap := cap) f (σ.seth i (σ.sh i + off ε)) (by
      show (σ.seth i (σ.sh i + off ε)).val f ≤ cap
      rw [show (σ.seth i (σ.sh i + off ε)).val f = σ.val f from rfl, hf]; exact hcap1)
    have h3 := WExec.fwd (cap := cap) i ((σ.seth i (σ.sh i + off ε)).setv f ((σ.seth i (σ.sh i + off ε)).val f - 1))
    have hbody := WExec.seq h1 (WExec.ifsF (P := .seq (.inc c) (.fwd i)) hb (WExec.seq h2 h3))
    set τ := ((σ.seth i (σ.sh i + off ε)).setv f ((σ.seth i (σ.sh i + off ε)).val f - 1)).seth i
      (((σ.seth i (σ.sh i + off ε)).setv f ((σ.seth i (σ.sh i + off ε)).val f - 1)).sh i + 1) with hτ
    have hτf : τ.val f = 0 := by simp [τ, hf]
    have hloop := WExec.whrT (by omega) hbody (WExec.whrF (P := unaryBody ε i f c) hτf)
    refine WExec.cast cap hloop ?_ (by omega)
    apply WState.eq
    · funext j
      by_cases hji : j = i
      · subst hji; simp [τ]; omega
      · simp [τ, Function.update_of_ne hji]
    · rfl
    · funext j
      by_cases hjf : j = f
      · subst hjf; simp [τ, hf]
      · by_cases hjc : j = c
        · subst hjc; simp [τ, Function.update_of_ne hjf]
        · simp [τ, Function.update_of_ne hjf]
    · rfl
  | r + 1, σ, hf, hones, hend, hc => by
    have hs := stp_eq ε
    have ho := off_le ε
    have h1 := preE_spec cap ε i σ
    have hb : wbit (σ.seth i (σ.sh i + off ε)) i = true := by
      have := hones 0 (by omega)
      simpa [wbit] using this
    have h2 := WExec.inc (cap := cap) c (σ.seth i (σ.sh i + off ε)) (by simp; omega)
    have h3 := WExec.fwd (cap := cap) i ((σ.seth i (σ.sh i + off ε)).setv c ((σ.seth i (σ.sh i + off ε)).val c + 1))
    have hbody := WExec.seq h1 (WExec.ifsT (Q := .seq (.dec f) (.fwd i)) hb (WExec.seq h2 h3))
    set τ := ((σ.seth i (σ.sh i + off ε)).setv c ((σ.seth i (σ.sh i + off ε)).val c + 1)).seth i
      (((σ.seth i (σ.sh i + off ε)).setv c ((σ.seth i (σ.sh i + off ε)).val c + 1)).sh i + 1) with hτ
    have hτs : τ.sh i = σ.sh i + stp ε := by simp [τ]; omega
    have hτst : τ.st i = σ.st i := by simp [τ]
    have hτf : τ.val f = 1 := by simp [τ, Function.update_of_ne hfc, hf]
    have hτc : τ.val c = σ.val c + 1 := by simp [τ]
    have ih := unary_loop ε i f c hfc hcap1 r τ hτf
      (fun k hk => by
        rw [hτst, hτs]
        have := hones (k + 1) (by omega)
        rw [show σ.sh i + stp ε + stp ε * k + off ε = σ.sh i + stp ε * (k + 1) + off ε by ring]
        exact this)
      (by rw [hτst, hτs, show σ.sh i + stp ε + stp ε * r + off ε = σ.sh i + stp ε * (r + 1) + off ε by ring]
          exact hend)
      (by rw [hτc]; omega)
    have hloop := WExec.whrT (by omega) hbody ih
    refine WExec.cast cap hloop ?_ (by omega)
    apply WState.eq
    · funext j
      by_cases hji : j = i
      · subst hji; simp [τ]; ring_nf; omega
      · simp [τ, Function.update_of_ne hji]
    · rfl
    · funext j
      by_cases hjf : j = f
      · subst hjf; simp [τ]
      · by_cases hjc : j = c
        · subst hjc; simp [τ, Function.update_of_ne hjf]; ring
        · simp [τ, Function.update_of_ne hjf, Function.update_of_ne hjc]
    · rfl

theorem skipPairs_spec (ε : Bool) (i : Fin (ns + 1)) (c : Fin nr) :
    ∀ (r : ℕ) (σ : WState ns nr), σ.val c = r → σ.val c ≤ cap →
      WExec cap (skipPairs ε i c) σ ((σ.setv c 0).seth i (σ.sh i + stp ε * r)) (7 * r + 1)
  | 0, σ, h0, _ => by
    have e : (σ.setv c 0).seth i (σ.sh i + stp ε * 0) = σ := WState.eq (by simp) rfl (by rw [← h0]; simp) rfl
    rw [e]
    exact WExec.whrF h0
  | r + 1, σ, hr, hc => by
    have hs := stp_eq ε
    have ho := off_le ε
    have h1 := WExec.dec (cap := cap) c σ hc
    have h2 := preE_spec cap ε i (σ.setv c (σ.val c - 1))
    have h3 := WExec.fwd (cap := cap) i ((σ.setv c (σ.val c - 1)).seth i ((σ.setv c (σ.val c - 1)).sh i + off ε))
    set τ := ((σ.setv c (σ.val c - 1)).seth i ((σ.setv c (σ.val c - 1)).sh i + off ε)).seth i
      (((σ.setv c (σ.val c - 1)).seth i ((σ.setv c (σ.val c - 1)).sh i + off ε)).sh i + 1) with hτ
    have ih := skipPairs_spec ε i c r τ (by simp [τ]; omega) (by simp [τ]; omega)
    refine WExec.cast cap (WExec.whrT (by omega) (WExec.seq h1 (WExec.seq h2 h3)) ih) ?_ (by omega)
    apply WState.eq
    · funext j
      by_cases hji : j = i
      · subst hji; simp [τ]; ring_nf; omega
      · simp [τ, Function.update_of_ne hji]
    · rfl
    · funext j
      by_cases hjc : j = c
      · subst hjc; simp [τ]
      · simp [τ, Function.update_of_ne hjc]
    · rfl

/-- **Skipping one field**: from the start of `enc ε (natWord x)` (after any prefix `pre`), with the flag and counter
registers at `0` and capacity `≥ natBitLength x + 1`, the head moves past the whole field and nothing else changes. -/
theorem skipNatM_spec (ε : Bool) (i : Fin (ns + 1)) (f c : Fin nr) (hfc : f ≠ c) (x : ℕ) (pre rest : List Bool)
    (σ : WState ns nr) (hst : σ.st i = pre ++ enc ε (RepairRepresentation.natWord x) ++ rest)
    (hsh : σ.sh i = pre.length) (hf : σ.val f = 0) (hc : σ.val c = 0) (hcap : natBitLength x + 1 ≤ cap) :
    WExec cap (skipNatM ε i f c) σ (σ.seth i (pre.length + stp ε * (RepairRepresentation.natWord x).length))
      (20 * natBitLength x + 20) := by
  set L := natBitLength x with hL
  have hf1 := WExec.inc (cap := cap) f σ (by omega)
  set σ1 := σ.setv f (σ.val f + 1) with hσ1
  have hσ1f : σ1.val f = 1 := by simp [σ1, hf]
  have hread : ∀ k, k < (RepairRepresentation.natWord x).length →
      readTapeBit (σ1.st i) (σ1.sh i + stp ε * k + off ε) = (RepairRepresentation.natWord x).getD k false := by
    intro k hk
    have e : σ1.st i = pre ++ (enc ε (RepairRepresentation.natWord x) ++ rest) := by
      simp [σ1, hst, List.append_assoc]
    rw [e, show σ1.sh i = pre.length by simp [σ1, hsh], Nat.add_assoc, read_pre]
    exact read_enc_bit ε rest _ k hk
  have hlen := natWord_length x
  have h2 := unary_loop cap ε i f c hfc (by omega) L σ1 hσ1f
    (fun k hk => by rw [hread k (by omega)]; exact natWord_getD_one x k hk)
    (by rw [hread L (by omega)]; exact natWord_getD_zero x)
    (by simp [σ1, Function.update_of_ne (Ne.symm hfc), hc]; omega)
  set σ2 := ((σ1.seth i (σ1.sh i + stp ε * L + stp ε)).setv c (σ1.val c + L)).setv f 0 with hσ2
  have h3 := skipPairs_spec cap ε i c L σ2 (by simp [σ2, σ1, Function.update_of_ne (Ne.symm hfc), hc])
    (by simp [σ2, σ1, Function.update_of_ne (Ne.symm hfc), hc]; omega)
  refine WExec.cast cap (WExec.seq hf1 (WExec.seq h2 h3)) ?_ (by omega)
  apply WState.eq
  · funext j
    by_cases hji : j = i
    · subst hji; simp [σ2, σ1, hsh, hlen]; ring
    · simp [σ2, σ1, Function.update_of_ne hji]
  · rfl
  · funext j
    by_cases hjf : j = f
    · subst hjf; simp [σ2, σ1, Function.update_of_ne hfc, hf]
    · by_cases hjc : j = c
      · subst hjc; simp [σ2, σ1, Function.update_of_ne hjf, hc]
      · simp [σ2, σ1, Function.update_of_ne hjf, Function.update_of_ne hjc]
  · rfl

/-! ## Reading one framed field into a unary register -/

/-- The payload bits of `natWord x`, read at their logical positions after the `0`. -/
theorem natWord_getD_payload (x m : ℕ) (hm : m < natBitLength x) :
    (RepairRepresentation.natWord x).getD (natBitLength x + 1 + m) false = x.testBit m := by
  rw [natWord_eq, List.getD_append_right _ _ _ _ (by simp only [List.length_replicate]; omega)]
  simp only [List.length_replicate, show natBitLength x + 1 + m - natBitLength x = m + 1 by omega,
    List.getD_cons_succ, WilliamsPublishedForm.fixedWidthNatBits]
  rw [List.getD_eq_getElem _ _ (by simpa using hm)]
  simp

theorem bitsValue_append_single : ∀ (l : List Bool) (b : Bool),
    CanonicalBinary.bitsValue (l ++ [b]) = CanonicalBinary.bitsValue l + b.toNat * 2 ^ l.length
  | [], b => by simp [CanonicalBinary.bitsValue]
  | a :: l, b => by
    simp only [List.cons_append, CanonicalBinary.bitsValue, bitsValue_append_single l b, List.length_cons, pow_succ]
    ring

theorem bitsValue_lt : ∀ (l : List Bool), CanonicalBinary.bitsValue l < 2 ^ l.length
  | [] => by simp [CanonicalBinary.bitsValue]
  | b :: l => by
    have ih := bitsValue_lt l
    simp only [CanonicalBinary.bitsValue, List.length_cons, pow_succ]
    cases b <;> simp <;> omega

theorem bitsValue_take_succ (bs : List Bool) (k : ℕ) (hk : k < bs.length) :
    CanonicalBinary.bitsValue (bs.take (k + 1)) =
      CanonicalBinary.bitsValue (bs.take k) + (bs.getD k false).toNat * 2 ^ k := by
  rw [List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some, bitsValue_append_single,
    List.length_take_of_le hk.le, List.getD_eq_getElem _ _ hk]

/-- `v += p`, with `p` restored through `t`. -/
def addTo (p v t : Fin nr) : WM ns nr := .seq (FinalPass.Hash4.wdup p v t) (WM.move t p)

/-- The doubling loop: `t −= 1`, `p += 2` until `t = 0`. -/
def dblLoop (p t : Fin nr) : WM ns nr := .whr t (.seq (.dec t) (.seq (.inc p) (.inc p)))

/-- `p := 2p`, through `t`. -/
def dbl (p t : Fin nr) : WM ns nr := .seq (WM.move p t) (dblLoop p t)

/-- One payload bit, least significant first: step to its cell, add the power `p` to `v` on `1`, double `p`, step to
the next marker. -/
def bitBody (ε : Bool) (i : Fin (ns + 1)) (v p t : Fin nr) : WM ns nr :=
  .seq (preE ε i) (.seq (.ifs i (addTo p v t) .skip) (.seq (dbl p t) (.fwd i)))

/-- **Read one framed field into `v`** (`v += x`): the unary prefix into `c`, then the `c` payload bits with the power
`p = 2^k` (the counted loop `wloop`); `f, c, p, t` are `0` again at the end. -/
def readNatM (ε : Bool) (i : Fin (ns + 1)) (f c v p t : Fin nr) : WM ns nr :=
  .seq (.inc f) (.seq (.whr f (unaryBody ε i f c))
    (.seq (.inc p) (.seq (.whr c (.seq (.dec c) (bitBody ε i v p t))) (WM.clear p))))

theorem addTo_spec (p v t : Fin nr) (hpv : p ≠ v) (hpt : p ≠ t) (hvt : v ≠ t) (σ : WState ns nr)
    (ht : σ.val t = 0) (hp : σ.val p ≤ cap) (hv : σ.val v + σ.val p ≤ cap) :
    WExec cap (addTo p v t) σ (σ.setv v (σ.val v + σ.val p)) (18 * σ.val p + 3) := by
  have h1 := FinalPass.Hash4.wdup_spec cap p v t hpv hpt hvt (σ.val p) σ rfl hp hv (by omega)
  have h2 := wmove_spec cap t p (Ne.symm hpt) (σ.val p)
    (((σ.setv p 0).setv v (σ.val v + σ.val p)).setv t (σ.val t + σ.val p))
    (by simp [ht]) (by simp [ht]; omega)
    (by simp [Function.update_apply, hpt, hpt.symm, hpv, hpv.symm, ht]; omega)
  refine WExec.cast cap (WExec.seq h1 h2) ?_ (by omega)
  refine WState.eq rfl rfl ?_ rfl
  funext j
  by_cases hjp : j = p
  · subst hjp; simp [Function.update_apply, hpt, hpt.symm, hpv, hpv.symm, ht]
  · by_cases hjt : j = t
    · subst hjt; simp [Function.update_apply, hjp, hvt, hvt.symm, ht]
    · by_cases hjv : j = v
      · subst hjv; simp [Function.update_apply, hjp, hjt]
      · simp [Function.update_apply, hjp, hjt, hjv]

theorem dblLoop_spec (p t : Fin nr) (hpt : p ≠ t) :
    ∀ (m : ℕ) (σ : WState ns nr), σ.val t = m → σ.val t ≤ cap → σ.val p + 2 * m ≤ cap →
      WExec cap (dblLoop p t) σ ((σ.setv t 0).setv p (σ.val p + 2 * m)) (11 * m + 1) := by
  intro m
  induction m with
  | zero =>
    intro σ h0 _ _
    have e : (σ.setv t 0).setv p (σ.val p + 2 * 0) = σ := by
      rw [Nat.mul_zero, Nat.add_zero, ← h0, wsetv_same, wsetv_same]
    rw [e]
    exact WExec.whrF h0
  | succ m ih =>
    intro σ hm ht hp
    have h1 := WExec.dec (cap := cap) t σ ht
    have h2 := WExec.inc (cap := cap) p (σ.setv t (σ.val t - 1))
      (by simp [Function.update_apply, hpt, hpt.symm]; omega)
    have h3 := WExec.inc (cap := cap) p ((σ.setv t (σ.val t - 1)).setv p ((σ.setv t (σ.val t - 1)).val p + 1))
      (by simp [Function.update_apply, hpt, hpt.symm]; omega)
    have h4 := ih (((σ.setv t (σ.val t - 1)).setv p ((σ.setv t (σ.val t - 1)).val p + 1)).setv p
      (((σ.setv t (σ.val t - 1)).setv p ((σ.setv t (σ.val t - 1)).val p + 1)).val p + 1))
      (by simp [Function.update_apply, hpt, hpt.symm]; omega)
      (by simp [Function.update_apply, hpt, hpt.symm]; omega)
      (by simp [Function.update_apply, hpt, hpt.symm]; omega)
    refine WExec.cast cap (WExec.whrT (by omega) (WExec.seq h1 (WExec.seq h2 h3)) h4) ?_ (by omega)
    refine WState.eq rfl rfl ?_ rfl
    funext j
    by_cases hjp : j = p
    · subst hjp; simp [Function.update_apply, hpt, hpt.symm]; omega
    · by_cases hjt : j = t
      · subst hjt; simp [Function.update_apply, hjp]
      · simp [Function.update_apply, hjp, hjt]

theorem dbl_spec (p t : Fin nr) (hpt : p ≠ t) (σ : WState ns nr) (ht : σ.val t = 0) (hp : 2 * σ.val p ≤ cap) :
    WExec cap (dbl p t) σ (σ.setv p (2 * σ.val p)) (18 * σ.val p + 3) := by
  have h1 := wmove_spec cap p t hpt (σ.val p) σ rfl (by omega) (by omega)
  have h2 := dblLoop_spec cap p t hpt (σ.val p) ((σ.setv p 0).setv t (σ.val t + σ.val p))
    (by simp [ht]) (by simp [ht]; omega) (by simp [Function.update_apply, hpt, hpt.symm]; omega)
  refine WExec.cast cap (WExec.seq h1 h2) ?_ (by omega)
  refine WState.eq rfl rfl ?_ rfl
  funext j
  by_cases hjp : j = p
  · subst hjp; simp [Function.update_apply, hpt, hpt.symm] <;> ring
  · by_cases hjt : j = t
    · subst hjt; simp [Function.update_apply, hjp, ht]
    · simp [Function.update_apply, hjp, hjt]

/-- The payload loop's state after `k` bits: the head `2k` cells on, `c = L − k`, `v = v₀ + value(first k bits)`,
`p = 2^k`. -/
def payState (ε : Bool) (σ : WState ns nr) (i : Fin (ns + 1)) (c v p : Fin nr) (L v₀ : ℕ) (bs : List Bool)
    (k : ℕ) : WState ns nr :=
  (((σ.seth i (σ.sh i + stp ε * k)).setv c (L - k)).setv v (v₀ + CanonicalBinary.bitsValue (bs.take k))).setv p (2 ^ k)

/-- **One payload bit** of the counted loop, from `payState k` (with `c` already decremented) to `payState (k+1)`. -/
theorem bitRound_spec (ε : Bool) (i : Fin (ns + 1)) (c v p t : Fin nr) (hcv : c ≠ v) (hcp : c ≠ p) (hct : c ≠ t)
    (hpv : p ≠ v) (hpt : p ≠ t) (hvt : v ≠ t) (σ : WState ns nr) (L v₀ : ℕ) (bs : List Bool) (hbs : bs.length = L)
    (ht : σ.val t = 0) (hread : ∀ m < L, readTapeBit (σ.st i) (σ.sh i + stp ε * m + off ε) = bs.getD m false)
    (hcap : v₀ + 2 ^ (L + 1) ≤ cap) (hval : ∀ k ≤ L, CanonicalBinary.bitsValue (bs.take k) < 2 ^ k)
    (k : ℕ) (hk : k < L) :
    WExec cap (bitBody ε i v p t) ((payState ε σ i c v p L v₀ bs k).setv c (L - k - 1))
      (payState ε σ i c v p L v₀ bs (k + 1)) (36 * 2 ^ L + 12) := by
  have hs := stp_eq ε
  have ho := off_le ε
  have hkL : 2 ^ k ≤ 2 ^ L := Nat.pow_le_pow_right (by norm_num) hk.le
  have hk1L : 2 ^ (k + 1) ≤ 2 ^ L := Nat.pow_le_pow_right (by norm_num) hk
  have hpowL : 2 ^ (L + 1) = 2 * 2 ^ L := by rw [pow_succ]; ring
  have hvk := hval k hk.le
  set T := (payState ε σ i c v p L v₀ bs k).setv c (L - k - 1) with hT
  have hTsh : T.sh i = σ.sh i + stp ε * k := by simp [T, payState]
  have hTst : T.st i = σ.st i := by simp [T, payState]
  have hTv : T.val v = v₀ + CanonicalBinary.bitsValue (bs.take k) := by
    simp [T, payState, Function.update_apply, hcv, hcv.symm, hcp, hcp.symm, hct, hct.symm, hpv, hpv.symm, hpt, hpt.symm, hvt, hvt.symm]
  have hTp : T.val p = 2 ^ k := by simp [T, payState, Function.update_apply, hcv, hcv.symm, hcp, hcp.symm, hct, hct.symm, hpv, hpv.symm, hpt, hpt.symm, hvt, hvt.symm]
  have hTt : T.val t = 0 := by simp [T, payState, Function.update_apply, hcv, hcv.symm, hcp, hcp.symm, hct, hct.symm, hpv, hpv.symm, hpt, hpt.symm, hvt, hvt.symm, ht]
  have h1 := preE_spec cap ε i T
  set b := bs.getD k false with hb
  have hbit : wbit (T.seth i (T.sh i + off ε)) i = b := by
    simp only [wbit, WState.seth_st, WState.seth_sh, Function.update_self, Function.update_apply]
    rw [hTst, hTsh]
    exact hread k hk
  set T1 := T.seth i (T.sh i + off ε) with hT1
  have hT1v : T1.val v = T.val v := rfl
  have hT1p : T1.val p = T.val p := rfl
  have hT1t : T1.val t = T.val t := rfl
  set T2 := T1.setv v (T1.val v + b.toNat * T1.val p) with hT2
  have h2 : WExec cap (.ifs i (addTo p v t) .skip) T1 T2 (18 * 2 ^ L + 4) := by
    cases hbv : b with
    | true =>
      have ha := addTo_spec cap p v t hpv hpt hvt T1 (by rw [hT1t, hTt]) (by rw [hT1p, hTp]; omega)
        (by rw [hT1v, hT1p, hTv, hTp]; omega)
      have e : T2 = T1.setv v (T1.val v + T1.val p) := by simp [T2, hbv]
      rw [e]
      exact WExec.mono (WExec.ifsT (by rw [hbit, hbv]) ha) (by rw [hT1p, hTp]; omega)
    | false =>
      have e : T2 = T1 := by simp [T2, hbv, wsetv_same]
      rw [e]
      exact WExec.mono (WExec.ifsF (by rw [hbit, hbv]) (WExec.skip T1)) (by omega)
  have hT2p : T2.val p = 2 ^ k := by simp [T2, Function.update_apply, hpv, hpv.symm, hT1p, hTp]
  have hT2t : T2.val t = 0 := by simp [T2, Function.update_apply, hvt, hvt.symm, hT1t, hTt]
  have h3 := dbl_spec cap p t hpt T2 hT2t (by rw [hT2p]; omega)
  set T3 := T2.setv p (2 * T2.val p) with hT3
  have h4 := WExec.fwd (cap := cap) i T3
  refine WExec.cast cap (WExec.seq h1 (WExec.seq h2 (WExec.seq h3 h4))) ?_ (by rw [hT2p]; omega)
  have hbv' := bitsValue_take_succ bs k (by omega)
  apply WState.eq
  · funext j
    by_cases hji : j = i
    · subst hji; simp [T3, T2, T1, hTsh, payState]; ring_nf; omega
    · simp [T3, T2, T1, T, payState, Function.update_apply, hji]
  · simp [T3, T2, T1, T, payState]
  · funext j
    by_cases hjp : j = p
    · subst hjp; simp [T3, payState, Function.update_apply, hT2p]; ring
    · by_cases hjv : j = v
      · subst hjv
        simp [T3, T2, T1, payState, Function.update_apply, hjp, hTv, hTp, hbv', hb]
        ring
      · by_cases hjc : j = c
        · subst hjc; simp [T3, T2, T1, T, payState, Function.update_apply, hjp, hjv]; omega
        · simp [T3, T2, T1, T, payState, Function.update_apply, hjp, hjv, hjc]
  · simp [T3, T2, T1, T, payState]

/-- **Reading one framed field into a unary register**: from the marker of `marks (natWord x)`, with `f, c, p, t` at
`0` and capacity `≥ v + 2^{natBitLength x + 1}`, the head moves past the field and `v` grows by `x`. -/
theorem readNatM_spec (ε : Bool) (i : Fin (ns + 1)) (f c v p t : Fin nr) (hfc : f ≠ c) (hfv : f ≠ v) (hfp : f ≠ p)
    (hft : f ≠ t) (hcv : c ≠ v) (hcp : c ≠ p) (hct : c ≠ t) (hpv : p ≠ v) (hpt : p ≠ t) (hvt : v ≠ t) (x : ℕ)
    (pre rest : List Bool) (σ : WState ns nr) (hst : σ.st i = pre ++ enc ε (RepairRepresentation.natWord x) ++ rest)
    (hsh : σ.sh i = pre.length) (hf : σ.val f = 0) (hc : σ.val c = 0) (hp : σ.val p = 0) (ht : σ.val t = 0)
    (hcap : σ.val v + 2 ^ (natBitLength x + 1) ≤ cap) :
    WExec cap (readNatM ε i f c v p t) σ
      ((σ.seth i (pre.length + stp ε * (RepairRepresentation.natWord x).length)).setv v (σ.val v + x))
      ((natBitLength x + 2) * (40 * 2 ^ natBitLength x + 40)) := by
  set L := natBitLength x with hL
  have hxL : x < 2 ^ L := Nat.lt_pow_succ_log_self (by norm_num) x
  have hpowL : 2 ^ (L + 1) = 2 * 2 ^ L := by rw [pow_succ]; ring
  have hLpow : L < 2 ^ L := Nat.lt_two_pow_self
  have hlen := natWord_length x
  have hf1 := WExec.inc (cap := cap) f σ (by omega)
  set σ1 := σ.setv f (σ.val f + 1) with hσ1
  have hσ1f : σ1.val f = 1 := by simp [σ1, hf]
  have hσ1st : σ1.st i = pre ++ (enc ε (RepairRepresentation.natWord x) ++ rest) := by
    simp [σ1, hst, List.append_assoc]
  have hσ1sh : σ1.sh i = pre.length := by simp [σ1, hsh]
  have hread : ∀ k, k < (RepairRepresentation.natWord x).length →
      readTapeBit (σ1.st i) (pre.length + stp ε * k + off ε) = (RepairRepresentation.natWord x).getD k false := by
    intro k hk
    rw [hσ1st, Nat.add_assoc, read_pre]
    exact read_enc_bit ε rest _ k hk
  have hs := stp_eq ε
  have ho := off_le ε
  have h2 := unary_loop cap ε i f c hfc (by omega) L σ1 hσ1f
    (fun k hk => by rw [hσ1sh, hread k (by omega)]; exact natWord_getD_one x k hk)
    (by rw [hσ1sh, hread L (by omega)]; exact natWord_getD_zero x)
    (by simp [σ1, Function.update_apply, hfc, hfc.symm, hfv, hfv.symm, hfp, hfp.symm, hft, hft.symm, hcv, hcv.symm, hcp, hcp.symm, hct, hct.symm, hpv, hpv.symm, hpt, hpt.symm, hvt, hvt.symm, hc]; omega)
  set σ2 := ((σ1.seth i (σ1.sh i + stp ε * L + stp ε)).setv c (σ1.val c + L)).setv f 0 with hσ2
  have hσ2p : σ2.val p = 0 := by simp [σ2, σ1, Function.update_apply, hfc, hfc.symm, hfv, hfv.symm, hfp, hfp.symm, hft, hft.symm, hcv, hcv.symm, hcp, hcp.symm, hct, hct.symm, hpv, hpv.symm, hpt, hpt.symm, hvt, hvt.symm, hp]
  have h3 := WExec.inc (cap := cap) p σ2 (by rw [hσ2p]; omega)
  set σ3 := σ2.setv p (σ2.val p + 1) with hσ3
  set bs := WilliamsPublishedForm.fixedWidthNatBits L x with hbs
  have hbsl : bs.length = L := by simp [bs, WilliamsPublishedForm.fixedWidthNatBits]
  have hσ3c : σ3.val c = L := by simp [σ3, σ2, σ1, Function.update_apply, hfc, hfc.symm, hfv, hfv.symm, hfp, hfp.symm, hft, hft.symm, hcv, hcv.symm, hcp, hcp.symm, hct, hct.symm, hpv, hpv.symm, hpt, hpt.symm, hvt, hvt.symm, hc]
  have hσ3p : σ3.val p = 1 := by simp [σ3, hσ2p]
  have hσ3v : σ3.val v = σ.val v := by simp [σ3, σ2, σ1, Function.update_apply, hfc, hfc.symm, hfv, hfv.symm, hfp, hfp.symm, hft, hft.symm, hcv, hcv.symm, hcp, hcp.symm, hct, hct.symm, hpv, hpv.symm, hpt, hpt.symm, hvt, hvt.symm]
  have hσ3t : σ3.val t = 0 := by simp [σ3, σ2, σ1, Function.update_apply, hfc, hfc.symm, hfv, hfv.symm, hfp, hfp.symm, hft, hft.symm, hcv, hcv.symm, hcp, hcp.symm, hct, hct.symm, hpv, hpv.symm, hpt, hpt.symm, hvt, hvt.symm, ht]
  have hσ3sh : σ3.sh i = pre.length + stp ε * (L + 1) := by simp [σ3, σ2, σ1, hsh]; ring
  have hσ3st : σ3.st i = σ1.st i := by simp [σ3, σ2]
  have h0 : payState ε σ3 i c v p L (σ.val v) bs 0 = σ3 := by
    apply WState.eq
    · funext j; by_cases hji : j = i
      · subst hji; simp [payState]
      · simp [payState, Function.update_apply, hji]
    · simp [payState]
    · funext j
      by_cases hjp : j = p
      · subst hjp; simp [payState, Function.update_apply, hσ3p]
      · by_cases hjv : j = v
        · subst hjv; simp [payState, Function.update_apply, hjp, hσ3v, CanonicalBinary.bitsValue]
        · by_cases hjc : j = c
          · subst hjc; simp [payState, Function.update_apply, hjp, hjv, hσ3c]
          · simp [payState, Function.update_apply, hjp, hjv, hjc]
    · simp [payState]
  have hreadP : ∀ m < L, readTapeBit (σ3.st i) (σ3.sh i + stp ε * m + off ε) = bs.getD m false := by
    intro m hm
    rw [hσ3st, hσ3sh, show pre.length + stp ε * (L + 1) + stp ε * m + off ε = pre.length + stp ε * (L + 1 + m) + off ε
      by ring,
      hread (L + 1 + m) (by omega), natWord_getD_payload x m hm]
    rw [List.getD_eq_getElem _ _ (by omega)]
    simp [bs, WilliamsPublishedForm.fixedWidthNatBits]
  have hvalk : ∀ k ≤ L, CanonicalBinary.bitsValue (bs.take k) < 2 ^ k := by
    intro k hk
    have h := bitsValue_lt (bs.take k)
    rwa [List.length_take_of_le (by omega)] at h
  have hloop := UnionMachine.Round.wloop cap c (bitBody ε i v p t) (36 * 2 ^ L + 12) L
    (payState ε σ3 i c v p L (σ.val v) bs)
    (fun k hk => by simp [payState, Function.update_apply, hcv, hcv.symm, hcp, hcp.symm, hct, hct.symm, hpv, hpv.symm, hpt, hpt.symm, hvt, hvt.symm])
    (by omega)
    (fun k hk => bitRound_spec cap ε i c v p t hcv hcp hct hpv hpt hvt σ3 L (σ.val v) bs hbsl hσ3t hreadP
      (by omega) hvalk k hk)
  rw [h0] at hloop
  set σ4 := payState ε σ3 i c v p L (σ.val v) bs L with hσ4
  have hσ4p : σ4.val p = 2 ^ L := by simp [σ4, payState]
  have h5 := wclear_spec cap p (2 ^ L) σ4 hσ4p (by rw [hσ4p]; omega)
  have hvalL : CanonicalBinary.bitsValue (bs.take L) = x := by
    rw [← hbsl, List.take_length, hbs, Transfer.bitsValue_fixedWidth]
    exact Nat.mod_eq_of_lt hxL
  refine WExec.cast cap (WExec.seq hf1 (WExec.seq h2 (WExec.seq h3 (WExec.seq hloop h5)))) ?_ ?_
  · apply WState.eq
    · funext j
      by_cases hji : j = i
      · subst hji; simp [σ4, payState, hσ3sh, hlen]; ring
      · simp [σ4, σ3, σ2, σ1, payState, Function.update_apply, hji]
    · simp [σ4, σ3, σ2, σ1, payState]
    · funext j
      by_cases hjp : j = p
      · subst hjp; simp [σ4, payState, Function.update_apply, hpv, hpv.symm, hp]
      · by_cases hjv : j = v
        · subst hjv; simp [σ4, payState, Function.update_apply, hjp, hvalL]
        · by_cases hjc : j = c
          · subst hjc; simp [σ4, payState, Function.update_apply, hjp, hjv, hc]
          · by_cases hjf : j = f
            · subst hjf; simp [σ4, σ3, σ2, payState, Function.update_apply, hjp, hjv, hjc, hf]
            · simp [σ4, σ3, σ2, σ1, payState, Function.update_apply, hjp, hjv, hjc, hjf]
    · simp [σ4, σ3, σ2, σ1, payState]
  · nlinarith

end NearCubicWires.WireExponent3_5.PrimAsm.ParseNat
