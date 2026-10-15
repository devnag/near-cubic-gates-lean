import Proof.Gates.WordPrograms.SInt
import Proof.Wire_3_5.PrimAsmWriteNat
import Proof.Wire_3_5.FinalPassFiltTabRef

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicGates.Close.TabMachine
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length binary_value)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat (appendO appendO_append appendO_nil)
open NearCubicGates.Close.WordPrograms.SInt (encS binary_encS)

/-! ## Two's complement -/

/-- The integer whose residue modulo `2^q` is the `q`-bit word `v`, in `[−2^{q−1}, 2^{q−1})`. -/
def tc (q v : ℕ) : ℤ := if v < 2 ^ (q - 1) then (v : ℤ) else (v : ℤ) - 2 ^ q

/-- `tc` recovers every integer of magnitude below `2^{q−1}` from its residue. -/
theorem tc_residue (q : ℕ) (hq : 1 ≤ q) (z : ℤ) (hz : z.natAbs < 2 ^ (q - 1)) :
    tc q (z % 2 ^ q).toNat = z := by
  have hp : (2 : ℤ) ^ q = 2 * 2 ^ (q - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hpos : (0 : ℤ) < 2 ^ (q - 1) := by positivity
  have hz' : -(2 : ℤ) ^ (q - 1) < z ∧ z < 2 ^ (q - 1) := by
    have : (z.natAbs : ℤ) < 2 ^ (q - 1) := by exact_mod_cast hz
    constructor <;> cases Int.natAbs_eq z <;> omega
  unfold tc
  rcases le_or_gt 0 z with h | h
  · have hm : z % 2 ^ q = z := Int.emod_eq_of_lt h (by omega)
    rw [hm]
    have hlt : z.toNat < 2 ^ (q - 1) := by
      have : (z.toNat : ℤ) < 2 ^ (q - 1) := by rw [Int.toNat_of_nonneg h]; exact hz'.2
      exact_mod_cast this
    rw [if_pos hlt, Int.toNat_of_nonneg h]
  · have hm : z % 2 ^ q = z + 2 ^ q := by
      rw [Int.emod_eq_add_self_emod]
      exact Int.emod_eq_of_lt (by omega) (by omega)
    rw [hm]
    have hnn : 0 ≤ z + 2 ^ q := by omega
    have hge : ¬ (z + 2 ^ q).toNat < 2 ^ (q - 1) := by
      intro hc
      have : ((z + 2 ^ q).toNat : ℤ) < 2 ^ (q - 1) := by exact_mod_cast hc
      rw [Int.toNat_of_nonneg hnn] at this; omega
    rw [if_neg hge, Int.toNat_of_nonneg hnn]; ring

/-- The bit transform of the decoder: with `top` set, the two's complement negation, low bit first. -/
def xb (top : Bool) : List Bool → Bool → List Bool
  | [], _ => []
  | b :: bs, seen => (if seen then !b else b) :: xb top bs (seen || (top && b))

theorem xb_false : ∀ (bs : List Bool), xb false bs false = bs
  | [] => rfl
  | b :: bs => by simp [xb, xb_false bs]

theorem xb_seen (top : Bool) : ∀ (bs : List Bool), xb top bs true = bs.map (!·)
  | [] => rfl
  | b :: bs => by simp [xb, xb_seen top bs]

theorem binary_not : ∀ (q x : ℕ), x < 2 ^ q → (binary q x).map (!·) = binary q (2 ^ q - 1 - x)
  | 0, _, _ => rfl
  | q + 1, x, h => by
    have h2 : 2 ^ (q + 1) = 2 * 2 ^ q := by ring
    simp only [binary, List.map_cons]
    rw [binary_not q (x / 2) (by omega)]
    have hp : 0 < 2 ^ q := Nat.pow_pos (by norm_num)
    congr 1
    · rcases Nat.mod_two_eq_zero_or_one x with hx | hx
      · have : (2 ^ (q + 1) - 1 - x) % 2 = 1 := by omega
        simp [hx, this]
      · have : (2 ^ (q + 1) - 1 - x) % 2 = 0 := by omega
        simp [hx, this]
    · congr 1; omega

/-- **Two's complement negation, streamed**: for `0 < v < 2^q`, the transform of `v`'s bits is `2^q − v`. -/
theorem xb_true_binary : ∀ (q v : ℕ), 0 < v → v < 2 ^ q → xb true (binary q v) false = binary q (2 ^ q - v)
  | 0, v, h0, h => by simp at h; omega
  | q + 1, v, h0, h => by
    have h2 : 2 ^ (q + 1) = 2 * 2 ^ q := by ring
    have hp : 0 < 2 ^ q := Nat.pow_pos (by norm_num)
    simp only [binary]
    rcases Nat.mod_two_eq_zero_or_one v with hv | hv
    · have e1 : (v % 2 == 1) = false := by simp [hv]
      rw [e1]
      simp only [xb, Bool.false_eq_true, ↓reduceIte, Bool.and_false, Bool.or_false]
      rw [xb_true_binary q (v / 2) (by omega) (by omega)]
      have : (2 ^ (q + 1) - v) % 2 = 0 := by omega
      simp only [this, List.cons.injEq]
      constructor
      · rfl
      · congr 1; omega
    · have e1 : (v % 2 == 1) = true := by simp [hv]
      rw [e1]
      simp only [xb, Bool.false_eq_true, ↓reduceIte, Bool.and_true, Bool.or_true]
      rw [xb_seen, binary_not q (v / 2) (by omega)]
      have : (2 ^ (q + 1) - v) % 2 = 1 := by omega
      simp only [this, List.cons.injEq]
      constructor
      · rfl
      · congr 1; omega

/-- The top bit of a `q`-bit word. -/
theorem binary_top (q v : ℕ) (hq : 1 ≤ q) (hv : v < 2 ^ q) :
    (binary q v).getD (q - 1) false = decide (2 ^ (q - 1) ≤ v) := by
  have hb := NearCubicWires.WireExponent3_5.FinalPass.Filt.binary_add (q - 1) 1 v
  rw [show q - 1 + 1 = q by omega] at hb
  rw [hb, List.getD_append_right _ _ _ _ (by simp)]
  have hlt : v / 2 ^ (q - 1) < 2 := by
    rw [Nat.div_lt_iff_lt_mul (Nat.pow_pos (by norm_num))]
    rw [show 2 ^ q = 2 ^ (q - 1) * 2 by rw [← pow_succ]; congr 1; omega] at hv; omega
  simp only [binary_length, Nat.sub_self, binary, List.getD_cons_zero]
  rcases Nat.lt_or_ge v (2 ^ (q - 1)) with h | h
  · have : v / 2 ^ (q - 1) = 0 := Nat.div_eq_of_lt h
    simp [this, Nat.not_le.mpr h]
  · have h1 : 1 ≤ v / 2 ^ (q - 1) := (Nat.le_div_iff_mul_le (Nat.pow_pos (by norm_num))).mpr (by omega)
    have : v / 2 ^ (q - 1) = 1 := by omega
    simp [this, h]

/-- **The decoded record**: sign = top bit, magnitude bits = the transform. -/
theorem binary_encS_tc (q v : ℕ) (hq : 1 ≤ q) (hv : v < 2 ^ q) :
    binary (q + 1) (encS (tc q v)) = decide (2 ^ (q - 1) ≤ v) :: xb (decide (2 ^ (q - 1) ≤ v)) (binary q v) false := by
  rw [binary_encS]
  have hp : 2 ^ q = 2 * 2 ^ (q - 1) := by rw [← pow_succ']; congr 1; omega
  unfold tc
  rcases Nat.lt_or_ge v (2 ^ (q - 1)) with h | h
  · simp only [if_pos h, Nat.not_le.mpr h, decide_false, xb_false]
    simp
  · have hn : ¬ v < 2 ^ (q - 1) := by omega
    simp only [if_neg hn, h, decide_true]
    have hneg : (v : ℤ) - 2 ^ q < 0 := by
      have : (v : ℤ) < 2 ^ q := by exact_mod_cast hv
      omega
    have habs : ((v : ℤ) - 2 ^ q).natAbs = 2 ^ q - v := by
      have : ((v : ℤ) - 2 ^ q) = -((2 ^ q - v : ℕ) : ℤ) := by push_cast [Nat.cast_sub hv.le]; ring
      rw [this, Int.natAbs_neg, Int.natAbs_natCast]
    rw [decide_eq_true hneg, habs, xb_true_binary q v (by have : 0 < 2 ^ (q - 1) := Nat.pow_pos (by norm_num); omega) hv]

/-! ## The programs -/

variable {ns nr : ℕ}

/-- Append one bit to an output stream (head at its end), counting in `CO`. -/
def emitX (O : Fin (ns + 1)) (CO : Fin nr) (b : Bool) : WMX ns nr := .wm (emitC O CO b)

theorem emitX_spec (cap : ℕ) (O : Fin (ns + 1)) (CO : Fin nr) (b : Bool) (σ : WState ns nr)
    (hO : σ.sh O = (σ.st O).length) (hc : σ.val CO < cap) : WXExec cap (emitX O CO b) σ (appendO σ O CO [b]) 7 :=
  WXExec.wm (emitC_spec cap O CO b σ hO hc)

def peek (OP : Fin (ns + 1)) (K1 K2 TOP : Fin nr) : WMX ns nr :=
  .seq (repK K1 K2 (WMX.fwd OP)) (.seq (.ifs OP (WMX.inc TOP) WMX.skip) (repK K1 K2 (WMX.bwd OP)))

/-- One bit of an entry: stream it out, negated after the first one when `TOP` is set. -/
def bitStep (OP OUT : Fin (ns + 1)) (CO CP TOP SEEN : Fin nr) : WMX ns nr :=
  .seq (emitX OUT CO true)
    (.seq (.ifs OP (.ifr SEEN (emitX OUT CO false) (.seq (emitX OUT CO true) (.ifr TOP (WMX.inc SEEN) WMX.skip)))
      (.ifr SEEN (emitX OUT CO true) (emitX OUT CO false))) (.wm (WM.fwdC OP CP)))

/-- One entry: its record `frame (binary (q+1) (encS (tc q v)))` appended to `OUT`. -/
def entry (OP OUT : Fin (ns + 1)) (K K1 K2 CO CP TOP SEEN : Fin nr) : WMX ns nr :=
  .seq (.seq (peek OP K1 K2 TOP)
    (.ifr TOP (.seq (emitX OUT CO true) (emitX OUT CO true)) (.seq (emitX OUT CO true) (emitX OUT CO false))))
    (.seq (repK K K2 (bitStep OP OUT CO CP TOP SEEN))
      (.seq (emitX OUT CO false) (.seq (.wm (WM.clear TOP)) (.wm (WM.clear SEEN)))))

/-- **The decoder**: `N` entries, then the record stream is closed and both heads return to `0`. -/
def decode (OP OUT : Fin (ns + 1)) (N N2 K K1 K2 CO CP TOP SEEN : Fin nr) : WMX ns nr :=
  .seq (repK N N2 (entry OP OUT K K1 K2 CO CP TOP SEEN))
    (.seq (emitX OUT CO false) (.seq (.wm (WM.rewind OUT CO)) (.wm (WM.rewind OP CP))))

/-! ## Specs -/

theorem readTapeBit_mid_app (pre bs rest : List Bool) (j : ℕ) (hj : j < bs.length) :
    readTapeBit (pre ++ bs ++ rest) (pre.length + j) = bs.getD j false := by
  unfold readTapeBit
  rw [List.append_assoc, List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left,
    List.getD_append _ _ _ _ hj]

/-- The seen flag after `j` bits. -/
def seenAt (top : Bool) (bs : List Bool) (j : ℕ) : Bool := top && (bs.take j).any id

theorem xb_getD (top : Bool) : ∀ (bs : List Bool) (s : Bool) (j : ℕ), j < bs.length →
    (xb top bs s).getD j false =
      if (s || (top && (bs.take j).any id)) then !(bs.getD j false) else bs.getD j false
  | [], _, _, h => by simp at h
  | b :: bs, s, 0, _ => by simp [xb]
  | b :: bs, s, j + 1, h => by
    simp only [xb, List.getD_cons_succ, List.take_succ_cons, List.any_cons]
    rw [xb_getD top bs _ j (by simpa using h)]
    cases s <;> cases top <;> cases b <;> simp

theorem xb_length (top : Bool) : ∀ (bs : List Bool) (s : Bool), (xb top bs s).length = bs.length
  | [], _ => rfl
  | b :: bs, s => by simp [xb, xb_length top bs]

theorem take_succ_getD (l : List Bool) (j : ℕ) (hj : j < l.length) :
    l.take (j + 1) = l.take j ++ [l.getD j false] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hj, List.getD_eq_getElem _ _ hj]; rfl

theorem marks_len (u : List Bool) : (Streaming.marks u).length = 2 * u.length := by
  induction u with
  | nil => rfl
  | cons b u ih => simp only [Streaming.marks, List.flatMap_cons, List.length_append, List.length_cons,
      List.length_nil] at ih ⊢; omega

theorem marks_snoc (l : List Bool) (b : Bool) : Streaming.marks (l ++ [b]) = Streaming.marks l ++ [true, b] := by
  simp [Streaming.marks]

theorem seenAt_succ (top : Bool) (bs : List Bool) (j : ℕ) (hj : j < bs.length) :
    seenAt top bs (j + 1) = (seenAt top bs j || (top && bs.getD j false)) := by
  unfold seenAt
  rw [take_succ_getD bs j hj, List.any_append]
  cases top <;> simp

section Specs
variable (cap : ℕ)

/-- `peek`: `TOP := ` the bit `n` cells ahead; everything else (the head included) unchanged. -/
theorem peek_spec {OP : Fin (ns + 1)} {K1 K2 TOP : Fin nr} (hK : K1 ≠ K2) (hKT : K1 ≠ TOP) (hK2T : K2 ≠ TOP)
    (σ : WState ns nr) (n : ℕ) (hK1 : σ.val K1 = n) (hK20 : σ.val K2 = 0) (hT : σ.val TOP = 0)
    (hcap : 2 * n + 1 ≤ cap) :
    WXExec cap (peek OP K1 K2 TOP) σ (σ.setv TOP (readTapeBit (σ.st OP) (σ.sh OP + n)).toNat) (32 * n + 16) := by
  set b := readTapeBit (σ.st OP) (σ.sh OP + n) with hb
  have h1 := Runs.repE (cap := cap) (body := WMX.fwd OP) hK 1 n (fun k => σ.seth OP (σ.sh OP + k)) (by omega)
    (fun k => by simp) (fun k => by simp)
    (fun k _ v1 v2 => by
      refine (WXExec.fwd cap OP _).cast cap ?_ le_rfl
      apply WState.eq <;> try rfl
      funext i; by_cases hi : i = OP
      · subst hi; simp; omega
      · simp [Function.update_of_ne hi]) (by simp [hK1]) (by simp [hK20])
  have e0 : σ.seth OP (σ.sh OP + 0) = σ := by
    apply WState.eq <;> try rfl
    funext i; by_cases hi : i = OP
    · subst hi; simp
    · simp [Function.update_of_ne hi]
  rw [e0] at h1
  set σ1 := σ.seth OP (σ.sh OP + n) with hσ1
  have hw : wbit σ1 OP = b := by simp [wbit, hσ1, hb]
  have h2 : WXExec cap (.ifs OP (WMX.inc TOP) WMX.skip) σ1 (σ1.setv TOP b.toNat) 4 := by
    cases hbv : b
    · rw [hbv] at hw
      exact (WXExec.ifsF hw (WXExec.skip cap σ1)).cast cap (BinW.setv_same (by simp [hσ1, hT])).symm (by omega)
    · rw [hbv] at hw
      have hi := WXExec.inc cap TOP σ1 (by simp [hσ1, hT]; omega)
      exact (WXExec.ifsT hw hi).cast cap (by simp [hσ1, hT]) (by omega)
  have h3 := Runs.repE (cap := cap) (body := WMX.bwd OP) hK 1 n
    (fun k => (σ.seth OP (σ.sh OP + n - k)).setv TOP b.toNat) (by omega)
    (fun k => by simp [Function.update_of_ne hKT]) (fun k => by simp [Function.update_of_ne hK2T])
    (fun k hk v1 v2 => by
      refine (WXExec.bwd cap OP _).cast cap ?_ le_rfl
      apply WState.eq <;> try rfl
      funext i; by_cases hi : i = OP
      · subst hi; simp; omega
      · simp [Function.update_of_ne hi]) (by simp [Function.update_of_ne hKT, hK1])
      (by simp [Function.update_of_ne hK2T, hK20])
  have e1 : (σ.seth OP (σ.sh OP + n - 0)).setv TOP b.toNat = σ1.setv TOP b.toNat := by simp [hσ1]
  have e2 : (σ.seth OP (σ.sh OP + n - n)).setv TOP b.toNat = σ.setv TOP b.toNat := by
    apply WState.eq <;> try rfl
    funext i; by_cases hi : i = OP
    · subst hi; simp
    · simp [Function.update_of_ne hi]
  rw [e1, e2] at h3
  exact WXExec.mono (WXExec.seq h1 (WXExec.seq h2 h3)) (by ring_nf; omega)

/-- The state after `j` bits of an entry's magnitude. -/
def bitSt (σ1 : WState ns nr) (OP OUT : Fin (ns + 1)) (CO CP SEEN : Fin nr) (h cp : ℕ) (top : Bool) (bs : List Bool)
    (j : ℕ) : WState ns nr :=
  (((appendO σ1 OUT CO (Streaming.marks ((xb top bs false).take j))).seth OP (h + j)).setv CP (cp + j)).setv SEEN
    (seenAt top bs j).toNat

theorem bitStep_spec {OP OUT : Fin (ns + 1)} {K K2 CO CP TOP SEEN : Fin nr} (hS : OP ≠ OUT)
    (hR : [K, K2, CO, CP, TOP, SEEN].Nodup) (σ1 : WState ns nr) (h cp : ℕ) (top : Bool) (bs : List Bool)
    (hOP : ∀ j < bs.length, readTapeBit (σ1.st OP) (h + j) = bs.getD j false)
    (hOUT : σ1.sh OUT = (σ1.st OUT).length) (hTOP : σ1.val TOP = top.toNat)
    (hcapO : σ1.val CO + 2 * bs.length < cap) (hcapP : cp + bs.length < cap)
    (j : ℕ) (hj : j < bs.length) (v1 v2 : ℕ) :
    WXExec cap (bitStep OP OUT CO CP TOP SEEN)
      (((bitSt σ1 OP OUT CO CP SEEN h cp top bs j).setv K v1).setv K2 v2)
      (((bitSt σ1 OP OUT CO CP SEEN h cp top bs (j + 1)).setv K v1).setv K2 v2) 30 := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, not_false_eq_true, List.nodup_nil,
    and_true] at hR
  obtain ⟨⟨hKK2, hKCO, hKCP, hKT, hKS⟩, ⟨hK2CO, hK2CP, hK2T, hK2S⟩, ⟨hCOCP, hCOT, hCOS⟩, ⟨hCPT, hCPS⟩, hTS⟩ := hR
  set xs := xb top bs false with hxs
  have hxl : xs.length = bs.length := xb_length top bs false
  set b := bs.getD j false with hb
  set out := xs.getD j false with hout
  have hout' : out = if seenAt top bs j then !b else b := by
    rw [hout, hxs, xb_getD top bs false j hj, Bool.false_or]; rfl
  have hmk : Streaming.marks ((xb top bs false).take (j + 1)) =
      Streaming.marks ((xb top bs false).take j) ++ [true, out] := by
    rw [take_succ_getD (xb top bs false) j (by rw [xb_length]; omega), marks_snoc]
  have hmkl : (Streaming.marks ((xb top bs false).take j)).length = 2 * j := by
    rw [marks_len, List.length_take, xb_length]; omega
  set τ := ((bitSt σ1 OP OUT CO CP SEEN h cp top bs j).setv K v1).setv K2 v2 with hτ
  have hτO : τ.sh OUT = (τ.st OUT).length := by
    simp [hτ, bitSt, appendO, Function.update_apply, Ne.symm hS, hOUT]
  have hτCO : τ.val CO = σ1.val CO + 2 * j := by
    simp [hτ, bitSt, appendO, Function.update_apply, hKCO, hK2CO, hCOCP, hCOS, Ne.symm hKCO, Ne.symm hK2CO,
      Ne.symm hCOCP, Ne.symm hCOS, xb_length, marks_len, List.length_take, Nat.min_eq_left hj.le]
  have e1 := emitX_spec cap OUT CO true τ hτO (by rw [hτCO]; omega)
  set τ1 := appendO τ OUT CO [true] with hτ1
  have hτ1O : τ1.sh OUT = (τ1.st OUT).length := by simp [hτ1, appendO, hτO]
  have hτ1CO : τ1.val CO = σ1.val CO + 2 * j + 1 := by simp [hτ1, appendO, hτCO]
  have hw : wbit τ1 OP = b := by
    have e1 : τ1.st OP = σ1.st OP := by simp [hτ1, hτ, bitSt, appendO, Function.update_apply, hS]
    have e2 : τ1.sh OP = h + j := by simp [hτ1, hτ, bitSt, appendO, Function.update_apply, hS]
    show readTapeBit (τ1.st OP) (τ1.sh OP) = b
    rw [e1, e2, hOP j hj]
  have hSE : τ1.val SEEN = (seenAt top bs j).toNat := by
    simp [hτ1, hτ, bitSt, appendO, Function.update_apply, hKS, hK2S, hCOS, Ne.symm hKS, Ne.symm hK2S, Ne.symm hCOS]
  have hTOP1 : τ1.val TOP = top.toNat := by
    simp [hτ1, hτ, bitSt, appendO, Function.update_apply, hKT, hK2T, hCOT, hCPT, hTS, Ne.symm hKT, Ne.symm hK2T,
      Ne.symm hCOT, Ne.symm hCPT, Ne.symm hTS, hTOP]
  -- the branch: emit `out`, update `SEEN`
  have hbr : WXExec cap (.ifs OP (.ifr SEEN (emitX OUT CO false) (.seq (emitX OUT CO true)
      (.ifr TOP (WMX.inc SEEN) WMX.skip))) (.ifr SEEN (emitX OUT CO true) (emitX OUT CO false))) τ1
      ((appendO τ1 OUT CO [out]).setv SEEN (seenAt top bs (j + 1)).toNat) 14 := by
    have hsucc := seenAt_succ top bs j hj
    have hlt : τ1.val CO < cap := by rw [hτ1CO]; omega
    cases hbv : b <;> cases hsv : seenAt top bs j
    · -- b = 0, not seen: emit 0
      have hv : τ1.val SEEN = 0 := by rw [hSE, hsv]; rfl
      have hw' : wbit τ1 OP = false := by rw [hw, hbv]
      have ho : out = false := by rw [hout', hsv, hbv]; rfl
      refine (WXExec.ifsF hw' (WXExec.ifrF hv (emitX_spec cap OUT CO false τ1 hτ1O hlt))).cast cap ?_ (by omega)
      rw [ho, hsucc, hsv, ← hb, hbv]
      apply WState.eq <;> try rfl
      funext r; by_cases hr : r = SEEN
      · rw [hr]; simp [appendO, Function.update_apply, hCOS, Ne.symm hCOS, hv]
      · simp [Function.update_of_ne hr]
    · -- b = 0, seen: emit 1
      have hv : τ1.val SEEN ≠ 0 := by rw [hSE, hsv]; decide
      have hw' : wbit τ1 OP = false := by rw [hw, hbv]
      have ho : out = true := by rw [hout', hsv, hbv]; rfl
      refine (WXExec.ifsF hw' (WXExec.ifrT hv (emitX_spec cap OUT CO true τ1 hτ1O hlt))).cast cap ?_ (by omega)
      rw [ho, hsucc, hsv]
      apply WState.eq <;> try rfl
      funext r; by_cases hr : r = SEEN
      · rw [hr]; simp [appendO, Function.update_apply, hCOS, Ne.symm hCOS, hSE, hsv]
      · simp [Function.update_of_ne hr]
    · -- b = 1, not seen: emit 1; `SEEN := top`
      have hv : τ1.val SEEN = 0 := by rw [hSE, hsv]; rfl
      have hw' : wbit τ1 OP = true := by rw [hw, hbv]
      have ho : out = true := by rw [hout', hsv, hbv]; rfl
      have e2 := emitX_spec cap OUT CO true τ1 hτ1O hlt
      set τ2 := appendO τ1 OUT CO [true] with hτ2
      have hτ2T : τ2.val TOP = top.toNat := by simp [hτ2, appendO, Function.update_apply, hCOT, Ne.symm hCOT, hTOP1]
      have hτ2S : τ2.val SEEN = 0 := by simp [hτ2, appendO, Function.update_apply, hCOS, Ne.symm hCOS, hv]
      have hbr2 : WXExec cap (.ifr TOP (WMX.inc SEEN) WMX.skip) τ2 (τ2.setv SEEN top.toNat) 4 := by
        cases top
        · exact (WXExec.ifrF (by rw [hτ2T]; rfl) (WXExec.skip cap τ2)).cast cap
            (BinW.setv_same (by rw [hτ2S]; rfl)).symm (by omega)
        · have hi := WXExec.inc cap SEEN τ2 (by rw [hτ2S]; omega)
          exact (WXExec.ifrT (by rw [hτ2T]; decide) hi).cast cap (by rw [hτ2S]; rfl) (by omega)
      refine (WXExec.ifsT hw' (WXExec.ifrF hv (WXExec.seq e2 hbr2))).cast cap ?_ (by omega)
      rw [ho, hsucc, hsv, ← hb, hbv]
      cases top <;> rfl
    · -- b = 1, seen: emit 0
      have hv : τ1.val SEEN ≠ 0 := by rw [hSE, hsv]; decide
      have hw' : wbit τ1 OP = true := by rw [hw, hbv]
      have ho : out = false := by rw [hout', hsv, hbv]; rfl
      refine (WXExec.ifsT hw' (WXExec.ifrT hv (emitX_spec cap OUT CO false τ1 hτ1O hlt))).cast cap ?_ (by omega)
      rw [ho, hsucc, hsv]
      apply WState.eq <;> try rfl
      funext r; by_cases hr : r = SEEN
      · rw [hr]; simp [appendO, Function.update_apply, hCOS, Ne.symm hCOS, hSE, hsv]
      · simp [Function.update_of_ne hr]
  set τ2 := (appendO τ1 OUT CO [out]).setv SEEN (seenAt top bs (j + 1)).toNat with hτ2
  have e3 := WXExec.wm (wfwdC_spec cap OP CP τ2 (by
    simp [hτ2, hτ1, hτ, bitSt, appendO, Function.update_apply, hKCP, hK2CP, hCOCP, hCPS, Ne.symm hKCP, Ne.symm hK2CP,
      Ne.symm hCOCP, Ne.symm hCPS]; omega))
  refine (WXExec.seq e1 (WXExec.seq hbr e3)).cast cap ?_ (by omega)
  -- the final state equality
  apply WState.eq
  · funext i
    by_cases h1 : i = OP
    · subst h1; simp [hτ2, hτ1, hτ, bitSt, appendO, Function.update_apply, hS]; omega
    · by_cases h2 : i = OUT
      · subst h2; simp [hτ2, hτ1, hτ, bitSt, appendO, Function.update_apply, h1, hmk, xb_length, marks_len,
          List.length_take, Nat.min_eq_left hj.le, Nat.min_eq_left (Nat.succ_le_of_lt hj)]; omega
      · simp [hτ2, hτ1, hτ, bitSt, appendO, Function.update_apply, h1, h2]
  · funext i
    by_cases h2 : i = OUT
    · subst h2; simp [hτ2, hτ1, hτ, bitSt, appendO, Function.update_apply, hmk]
    · simp [hτ2, hτ1, hτ, bitSt, appendO, Function.update_apply, h2]
  · funext r
    simp only [hτ2, hτ1, hτ, bitSt, appendO, WState.setv_val, WState.seth_val, WState.sets_val, Function.update_apply]
    by_cases r1 : r = K2
    · subst r1; simp [Ne.symm hKK2, hK2CO, hK2CP, hK2S]
    · by_cases r2 : r = K
      · subst r2; simp [hKK2, hKCO, hKCP, hKS]
      · by_cases r3 : r = CP
        · subst r3; simp [r1, r2, Ne.symm hKCP, Ne.symm hK2CP, hCOCP, Ne.symm hCOCP, hCPS]; omega
        · by_cases r4 : r = SEEN
          · subst r4; simp [r1, r2, r3, Ne.symm hKS, Ne.symm hK2S, Ne.symm hCPS, Ne.symm hCOS]
          · by_cases r5 : r = CO
            · subst r5; simp [r1, r2, r3, r4, Ne.symm hKCO, Ne.symm hK2CO, hCOCP, hCOS, hmk, hmkl, marks_len]; omega
            · simp [r1, r2, r3, r4, r5]
  · rfl

/-- The record of one decoded entry. -/
def decRec (q v : ℕ) : List Bool := frame (binary (q + 1) (encS (tc q v)))

theorem decRec_eq (q v : ℕ) (hq : 1 ≤ q) (hv : v < 2 ^ q) :
    decRec q v = [true, decide (2 ^ (q - 1) ≤ v)] ++
      Streaming.marks (xb (decide (2 ^ (q - 1) ≤ v)) (binary q v) false) ++ [false] := by
  rw [decRec, binary_encS_tc q v hq hv, frame, frame_eq_frameP]
  rfl

/-- The head of an entry: the sign is peeked and its record's first pair emitted. -/
theorem entryHead_spec {OP OUT : Fin (ns + 1)} {K1 K2 CO TOP : Fin nr} (hR : [K1, K2, CO, TOP].Nodup)
    (σ : WState ns nr) (q : ℕ) (top : Bool) (htop : readTapeBit (σ.st OP) (σ.sh OP + (q - 1)) = top)
    (hOUT : σ.sh OUT = (σ.st OUT).length) (hK1 : σ.val K1 = q - 1) (hK2 : σ.val K2 = 0) (hT : σ.val TOP = 0)
    (hcapO : σ.val CO + 2 < cap) (hcap : 2 * q + 1 ≤ cap) :
    WXExec cap (.seq (peek OP K1 K2 TOP) (.ifr TOP (.seq (emitX OUT CO true) (emitX OUT CO true))
      (.seq (emitX OUT CO true) (emitX OUT CO false)))) σ (appendO (σ.setv TOP top.toNat) OUT CO [true, top])
      (32 * q + 33) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, not_false_eq_true, List.nodup_nil,
    and_true] at hR
  obtain ⟨⟨hK1K2, hK1CO, hK1T⟩, ⟨hK2CO, hK2T⟩, hCOT⟩ := hR
  have hpk := peek_spec cap (OP := OP) hK1K2 hK1T hK2T σ (q - 1) hK1 hK2 hT (by omega)
  rw [htop] at hpk
  have hAO : (σ.setv TOP top.toNat).sh OUT = ((σ.setv TOP top.toNat).st OUT).length := by simp [hOUT]
  have hACO : (σ.setv TOP top.toNat).val CO = σ.val CO := by simp [Function.update_of_ne hCOT]
  have e1 := emitX_spec cap OUT CO true _ hAO (by rw [hACO]; omega)
  have hA1O : (appendO (σ.setv TOP top.toNat) OUT CO [true]).sh OUT =
      ((appendO (σ.setv TOP top.toNat) OUT CO [true]).st OUT).length := by simp [appendO, hOUT]
  have hA1CO : (appendO (σ.setv TOP top.toNat) OUT CO [true]).val CO < cap := by
    simp [appendO, Function.update_of_ne hCOT]; omega
  have hTv : (σ.setv TOP top.toNat).val TOP = top.toNat := by simp
  cases ht : top
  · have e2 := emitX_spec cap OUT CO false _ hA1O hA1CO
    rw [appendO_append] at e2
    have hv : (σ.setv TOP (false : Bool).toNat).val TOP = 0 := by simp
    have hb : WXExec cap (.ifr TOP (.seq (emitX OUT CO true) (emitX OUT CO true))
        (.seq (emitX OUT CO true) (emitX OUT CO false))) (σ.setv TOP (false : Bool).toNat)
        (appendO (σ.setv TOP (false : Bool).toNat) OUT CO [true, false]) 16 := by
      rw [ht] at e1 e2; exact WXExec.mono (WXExec.ifrF hv (WXExec.seq e1 e2)) (by omega)
    rw [ht] at hpk
    exact (WXExec.seq hpk hb).mono (by omega)
  · have e2 := emitX_spec cap OUT CO true _ hA1O hA1CO
    rw [appendO_append] at e2
    have hv : (σ.setv TOP (true : Bool).toNat).val TOP ≠ 0 := by simp
    have hb : WXExec cap (.ifr TOP (.seq (emitX OUT CO true) (emitX OUT CO true))
        (.seq (emitX OUT CO true) (emitX OUT CO false))) (σ.setv TOP (true : Bool).toNat)
        (appendO (σ.setv TOP (true : Bool).toNat) OUT CO [true, true]) 16 := by
      rw [ht] at e1 e2; exact WXExec.mono (WXExec.ifrT hv (WXExec.seq e1 e2)) (by omega)
    rw [ht] at hpk
    exact (WXExec.seq hpk hb).mono (by omega)

theorem bitSt_zero (σ1 : WState ns nr) {OP OUT : Fin (ns + 1)} {CO CP SEEN : Fin nr} (h : ℕ) (top : Bool)
    (bs : List Bool) (hOPh : σ1.sh OP = h) (hSE : σ1.val SEEN = 0) :
    bitSt σ1 OP OUT CO CP SEEN h (σ1.val CP) top bs 0 = σ1 := by
  unfold bitSt
  rw [List.take_zero, show Streaming.marks ([] : List Bool) = [] from rfl, appendO_nil, Nat.add_zero, Nat.add_zero]
  have e : seenAt top bs 0 = false := by simp [seenAt]
  rw [e]
  apply WState.eq
  · funext i; by_cases hi : i = OP
    · subst hi; simp [hOPh]
    · simp [Function.update_of_ne hi]
  · rfl
  · funext r; by_cases r1 : r = SEEN
    · subst r1; simp [hSE]
    · by_cases r2 : r = CP
      · subst r2; simp [Function.update_of_ne r1]
      · simp [Function.update_of_ne r1, Function.update_of_ne r2]
  · rfl

/-- The tail of an entry: the closing `false`, `TOP` and `SEEN` cleared. -/
theorem entryTail_spec {OUT : Fin (ns + 1)} {CO TOP SEEN : Fin nr} (hR : [CO, TOP, SEEN].Nodup) (σ : WState ns nr)
    (a b : Bool) (hO : σ.sh OUT = (σ.st OUT).length) (hc : σ.val CO < cap) (hT : σ.val TOP = a.toNat)
    (hS : σ.val SEEN = b.toNat) (hcap : 1 ≤ cap) :
    WXExec cap (.seq (emitX OUT CO false) (.seq (.wm (WM.clear TOP)) (.wm (WM.clear SEEN)))) σ
      (((appendO σ OUT CO [false]).setv TOP 0).setv SEEN 0) 17 := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, not_false_eq_true, List.nodup_nil,
    and_true] at hR
  obtain ⟨⟨hCOT, hCOS⟩, hTS⟩ := hR
  have e4 := emitX_spec cap OUT CO false σ hO hc
  have hT3 : (appendO σ OUT CO [false]).val TOP = a.toNat := by simp [appendO, Function.update_of_ne (Ne.symm hCOT), hT]
  have e5 := WXExec.wm (wclear_spec cap TOP a.toNat _ hT3 (by rw [hT3]; cases a <;> simp <;> omega))
  have hS4 : ((appendO σ OUT CO [false]).setv TOP 0).val SEEN = b.toNat := by
    simp [appendO, Function.update_of_ne (Ne.symm hCOS), Function.update_of_ne (Ne.symm hTS), hS]
  have e6 := WXExec.wm (wclear_spec cap SEEN b.toNat _ hS4 (by rw [hS4]; cases b <;> simp <;> omega))
  exact (WXExec.seq e4 (WXExec.seq e5 e6)).mono (by cases a <;> cases b <;> simp <;> omega)

/-- **One entry**: the record of the `q`-bit word `v` at `OP`'s head is appended to `OUT`; `OP` advances by `q`. -/
theorem entry_spec {OP OUT : Fin (ns + 1)} {K K1 K2 CO CP TOP SEEN : Fin nr} (hS : OP ≠ OUT)
    (hR : [K, K1, K2, CO, CP, TOP, SEEN].Nodup) (σ : WState ns nr) (q v : ℕ) (pre rest : List Bool) (hq : 1 ≤ q)
    (hv : v < 2 ^ q) (hOP : σ.st OP = pre ++ binary q v ++ rest) (hOPh : σ.sh OP = pre.length)
    (hOUT : σ.sh OUT = (σ.st OUT).length) (hK : σ.val K = q) (hK1 : σ.val K1 = q - 1) (hK2 : σ.val K2 = 0)
    (hT : σ.val TOP = 0) (hSE : σ.val SEEN = 0) (hcapO : σ.val CO + 2 * q + 3 < cap)
    (hcapP : σ.val CP + q < cap) (hcap : 2 * q + 1 ≤ cap) :
    WXExec cap (entry OP OUT K K1 K2 CO CP TOP SEEN) σ
      (((appendO σ OUT CO (decRec q v)).seth OP (pre.length + q)).setv CP (σ.val CP + q)) (80 * q + 60) := by
  have hR' := hR
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, not_false_eq_true, List.nodup_nil,
    and_true] at hR'
  obtain ⟨⟨hKK1, hKK2, hKCO, hKCP, hKT, hKS⟩, ⟨hK1K2, hK1CO, hK1CP, hK1T, hK1S⟩, ⟨hK2CO, hK2CP, hK2T, hK2S⟩,
    ⟨hCOCP, hCOT, hCOS⟩, ⟨hCPT, hCPS⟩, hTS⟩ := hR'
  have hbl : (binary q v).length = q := by simp
  have htopb : readTapeBit (σ.st OP) (σ.sh OP + (q - 1)) = decide (2 ^ (q - 1) ≤ v) := by
    rw [hOP, hOPh, readTapeBit_mid_app pre (binary q v) rest (q - 1) (by rw [binary_length]; exact Nat.sub_lt hq Nat.one_pos)]
    exact binary_top q v hq hv
  have hhead := entryHead_spec cap (OP := OP) (OUT := OUT) (K1 := K1) (K2 := K2) (CO := CO) (TOP := TOP)
    (by simp [hK1K2, hK1CO, hK1T, hK2CO, hK2T, hCOT]) σ q _ htopb hOUT hK1 hK2 hT (by omega) hcap
  set top := decide (2 ^ (q - 1) ≤ v) with htop
  set σ1 := appendO (σ.setv TOP top.toNat) OUT CO [true, top] with hσ1
  have h1OP : ∀ j < (binary q v).length, readTapeBit (σ1.st OP) (pre.length + j) = (binary q v).getD j false := by
    intro j hj
    have : σ1.st OP = σ.st OP := by simp [hσ1, appendO, Function.update_apply, hS]
    rw [this, hOP, readTapeBit_mid_app pre _ rest j hj]
  have h1O : σ1.sh OUT = (σ1.st OUT).length := by simp [hσ1, appendO, hOUT]
  have h1T : σ1.val TOP = top.toNat := by simp [hσ1, appendO, Function.update_apply, hCOT, Ne.symm hCOT]
  have h1CO : σ1.val CO = σ.val CO + 2 := by simp [hσ1, appendO, Function.update_of_ne hCOT]
  have h1CP : σ1.val CP = σ.val CP := by
    simp [hσ1, appendO, Function.update_of_ne (Ne.symm hCOCP), Function.update_of_ne hCPT]
  have h1h : σ1.sh OP = pre.length := by simp [hσ1, appendO, Function.update_of_ne hS, hOPh]
  have h1S : σ1.val SEEN = 0 := by
    simp [hσ1, appendO, Function.update_of_ne (Ne.symm hCOS), Function.update_of_ne (Ne.symm hTS), hSE]
  have hst0 := bitSt_zero σ1 (OUT := OUT) (CO := CO) (CP := CP) pre.length top (binary q v) h1h h1S
  rw [h1CP] at hst0
  have hloop := Runs.repE (cap := cap) (body := bitStep OP OUT CO CP TOP SEEN) hKK2 30 q
    (bitSt σ1 OP OUT CO CP SEEN pre.length (σ.val CP) top (binary q v)) (by omega)
    (fun k => by simp [bitSt, appendO, Function.update_apply, hKS, hKCP, hKCO])
    (fun k => by simp [bitSt, appendO, Function.update_apply, hK2S, hK2CP, hK2CO])
    (fun k hk v1 v2 => bitStep_spec cap (K := K) (K2 := K2) hS (by simp [hKK2, hKCO, hKCP, hKT, hKS, hK2CO,
      hK2CP, hK2T, hK2S, hCOCP, hCOT, hCOS, hCPT, hCPS, hTS]) σ1 pre.length (σ.val CP) top (binary q v) h1OP h1O h1T
      (by rw [h1CO, hbl]; omega) (by rw [hbl]; omega) k (by omega) v1 v2)
    (by rw [hst0]; simp [hσ1, appendO, Function.update_apply, hKCO, hKT, hK])
    (by rw [hst0]; simp [hσ1, appendO, Function.update_apply, hK2CO, hK2T, hK2])
  rw [hst0] at hloop
  have hmk : Streaming.marks ((xb top (binary q v) false).take q) = Streaming.marks (xb top (binary q v) false) := by
    rw [List.take_of_length_le (by rw [xb_length, hbl])]
  have htail := entryTail_spec cap (OUT := OUT) (CO := CO) (TOP := TOP) (SEEN := SEEN) (by simp [hCOT, hCOS, hTS])
    (bitSt σ1 OP OUT CO CP SEEN pre.length (σ.val CP) top (binary q v) q) top (seenAt top (binary q v) q)
    (by simp [bitSt, appendO, Function.update_apply, Ne.symm hS, h1O])
    (by simp [bitSt, appendO, Function.update_apply, hCOCP, hCOS, h1CO, marks_len, xb_length, hbl]; omega)
    (by simp [bitSt, appendO, Function.update_apply, hCOT, hCPT, hTS, Ne.symm hCOT, Ne.symm hCPT, Ne.symm hTS, h1T])
    (by simp [bitSt]) (by omega)
  have hcost : 32 * q + 33 + 1 + (q * (30 + 8) + 7 * q + 3 + 1 + 17) ≤ 80 * q + 60 := by
    have : q * (30 + 8) = 38 * q := by ring
    omega
  refine (WXExec.seq hhead (WXExec.seq hloop htail)).cast cap ?_ hcost
  -- the final state
  have hrec : [true, top] ++ Streaming.marks (xb top (binary q v) false) ++ [false] = decRec q v := by
    rw [decRec_eq q v hq hv]
  unfold bitSt
  rw [hmk, hσ1, appendO_append]
  apply WState.eq
  · funext i
    by_cases h1 : i = OP
    · subst h1; simp [appendO, Function.update_apply, hS]
    · by_cases h2 : i = OUT
      · subst h2; simp [appendO, Function.update_apply, h1, ← hrec, marks_len, xb_length, hbl, hOUT]; omega
      · simp [appendO, Function.update_apply, h1, h2]
  · funext i
    by_cases h2 : i = OUT
    · subst h2; simp [appendO, Function.update_apply, ← hrec]
    · simp [appendO, Function.update_apply, h2]
  · funext r
    simp only [appendO, WState.setv_val, WState.seth_val, WState.sets_val, Function.update_apply]
    by_cases r1 : r = SEEN
    · subst r1; simp [Ne.symm hTS, hCPS, Ne.symm hCPS, hCOS, Ne.symm hCOS, hSE]
    · by_cases r2 : r = TOP
      · subst r2; simp [r1, hCPT, Ne.symm hCPT, hCOT, Ne.symm hCOT, hT]
      · by_cases r3 : r = CP
        · subst r3; simp [r1, r2, hCOCP, Ne.symm hCOCP]
        · by_cases r4 : r = CO
          · subst r4; simp [r1, r2, r3, ← hrec, marks_len, xb_length, hbl]; omega
          · simp [r1, r2, r3, r4]
  · rfl

/-- The decoded records of a list of entries. -/
def decRecs (q : ℕ) (vals : List ℕ) : List Bool := vals.flatMap (decRec q)

theorem decRec_length (q v : ℕ) : (decRec q v).length = 2 * q + 3 := by
  simp [decRec, frame_length]; ring

theorem decRecs_length (q : ℕ) (vals : List ℕ) : (decRecs q vals).length = vals.length * (2 * q + 3) := by
  induction vals with
  | nil => simp [decRecs]
  | cons v vals ih => simp only [decRecs, List.flatMap_cons, List.length_append, decRec_length] at ih ⊢; rw [ih]; simp; ring

theorem flatMap_binary_length (q : ℕ) (vals : List ℕ) : (vals.flatMap (binary q)).length = vals.length * q := by
  induction vals with
  | nil => simp
  | cons v vals ih => simp only [List.flatMap_cons, List.length_append, binary_length] at ih ⊢; rw [ih]; simp; ring

/-- The decoder's state after `i` entries. -/
def decSt (σ : WState ns nr) (OP OUT : Fin (ns + 1)) (CO CP : Fin nr) (q : ℕ) (vals : List ℕ) (i : ℕ) :
    WState ns nr :=
  ((appendO σ OUT CO (decRecs q (vals.take i))).seth OP (i * q)).setv CP (i * q)

/-- The cost bound of `decode`. -/
def decodeCost (N q : ℕ) : ℕ := N * (100 * q + 100) + 30

/-- **The decoder.** The raw stream holds the `q`-bit words `vals` (then anything); the fresh output stream ends
as the record stream of their two's complement values in the sign-magnitude format; every head returns to `0`
and every register to its value. -/
theorem decode_spec {OP OUT : Fin (ns + 1)} {N N2 K K1 K2 CO CP TOP SEEN : Fin nr} (hS : OP ≠ OUT)
    (hR : [N, N2, K, K1, K2, CO, CP, TOP, SEEN].Nodup) (σ : WState ns nr) (q : ℕ) (vals : List ℕ) (rest : List Bool)
    (hq : 1 ≤ q) (hv : ∀ v ∈ vals, v < 2 ^ q) (hOP : σ.st OP = vals.flatMap (binary q) ++ rest) (hOPh : σ.sh OP = 0)
    (hOUT : σ.st OUT = []) (hOUTh : σ.sh OUT = 0) (hN : σ.val N = vals.length) (hN2 : σ.val N2 = 0)
    (hK : σ.val K = q) (hK1 : σ.val K1 = q - 1) (hK2 : σ.val K2 = 0) (hCO : σ.val CO = 0) (hCP : σ.val CP = 0)
    (hT : σ.val TOP = 0) (hSE : σ.val SEEN = 0) (hcap : vals.length * (2 * q + 3) + 2 * q + 4 ≤ cap) :
    WXExec cap (decode OP OUT N N2 K K1 K2 CO CP TOP SEEN) σ
      (σ.sets OUT (recStream (vals.map fun v => binary (q + 1) (encS (tc q v))))) (decodeCost vals.length q) := by
  have hR' := hR
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, not_false_eq_true, List.nodup_nil,
    and_true] at hR'
  obtain ⟨⟨hNN2, hNK, hNK1, hNK2, hNCO, hNCP, hNT, hNS⟩, ⟨hN2K, hN2K1, hN2K2, hN2CO, hN2CP, hN2T, hN2S⟩,
    ⟨hKK1, hKK2, hKCO, hKCP, hKT, hKS⟩, ⟨hK1K2, hK1CO, hK1CP, hK1T, hK1S⟩, ⟨hK2CO, hK2CP, hK2T, hK2S⟩,
    ⟨hCOCP, hCOT, hCOS⟩, ⟨hCPT, hCPS⟩, hTS⟩ := hR'
  have hR7 : [K, K1, K2, CO, CP, TOP, SEEN].Nodup := by
    simp [hKK1, hKK2, hKCO, hKCP, hKT, hKS, hK1K2, hK1CO, hK1CP, hK1T, hK1S, hK2CO, hK2CP, hK2T, hK2S, hCOCP, hCOT,
      hCOS, hCPT, hCPS, hTS]
  have hd0 : decSt σ OP OUT CO CP q vals 0 = σ := by
    unfold decSt
    rw [List.take_zero, show decRecs q [] = [] from rfl, appendO_nil, Nat.zero_mul]
    apply WState.eq
    · funext i; by_cases hi : i = OP
      · subst hi; simp [hOPh]
      · simp [Function.update_of_ne hi]
    · rfl
    · funext r; by_cases hr : r = CP
      · subst hr; simp [hCP]
      · simp [Function.update_of_ne hr]
    · rfl
  have hstep : ∀ i < vals.length, ∀ v1 v2 : ℕ,
      WXExec cap (entry OP OUT K K1 K2 CO CP TOP SEEN) (((decSt σ OP OUT CO CP q vals i).setv N v1).setv N2 v2)
        (((decSt σ OP OUT CO CP q vals (i + 1)).setv N v1).setv N2 v2) (80 * q + 60) := by
    intro i hi v1 v2
    have hsplit : vals.flatMap (binary q) =
        (vals.take i).flatMap (binary q) ++ binary q vals[i] ++ (vals.drop (i + 1)).flatMap (binary q) := by
      have hv' : vals = vals.take i ++ vals[i] :: vals.drop (i + 1) := by
        conv_lhs => rw [← List.take_append_drop i vals, List.drop_eq_getElem_cons hi]
      conv_lhs => rw [hv']
      rw [List.flatMap_append, List.flatMap_cons, List.append_assoc]
    have hpl : ((vals.take i).flatMap (binary q)).length = i * q := by
      rw [flatMap_binary_length, List.length_take]; rw [Nat.min_eq_left hi.le]
    have hrl : (decRecs q (vals.take i)).length = i * (2 * q + 3) := by
      rw [decRecs_length, List.length_take, Nat.min_eq_left hi.le]
    have hcapO : (((decSt σ OP OUT CO CP q vals i).setv N v1).setv N2 v2).val CO + 2 * q + 3 < cap := by
      simp [decSt, appendO, Function.update_apply, hNCO, hN2CO, hCOCP, Ne.symm hNCO, Ne.symm hN2CO, Ne.symm hCOCP,
        hCO, hrl]
      have : i * (2 * q + 3) + (2 * q + 3) ≤ vals.length * (2 * q + 3) := by
        rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hi
      omega
    have e := entry_spec cap hS hR7 (((decSt σ OP OUT CO CP q vals i).setv N v1).setv N2 v2) q vals[i]
      ((vals.take i).flatMap (binary q)) ((vals.drop (i + 1)).flatMap (binary q) ++ rest) hq
      (hv _ (List.getElem_mem hi))
      (by simp [decSt, appendO, Function.update_apply, hS, hOP, hsplit, List.append_assoc])
      (by simp [decSt, appendO, Function.update_apply, hS, hpl])
      (by simp [decSt, appendO, Function.update_apply, hOUT, hOUTh, Ne.symm hS])
      (by simp [decSt, appendO, Function.update_apply, hNK, hN2K, hKCO, hKCP, Ne.symm hNK, Ne.symm hN2K, hK])
      (by simp [decSt, appendO, Function.update_apply, hNK1, hN2K1, hK1CO, hK1CP, Ne.symm hNK1, Ne.symm hN2K1, hK1])
      (by simp [decSt, appendO, Function.update_apply, hNK2, hN2K2, hK2CO, hK2CP, Ne.symm hNK2, Ne.symm hN2K2, hK2])
      (by simp [decSt, appendO, Function.update_apply, hNT, hN2T, hCOT, hCPT, Ne.symm hNT, Ne.symm hN2T,
        Ne.symm hCOT, Ne.symm hCPT, hT])
      (by simp [decSt, appendO, Function.update_apply, hNS, hN2S, hCOS, hCPS, Ne.symm hNS, Ne.symm hN2S,
        Ne.symm hCOS, Ne.symm hCPS, hSE]) hcapO
      (by simp [decSt, Function.update_apply, hNCP, hN2CP, Ne.symm hNCP, Ne.symm hN2CP]
          have : i * q + q ≤ vals.length * q := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hi
          nlinarith) (by omega)
    refine e.cast cap ?_ le_rfl
    have htk : decRecs q (vals.take (i + 1)) = decRecs q (vals.take i) ++ decRec q vals[i] := by
      unfold decRecs; rw [List.take_add_one, List.getElem?_eq_getElem hi, List.flatMap_append]; simp
    unfold decSt
    rw [htk, hpl]
    apply WState.eq
    · funext j
      by_cases h1 : j = OP
      · subst h1; simp [appendO, Function.update_apply, hS]; ring
      · by_cases h2 : j = OUT
        · subst h2; simp [appendO, Function.update_apply, h1, hOUT, hOUTh]
        · simp [appendO, Function.update_apply, h1, h2]
    · funext j
      by_cases h2 : j = OUT
      · subst h2; simp [appendO, Function.update_apply, hOUT]
      · simp [appendO, Function.update_apply, h2]
    · funext r
      simp only [appendO, WState.setv_val, WState.seth_val, WState.sets_val, Function.update_apply]
      by_cases r1 : r = N2
      · subst r1; simp [hN2CO, hN2CP]
      · by_cases r2 : r = N
        · subst r2; simp [r1, hNCO, hNCP]
        · by_cases r3 : r = CP
          · subst r3; simp [r1, r2, hCOCP, Ne.symm hCOCP]; ring
          · by_cases r4 : r = CO
            · subst r4; simp [r1, r2, r3, Nat.add_assoc]
            · simp [r1, r2, r3, r4]
    · rfl
  have hloop := Runs.repE (cap := cap) (body := entry OP OUT K K1 K2 CO CP TOP SEEN) hNN2 (80 * q + 60) vals.length
    (decSt σ OP OUT CO CP q vals) (by nlinarith)
    (fun k => by simp [decSt, appendO, Function.update_apply, hNCO, hNCP, hd0])
    (fun k => by simp [decSt, appendO, Function.update_apply, hN2CO, hN2CP, hd0])
    hstep (by rw [hd0, hN]) (by rw [hd0, hN2])
  rw [hd0] at hloop
  -- closing: the final `false`, both rewinds
  set σ1 := decSt σ OP OUT CO CP q vals vals.length with hσ1
  have hrl : (decRecs q vals).length = vals.length * (2 * q + 3) := decRecs_length q vals
  have h1O : σ1.sh OUT = (σ1.st OUT).length := by
    simp [hσ1, decSt, appendO, Function.update_apply, Ne.symm hS, hOUT, hOUTh]
  have h1CO : σ1.val CO = (decRecs q vals).length := by
    simp [hσ1, decSt, appendO, Function.update_apply, hCOCP, hCO]
  have e1 := emitX_spec cap OUT CO false σ1 h1O (by rw [h1CO, hrl]; omega)
  have e2 := WXExec.wm (wrewind_spec cap OUT CO ((decRecs q vals).length + 1) (appendO σ1 OUT CO [false])
    (by simp [appendO, h1CO]) (by simp [appendO, h1CO, hrl]; omega))
  set σ2 := ((appendO σ1 OUT CO [false]).setv CO 0).seth OUT
    ((appendO σ1 OUT CO [false]).sh OUT - ((decRecs q vals).length + 1)) with hσ2
  have e3 := WXExec.wm (wrewind_spec cap OP CP (vals.length * q) σ2
    (by simp [hσ2, hσ1, decSt, appendO, Function.update_apply, Ne.symm hCOCP])
    (by simp [hσ2, hσ1, decSt, appendO, Function.update_apply, Ne.symm hCOCP]; nlinarith))
  refine (WXExec.seq hloop (WXExec.seq e1 (WXExec.seq e2 e3))).cast cap ?_ (by
    unfold decodeCost; rw [hrl]; nlinarith)
  have hrec : decRecs q vals ++ [false] = recStream (vals.map fun v => binary (q + 1) (encS (tc q v))) := by
    unfold decRecs recStream; rw [List.flatMap_map]; rfl
  apply WState.eq
  · funext j
    by_cases h1 : j = OP
    · subst h1; simp [hσ2, hσ1, decSt, appendO, Function.update_apply, hS, hOPh]
    · by_cases h2 : j = OUT
      · subst h2; simp [hσ2, hσ1, decSt, appendO, Function.update_apply, h1, hOUT, hOUTh]
      · simp [hσ2, hσ1, decSt, appendO, Function.update_apply, h1, h2]
  · funext j
    by_cases h2 : j = OUT
    · subst h2; simp [hσ2, hσ1, decSt, appendO, Function.update_apply, hOUT, List.take_length, ← hrec]
    · simp [hσ2, hσ1, decSt, appendO, Function.update_apply, h2]
  · funext r
    simp only [hσ2, hσ1, decSt, appendO, WState.setv_val, WState.seth_val, WState.sets_val, Function.update_apply]
    by_cases r1 : r = CP
    · subst r1; simp [hCP]
    · by_cases r2 : r = CO
      · subst r2; simp [r1, hCO]
      · simp [r1, r2]
  · rfl

end Specs

end NearCubicGates.Close.TabMachine
