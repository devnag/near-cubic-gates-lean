import Proof.Gates.WordPrograms.BinW
import Proof.Gates.WordPrograms.Hoare

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicGates.Close.WordPrograms.SInt
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length binary_value)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (NumOn)
open NearCubicWires.WireExponent3_5.UnionMachine.Round (mapS_keepA)
open NearCubicWires.WireExponent3_5.UnionMachine.RegRat (mulCost)

variable {ns nr : ℕ}

/-! ## The format -/

/-- Sign and magnitude, sign in the low bit. -/
def encS (z : ℤ) : ℕ := 2 * z.natAbs + if z < 0 then 1 else 0

/-- The signed value of a magnitude and a sign bit. -/
def sval (m : ℕ) (s : Bool) : ℤ := if s then -(m : ℤ) else m

theorem encS_lt {z : ℤ} {W : ℕ} (h : z.natAbs < 2 ^ W) : encS z < 2 ^ (W + 1) := by
  unfold encS; rw [pow_succ]; split <;> omega

theorem encS_div (z : ℤ) : encS z / 2 = z.natAbs := by unfold encS; split <;> omega

theorem encS_mod (z : ℤ) : encS z % 2 = if z < 0 then 1 else 0 := by unfold encS; split <;> omega

@[simp] theorem encS_zero : encS 0 = 0 := rfl

theorem encS_inj {a b : ℤ} (h : encS a = encS b) : a = b := by
  have h1 : a.natAbs = b.natAbs := by rw [← encS_div a, ← encS_div b, h]
  have h2 : (if a < 0 then 1 else 0) = (if b < 0 then 1 else 0) := by rw [← encS_mod a, ← encS_mod b, h]
  rcases Int.natAbs_eq a with ha | ha <;> rcases Int.natAbs_eq b with hb | hb <;>
    split_ifs at h2 with h3 h4 <;> omega

theorem binary_encS (W : ℕ) (z : ℤ) : binary (W + 1) (encS z) = decide (z < 0) :: binary W z.natAbs := by
  simp only [binary, encS_div, encS_mod]
  split <;> simp_all

/-- The printer's sign-magnitude field is the `encS` word. -/
theorem signMagnitude_eq (W : ℕ) (z : ℤ) : MatrixScoreBatch.signMagnitude W z = binary (W + 1) (encS z) := by
  rw [binary_encS]; rfl

/-- `encS` of a magnitude with a sign bit: the sign is dropped at zero. -/
theorem encS_sval (m : ℕ) (s : Bool) : encS (sval m s) = 2 * m + if s ∧ m ≠ 0 then 1 else 0 := by
  unfold encS sval
  cases s <;> simp <;> split_ifs <;> omega

theorem natAbs_sval (m : ℕ) (s : Bool) : (sval m s).natAbs = m := by
  unfold sval; cases s <;> simp

/-- A signed integer on a stream. -/
def SNumOn (σ : WState ns nr) (X : Fin (ns + 1)) (W : ℕ) (z : ℤ) : Prop :=
  NumOn σ X (W + 1) (encS z) ∧ z.natAbs < 2 ^ W

theorem SNumOn.lt {σ : WState ns nr} {X : Fin (ns + 1)} {W : ℕ} {z : ℤ} (h : SNumOn σ X W z) :
    encS z < 2 ^ (W + 1) := encS_lt h.2

theorem sNumOn_sets_self (σ : WState ns nr) (X : Fin (ns + 1)) (W : ℕ) (z : ℤ) (h : σ.sh X = 0)
    (hz : z.natAbs < 2 ^ W) : SNumOn (σ.sets X (frame (binary (W + 1) (encS z)))) X W z :=
  ⟨BinW.numOn_sets_self σ X _ _ h, hz⟩

theorem SameExcept.sNumOn {σ τ : WState ns nr} {S : List (Fin (ns + 1))} {Rg : List (Fin nr)}
    (h : SameExcept σ τ S Rg) {X : Fin (ns + 1)} (hX : X ∉ S) {W : ℕ} {z : ℤ} (hn : SNumOn σ X W z) :
    SNumOn τ X W z := ⟨h.numOn hX hn.1, hn.2⟩

/-! ## The sign bit -/

/-- `S := ` the low bit of `X` (bit `1` of its frame); `S` is `0` before. -/
def sgnBitW (X : Fin (ns + 1)) (S : Fin nr) : WM ns nr := .seq (.fwd X) (.seq (.ifs X (.inc S) .skip) (.bwd X))

theorem sgnBitW_spec (cap : ℕ) {X : Fin (ns + 1)} {S : Fin nr} (σ : WState ns nr) (W e : ℕ)
    (hX : NumOn σ X (W + 1) e) (hS : σ.val S = 0) (hcap : 1 ≤ cap) :
    WExec cap (sgnBitW X S) σ (σ.setv S (e % 2)) 8 := by
  have hb : wbit (σ.seth X (σ.sh X + 1)) X = (e % 2 == 1) := by
    simp only [wbit, WState.seth_st, WState.seth_sh, Function.update_self, hX.1, hX.2, binary, frame]
    rfl
  have h1 := WExec.fwd (cap := cap) X σ
  rcases Nat.mod_two_eq_zero_or_one e with he | he
  · have hb' : wbit (σ.seth X (σ.sh X + 1)) X = false := by rw [hb, he]; rfl
    have h2 := WExec.ifsF (P := .inc S) hb' (WExec.skip (cap := cap) (σ.seth X (σ.sh X + 1)))
    have h3 := WExec.bwd (cap := cap) X (σ.seth X (σ.sh X + 1))
    refine WExec.cast cap (WExec.seq h1 (WExec.seq h2 h3)) ?_ (by omega)
    apply WState.eq
    · funext i; by_cases hi : i = X
      · subst hi; simp [hX.2]
      · simp [Function.update_of_ne hi]
    · rfl
    · simp [he, ← hS]
    · rfl
  · have hb' : wbit (σ.seth X (σ.sh X + 1)) X = true := by rw [hb, he]; rfl
    have hi := WExec.inc (cap := cap) S (σ.seth X (σ.sh X + 1)) (by simp [hS]; omega)
    have h2 := WExec.ifsT (Q := .skip) hb' hi
    have h3 := WExec.bwd (cap := cap) X ((σ.seth X (σ.sh X + 1)).setv S ((σ.seth X (σ.sh X + 1)).val S + 1))
    refine WExec.cast cap (WExec.seq h1 (WExec.seq h2 h3)) ?_ (by omega)
    apply WState.eq
    · funext i; by_cases hi : i = X
      · subst hi; simp [hX.2]
      · simp [Function.update_of_ne hi]
    · rfl
    · simp [he, hS]
    · rfl

/-! ## Zero test -/

/-- The zero pass's state: no one bit seen so far. -/
def zN (a _b c : Bool) : Bool := c && !a

theorem mapS_zN : ∀ (as bs : List Bool) (c : Bool), as.length = bs.length →
    (mapS keepA zN as bs c).2 = (c && as.all (· == false))
  | [], [], c, _ => by simp [mapS]
  | a :: as, b :: bs, c, h => by
    simp only [mapS]
    rw [mapS_zN as bs _ (by simpa using h)]
    cases a <;> cases c <;> simp [zN]
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h

theorem binary_all_false : ∀ (W m : ℕ), m < 2 ^ W → ((binary W m).all (· == false) = decide (m = 0))
  | 0, m, h => by simp at h; simp [binary, h]
  | W + 1, m, h => by
    simp only [binary, List.all_cons]
    rw [binary_all_false W (m / 2) (by rw [pow_succ] at h; omega)]
    rcases Nat.mod_two_eq_zero_or_one m with hm | hm <;> simp [hm] <;> omega

/-- `F := [a = 0]` (`B`: any word of the same width; both kept). -/
def zTestW (A B : Fin (ns + 1)) (F R : Fin nr) : WM ns nr := .seq (.inc F) (mapPass keepA zN A B F R)

theorem zTestW_spec (cap W : ℕ) {A B : Fin (ns + 1)} {F R : Fin nr} (hAB : A ≠ B) (hFR : F ≠ R) (σ : WState ns nr)
    (a b : ℕ) (hA : NumOn σ A W a) (hB : NumOn σ B W b) (hF : σ.val F = 0) (hR : σ.val R = 0) (ha : a < 2 ^ W)
    (hcap : 2 * W + 1 ≤ cap) : WExec cap (zTestW A B F R) σ (σ.setv F (decide (a = 0)).toNat) (41 * W + 7) := by
  have h1 := WExec.inc (cap := cap) F σ (by omega)
  rw [hF] at h1
  have h2 := mapPass_spec cap keepA zN A B F R hAB hFR (by omega) (binary W a) (binary W b) [] [false] true
    (σ.setv F 1) (by simp) (by simp [hA.1, BinW.frame_frameP]) (by simpa using hA.2)
    (by simp [hB.1, BinW.frame_frameP]) (by simpa using hB.2) (by simp) (by simp [Ne.symm hFR, hR]) (by simp; omega)
  rw [mapS_keepA zN _ _ _ (by simp), mapS_zN _ _ _ (by simp), binary_length, binary_all_false W a ha] at h2
  refine WExec.cast cap (WExec.seq h1 h2) ?_ (by omega)
  rw [Bool.true_and]
  apply WState.eq
  · rfl
  · simp [← BinW.frame_frameP, ← hA.1]
  · simp
  · rfl

/-- `M := |x|`, `S := [x < 0]` (`M`: any width-`W+1` word; `S = 0` before). -/
def split (X M : Fin (ns + 1)) (S F R : Fin nr) : WMX ns nr :=
  .seq (BinW.copy M X F R) (.seq (BinW.half M R) (.wm (sgnBitW X S)))

section Split
variable (cap W : ℕ) {X M : Fin (ns + 1)} {S F R : Fin nr}

theorem split_spec (hXM : X ≠ M) (hFR : F ≠ R) (σ : WState ns nr) (x : ℤ) (m0 : ℕ)
    (hX : SNumOn σ X W x) (hM : NumOn σ M (W + 1) m0) (hS : σ.val S = 0) (hF : σ.val F = 0) (hR : σ.val R = 0)
    (hcap : 2 * (W + 1) + 1 ≤ cap) :
    WXExec cap (split X M S F R) σ ((σ.sets M (frame (binary (W + 1) x.natAbs))).setv S (decide (x < 0)).toNat)
      (76 * W + 125) := by
  have h1 := BinW.copy_spec cap (W + 1) (Ne.symm hXM) hFR σ m0 (encS x) hM hX.1 hF hR (by omega)
  set σ1 := σ.sets M (frame (binary (W + 1) (encS x))) with hσ1
  have hM1 : NumOn σ1 M (W + 1) (encS x) := BinW.numOn_sets_self σ M _ _ hM.2
  have h2 := BinW.half_spec cap (W + 1) σ1 (encS x) hM1 (by simpa [hσ1] using hR) hX.lt (by omega)
  set σ2 := σ1.sets M (frame (binary (W + 1) (encS x / 2))) with hσ2
  have hX2 : NumOn σ2 X (W + 1) (encS x) := BinW.numOn_sets_ne (BinW.numOn_sets_ne hX.1 hXM _) hXM _
  have h3 := sgnBitW_spec cap σ2 W (encS x) hX2 (by simpa [hσ2, hσ1] using hS) (by omega)
  refine WXExec.seq' cap h1 (WXExec.seq' cap h2 (WXExec.wm h3) le_rfl) (by omega) |>.cast cap ?_ le_rfl
  rw [hσ2, hσ1, BinW.sets_sets, encS_div, encS_mod]
  congr 1
  rcases lt_or_ge x 0 with h | h
  · simp [h]
  · simp [h, not_lt.mpr h]

end Split

/-- `X := sval m s` (normalized), `S := 0`; `M` holds `m < 2^W`, `X` any width-`W+1` word, `S ∈ {0,1}`. -/
def join (M X : Fin (ns + 1)) (S F R : Fin nr) : WMX ns nr :=
  .seq (.wm (zTestW M X F R))
    (.seq (.ifr F (.seq (WMX.dec F) (.ifr S (WMX.dec S) WMX.skip)) WMX.skip)
      (.seq (BinW.copy X M F R)
        (.ifr S (.seq (WMX.dec S) (.seq (WMX.inc F) (BinW.shlc X M F R))) (BinW.shlc X M F R))))

section Join
variable (cap W : ℕ) {X M : Fin (ns + 1)} {S F R : Fin nr}

theorem join_spec (hXM : X ≠ M) (hFR : F ≠ R) (hSF : S ≠ F) (hSR : S ≠ R) (σ : WState ns nr) (m x0 : ℕ) (s : Bool)
    (hM : NumOn σ M (W + 1) m) (hm : m < 2 ^ W) (hX : NumOn σ X (W + 1) x0) (hS : σ.val S = s.toNat)
    (hF : σ.val F = 0) (hR : σ.val R = 0) (hcap : 2 * (W + 1) + 1 ≤ cap) :
    WXExec cap (join M X S F R) σ ((σ.sets X (frame (binary (W + 1) (encS (sval m s))))).setv S 0)
      (130 * W + 160) := by
  have hm1 : m < 2 ^ (W + 1) := by rw [pow_succ]; omega
  have h1 := WXExec.wm (zTestW_spec cap (W + 1) (Ne.symm hXM) hFR σ m x0 hM hX hF hR hm1 (by omega))
  set σ1 := σ.setv F (decide (m = 0)).toNat with hσ1
  -- normalize the sign of zero
  set s' : Bool := s && decide (m ≠ 0) with hs'
  have h2 : WXExec cap (.ifr F (.seq (WMX.dec F) (.ifr S (WMX.dec S) WMX.skip)) WMX.skip) σ1
      (σ.setv S s'.toNat) 5 := by
    by_cases hm0 : m = 0
    · have hv : σ1.val F ≠ 0 := by simp [hσ1, hm0]
      have hd := WXExec.dec cap F σ1 (by simp [hσ1, hm0]; omega)
      set σ2 := σ1.setv F (σ1.val F - 1) with hσ2
      cases s
      · have hv2 : σ2.val S = 0 := by simp [hσ2, hσ1, Function.update_of_ne hSF, hS]
        refine WXExec.mono (WXExec.ifrT hv (WXExec.seq hd (WXExec.ifrF hv2 (WXExec.skip cap σ2)))) (by omega)
          |>.cast cap ?_ le_rfl
        apply WState.eq <;> try rfl
        funext r; simp [hσ2, hσ1, Function.update_apply, hm0, hs', hF]; split_ifs <;> simp_all
      · have hv2 : σ2.val S ≠ 0 := by simp [hσ2, hσ1, Function.update_of_ne hSF, hS]
        have hd2 := WXExec.dec cap S σ2 (by simp [hσ2, hσ1, Function.update_of_ne hSF, hS]; omega)
        refine WXExec.mono (WXExec.ifrT hv (WXExec.seq hd (WXExec.ifrT hv2 hd2))) (by omega) |>.cast cap ?_ le_rfl
        apply WState.eq <;> try rfl
        funext r; simp [hσ2, hσ1, Function.update_apply, hm0, hs', hF, hS]; split_ifs <;> simp_all
    · have hv : σ1.val F = 0 := by simp [hσ1, hm0]
      refine WXExec.mono (WXExec.ifrF hv (WXExec.skip cap σ1)) (by omega) |>.cast cap ?_ le_rfl
      apply WState.eq <;> try rfl
      funext r; simp [hσ1, Function.update_apply, hm0, hs', hF, hS]; split_ifs <;> simp_all
  set σ2 := σ.setv S s'.toNat with hσ2
  have hM2 : NumOn σ2 M (W + 1) m := BinW.numOn_setv hM _ _
  have hX2 : NumOn σ2 X (W + 1) x0 := BinW.numOn_setv hX _ _
  have h3 := BinW.copy_spec cap (W + 1) hXM hFR σ2 x0 m hX2 hM2 (by simp [hσ2, Function.update_of_ne (Ne.symm hSF), hF])
    (by simp [hσ2, Function.update_of_ne (Ne.symm hSR), hR]) (by omega)
  set σ3 := σ2.sets X (frame (binary (W + 1) m)) with hσ3
  have hX3 : NumOn σ3 X (W + 1) m := BinW.numOn_sets_self σ2 X _ _ (by simpa [hσ2] using hX.2)
  have hM3 : NumOn σ3 M (W + 1) m := BinW.numOn_sets_ne hM2 (Ne.symm hXM) _
  have hF3 : σ3.val F = 0 := by simp [hσ3, hσ2, Function.update_of_ne (Ne.symm hSF), hF]
  have hR3 : σ3.val R = 0 := by simp [hσ3, hσ2, Function.update_of_ne (Ne.symm hSR), hR]
  have hfin : 2 * m + (if s' then 1 else 0) = encS (sval m s) := by
    rw [encS_sval, hs']; cases s <;> simp
  have h4 : WXExec cap (.ifr S (.seq (WMX.dec S) (.seq (WMX.inc F) (BinW.shlc X M F R))) (BinW.shlc X M F R)) σ3
      ((σ.sets X (frame (binary (W + 1) (encS (sval m s))))).setv S 0) (41 * (W + 1) + 10) := by
    cases hsc : s'
    · have hv : σ3.val S = 0 := by simp [hσ3, hσ2, hsc]
      have hsh := BinW.shlc_spec cap (W + 1) hXM hFR σ3 m m false hX3 hM3 (by simpa using hF3) hR3 hm1 (by omega)
      refine WXExec.mono (WXExec.ifrF hv hsh) (by omega) |>.cast cap ?_ le_rfl
      rw [← hfin, hsc]
      have hov : decide (2 ^ (W + 1) ≤ 2 * m + (false : Bool).toNat) = false := by
        simp; rw [pow_succ]; omega
      apply WState.eq <;> try rfl
      · funext i; by_cases hi : i = X
        · subst hi; simp [hσ3]
        · simp [hσ3, hσ2, Function.update_of_ne hi]
      · funext r; simp [hσ3, hσ2, Function.update_apply, hov, hsc]; split_ifs <;> simp_all
    · have hv : σ3.val S ≠ 0 := by simp [hσ3, hσ2, hsc]
      have hd := WXExec.dec cap S σ3 (by simp [hσ3, hσ2, hsc]; omega)
      set σ4 := σ3.setv S (σ3.val S - 1) with hσ4
      have hi := WXExec.inc cap F σ4 (by simp [hσ4, Function.update_of_ne (Ne.symm hSF), hF3]; omega)
      set σ5 := σ4.setv F (σ4.val F + 1) with hσ5
      have hsh := BinW.shlc_spec cap (W + 1) hXM hFR σ5 m m true (BinW.numOn_setv (BinW.numOn_setv hX3 _ _) _ _)
        (BinW.numOn_setv (BinW.numOn_setv hM3 _ _) _ _)
        (by simp [hσ5, hσ4, Function.update_of_ne (Ne.symm hSF), hF3]) (by
          simp [hσ5, hσ4, Function.update_of_ne (Ne.symm hSR), Function.update_of_ne (Ne.symm hFR), hR3]) hm1
        (by omega)
      refine WXExec.mono (WXExec.ifrT hv (WXExec.seq hd (WXExec.seq hi hsh))) (by omega) |>.cast cap ?_ le_rfl
      rw [← hfin, hsc]
      have hov : decide (2 ^ (W + 1) ≤ 2 * m + (true : Bool).toNat) = false := by
        simp; rw [pow_succ]; omega
      apply WState.eq <;> try rfl
      · funext i; by_cases hi : i = X
        · subst hi; simp [hσ5, hσ4, hσ3]
        · simp [hσ5, hσ4, hσ3, hσ2, Function.update_of_ne hi]
      · funext r; simp [hσ5, hσ4, hσ3, hσ2, Function.update_apply, hov, hsc, hF3]; split_ifs <;> simp_all
  exact WXExec.seq' cap h1 (WXExec.seq' cap h2 (WXExec.seq' cap h3 h4 le_rfl) le_rfl) (by omega)

end Join

/-! ## The signed sum of two magnitudes with signs -/

/-- After the core: `M` holds `|v|`, `S` a sign with `sval |v| s' = v`, `T = 0`, `N` some scratch word; only
`M N S T` changed. -/
def CorePost (σ : WState ns nr) (M N : Fin (ns + 1)) (S T : Fin nr) (W : ℕ) (v : ℤ) (τ : WState ns nr) : Prop :=
  NumOn τ M (W + 1) v.natAbs ∧ (∃ s' : Bool, sval v.natAbs s' = v ∧ τ.val S = s'.toNat) ∧ τ.val T = 0 ∧
    (∃ k, NumOn τ N (W + 1) k) ∧ SameExcept σ τ [M, N] [S, T]

/-- The compare-and-subtract arm: `M := |m − n|`; if `m < n` the sign register is set by `fix`. -/
def subArm (M N : Fin (ns + 1)) (F R : Fin nr) (fix : WMX ns nr) : WMX ns nr :=
  .seq (BinW.lt M N F R)
    (.ifr F (.seq (WMX.dec F) (.seq (BinW.sub N M F R) (.seq (BinW.copy M N F R) fix))) (BinW.sub M N F R))

/-- The core: from magnitudes `m n` with signs `s t`, `M := |sval m s + sval n t|` with its sign in `S`. -/
def addCore (M N : Fin (ns + 1)) (S T F R : Fin nr) : WMX ns nr :=
  .ifr S
    (.ifr T (.seq (BinW.add M N F R) (WMX.dec T)) (subArm M N F R (WMX.dec S)))
    (.ifr T (.seq (WMX.dec T) (subArm M N F R (WMX.inc S))) (BinW.add M N F R))

section Core
variable (cap W : ℕ) {M N : Fin (ns + 1)} {S T F R : Fin nr}

theorem subArm_spec (hMN : M ≠ N) (hFR : F ≠ R) (σ : WState ns nr) (m n : ℕ) (fix : WMX ns nr) (cf : ℕ)
    (hM : NumOn σ M (W + 1) m) (hN : NumOn σ N (W + 1) n) (hm : m < 2 ^ (W + 1)) (hn : n < 2 ^ (W + 1))
    (hF : σ.val F = 0) (hR : σ.val R = 0) (hcap : 2 * (W + 1) + 1 ≤ cap) (Q : WState ns nr → Prop)
    (hlt : m < n → Runs cap fix ((σ.sets N (frame (binary (W + 1) (n - m)))).sets M (frame (binary (W + 1) (n - m))))
      cf Q)
    (hge : n ≤ m → Q (σ.sets M (frame (binary (W + 1) (m - n))))) :
    Runs cap (subArm M N F R fix) σ (123 * W + 150 + cf) Q := by
  have h1 := BinW.lt_spec cap (W + 1) hMN hFR σ m n hM hN hF hR hm hn (by omega)
  have hF0 : (σ.setv F (decide (m < n)).toNat).setv F 0 = σ := by
    apply WState.eq <;> try rfl
    funext r; by_cases hr : r = F
    · subst hr; simp [hF]
    · simp [Function.update_of_ne hr]
  by_cases hmn : m < n
  · have hv : (σ.setv F (decide (m < n)).toNat).val F ≠ 0 := by simp [hmn]
    have hd := WXExec.dec cap F (σ.setv F (decide (m < n)).toNat) (by simp [hmn]; omega)
    have hd' : WXExec cap (WMX.dec F) (σ.setv F (decide (m < n)).toNat) σ 1 :=
      hd.cast cap (by
        rw [show (σ.setv F (decide (m < n)).toNat).val F - 1 = 0 by simp [hmn]]; exact hF0) le_rfl
    have hs := BinW.sub_spec cap (W + 1) (Ne.symm hMN) hFR σ n m hN hM hF hR hmn.le hn (by omega)
    have hc := BinW.copy_spec cap (W + 1) hMN hFR (σ.sets N (frame (binary (W + 1) (n - m)))) m (n - m)
      (BinW.numOn_sets_ne hM hMN _) (BinW.numOn_sets_self σ N _ _ hN.2) (by simpa using hF) (by simpa using hR)
      (by omega)
    exact (Runs.seqE h1 (Runs.ifrT hv (Runs.seqE hd' (Runs.seqE hs (Runs.seqE hc (hlt hmn)))))).cost (by omega)
  · have hv : (σ.setv F (decide (m < n)).toNat).val F = 0 := by simp [hmn]
    have hs := BinW.sub_spec cap (W + 1) hMN hFR (σ.setv F (decide (m < n)).toNat) m n (BinW.numOn_setv hM _ _)
      (BinW.numOn_setv hN _ _) hv (by simp [Function.update_of_ne (Ne.symm hFR), hR]) (by omega) hm (by omega)
    have e : (σ.setv F (decide (m < n)).toNat).sets M (frame (binary (W + 1) (m - n))) =
        σ.sets M (frame (binary (W + 1) (m - n))) := by
      apply WState.eq <;> try rfl
      funext r; by_cases hr : r = F
      · subst hr; simp [hmn, hF]
      · simp [Function.update_of_ne hr]
    rw [e] at hs
    exact (Runs.seqE h1 (Runs.ifrF hv (Runs.of hs (hge (by omega))))).cost (by omega)

theorem addCore_spec (hMN : M ≠ N) (hFR : F ≠ R) (hST : S ≠ T) (hTF : T ≠ F)
    (hTR : T ≠ R) (σ : WState ns nr) (m n : ℕ) (s t : Bool) (hM : NumOn σ M (W + 1) m) (hN : NumOn σ N (W + 1) n)
    (hm : m < 2 ^ W) (hn : n < 2 ^ W) (hS : σ.val S = s.toNat) (hT : σ.val T = t.toNat) (hF : σ.val F = 0)
    (hR : σ.val R = 0) (hcap : 2 * (W + 1) + 1 ≤ cap) :
    Runs cap (addCore M N S T F R) σ (123 * W + 160) (CorePost σ M N S T W (sval m s + sval n t)) := by
  have hm1 : m < 2 ^ (W + 1) := by rw [pow_succ]; omega
  have hn1 : n < 2 ^ (W + 1) := by rw [pow_succ]; omega
  have hmn1 : m + n < 2 ^ (W + 1) := by rw [pow_succ]; omega
  have hfr : ∀ (τ : WState ns nr), (∀ x, x ≠ M → x ≠ N → τ.st x = σ.st x ∧ τ.sh x = σ.sh x) →
      (∀ r, r ≠ S → r ≠ T → τ.val r = σ.val r) → τ.cell = σ.cell → SameExcept σ τ [M, N] [S, T] := by
    intro τ h1 h2 h3
    refine ⟨fun x hx => ?_, fun r hr => ?_, h3⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx; exact h1 x hx.1 hx.2
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr; exact h2 r hr.1 hr.2
  cases s <;> cases t
  · -- both nonnegative: `M := m + n`
    have hv : σ.val S = 0 := by simpa using hS
    have hv' : σ.val T = 0 := by simpa using hT
    have h := BinW.add_spec cap (W + 1) hMN hFR σ m n hM hN hF hR hmn1 (by omega)
    refine (Runs.ifrF hv (Runs.ifrF hv' (Runs.of h ?_))).cost (by omega)
    have e : (sval m false + sval n false).natAbs = m + n := by simp [sval]; omega
    refine ⟨by rw [e]; exact BinW.numOn_sets_self σ M _ _ hM.2, ⟨false, ?_, by simpa using hS⟩, by simpa using hT,
      ⟨n, BinW.numOn_sets_ne hN (Ne.symm hMN) _⟩, hfr _ (fun x h1 _ => ?_) (fun _ _ _ => rfl) rfl⟩
    · rw [e]; simp [sval]
    · simp [Function.update_of_ne h1]
  · -- `m − n`
    have hv : σ.val S = 0 := by simpa using hS
    have hv' : σ.val T ≠ 0 := by simp [hT]
    have hd := WXExec.dec cap T σ (by simp [hT]; omega)
    have hT1 : (σ.setv T (σ.val T - 1)).val T = 0 := by simp [hT]
    have hsub := subArm_spec cap W hMN hFR (σ.setv T (σ.val T - 1)) m n (WMX.inc S) 3 (BinW.numOn_setv hM _ _)
      (BinW.numOn_setv hN _ _) hm1 hn1 (by simp [Function.update_of_ne (Ne.symm hTF), hF])
      (by simp [Function.update_of_ne (Ne.symm hTR), hR]) hcap (CorePost σ M N S T W (sval m false + sval n true))
      (fun hmn => ?_) (fun hmn => ?_)
    · exact (Runs.ifrF hv (Runs.ifrT hv' (Runs.seqE hd hsub))).cost (by omega)
    · -- `m < n`: `M := n − m`, sign `1`
      have hi := WXExec.inc cap S (((σ.setv T (σ.val T - 1)).sets N (frame (binary (W + 1) (n - m)))).sets M
        (frame (binary (W + 1) (n - m)))) (by simp [Function.update_of_ne hST, hS]; omega)
      refine Runs.of hi ?_
      have e : (sval m false + sval n true).natAbs = n - m := by simp [sval]; omega
      refine ⟨⟨by rw [e]; simp, by simp [hM.2]⟩, ⟨true, ?_, ?_⟩, ?_, ⟨n - m, by simp [Function.update_of_ne (Ne.symm hMN)],
        by simp [hN.2]⟩, hfr _ (fun x h1 h2 => ?_) (fun r h1 h2 => ?_) rfl⟩
      · rw [e]; simp [sval]; omega
      · simp [Function.update_of_ne hST, hS]
      · simp [Function.update_of_ne (Ne.symm hST), hT]
      · simp [Function.update_of_ne h1, Function.update_of_ne h2]
      · simp [Function.update_of_ne h1, Function.update_of_ne h2]
    · -- `n ≤ m`: `M := m − n`, sign `0`
      have e : (sval m false + sval n true).natAbs = m - n := by simp [sval]; omega
      refine ⟨⟨by rw [e]; simp, by simp [hM.2]⟩, ⟨false, ?_, ?_⟩, ?_, ⟨n, by simp [Function.update_of_ne (Ne.symm hMN), hN.1],
        by simp [hN.2]⟩, hfr _ (fun x h1 _ => ?_) (fun r h1 h2 => ?_) rfl⟩
      · rw [e]; simp [sval]; omega
      · simp [Function.update_of_ne hST, hS]
      · simp [hT]
      · simp [Function.update_of_ne h1]
      · simp [Function.update_of_ne h2]
  · -- `−m + n`
    have hv : σ.val S ≠ 0 := by simp [hS]
    have hv' : σ.val T = 0 := by simpa using hT
    have hsub := subArm_spec cap W hMN hFR σ m n (WMX.dec S) 1 hM hN hm1 hn1 hF hR hcap
      (CorePost σ M N S T W (sval m true + sval n false)) (fun hmn => ?_) (fun hmn => ?_)
    · exact (Runs.ifrT hv (Runs.ifrF hv' hsub)).cost (by omega)
    · have hi := WXExec.dec cap S ((σ.sets N (frame (binary (W + 1) (n - m)))).sets M
        (frame (binary (W + 1) (n - m)))) (by simp [hS]; omega)
      refine Runs.of hi ?_
      have e : (sval m true + sval n false).natAbs = n - m := by simp [sval]; omega
      refine ⟨⟨by rw [e]; simp, by simp [hM.2]⟩, ⟨false, ?_, ?_⟩, ?_, ⟨n - m, by simp [Function.update_of_ne (Ne.symm hMN)],
        by simp [hN.2]⟩, hfr _ (fun x h1 h2 => ?_) (fun r h1 h2 => ?_) rfl⟩
      · rw [e]; simp [sval]; omega
      · simp [hS]
      · simp [Function.update_of_ne (Ne.symm hST), hT]
      · simp [Function.update_of_ne h1, Function.update_of_ne h2]
      · simp [Function.update_of_ne h1]
    · have e : (sval m true + sval n false).natAbs = m - n := by simp [sval]; omega
      refine ⟨by rw [e]; exact BinW.numOn_sets_self _ M _ _ hM.2, ⟨true, ?_, by simpa using hS⟩, by simpa using hT,
        ⟨n, BinW.numOn_sets_ne hN (Ne.symm hMN) _⟩, hfr _ (fun x h1 _ => ?_) (fun _ _ _ => rfl) rfl⟩
      · rw [e]; simp [sval]; omega
      · simp [Function.update_of_ne h1]
  · -- both negative: `M := m + n`, sign `1`
    have hv : σ.val S ≠ 0 := by simp [hS]
    have hv' : σ.val T ≠ 0 := by simp [hT]
    have h := BinW.add_spec cap (W + 1) hMN hFR σ m n hM hN hF hR hmn1 (by omega)
    have hd := WXExec.dec cap T (σ.sets M (frame (binary (W + 1) (m + n)))) (by simp [hT]; omega)
    refine (Runs.ifrT hv (Runs.ifrT hv' (Runs.seqE h (Runs.of hd ?_)))).cost (by omega)
    have e : (sval m true + sval n true).natAbs = m + n := by simp [sval]; omega
    refine ⟨⟨by rw [e]; simp, by simp [hM.2]⟩, ⟨true, ?_, ?_⟩, ?_, ⟨n, by simp [Function.update_of_ne (Ne.symm hMN), hN.1],
      by simp [hN.2]⟩, hfr _ (fun x h1 _ => ?_) (fun r _ h2 => ?_) rfl⟩
    · rw [e]; simp [sval]; omega
    · simp [Function.update_of_ne hST, hS]
    · simp [hT]
    · simp [Function.update_of_ne h1]
    · simp [Function.update_of_ne h2]

end Core

theorem sval_natAbs (x : ℤ) : sval x.natAbs (decide (x < 0)) = x := by
  unfold sval; rcases lt_or_ge x 0 with h | h
  · simp [h, Int.ofNat_natAbs_of_nonpos h.le]
  · simp [not_lt.mpr h, Int.natAbs_of_nonneg h]

theorem sval_not (m : ℕ) (s : Bool) : sval m (!s) = -sval m s := by unfold sval; cases s <;> simp

theorem sval_mul (m n : ℕ) (s t : Bool) : sval (m * n) (s ^^ t) = sval m s * sval n t := by
  unfold sval; cases s <;> cases t <;> simp

/-! ## The operations -/

/-- Flip a sign register (`0 ↔ 1`). -/
def flip (S : Fin nr) : WMX ns nr := .ifr S (WMX.dec S) (WMX.inc S)

theorem flip_spec (cap : ℕ) (S : Fin nr) (σ : WState ns nr) (s : Bool) (hS : σ.val S = s.toNat) (hcap : 1 ≤ cap) :
    WXExec cap (flip S) σ (σ.setv S (!s).toNat) 4 := by
  cases s
  · have h := WXExec.inc cap S σ (by simp [hS]; omega)
    exact (WXExec.ifrF (P := WMX.dec S) (by simpa using hS) h).cast cap (by simp [hS]) (by omega)
  · have h := WXExec.dec cap S σ (by simp [hS]; omega)
    exact (WXExec.ifrT (Q := WMX.inc S) (by simp [hS]) h).cast cap (by simp [hS]) (by omega)

/-- `X := x + y`. -/
def sadd (X Y M N : Fin (ns + 1)) (S T F R : Fin nr) : WMX ns nr :=
  .seq (split X M S F R) (.seq (split Y N T F R) (.seq (addCore M N S T F R) (join M X S F R)))

/-- `X := x − y`. -/
def ssub (X Y M N : Fin (ns + 1)) (S T F R : Fin nr) : WMX ns nr :=
  .seq (split X M S F R) (.seq (split Y N T F R) (.seq (flip T) (.seq (addCore M N S T F R) (join M X S F R))))

/-- `X := −x`. -/
def sneg (X M : Fin (ns + 1)) (S F R : Fin nr) : WMX ns nr :=
  .seq (split X M S F R) (.seq (flip S) (join M X S F R))

/-- `X := x·y` (scratch words `C D`, extra scratch register `G`). -/
def smul (X Y M N C D : Fin (ns + 1)) (S T F R G : Fin nr) : WMX ns nr :=
  .seq (split X M S F R) (.seq (split Y N T F R) (.seq (BinW.mul M N C D F R G)
    (.seq (.ifr T (.seq (WMX.dec T) (flip S)) WMX.skip) (join C X S F R))))

/-- `F := [x < y]`. -/
def slt (X Y M N : Fin (ns + 1)) (S T F R : Fin nr) : WMX ns nr :=
  .seq (split X M S F R) (.seq (split Y N T F R)
    (.ifr S (.ifr T (.seq (WMX.dec S) (.seq (WMX.dec T) (BinW.lt N M F R))) (.seq (WMX.dec S) (WMX.inc F)))
      (.ifr T (WMX.dec T) (BinW.lt M N F R))))

/-- The frame of an operation: only the listed streams changed, every register as before. -/
def OpPost (σ : WState ns nr) (X M N : Fin (ns + 1)) (W : ℕ) (z : ℤ) (τ : WState ns nr) : Prop :=
  SNumOn τ X W z ∧ (∃ a, NumOn τ M (W + 1) a) ∧ (∃ b, NumOn τ N (W + 1) b) ∧ SameExcept σ τ [X, M, N] []

section Ops
variable (cap W : ℕ) {X Y M N C D : Fin (ns + 1)} {S T F R G : Fin nr}

/-- Split both operands, then run `k` with their magnitudes and signs in place. -/
theorem split2 (hS4 : [X, Y, M, N].Nodup) (hR4 : [S, T, F, R].Nodup) (σ : WState ns nr) (x y : ℤ) (m0 n0 : ℕ)
    (hX : SNumOn σ X W x) (hY : SNumOn σ Y W y) (hM : NumOn σ M (W + 1) m0) (hN : NumOn σ N (W + 1) n0)
    (hS : σ.val S = 0) (hT : σ.val T = 0) (hF : σ.val F = 0) (hR : σ.val R = 0) (hcap : 2 * (W + 1) + 1 ≤ cap)
    (P : WMX ns nr) (c : ℕ) (Q : WState ns nr → Prop)
    (hk : ∀ τ, SNumOn τ X W x → SNumOn τ Y W y → NumOn τ M (W + 1) x.natAbs → NumOn τ N (W + 1) y.natAbs →
      τ.val S = (decide (x < 0)).toNat → τ.val T = (decide (y < 0)).toNat → τ.val F = 0 → τ.val R = 0 →
      SameExcept σ τ [M, N] [S, T] → Runs cap P τ c Q) :
    Runs cap (.seq (split X M S F R) (.seq (split Y N T F R) P)) σ (152 * W + 252 + c) Q := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, not_false_eq_true, List.nodup_nil, and_true] at hS4 hR4
  obtain ⟨⟨hXY, hXM, hXN⟩, ⟨hYM, hYN⟩, hMN⟩ := hS4
  obtain ⟨⟨hST, hSF, hSR⟩, ⟨hTF, hTR⟩, hFR⟩ := hR4
  have h1 := split_spec (S := S) cap W hXM hFR σ x m0 hX hM hS hF hR hcap
  set σ1 := (σ.sets M (frame (binary (W + 1) x.natAbs))).setv S (decide (x < 0)).toNat with hσ1
  have hY1 : SNumOn σ1 Y W y := ⟨BinW.numOn_setv (BinW.numOn_sets_ne hY.1 hYM _) _ _, hY.2⟩
  have hN1 : NumOn σ1 N (W + 1) n0 := BinW.numOn_setv (BinW.numOn_sets_ne hN (Ne.symm hMN) _) _ _
  have h2 := split_spec (S := T) cap W hYN hFR σ1 y n0 hY1 hN1 (by simp [hσ1, Function.update_of_ne (Ne.symm hST), hT])
    (by simp [hσ1, Function.update_of_ne (Ne.symm hSF), hF]) (by simp [hσ1, Function.update_of_ne (Ne.symm hSR), hR])
    hcap
  set σ2 := (σ1.sets N (frame (binary (W + 1) y.natAbs))).setv T (decide (y < 0)).toNat with hσ2
  refine (Runs.seqE h1 (Runs.seqE h2 (hk σ2 ⟨?_, hX.2⟩ ⟨?_, hY.2⟩ ?_ ?_ ?_ ?_ ?_ ?_ ?_))).cost (by omega)
  · exact BinW.numOn_setv (BinW.numOn_sets_ne (BinW.numOn_setv (BinW.numOn_sets_ne hX.1 hXM _) _ _) hXN _) _ _
  · exact BinW.numOn_setv (BinW.numOn_sets_ne hY1.1 hYN _) _ _
  · exact BinW.numOn_setv (BinW.numOn_sets_ne (BinW.numOn_setv (BinW.numOn_sets_self σ M _ _ hM.2) _ _)
      hMN _) _ _
  · exact BinW.numOn_setv (BinW.numOn_sets_self σ1 N _ _ (by simp [hσ1, hN.2])) _ _
  · simp [hσ2, hσ1, Function.update_of_ne hST]
  · simp [hσ2]
  · simp [hσ2, hσ1, Function.update_of_ne (Ne.symm hTF), Function.update_of_ne (Ne.symm hSF), hF]
  · simp [hσ2, hσ1, Function.update_of_ne (Ne.symm hTR), Function.update_of_ne (Ne.symm hSR), hR]
  · refine ⟨fun z hz => ?_, fun r hr => ?_, rfl⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
      simp [hσ2, hσ1, Function.update_of_ne hz.1, Function.update_of_ne hz.2]
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [hσ2, hσ1, Function.update_of_ne hr.1, Function.update_of_ne hr.2]

theorem coreJoin (hS4 : [X, Y, M, N].Nodup) (hR4 : [S, T, F, R].Nodup) (σ τ : WState ns nr) (x m n : ℕ)
    (s t : Bool) (hX : NumOn τ X (W + 1) x) (hM : NumOn τ M (W + 1) m) (hN : NumOn τ N (W + 1) n) (hm : m < 2 ^ W)
    (hn : n < 2 ^ W) (hS : τ.val S = s.toNat) (hT : τ.val T = t.toNat) (hF : τ.val F = 0) (hR : τ.val R = 0)
    (hSσ : σ.val S = 0) (hTσ : σ.val T = 0) (hfr : SameExcept σ τ [M, N] [S, T])
    (hv : (sval m s + sval n t).natAbs < 2 ^ W) (hcap : 2 * (W + 1) + 1 ≤ cap) :
    Runs cap (.seq (addCore M N S T F R) (join M X S F R)) τ (253 * W + 321)
      (OpPost σ X M N W (sval m s + sval n t)) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, not_false_eq_true, List.nodup_nil, and_true] at hS4 hR4
  obtain ⟨⟨hXY, hXM, hXN⟩, ⟨hYM, hYN⟩, hMN⟩ := hS4
  obtain ⟨⟨hST, hSF, hSR⟩, ⟨hTF, hTR⟩, hFR⟩ := hR4
  refine Runs.seq' (c2 := 130 * W + 160) (addCore_spec cap W hMN hFR hST hTF hTR τ m n s t hM hN hm hn hS hT hF hR hcap)
    (fun ρ hρ => ?_) (by omega)
  obtain ⟨hMρ, ⟨s', hs', hSρ⟩, hTρ, ⟨k, hNρ⟩, hfrρ⟩ := hρ
  have hXρ : NumOn ρ X (W + 1) x := hfrρ.numOn (by simp [hXM, hXN]) hX
  have hj := join_spec cap W hXM hFR hSF hSR ρ _ x s' hMρ hv hXρ hSρ
    (by rw [hfrρ.val (by simp [Ne.symm hSF, Ne.symm hTF]), hF]) (by rw [hfrρ.val (by simp [Ne.symm hSR, Ne.symm hTR]), hR])
    hcap
  refine (Runs.of hj ⟨⟨?_, hv⟩, ⟨_, BinW.numOn_setv (BinW.numOn_sets_ne hMρ (Ne.symm hXM) _) _ _⟩,
    ⟨k, BinW.numOn_setv (BinW.numOn_sets_ne hNρ (Ne.symm hXN) _) _ _⟩, ?_⟩).cost (by omega)
  · rw [hs']; exact BinW.numOn_setv (BinW.numOn_sets_self ρ X _ _ hXρ.2) _ _
  · have h1 := hfr.comp' hfrρ
    refine ⟨fun z hz => ?_, fun r _ => ?_, by simp [h1.cell]⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
      have := h1.1 z (by simp [hz.2.1, hz.2.2])
      simp [Function.update_of_ne hz.1, this.1, this.2]
    · by_cases hrS : r = S
      · subst hrS; simp [hSσ]
      · by_cases hrT : r = T
        · subst hrT; simp [Function.update_of_ne (Ne.symm hST), hTρ, hTσ]
        · simp [Function.update_of_ne hrS, h1.val (r := r) (by simp [hrS, hrT])]

include cap in
theorem sadd_spec (hS4 : [X, Y, M, N].Nodup) (hR4 : [S, T, F, R].Nodup) (σ : WState ns nr) (x y : ℤ) (m0 n0 : ℕ)
    (hX : SNumOn σ X W x) (hY : SNumOn σ Y W y) (hM : NumOn σ M (W + 1) m0) (hN : NumOn σ N (W + 1) n0)
    (hS : σ.val S = 0) (hT : σ.val T = 0) (hF : σ.val F = 0) (hR : σ.val R = 0) (hxy : (x + y).natAbs < 2 ^ W)
    (hcap : 2 * (W + 1) + 1 ≤ cap) :
    Runs cap (sadd X Y M N S T F R) σ (410 * W + 600) (OpPost σ X M N W (x + y)) := by
  have hS4' := hS4
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, not_false_eq_true, List.nodup_nil, and_true] at hS4'
  refine (split2 cap W hS4 hR4 σ x y m0 n0 hX hY hM hN hS hT hF hR hcap _ (253 * W + 321) _
    (fun τ hXτ _ hMτ hNτ hSτ hTτ hFτ hRτ hfr => ?_)).cost (by omega)
  have h := coreJoin cap W hS4 hR4 σ τ (encS x) x.natAbs y.natAbs (decide (x < 0)) (decide (y < 0)) hXτ.1 hMτ hNτ hX.2
    hY.2 hSτ hTτ hFτ hRτ hS hT hfr (by rwa [sval_natAbs, sval_natAbs]) hcap
  rwa [sval_natAbs, sval_natAbs] at h

include cap in
theorem ssub_spec (hS4 : [X, Y, M, N].Nodup) (hR4 : [S, T, F, R].Nodup) (σ : WState ns nr) (x y : ℤ) (m0 n0 : ℕ)
    (hX : SNumOn σ X W x) (hY : SNumOn σ Y W y) (hM : NumOn σ M (W + 1) m0) (hN : NumOn σ N (W + 1) n0)
    (hS : σ.val S = 0) (hT : σ.val T = 0) (hF : σ.val F = 0) (hR : σ.val R = 0) (hxy : (x - y).natAbs < 2 ^ W)
    (hcap : 2 * (W + 1) + 1 ≤ cap) :
    Runs cap (ssub X Y M N S T F R) σ (420 * W + 610) (OpPost σ X M N W (x - y)) := by
  have hR4' := hR4
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, not_false_eq_true, List.nodup_nil, and_true] at hR4'
  obtain ⟨⟨hST, hSF, hSR⟩, ⟨hTF, hTR⟩, hFR⟩ := hR4'
  refine (split2 cap W hS4 hR4 σ x y m0 n0 hX hY hM hN hS hT hF hR hcap _ (253 * W + 326) _
    (fun τ hXτ _ hMτ hNτ hSτ hTτ hFτ hRτ hfr => ?_)).cost (by omega)
  have hf := flip_spec cap T τ (decide (y < 0)) hTτ (by omega)
  have e : sval x.natAbs (decide (x < 0)) + sval y.natAbs (!decide (y < 0)) = x - y := by
    rw [sval_not, sval_natAbs, sval_natAbs]; ring
  have h := coreJoin cap W hS4 hR4 σ (τ.setv T (!decide (y < 0)).toNat) (encS x) x.natAbs y.natAbs (decide (x < 0))
    (!decide (y < 0)) (BinW.numOn_setv hXτ.1 _ _) (BinW.numOn_setv hMτ _ _) (BinW.numOn_setv hNτ _ _) hX.2 hY.2
    (by simp [Function.update_of_ne hST, hSτ]) (by simp) (by simp [Function.update_of_ne (Ne.symm hTF), hFτ])
    (by simp [Function.update_of_ne (Ne.symm hTR), hRτ]) hS hT (hfr.comp' (sameExcept_setv τ (S := []) (Rg := [T])
      (by simp) _) |>.weaken (by simp) (by simp)) (by rw [e]; exact hxy) hcap
  rw [e] at h
  exact (Runs.seqE hf h).cost (by omega)

include cap in
theorem sneg_spec (hXM : X ≠ M) (hR3 : [S, F, R].Nodup) (σ : WState ns nr) (x : ℤ) (m0 : ℕ) (hX : SNumOn σ X W x)
    (hM : NumOn σ M (W + 1) m0) (hS : σ.val S = 0) (hF : σ.val F = 0) (hR : σ.val R = 0)
    (hcap : 2 * (W + 1) + 1 ≤ cap) :
    Runs cap (sneg X M S F R) σ (210 * W + 300)
      (fun τ => SNumOn τ X W (-x) ∧ (∃ a, NumOn τ M (W + 1) a) ∧ SameExcept σ τ [X, M] []) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, not_false_eq_true, List.nodup_nil, and_true] at hR3
  obtain ⟨⟨hSF, hSR⟩, hFR⟩ := hR3
  have h1 := split_spec cap W hXM hFR σ x m0 hX hM hS hF hR hcap
  set σ1 := (σ.sets M (frame (binary (W + 1) x.natAbs))).setv S (decide (x < 0)).toNat with hσ1
  have h2 := flip_spec cap S σ1 (decide (x < 0)) (by simp [hσ1]) (by omega)
  set σ2 := σ1.setv S (!decide (x < 0)).toNat with hσ2
  have h3 := join_spec cap W hXM hFR hSF hSR σ2 x.natAbs (encS x) (!decide (x < 0))
    (BinW.numOn_setv (BinW.numOn_setv (BinW.numOn_sets_self σ M _ _ hM.2) _ _) _ _) hX.2
    (BinW.numOn_setv (BinW.numOn_setv (BinW.numOn_sets_ne hX.1 hXM _) _ _) _ _) (by simp [hσ2])
    (by simp [hσ2, hσ1, Function.update_of_ne (Ne.symm hSF), hF]) (by simp [hσ2, hσ1, Function.update_of_ne (Ne.symm hSR), hR])
    hcap
  have e : sval x.natAbs (!decide (x < 0)) = -x := by rw [sval_not, sval_natAbs]
  rw [e] at h3
  refine (Runs.seqE h1 (Runs.seqE h2 (Runs.of h3 ⟨⟨?_, by simpa using hX.2⟩, ⟨x.natAbs, ?_⟩, ?_⟩))).cost (by omega)
  · exact BinW.numOn_setv (BinW.numOn_sets_self _ X _ _ (by simp [hσ2, hσ1, hX.1.2])) _ _
  · exact BinW.numOn_setv (BinW.numOn_sets_ne (BinW.numOn_setv (BinW.numOn_setv (BinW.numOn_sets_self σ M _ _ hM.2) _ _)
      _ _) (Ne.symm hXM) _) _ _
  · refine ⟨fun z hz => ?_, fun r _ => ?_, rfl⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
      simp [hσ2, hσ1, Function.update_of_ne hz.1, Function.update_of_ne hz.2]
    · by_cases hr : r = S
      · subst hr; simp [hS]
      · simp [hσ2, hσ1, Function.update_of_ne hr]

include cap in
theorem slt_spec (hS4 : [X, Y, M, N].Nodup) (hR4 : [S, T, F, R].Nodup) (σ : WState ns nr) (x y : ℤ) (m0 n0 : ℕ)
    (hX : SNumOn σ X W x) (hY : SNumOn σ Y W y) (hM : NumOn σ M (W + 1) m0) (hN : NumOn σ N (W + 1) n0)
    (hS : σ.val S = 0) (hT : σ.val T = 0) (hF : σ.val F = 0) (hR : σ.val R = 0) (hcap : 2 * (W + 1) + 1 ≤ cap) :
    Runs cap (slt X Y M N S T F R) σ (200 * W + 320)
      (fun τ => τ.val F = (decide (x < y)).toNat ∧ (∃ a, NumOn τ M (W + 1) a) ∧ (∃ b, NumOn τ N (W + 1) b) ∧
        SameExcept σ τ [M, N] [F]) := by
  have hS4' := hS4
  have hR4' := hR4
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, not_false_eq_true, List.nodup_nil, and_true] at hS4' hR4'
  obtain ⟨⟨hXY, hXM, hXN⟩, ⟨hYM, hYN⟩, hMN⟩ := hS4'
  obtain ⟨⟨hST, hSF, hSR⟩, ⟨hTF, hTR⟩, hFR⟩ := hR4'
  refine (split2 cap W hS4 hR4 σ x y m0 n0 hX hY hM hN hS hT hF hR hcap _ (41 * W + 60) _
    (fun τ _ _ hMτ hNτ hSτ hTτ hFτ hRτ hfr => ?_)).cost (by omega)
  have hm1 : x.natAbs < 2 ^ (W + 1) := by rw [pow_succ]; have := hX.2; omega
  have hn1 : y.natAbs < 2 ^ (W + 1) := by rw [pow_succ]; have := hY.2; omega
  -- the frame of the final states
  have fin : ∀ (ρ : WState ns nr), (∀ z, z ≠ M → z ≠ N → ρ.st z = τ.st z ∧ ρ.sh z = τ.sh z) → ρ.val S = 0 →
      ρ.val T = 0 → (∀ r, r ≠ S → r ≠ T → r ≠ F → ρ.val r = τ.val r) → ρ.cell = τ.cell →
      SameExcept σ ρ [M, N] [F] := by
    intro ρ h1 h2 h3 h4 h5
    refine ⟨fun z hz => ?_, fun r hr => ?_, by rw [h5, hfr.cell]⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
      rw [(h1 z hz.1 hz.2).1, (h1 z hz.1 hz.2).2]; exact hfr.1 z (by simp [hz.1, hz.2])
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      by_cases hrS : r = S
      · subst hrS; rw [h2, hS]
      · by_cases hrT : r = T
        · subst hrT; rw [h3, hT]
        · rw [h4 r hrS hrT hr]; exact hfr.val (by simp [hrS, hrT])
  rcases lt_or_ge x 0 with hx | hx <;> rcases lt_or_ge y 0 with hy | hy
  · -- both negative: `x < y ↔ |y| < |x|`
    have hv : τ.val S ≠ 0 := by simp [hSτ, hx]
    have hv' : τ.val T ≠ 0 := by simp [hTτ, hy]
    have hd1 := WXExec.dec cap S τ (by simp [hSτ, hx]; omega)
    have hd2 := WXExec.dec cap T (τ.setv S (τ.val S - 1)) (by simp [Function.update_of_ne (Ne.symm hST), hTτ, hy]; omega)
    have hl := BinW.lt_spec cap (W + 1) (Ne.symm hMN) hFR ((τ.setv S (τ.val S - 1)).setv T
      ((τ.setv S (τ.val S - 1)).val T - 1)) y.natAbs x.natAbs (BinW.numOn_setv (BinW.numOn_setv hNτ _ _) _ _)
      (BinW.numOn_setv (BinW.numOn_setv hMτ _ _) _ _) (by simp [Function.update_of_ne (Ne.symm hTF),
        Function.update_of_ne (Ne.symm hSF), hFτ]) (by simp [Function.update_of_ne (Ne.symm hTR),
        Function.update_of_ne (Ne.symm hSR), hRτ]) hn1 hm1 (by omega)
    refine (Runs.ifrT hv (Runs.ifrT hv' (Runs.seqE hd1 (Runs.seqE hd2 (Runs.of hl ⟨?_, ⟨x.natAbs, ?_⟩, ⟨y.natAbs, ?_⟩,
      ?_⟩))))).cost
      (by omega)
    · have : (y.natAbs < x.natAbs) = (x < y) := by apply propext; omega
      simp [this]
    · exact BinW.numOn_setv (BinW.numOn_setv (BinW.numOn_setv hMτ _ _) _ _) _ _
    · exact BinW.numOn_setv (BinW.numOn_setv (BinW.numOn_setv hNτ _ _) _ _) _ _
    · refine fin _ (fun z _ _ => by simp) ?_ ?_ (fun r h1 h2 h3 => ?_) rfl
      · simp [Function.update_apply, hSF, hST, hSτ, hx]
      · simp [Function.update_apply, hTF, Ne.symm hST, hTτ, hy]
      · simp [Function.update_of_ne h1, Function.update_of_ne h2, Function.update_of_ne h3]
  · -- `x < 0 ≤ y`: true
    have hv : τ.val S ≠ 0 := by simp [hSτ, hx]
    have hv' : τ.val T = 0 := by simp [hTτ, not_lt.mpr hy]
    have hd1 := WXExec.dec cap S τ (by simp [hSτ, hx]; omega)
    have hi := WXExec.inc cap F (τ.setv S (τ.val S - 1)) (by simp [Function.update_of_ne (Ne.symm hSF), hFτ]; omega)
    refine (Runs.ifrT hv (Runs.ifrF hv' (Runs.seqE hd1 (Runs.of hi ⟨?_, ⟨x.natAbs, ?_⟩, ⟨y.natAbs, ?_⟩, ?_⟩)))).cost
      (by omega)
    · have : x < y := by omega
      simp [this, Function.update_of_ne (Ne.symm hSF), hFτ]
    · exact BinW.numOn_setv (BinW.numOn_setv hMτ _ _) _ _
    · exact BinW.numOn_setv (BinW.numOn_setv hNτ _ _) _ _
    · refine fin _ (fun z _ _ => by simp) ?_ ?_ (fun r h1 h2 h3 => ?_) rfl
      · simp [Function.update_of_ne hSF, hSτ, hx]
      · simp [Function.update_apply, hTF, Ne.symm hST, hv']
      · simp [Function.update_of_ne h1, Function.update_of_ne h3]
  · -- `y < 0 ≤ x`: false
    have hv : τ.val S = 0 := by simp [hSτ, not_lt.mpr hx]
    have hv' : τ.val T ≠ 0 := by simp [hTτ, hy]
    have hd := WXExec.dec cap T τ (by simp [hTτ, hy]; omega)
    refine (Runs.ifrF hv (Runs.ifrT hv' (Runs.of hd ⟨?_, ⟨x.natAbs, ?_⟩, ⟨y.natAbs, ?_⟩, ?_⟩))).cost (by omega)
    · have : ¬ x < y := by omega
      simp [this, Function.update_of_ne (Ne.symm hTF), hFτ]
    · exact BinW.numOn_setv hMτ _ _
    · exact BinW.numOn_setv hNτ _ _
    · refine fin _ (fun z _ _ => by simp) ?_ ?_ (fun r h1 h2 h3 => ?_) rfl
      · simp [Function.update_of_ne hST, hv]
      · simp [hTτ, hy]
      · simp [Function.update_of_ne h2]
  · -- both nonnegative
    have hv : τ.val S = 0 := by simp [hSτ, not_lt.mpr hx]
    have hv' : τ.val T = 0 := by simp [hTτ, not_lt.mpr hy]
    have hl := BinW.lt_spec cap (W + 1) hMN hFR τ x.natAbs y.natAbs hMτ hNτ hFτ hRτ hm1 hn1 (by omega)
    refine (Runs.ifrF hv (Runs.ifrF hv' (Runs.of hl ⟨?_, ⟨x.natAbs, ?_⟩, ⟨y.natAbs, ?_⟩, ?_⟩))).cost (by omega)
    · have : (x.natAbs < y.natAbs) = (x < y) := by apply propext; omega
      simp [this]
    · exact BinW.numOn_setv hMτ _ _
    · exact BinW.numOn_setv hNτ _ _
    · refine fin _ (fun z _ _ => by simp) ?_ ?_ (fun r _ _ h3 => ?_) rfl
      · simp [Function.update_of_ne hSF, hv]
      · simp [Function.update_of_ne hTF, hv']
      · simp [Function.update_of_ne h3]

/-- The cost bound of `smul`. -/
def smulCost (W : ℕ) : ℕ := 300 * (W + 2) ^ 2 + 300 * W + 450

include cap in
theorem smul_spec (hS6 : [X, Y, M, N, C, D].Nodup) (hR5 : [S, T, F, R, G].Nodup) (σ : WState ns nr) (x y : ℤ)
    (m0 n0 c0 d0 : ℕ) (hX : SNumOn σ X W x) (hY : SNumOn σ Y W y) (hM : NumOn σ M (W + 1) m0)
    (hN : NumOn σ N (W + 1) n0) (hC : NumOn σ C (W + 1) c0) (hD : NumOn σ D (W + 1) d0) (hS : σ.val S = 0)
    (hT : σ.val T = 0) (hF : σ.val F = 0) (hR : σ.val R = 0) (hG : σ.val G = 0) (hxy : (x * y).natAbs < 2 ^ W)
    (hcap : 2 * (W + 1) + 1 ≤ cap) :
    Runs cap (smul X Y M N C D S T F R G) σ (smulCost W)
      (fun τ => SNumOn τ X W (x * y) ∧ (∃ a, NumOn τ M (W + 1) a) ∧ (∃ b, NumOn τ N (W + 1) b) ∧
        (∃ c, NumOn τ C (W + 1) c) ∧ (∃ d, NumOn τ D (W + 1) d) ∧ SameExcept σ τ [X, M, N, C, D] []) := by
  have hS6' := hS6
  have hR5' := hR5
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, not_false_eq_true, List.nodup_nil,
    and_true] at hS6' hR5'
  obtain ⟨⟨hXY, hXM, hXN, hXC, hXD⟩, ⟨hYM, hYN, hYC, hYD⟩, ⟨hMN, hMC, hMD⟩, ⟨hNC, hND⟩, hCD⟩ := hS6'
  obtain ⟨⟨hST, hSF, hSR, hSG⟩, ⟨hTF, hTR, hTG⟩, ⟨hFR, hFG⟩, hRG⟩ := hR5'
  have hS4 : [X, Y, M, N].Nodup := by simp [hXY, hXM, hXN, hYM, hYN, hMN]
  have hR4 : [S, T, F, R].Nodup := by simp [hST, hSF, hSR, hTF, hTR, hFR]
  have hmn : x.natAbs * y.natAbs < 2 ^ W := by rw [← Int.natAbs_mul]; exact hxy
  have hmn1 : x.natAbs * y.natAbs < 2 ^ (W + 1) := by rw [pow_succ]; omega
  have hn1 : y.natAbs < 2 ^ (W + 1) := by rw [pow_succ]; have := hY.2; omega
  refine (split2 cap W hS4 hR4 σ x y m0 n0 hX hY hM hN hS hT hF hR hcap _
    (mulCost (W + 1) + 1 + 10 + 1 + (130 * W + 160)) (fun τ => SNumOn τ X W (x * y) ∧ (∃ a, NumOn τ M (W + 1) a) ∧
      (∃ b, NumOn τ N (W + 1) b) ∧ (∃ c, NumOn τ C (W + 1) c) ∧ (∃ d, NumOn τ D (W + 1) d) ∧
      SameExcept σ τ [X, M, N, C, D] []) (fun τ hXτ _ hMτ hNτ hSτ hTτ hFτ hRτ hfr => ?_)).cost (by
      unfold smulCost; have := BinW.mulCost_le (W + 1); nlinarith)
  have hCτ : NumOn τ C (W + 1) c0 := hfr.numOn (by simp [Ne.symm hMC, Ne.symm hNC]) hC
  have hDτ : NumOn τ D (W + 1) d0 := hfr.numOn (by simp [Ne.symm hMD, Ne.symm hND]) hD
  have hGτ : τ.val G = 0 := by rw [hfr.val (by simp [Ne.symm hSG, Ne.symm hTG])]; exact hG
  have hm := BinW.mul_spec cap (W + 1) hMN hMC hMD hNC hND hCD hFR hFG hRG τ x.natAbs y.natAbs c0 d0 hMτ hNτ hCτ hDτ
    hFτ hRτ hGτ hmn1 hn1 (by omega)
  set τ1 := (τ.sets C (frame (binary (W + 1) (x.natAbs * y.natAbs)))).sets D (frame (binary (W + 1) 0)) with hτ1
  -- the sign: `S := s xor t`, `T := 0`
  have hsg : WXExec cap (.ifr T (.seq (WMX.dec T) (flip S)) WMX.skip) τ1
      (τ1.setv S (decide (x < 0) ^^ decide (y < 0)).toNat |>.setv T 0) 7 := by
    by_cases hy : y < 0
    · have hv : τ1.val T ≠ 0 := by simp [hτ1, hTτ, hy]
      have hd := WXExec.dec cap T τ1 (by simp [hτ1, hTτ, hy]; omega)
      have hf := flip_spec cap S (τ1.setv T (τ1.val T - 1)) (decide (x < 0))
        (by simp [hτ1, Function.update_of_ne hST, hSτ]) (by omega)
      refine (WXExec.ifrT hv (WXExec.seq hd hf)).cast cap ?_ (by omega)
      apply WState.eq <;> try rfl
      funext r; simp only [WState.setv_val, Function.update_apply]
      by_cases h1 : r = S
      · subst h1; simp [hST, hy]
      · by_cases h2 : r = T
        · subst h2; simp [h1, hτ1, hTτ, hy]
        · simp [h1, h2]
    · have hv : τ1.val T = 0 := by simp [hτ1, hTτ, hy]
      refine (WXExec.ifrF hv (WXExec.skip cap τ1)).cast cap ?_ (by omega)
      apply WState.eq <;> try rfl
      funext r; simp only [WState.setv_val, Function.update_apply]
      by_cases h1 : r = S
      · subst h1; simp [hST, hy, hτ1, hSτ]
      · by_cases h2 : r = T
        · subst h2; simp [hv]
        · simp [h1, h2]
  set τ2 := (τ1.setv S (decide (x < 0) ^^ decide (y < 0)).toNat).setv T 0 with hτ2
  have hj := join_spec cap W hXC hFR hSF hSR τ2 _ (encS x) (decide (x < 0) ^^ decide (y < 0))
    (by simp only [hτ2, hτ1]; exact BinW.numOn_setv (BinW.numOn_setv (BinW.numOn_sets_ne (BinW.numOn_sets_self τ C _ _
      hCτ.2) hCD _) _ _) _ _) hmn
    (by simp only [hτ2, hτ1]; exact BinW.numOn_setv (BinW.numOn_setv (BinW.numOn_sets_ne (BinW.numOn_sets_ne hXτ.1
      hXC _) hXD _) _ _) _ _)
    (by simp [hτ2, Function.update_of_ne hST]) (by simp [hτ2, hτ1, Function.update_of_ne (Ne.symm hTF),
      Function.update_of_ne (Ne.symm hSF), hFτ]) (by simp [hτ2, hτ1, Function.update_of_ne (Ne.symm hTR),
      Function.update_of_ne (Ne.symm hSR), hRτ]) hcap
  rw [sval_mul, sval_natAbs, sval_natAbs] at hj
  refine (Runs.seqE hm (Runs.seqE hsg (Runs.of hj ?_))).cost (by omega)
  refine ⟨⟨?_, hxy⟩, ⟨x.natAbs, ?_⟩, ⟨y.natAbs, ?_⟩, ⟨x.natAbs * y.natAbs, ?_⟩, ⟨0, ?_⟩, ?_⟩
  · exact BinW.numOn_setv (BinW.numOn_sets_self _ X _ _ (by simp [hτ2, hτ1, hXτ.1.2])) _ _
  · exact BinW.numOn_setv (BinW.numOn_sets_ne (BinW.numOn_setv (BinW.numOn_setv (BinW.numOn_sets_ne
      (BinW.numOn_sets_ne hMτ hMC _) hMD _) _ _) _ _) (Ne.symm hXM) _) _ _
  · exact BinW.numOn_setv (BinW.numOn_sets_ne (BinW.numOn_setv (BinW.numOn_setv (BinW.numOn_sets_ne
      (BinW.numOn_sets_ne hNτ hNC _) hND _) _ _) _ _) (Ne.symm hXN) _) _ _
  · exact BinW.numOn_setv (BinW.numOn_sets_ne (BinW.numOn_setv (BinW.numOn_setv (BinW.numOn_sets_ne
      (BinW.numOn_sets_self τ C _ _ hCτ.2) hCD _) _ _) _ _) (Ne.symm hXC) _) _ _
  · simp only [hτ2, hτ1]
    exact BinW.numOn_setv (BinW.numOn_sets_ne (BinW.numOn_setv (BinW.numOn_setv
      (BinW.numOn_sets_self (τ.sets C (frame (binary (W + 1) (x.natAbs * y.natAbs)))) D _ _ hDτ.2) _ _) _ _)
      (Ne.symm hXD) _) _ _
  · refine ⟨fun z hz => ?_, fun r _ => ?_, by simp [hτ2, hτ1, hfr.cell]⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
      obtain ⟨h1, h2, h3, h4, h5⟩ := hz
      simp [hτ2, hτ1, Function.update_of_ne h1, Function.update_of_ne h4, Function.update_of_ne h5,
        hfr.st (x := z) (by simp [h2, h3]), hfr.sh (x := z) (by simp [h2, h3])]
    · by_cases h1 : r = S
      · subst h1; simp [hS]
      · by_cases h2 : r = T
        · subst h2; simp [Function.update_of_ne (Ne.symm hST), hτ2, hT]
        · simp [hτ2, hτ1, Function.update_of_ne h1, Function.update_of_ne h2, hfr.val (r := r) (by simp [h1, h2])]

end Ops

/-! Programs are opaque to consumers: use the spec theorems. -/
attribute [irreducible] split join addCore subArm flip sadd ssub sneg smul slt sgnBitW zTestW

end NearCubicGates.Close.WordPrograms.SInt
