import Proof.Gates.Cells.Comp
import Proof.Gates.WordPrograms.RegArith
import Proof.Gates.Interfaces.WordFn

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace NearCubicGates.Close.Cells

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length binary_value)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms

theorem wtb_end (l : List Bool) (b : Bool) : writeTapeBit l l.length b = l ++ [b] := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [writeTapeBit, ih]

section Tools
variable {ns nr : ℕ} (cap : ℕ)

/-- Empty a register. -/
def clearR (Rg : Fin nr) : WMX ns nr := .whr Rg (WMX.dec Rg)

theorem clearR_spec (Rg : Fin nr) :
    ∀ (j : ℕ) (σ : WState ns nr), σ.val Rg = j → j ≤ cap → WXExec cap (clearR Rg) σ (σ.setv Rg 0) (3 * j + 1) := by
  intro j
  induction j with
  | zero =>
    intro σ hv _
    rw [BinW.setv_same hv]; exact WXExec.whrF hv
  | succ j ih =>
    intro σ hv hj
    have h1 := WXExec.dec cap Rg σ (by omega)
    rw [hv, show j + 1 - 1 = j by omega] at h1
    have h3 := ih (σ.setv Rg j) (by simp) (by omega)
    rw [wsetv_setv] at h3
    exact WXExec.mono (WXExec.whrT (by omega) h1 h3) (by omega)

/-- Add a constant to a register. -/
def incN (Rg : Fin nr) : ℕ → WMX ns nr
  | 0 => WMX.skip
  | k + 1 => .seq (WMX.inc Rg) (incN Rg k)

theorem incN_spec (Rg : Fin nr) :
    ∀ (k : ℕ) (σ : WState ns nr), σ.val Rg + k ≤ cap →
      WXExec cap (incN Rg k) σ (σ.setv Rg (σ.val Rg + k)) (4 * k) := by
  intro k
  induction k with
  | zero => intro σ _; simp only [Nat.add_zero, wsetv_same, Nat.mul_zero]; exact WXExec.skip cap σ
  | succ k ih =>
    intro σ hk
    have h1 := WXExec.inc cap Rg σ (by omega)
    have h2 := ih (σ.setv Rg (σ.val Rg + 1)) (by simp; omega)
    simp only [WState.setv_val, Function.update_self, wsetv_setv] at h2
    rw [show σ.val Rg + 1 + k = σ.val Rg + (k + 1) by ring] at h2
    exact WXExec.mono (WXExec.seq h1 h2) (by omega)

/-- `X := 2·X` (`Y`, `T` scratch at `0`). -/
def dblR (X Y T : Fin nr) : WMX ns nr := .seq (addR X Y T) (.seq (addR Y X T) (clearR Y))

theorem dblR_spec {X Y T : Fin nr} (hXY : X ≠ Y) (hXT : X ≠ T) (hYT : Y ≠ T) (σ : WState ns nr)
    (hY : σ.val Y = 0) (hT : σ.val T = 0) (hcap : 2 * σ.val X ≤ cap) :
    WXExec cap (dblR X Y T) σ (σ.setv X (2 * σ.val X)) (60 * σ.val X + 10) := by
  have h1 := addR_spec cap hXY hXT hYT σ hT (by omega)
  rw [hY, zero_add] at h1
  set σ1 := σ.setv Y (σ.val X) with hσ1
  have h2 := addR_spec cap (Ne.symm hXY) hYT hXT σ1 (by simp [σ1, Function.update_of_ne (Ne.symm hYT), hT])
    (by simp [σ1, Function.update_of_ne hXY]; omega)
  set σ2 := σ1.setv X (σ1.val X + σ1.val Y) with hσ2
  have h3 := clearR_spec cap Y (σ.val X) σ2 (by simp [σ2, σ1, Function.update_of_ne (Ne.symm hXY)]) (by omega)
  have e1 : σ1.val Y = σ.val X := by simp [σ1]
  have e2 : σ1.val X = σ.val X := by simp [σ1, Function.update_of_ne hXY]
  rw [e1] at h2
  refine (WXExec.seq h1 (WXExec.seq h2 h3)).cast cap ?_ (by omega)
  refine WState.eq rfl rfl ?_ rfl
  funext r
  simp only [σ2, σ1, WState.setv_val, Function.update_apply, e2]
  by_cases rY : r = Y
  · subst rY; simp [Ne.symm hXY, hY]
  · by_cases rX : r = X
    · subst rX; simp [hXY]; ring
    · simp [rY, rX]

/-- `[true, false]` repeated `k` times. -/
def zp (k : ℕ) : List Bool := (List.replicate k [true, false]).flatten

theorem zp_succ (k : ℕ) : zp (k + 1) = zp k ++ [true, false] := by
  simp [zp, List.replicate_succ']

theorem zp_length (k : ℕ) : (zp k).length = 2 * k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [zp_succ]; simp [ih]; ring

theorem binary_zero (W : ℕ) : binary W 0 = List.replicate W false := by
  induction W with
  | zero => rfl
  | succ W ih => simp [binary, ih, List.replicate_succ]

theorem frame_zero (W : ℕ) : frame (binary W 0) = zp W ++ [false] := by
  rw [binary_zero]
  induction W with
  | zero => rfl
  | succ W ih => simp [List.replicate_succ, frame, ih, zp]

def wPair (X : Fin (ns + 1)) : WMX ns nr :=
  .seq (WMX.wr X true) (.seq (WMX.fwd X) (.seq (WMX.wr X false) (WMX.fwd X)))

def bPair (X : Fin (ns + 1)) : WMX ns nr := .seq (WMX.bwd X) (WMX.bwd X)

/-- Write the zero word of width `σ.val G` on a fresh stream `X`. -/
def initNum (G G2 : Fin nr) (X : Fin (ns + 1)) : WMX ns nr :=
  .seq (repK G G2 (wPair X)) (.seq (WMX.wr X false) (repK G G2 (bPair X)))

theorem initNum_spec {G G2 : Fin nr} (hGA : G ≠ G2) (X : Fin (ns + 1)) (σ : WState ns nr) (hX : σ.st X = [])
    (hh : σ.sh X = 0) (hA2 : σ.val G2 = 0) (hcap : 2 * σ.val G ≤ cap) :
    WXExec cap (initNum G G2 X) σ (σ.sets X (frame (binary (σ.val G) 0))) (50 * σ.val G + 10) := by
  set W := σ.val G with hW
  -- the writing loop
  let st1 : ℕ → WState ns nr := fun k => (σ.sets X (zp k)).seth X (2 * k)
  have l1 := Runs.repE (cap := cap) (K := G) (K2 := G2) (body := wPair X) hGA 7 W st1 (by omega)
    (fun k => by simp [st1]) (fun k => by simp [st1])
    (by
      intro k _ v1 v2
      set τ := ((st1 k).setv G v1).setv G2 v2 with hτ
      have hτs : τ.st X = zp k := by simp [τ, st1]
      have hτh : τ.sh X = 2 * k := by simp [τ, st1]
      have w1 : WXExec cap (WMX.wr X true) τ (τ.sets X (zp k ++ [true])) 1 := by
        have := WXExec.wr cap X true τ
        rwa [hτs, hτh, ← zp_length, wtb_end] at this
      set τ1 := τ.sets X (zp k ++ [true]) with hτ1
      have w2 : WXExec cap (WMX.fwd X) τ1 (τ1.seth X (2 * k + 1)) 1 := by
        have := WXExec.fwd cap X τ1
        have hh : τ1.sh X = 2 * k := by simp [τ1, hτh]
        rwa [hh] at this
      set τ2 := τ1.seth X (2 * k + 1) with hτ2
      have w3 : WXExec cap (WMX.wr X false) τ2 (τ2.sets X (zp k ++ [true] ++ [false])) 1 := by
        have := WXExec.wr cap X false τ2
        have hs : τ2.st X = zp k ++ [true] := by simp [τ2, τ1]
        have hh : τ2.sh X = (zp k ++ [true]).length := by simp [τ2, zp_length]
        rwa [hs, hh, wtb_end] at this
      set τ3 := τ2.sets X (zp k ++ [true] ++ [false]) with hτ3
      have w4 : WXExec cap (WMX.fwd X) τ3 (τ3.seth X (2 * k + 2)) 1 := by
        have := WXExec.fwd cap X τ3
        have hh : τ3.sh X = 2 * k + 1 := by simp [τ3, τ2]
        rwa [hh] at this
      refine WXExec.cast cap (WXExec.seq w1 (WXExec.seq w2 (WXExec.seq w3 w4))) ?_ (by omega)
      refine WState.eq ?_ ?_ ?_ rfl
      · funext i; by_cases hi : i = X
        · subst hi; simp [τ3, τ2, τ1, τ, st1]; ring
        · simp [τ3, τ2, τ1, τ, st1, Function.update_of_ne hi]
      · funext i; by_cases hi : i = X
        · subst hi; simp [τ3, τ2, τ1, τ, st1, zp_succ]
        · simp [τ3, τ2, τ1, τ, st1, Function.update_of_ne hi]
      · rfl)
    (by simp [st1, hW]) (by simp [st1, hA2])
  have e0 : st1 0 = σ := by
    refine WState.eq ?_ ?_ rfl rfl
    · funext i; by_cases hi : i = X
      · subst hi; simp [st1, hh]
      · simp [st1, Function.update_of_ne hi]
    · funext i; by_cases hi : i = X
      · subst hi; simp [st1, hX, zp]
      · simp [st1, Function.update_of_ne hi]
  rw [e0] at l1
  -- the final mark
  have m1 := WXExec.wr cap X false (st1 W)
  have hs1 : (st1 W).st X = zp W := by simp [st1]
  have hh1 : (st1 W).sh X = 2 * W := by simp [st1]
  rw [hs1, hh1, ← zp_length, wtb_end, ← frame_zero] at m1
  -- the rewinding loop
  let st2 : ℕ → WState ns nr := fun k => (σ.sets X (frame (binary W 0))).seth X (2 * (W - k))
  have l2 := Runs.repE (cap := cap) (K := G) (K2 := G2) (body := bPair X) hGA 3 W st2 (by omega)
    (fun k => by simp [st2]) (fun k => by simp [st2])
    (by
      intro k hk v1 v2
      set τ := ((st2 k).setv G v1).setv G2 v2
      have w1 := WXExec.bwd cap X τ
      have w2 := WXExec.bwd cap X (τ.seth X (τ.sh X - 1))
      refine WXExec.cast cap (WXExec.seq w1 w2) ?_ (by omega)
      refine WState.eq ?_ rfl rfl rfl
      funext i; by_cases hi : i = X
      · subst hi; simp [τ, st2]; omega
      · simp [τ, st2, Function.update_of_ne hi])
    (by simp [st2, hW]) (by simp [st2, hA2])
  have e1 : (st1 W).sets X (frame (binary W 0)) = st2 0 := by
    refine WState.eq ?_ ?_ rfl rfl
    · funext i; by_cases hi : i = X
      · subst hi; simp [st1, st2]
      · simp [st1, st2, Function.update_of_ne hi]
    · funext i; by_cases hi : i = X
      · subst hi; simp [st1, st2]
      · simp [st1, st2, Function.update_of_ne hi]
  have e2 : st2 W = σ.sets X (frame (binary W 0)) := by
    refine WState.eq ?_ rfl rfl rfl
    funext i; by_cases hi : i = X
    · subst hi; simp [st2, hh]
    · simp [st2, Function.update_of_ne hi]
  rw [e1] at m1
  rw [e2] at l2
  exact WXExec.seq' cap l1 (WXExec.seq' cap m1 l2 le_rfl) (by ring_nf; omega)

/-- Move stream `X` back by the value of register `Rg` (clearing it). -/
def rewindR (X : Fin (ns + 1)) (Rg : Fin nr) : WMX ns nr := .whr Rg (.seq (WMX.dec Rg) (WMX.bwd X))

theorem rewindR_spec (X : Fin (ns + 1)) (Rg : Fin nr) :
    ∀ (j : ℕ) (σ : WState ns nr), σ.val Rg = j → σ.sh X = j → j ≤ cap →
      WXExec cap (rewindR X Rg) σ ((σ.setv Rg 0).seth X 0) (5 * j + 1) := by
  intro j
  induction j with
  | zero =>
    intro σ hv hs _
    have e : (σ.setv Rg 0).seth X 0 = σ := by
      refine WState.eq ?_ rfl ?_ rfl
      · funext i; by_cases hi : i = X
        · subst hi; simp [hs]
        · simp [Function.update_of_ne hi]
      · funext r; by_cases hr : r = Rg
        · subst hr; simp [hv]
        · simp [Function.update_of_ne hr]
    rw [e]; exact WXExec.whrF hv
  | succ j ih =>
    intro σ hv hs hj
    have h1 := WXExec.dec cap Rg σ (by omega)
    rw [hv, show j + 1 - 1 = j by omega] at h1
    have h2 := WXExec.bwd cap X (σ.setv Rg j)
    simp only [WState.setv_sh, hs, show j + 1 - 1 = j by omega] at h2
    have h3 := ih ((σ.setv Rg j).seth X j) (by simp) (by simp) (by omega)
    have e : ((((σ.setv Rg j).seth X j).setv Rg 0).seth X 0) = ((σ.setv Rg 0).seth X 0) := by
      refine WState.eq ?_ rfl ?_ rfl
      · funext i; by_cases hi : i = X
        · subst hi; simp
        · simp [Function.update_of_ne hi]
      · funext r; by_cases hr : r = Rg
        · subst hr; simp
        · simp [Function.update_of_ne hr]
    rw [e] at h3
    exact WXExec.mono (WXExec.whrT (by omega) (WXExec.seq h1 h2) h3) (by omega)

/-- Write `N` copies of the bit `b` on a fresh stream `X`, head back at `0` (`N` in register `Nr`, `S` scratch). -/
def fillB (Nr S : Fin nr) (X : Fin (ns + 1)) (b : Bool) : WMX ns nr :=
  .seq (repK Nr S (.seq (WMX.wr X b) (WMX.fwd X))) (repK Nr S (WMX.bwd X))

theorem fillB_spec {Nr S : Fin nr} (hNS : Nr ≠ S) (X : Fin (ns + 1)) (b : Bool) (σ : WState ns nr)
    (hX : σ.st X = []) (hh : σ.sh X = 0) (hS : σ.val S = 0) (hcap : 2 * σ.val Nr ≤ cap) :
    WXExec cap (fillB Nr S X b) σ (σ.sets X (List.replicate (σ.val Nr) b)) (40 * σ.val Nr + 10) := by
  set N := σ.val Nr with hN
  let st1 : ℕ → WState ns nr := fun k => (σ.sets X (List.replicate k b)).seth X k
  have l1 := Runs.repE (cap := cap) (K := Nr) (K2 := S) (body := .seq (WMX.wr X b) (WMX.fwd X)) hNS 3 N st1
    (by omega) (fun k => by simp [st1]) (fun k => by simp [st1])
    (by
      intro k _ v1 v2
      set τ := ((st1 k).setv Nr v1).setv S v2 with hτ
      have w1 := WXExec.wr cap X b τ
      have hτs : τ.st X = List.replicate k b := by simp [τ, st1]
      have hτh : τ.sh X = k := by simp [τ, st1]
      have we := wtb_end (List.replicate k b) b
      rw [List.length_replicate] at we
      rw [hτs, hτh, we] at w1
      set τ1 := τ.sets X (List.replicate k b ++ [b])
      have w2 := WXExec.fwd cap X τ1
      have est : st1 (k + 1) = (σ.sets X (List.replicate k b ++ [b])).seth X (k + 1) := by
        simp only [st1]; rw [List.replicate_succ']
      rw [est]
      refine WXExec.cast cap (WXExec.seq w1 w2) ?_ (by omega)
      refine WState.eq ?_ ?_ rfl rfl
      · funext i; by_cases hi : i = X
        · subst hi; simp [τ1, τ, st1]
        · simp [τ1, τ, st1, Function.update_of_ne hi]
      · funext i; by_cases hi : i = X
        · subst hi; simp [τ1, τ, st1]
        · simp [τ1, τ, st1, Function.update_of_ne hi])
    (by simp [st1, hN]) (by simp [st1, hS])
  have e0 : st1 0 = σ := by
    refine WState.eq ?_ ?_ rfl rfl
    · funext i; by_cases hi : i = X
      · subst hi; simp [st1, hh]
      · simp [st1, Function.update_of_ne hi]
    · funext i; by_cases hi : i = X
      · subst hi; simp [st1, hX]
      · simp [st1, Function.update_of_ne hi]
  rw [e0] at l1
  let st2 : ℕ → WState ns nr := fun k => (σ.sets X (List.replicate N b)).seth X (N - k)
  have l2 := Runs.repE (cap := cap) (K := Nr) (K2 := S) (body := WMX.bwd X) hNS 1 N st2 (by omega)
    (fun k => by simp [st2]) (fun k => by simp [st2])
    (by
      intro k hk v1 v2
      set τ := ((st2 k).setv Nr v1).setv S v2
      have w1 := WXExec.bwd cap X τ
      refine WXExec.cast cap w1 ?_ le_rfl
      refine WState.eq ?_ rfl rfl rfl
      funext i; by_cases hi : i = X
      · subst hi; simp [τ, st2]; omega
      · simp [τ, st2, Function.update_of_ne hi])
    (by simp [st2, hN]) (by simp [st2, hS])
  have e1 : st1 N = st2 0 := by
    refine WState.eq ?_ rfl rfl rfl
    funext i; by_cases hi : i = X
    · subst hi; simp [st1, st2]
    · simp [st1, st2, Function.update_of_ne hi]
  have e2 : st2 N = σ.sets X (List.replicate N b) := by
    refine WState.eq ?_ rfl rfl rfl
    funext i; by_cases hi : i = X
    · subst hi; simp [st2, hh]
    · simp [st2, Function.update_of_ne hi]
  rw [e1] at l1
  rw [e2] at l2
  exact WXExec.mono (WXExec.seq l1 l2) (by ring_nf; omega)

/-- `c` doublings of `X`. -/
def dblC (X Y T : Fin nr) : ℕ → WMX ns nr
  | 0 => WMX.skip
  | c + 1 => .seq (dblR X Y T) (dblC X Y T c)

theorem dblC_spec {X Y T : Fin nr} (hXY : X ≠ Y) (hXT : X ≠ T) (hYT : Y ≠ T) :
    ∀ (c : ℕ) (σ : WState ns nr), σ.val Y = 0 → σ.val T = 0 → 2 ^ c * σ.val X ≤ cap →
      WXExec cap (dblC X Y T c) σ (σ.setv X (2 ^ c * σ.val X)) (60 * (2 ^ c * σ.val X - σ.val X) + 11 * c) := by
  intro c
  induction c with
  | zero => intro σ _ _ _; simp only [pow_zero, one_mul, wsetv_same]; exact WXExec.mono (WXExec.skip cap σ) (by omega)
  | succ c ih =>
    intro σ hY hT hcap
    have hp1 : 1 ≤ 2 ^ c := Nat.one_le_two_pow
    set x := σ.val X with hx
    have e1 : 2 ^ (c + 1) * x = 2 ^ c * (2 * x) := by ring
    have hge : x ≤ 2 ^ c * x := Nat.le_mul_of_pos_left _ (by omega)
    have h1 := dblR_spec cap hXY hXT hYT σ hY hT (by rw [e1] at hcap; nlinarith)
    have h2 := ih (σ.setv X (2 * x)) (by simp [Function.update_of_ne (Ne.symm hXY), hY])
      (by simp [Function.update_of_ne (Ne.symm hXT), hT]) (by simp; rw [e1] at hcap; linarith)
    simp only [WState.setv_val, Function.update_self, wsetv_setv] at h2
    refine (WXExec.seq h1 h2).cast cap (by congr 1; ring) ?_
    rw [e1]
    have : 2 ^ c * (2 * x) = 2 * (2 ^ c * x) := by ring
    rw [this]
    omega

def pw2 (X Y T G G2 : Fin nr) (c : ℕ) : WMX ns nr := repK G G2 (dblC X Y T c)

theorem pw2_spec {X Y T G G2 : Fin nr} (hR : [X, Y, T, G, G2].Nodup) (c : ℕ) (σ : WState ns nr)
    (hY : σ.val Y = 0) (hT : σ.val T = 0) (hG2 : σ.val G2 = 0)
    (hcap : 2 ^ (c * σ.val G) * σ.val X ≤ cap) (hcapG : 2 * σ.val G ≤ cap) :
    WXExec cap (pw2 X Y T G G2 c) σ (σ.setv X (2 ^ (c * σ.val G) * σ.val X))
      (σ.val G * (60 * (2 ^ (c * σ.val G) * σ.val X) + 11 * c + 8) + 7 * σ.val G + 3) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, not_false_eq_true, List.nodup_nil,
    and_true] at hR
  obtain ⟨⟨h1, h2, h3, h4⟩, ⟨h5, h6, h7⟩, ⟨h8, h9⟩, h10⟩ := hR
  set n := σ.val G with hn
  set x := σ.val X with hx
  let st : ℕ → WState ns nr := fun k => σ.setv X (2 ^ (c * k) * x)
  have hmono : ∀ k ≤ n, 2 ^ (c * k) * x ≤ 2 ^ (c * n) * x := fun k hk =>
    Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ hk))
  have l := Runs.repE (cap := cap) (K := G) (K2 := G2) (body := dblC X Y T c) h10 (60 * (2 ^ (c * n) * x) + 11 * c) n st
    hcapG (fun k => by simp [st, Function.update_of_ne (Ne.symm h3)])
    (fun k => by simp [st, Function.update_of_ne (Ne.symm h4)])
    (by
      intro k hk v1 v2
      have hd := dblC_spec cap h1 h2 h5 c (((st k).setv G v1).setv G2 v2)
        (by simp [st, Function.update_of_ne h6, Function.update_of_ne h7, Function.update_of_ne (Ne.symm h1), hY])
        (by simp [st, Function.update_of_ne h8, Function.update_of_ne h9, Function.update_of_ne (Ne.symm h2), hT])
        (by
          simp [st, Function.update_of_ne h3, Function.update_of_ne h4]
          have := hmono (k + 1) hk
          rw [show c * (k + 1) = c * k + c by ring, pow_add] at this
          have e : 2 ^ c * (2 ^ (c * k) * x) = 2 ^ (c * k) * 2 ^ c * x := by ring
          omega)
      have ev : (((st k).setv G v1).setv G2 v2).val X = 2 ^ (c * k) * x := by
        simp [st, Function.update_of_ne h3, Function.update_of_ne h4]
      rw [ev] at hd
      refine hd.cast cap ?_ ?_
      · refine WState.eq rfl rfl ?_ rfl
        funext r
        simp only [st, WState.setv_val, Function.update_apply]
        by_cases rX : r = X
        · subst rX; simp [h3, h4]; rw [show c * (k + 1) = c * k + c by ring, pow_add]; ring
        · simp [rX]
      · have := hmono (k + 1) hk
        rw [show c * (k + 1) = c * k + c by ring, pow_add] at this
        have : 2 ^ c * (2 ^ (c * k) * x) = 2 ^ (c * k) * 2 ^ c * x := by ring
        omega)
    (by simp [st, Function.update_of_ne (Ne.symm h3), hn]) (by simp [st, Function.update_of_ne (Ne.symm h4), hG2])
  have e0 : st 0 = σ := by simp [st, hx, wsetv_same]
  rw [e0] at l
  refine l.mono ?_
  ring_nf; omega

def countOnes (I : Fin (ns + 1)) (G G2 : Fin nr) : WMX ns nr :=
  .seq (WMX.fwd I) (.seq (.whs I (.seq (WMX.inc G) (.seq (WMX.fwd I) (WMX.fwd I))))
    (.seq (WMX.bwd I) (repK G G2 (.seq (WMX.bwd I) (WMX.bwd I)))))

/-- The number of leading `true`s. -/
def leadOnes : List Bool → ℕ
  | [] => 0
  | true :: w => leadOnes w + 1
  | false :: _ => 0

theorem leadOnes_true : ∀ (w : List Bool) (j : ℕ), j < leadOnes w → w.getD j false = true
  | [], j, h => by simp [leadOnes] at h
  | true :: w, 0, _ => rfl
  | true :: w, j + 1, h => by simp only [leadOnes] at h; simpa using leadOnes_true w j (by omega)
  | false :: _, j, h => by simp [leadOnes] at h

theorem leadOnes_false : ∀ w : List Bool, w.getD (leadOnes w) false = false
  | [] => rfl
  | true :: w => by simpa [leadOnes] using leadOnes_false w
  | false :: _ => rfl

theorem leadOnes_le : ∀ w : List Bool, leadOnes w ≤ w.length
  | [] => le_rfl
  | true :: w => by simp only [leadOnes, List.length_cons]; have := leadOnes_le w; omega
  | false :: _ => by simp [leadOnes]

theorem frame_odd_rd (u : List Bool) (i : ℕ) : readTapeBit (frame u) (2 * i + 1) = u.getD i false := by
  unfold readTapeBit; exact frame_odd' u i

theorem countOnes_spec (I : Fin (ns + 1)) {G G2 : Fin nr} (hGG : G ≠ G2) (σ : WState ns nr) (w : List Bool)
    (hI : σ.st I = frame w) (hh : σ.sh I = 0) (hG : σ.val G = 0) (hG2 : σ.val G2 = 0)
    (hcap : 2 * w.length + 4 ≤ cap) :
    WXExec cap (countOnes I G G2) σ (σ.setv G (leadOnes w)) (30 * leadOnes w + 20) := by
  set L := leadOnes w with hL
  have hLw := leadOnes_le w
  -- the scan
  have scan : ∀ r j, j + r = L → ∀ τ : WState ns nr, τ = (σ.seth I (2 * j + 1)).setv G j →
      WXExec cap (.whs I (.seq (WMX.inc G) (.seq (WMX.fwd I) (WMX.fwd I)))) τ ((σ.seth I (2 * L + 1)).setv G L)
        (r * 10 + 1) := by
    intro r
    induction r with
    | zero =>
      intro j hj τ hτ
      rw [Nat.add_zero] at hj; subst hj; subst hτ
      refine WXExec.whsF ?_
      show readTapeBit _ _ = false
      simp [hI, frame_odd_rd]
      simpa [List.getD_eq_getElem?_getD] using leadOnes_false w
    | succ r ih =>
      intro j hj τ hτ
      subst hτ
      have hb : wbit ((σ.seth I (2 * j + 1)).setv G j) I = true := by
        show readTapeBit _ _ = true
        simp [hI, frame_odd_rd]; exact leadOnes_true w j (by omega)
      have i1 := WXExec.inc cap G ((σ.seth I (2 * j + 1)).setv G j) (by simp; omega)
      set τ1 := ((σ.seth I (2 * j + 1)).setv G j).setv G (((σ.seth I (2 * j + 1)).setv G j).val G + 1)
      have i2 := WXExec.fwd cap I τ1
      have i3 := WXExec.fwd cap I (τ1.seth I (τ1.sh I + 1))
      have e : (τ1.seth I (τ1.sh I + 1)).seth I ((τ1.seth I (τ1.sh I + 1)).sh I + 1) =
          (σ.seth I (2 * (j + 1) + 1)).setv G (j + 1) := by
        refine WState.eq ?_ rfl ?_ rfl
        · funext i; by_cases hi : i = I
          · subst hi; simp [τ1]; ring
          · simp [τ1, Function.update_of_ne hi]
        · funext q; by_cases hq : q = G
          · subst hq; simp [τ1]
          · simp [τ1, Function.update_of_ne hq]
      rw [e] at i3
      have rest := ih (j + 1) (by omega) _ rfl
      exact WXExec.mono (WXExec.whsT hb (WXExec.seq i1 (WXExec.seq i2 i3)) rest) (by ring_nf; omega)
  have f0 := WXExec.fwd cap I σ
  rw [hh] at f0
  have s1 := scan L 0 (by omega) (σ.seth I (0 + 1)) (by
    refine WState.eq rfl rfl ?_ rfl
    funext q; by_cases hq : q = G
    · subst hq; simp [hG]
    · simp [Function.update_of_ne hq])
  have b1 := WXExec.bwd cap I ((σ.seth I (2 * L + 1)).setv G L)
  -- the return
  let st : ℕ → WState ns nr := fun k => (σ.seth I (2 * L - 2 * k)).setv G L
  have l := Runs.repE (cap := cap) (K := G) (K2 := G2) (body := .seq (WMX.bwd I) (WMX.bwd I)) hGG 3 L st
    (by omega) (fun k => by simp [st]) (fun k => by simp [st, Function.update_of_ne (Ne.symm hGG)])
    (by
      intro k hk v1 v2
      have w1 := WXExec.bwd cap I (((st k).setv G v1).setv G2 v2)
      have w2 := WXExec.bwd cap I ((((st k).setv G v1).setv G2 v2).seth I
        ((((st k).setv G v1).setv G2 v2).sh I - 1))
      refine WXExec.cast cap (WXExec.seq w1 w2) ?_ (by omega)
      refine WState.eq ?_ rfl rfl rfl
      funext i; by_cases hi : i = I
      · subst hi; simp [st]; omega
      · simp [st, Function.update_of_ne hi])
    (by simp [st]) (by simp [st, Function.update_of_ne (Ne.symm hGG), hG2])
  have e1 : ((σ.seth I (2 * L + 1)).setv G L).seth I (((σ.seth I (2 * L + 1)).setv G L).sh I - 1) = st 0 := by
    refine WState.eq ?_ rfl rfl rfl
    funext i; by_cases hi : i = I
    · subst hi; simp [st]
    · simp [st, Function.update_of_ne hi]
  have e2 : st L = σ.setv G L := by
    refine WState.eq ?_ rfl rfl rfl
    funext i; by_cases hi : i = I
    · subst hi; simp [st, hh]
    · simp [st, Function.update_of_ne hi]
  rw [e1] at b1
  rw [e2] at l
  exact WXExec.mono (WXExec.seq f0 (WXExec.seq s1 (WXExec.seq b1 l))) (by ring_nf; omega)

/-- One program per stream of a list. -/
def forStreams (P : Fin (ns + 1) → WMX ns nr) : List (Fin (ns + 1)) → WMX ns nr
  | [] => WMX.skip
  | X :: l => .seq (P X) (forStreams P l)

/-- Each `P X` writes `f X` on the fresh stream `X`, leaving everything else (registers as at the start). -/
theorem forStreams_spec (P : Fin (ns + 1) → WMX ns nr) (f : Fin (ns + 1) → List Bool) (c : ℕ) (vals : Fin nr → ℕ)
    (hP : ∀ X τ, τ.st X = [] → τ.sh X = 0 → τ.val = vals → WXExec cap (P X) τ (τ.sets X (f X)) c) :
    ∀ (l : List (Fin (ns + 1))) (σ : WState ns nr), l.Nodup → (∀ X ∈ l, σ.st X = [] ∧ σ.sh X = 0) →
      σ.val = vals →
      WXExec cap (forStreams P l) σ { σ with st := fun i => if i ∈ l then f i else σ.st i } (l.length * (c + 1)) := by
  intro l
  induction l with
  | nil =>
    intro σ _ _ _
    have : { σ with st := fun i => if i ∈ ([] : List (Fin (ns + 1))) then f i else σ.st i } = σ := by
      refine WState.eq rfl ?_ rfl rfl; funext i; simp
    rw [this]; simpa [forStreams] using WXExec.skip cap σ
  | cons X l ih =>
    intro σ hnd h0 hv
    have hX := h0 X (by simp)
    have h1 := hP X σ hX.1 hX.2 hv
    have hnd' := List.nodup_cons.mp hnd
    have h2 := ih (σ.sets X (f X)) hnd'.2 (fun Y hY => by
        have hYX : Y ≠ X := fun e => hnd'.1 (e ▸ hY)
        have := h0 Y (by simp [hY])
        simp [Function.update_of_ne hYX, this]) (by simp [hv])
    refine WXExec.mono (WXExec.seq h1 h2 |>.cast cap ?_ le_rfl) (by simp; ring_nf; omega)
    refine WState.eq rfl ?_ rfl rfl
    funext i
    by_cases hi : i = X
    · subst hi; simp [hnd'.1]
    · simp [Function.update_of_ne hi, hi]

end Tools

end NearCubicGates.Close.Cells
