import SourceAdapters.Refuter.CheckerPass

/-!
# Reading the guessed cutoff `r` (input 7, F01 machine layer, part 13)

proof of `lem:multitape-refuter`: "the hierarchy verifier guesses a positive length `r` in unary". `readR` reads the
guessed bits `1^r 0` from the witness (bits beyond it read `0`), counts `r` into `R0` and writes the
cutoff stream `RS = 1^r` over an all-blank stream (head back at `0`). Cost `O(r + 1)`.
-/

namespace NearCubicGates.Adapters.Refuter.Mach

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.WordPrograms
open NearCubicGates.Adapters.Refuter

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable (cap : ℕ)

/-- The guessed unary number at position `p` (fuel `f`). -/
def gun (wD : List Bool) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | f + 1, p => if gbit wD p then gun wD f (p + 1) + 1 else 0

/-- Ones written at cells `0, …, k-1`. -/
def wones (L0 : List Bool) : ℕ → List Bool
  | 0 => L0
  | k + 1 => writeTapeBit (wones L0 k) k true

theorem wones_read (L0 : List Bool) (h0 : ∀ h, readTapeBit L0 h = false) :
    ∀ k h, readTapeBit (wones L0 k) h = decide (h < k)
  | 0, h => by simp [wones, h0]
  | k + 1, h => by
    simp only [wones]
    rw [readTapeBit_writeTapeBit, wones_read L0 h0 k h]
    by_cases hh : h = k <;> simp [hh] <;> omega

def readRBody : Pg :=
  .seq (clr rBIT) (.seq (WMX.inc rR0) (.seq (WMX.wr sRS true) (.seq (WMX.fwd sRS) (readG sWIT rBIT rWP))))

def readR : Pg := .seq (readG sWIT rBIT rWP) (.seq (.whr rBIT readRBody) (.seq (bwdK sRS rR0 rTB) (clr rWP)))

/-- The state after `k` ones and the next bit read. -/
def rstate (σ : St) (wD : List Bool) (p k : ℕ) : St :=
  ((((σ.setv rBIT (gbit wD (p + k)).toNat).setv rR0 k).setv rWP (σ.val rWP + witMoves wD p (p + k + 1))).seth
    sWIT (2 * min (p + k + 1) wD.length) |>.sets sRS (wones (σ.st sRS) k)) |>.seth sRS k

theorem readRLoop_spec (σ : St) (wD : List Bool) (p : ℕ) (hst : σ.st sWIT = RepairOrdinary.frame wD)
    (_hsh : σ.sh sRS = 0) (hcap : 2 * σ.val rWP + 4 * wD.length + 8 ≤ cap) :
    ∀ f k, wD.length < p + k + f → k ≤ wD.length - p →
      (∀ j < k, gbit wD (p + j) = true) →
      WXExec cap (.whr rBIT readRBody) (rstate σ wD p k) (rstate σ wD p (k + gun wD f (p + k)))
        (gun wD f (p + k) * 40 + 1) := by
  intro f
  induction f with
  | zero =>
    intro k hL hk hpre
    have hg : gbit wD (p + k) = false := gbit_beyond wD (by omega)
    simp only [gun, Nat.add_zero, Nat.zero_mul, Nat.zero_add]
    exact WXExec.whrF (by simp [rstate, hg])
  | succ f ih =>
    intro k hL hk hpre
    cases hg : gbit wD (p + k)
    · simp only [gun, hg, if_false, Nat.add_zero, Nat.zero_mul, Nat.zero_add]
      exact WXExec.whrF (by simp [rstate, hg])
    · have hpk : p + k < wD.length := by
        by_contra hc; rw [gbit_beyond wD (by omega)] at hg; exact absurd hg (by decide)
      have hw : witMoves wD p (p + k + 1) ≤ 2 * wD.length := by unfold witMoves; omega
      set σk := rstate σ wD p k with hσk
      have e1 := clr_spec cap rBIT σk (by simp [σk, rstate, hg]; lomega)
      obtain ⟨σ1, e1, h1⟩ := exEq cap e1
      have e2 := WXExec.inc cap rR0 σ1 (by simp [h1, σk, rstate]; lomega)
      obtain ⟨σ2, e2, h2⟩ := exEq cap e2
      have e3 := WXExec.wr cap sRS true σ2
      obtain ⟨σ3, e3, h3⟩ := exEq cap e3
      have e4 := WXExec.fwd cap sRS σ3
      obtain ⟨σ4, e4, h4⟩ := exEq cap e4
      have e5 := readG_spec cap (W := sWIT) (B := rBIT) (WP := rWP) (by decide) σ4 wD (p + k + 1)
        (by simp [h4, h3, h2, h1, σk, rstate, hst]) (by simp [h4, h3, h2, h1, σk, rstate])
        (by simp [h4, h3, h2, h1, σk, rstate]; lomega) (by simp [h4, h3, h2, h1, σk, rstate, Function.update_apply]; lomega)
      have heq : ((σ4.setv rBIT (σ4.val rBIT + (gbit wD (p + k + 1)).toNat)).setv rWP
          (σ4.val rWP + 2 * (min (p + k + 1 + 1) wD.length - min (p + k + 1) wD.length))).seth sWIT
            (2 * min (p + k + 1 + 1) wD.length) = rstate σ wD p (k + 1) := by
        rw [h4, h3, h2, h1]
        simp only [σk, rstate, wones, witMoves, ← Nat.add_assoc]
        wsta
      rw [heq] at e5
      have hrest := ih (k + 1) (by omega) (by omega) (by
        intro j hj
        by_cases hjk : j = k
        · subst hjk; exact hg
        · exact hpre j (by omega))
      have hgun : gun wD (f + 1) (p + k) = gun wD f (p + (k + 1)) + 1 := by
        simp [gun, hg, Nat.add_assoc]
      rw [hgun]
      rw [show k + (gun wD f (p + (k + 1)) + 1) = k + 1 + gun wD f (p + (k + 1)) by ring]
      refine (WXExec.whrT (by simp [σk, rstate, hg]) (WXExec.seq e1 (WXExec.seq e2 (WXExec.seq e3
        (WXExec.seq e4 e5)))) hrest).mono ?_
      simp [h3, h2, h1, σk, rstate, hg]
      ring_nf; omega

theorem gun_stop (wD : List Bool) : ∀ f p, wD.length < p + f → gbit wD (p + gun wD f p) = false
  | 0, p, h => gbit_beyond wD (by simp [gun]; omega)
  | f + 1, p, h => by
    simp only [gun]
    cases hg : gbit wD p
    · simpa using hg
    · simp only [if_true]
      have := gun_stop wD f (p + 1) (by omega)
      rw [show p + (gun wD f (p + 1) + 1) = p + 1 + gun wD f (p + 1) by ring]; exact this

theorem gun_le (wD : List Bool) : ∀ f p, gun wD f p ≤ wD.length - p
  | 0, p => by simp [gun]
  | f + 1, p => by
    simp only [gun]
    split
    · rename_i hg
      have hp : p < wD.length := by
        by_contra hc; rw [gbit_beyond wD (by omega)] at hg; exact absurd hg (by decide)
      have := gun_le wD f (p + 1); omega
    · omega

theorem gun_true (wD : List Bool) : ∀ f p j, j < gun wD f p → gbit wD (p + j) = true
  | 0, p, j, h => by simp [gun] at h
  | f + 1, p, j, h => by
    simp only [gun] at h
    cases hg : gbit wD p
    · simp [hg] at h
    · simp only [hg, if_true] at h
      cases j with
      | zero => simpa using hg
      | succ j =>
        have := gun_true wD f (p + 1) j (by omega)
        rw [show p + (j + 1) = p + 1 + j by ring]; exact this

/-- **Reading `r`.** `r = gun wD (|wD|+1) p`; `R0 := r`, `RS := 1^r` over the old (blank) contents,
the witness head after the closing `0`; cost `70(r+1)`. -/
theorem readR_spec (σ : St) (wD : List Bool) (p : ℕ) (hst : σ.st sWIT = RepairOrdinary.frame wD)
    (hsh : σ.sh sWIT = 2 * min p wD.length) (hBIT : σ.val rBIT = 0) (hR0 : σ.val rR0 = 0)
    (hRS : σ.sh sRS = 0) (hTB : σ.val rTB = 0) (hWP : σ.val rWP = 0)
    (hcap : 4 * wD.length + 8 ≤ cap) :
    WXExec cap readR σ
      (((σ.setv rR0 (gun wD (wD.length + 1) p)).seth sWIT
        (2 * min (p + gun wD (wD.length + 1) p + 1) wD.length)).sets sRS
          (wones (σ.st sRS) (gun wD (wD.length + 1) p)))
      (70 * (gun wD (wD.length + 1) p + 1)) := by
  have hr := gun_le wD (wD.length + 1) p
  have hstop := gun_stop wD (wD.length + 1) p (by omega)
  have e1 := readG_spec cap (W := sWIT) (B := rBIT) (WP := rWP) (by decide) σ wD p hst hsh (by lomega)
    (by lomega)
  have heq : ((σ.setv rBIT (σ.val rBIT + (gbit wD p).toNat)).setv rWP
      (σ.val rWP + 2 * (min (p + 1) wD.length - min p wD.length))).seth sWIT (2 * min (p + 1) wD.length) =
      rstate σ wD p 0 := by
    simp only [rstate, wones, witMoves, Nat.add_zero]
    wst
  rw [heq] at e1
  have e2 := readRLoop_spec cap σ wD p hst hRS (by lomega) (wD.length + 1) 0 (by omega) (by omega)
    (fun j hj => absurd hj (Nat.not_lt_zero _))
  simp only [Nat.zero_add] at e2
  have e3 := bwdK_spec cap (S := sRS) (K := rR0) (K2 := rTB) (by decide)
    (rstate σ wD p (gun wD (wD.length + 1) p)) (by simp [rstate, hTB]) (by simp [rstate]; lomega)
  obtain ⟨σ3, e3, h3⟩ := exEq cap e3
  have hw : witMoves wD p (p + gun wD (wD.length + 1) p + 1) ≤ 2 * (gun wD (wD.length + 1) p + 1) := by
    unfold witMoves; omega
  have e4 := clr_spec cap rWP σ3 (by simp [h3, rstate, Function.update_apply, hWP]; lomega)
  refine (WXExec.seq e1 (WXExec.seq e2 (WXExec.seq e3 e4))).cast cap ?_ (by
    simp [h3, rstate, Function.update_apply, hWP]; lomega)
  rw [h3]
  simp only [rstate, hstop]
  wst

end NearCubicGates.Adapters.Refuter.Mach
