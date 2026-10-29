import SourceAdapters.Refuter.NextRecord

/-!
# The tapes of the second simulation (input 7, the record codec, part 6)

proof of `cor:framed-refuter`: "For the second simulation, when `i<s`, it prepares `fr(x_{i+1})` and `fr(v)`, where it
guesses exactly `g(N)` bits `v`." `copyX` copies the incremented input `fr(x_{i+1})` over the first
simulation's `XS` (same length `2N+1`); `readV` reads the next `g` guessed bits from the witness and writes
`fr(v)` over `YS` (same length `2g+1`). Both return their heads to `0`; the costs are `O(N)` with absolute
constants.
-/

namespace NearCubicGates.Adapters.Refuter.Mach

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairSource
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.WordPrograms
open NearCubicGates.Adapters.Refuter

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable (cap : ℕ)

theorem wcopy_length (old src : List Bool) : ∀ k, k ≤ old.length → (wcopy old src k).length = old.length
  | 0, _ => rfl
  | k + 1, h => by simp only [wcopy, wtb_length, wcopy_length old src k (by omega)]; omega

theorem wcopy_full (old src : List Bool) (h : old.length = src.length) : wcopy old src src.length = src := by
  apply list_eq_of_read (by rw [wcopy_length old src _ (by omega)]; exact h)
  intro p hp
  rw [wcopy_length old src _ (by omega)] at hp
  exact wcopy_read old src _ p (by omega)

/-! ## Copying `fr(x_{i+1})` over `XS` -/

def cpCell : Pg := .seq (.ifs sIN (WMX.wr sXS true) (WMX.wr sXS false)) (.seq (WMX.fwd sIN) (WMX.fwd sXS))

def copyX : Pg :=
  .seq (addR rTE rTD rTA) (.seq (addR rTE rTD rTA) (.seq (WMX.inc rTD) (.seq (bwdK sIN rTD rTB)
    (.seq (repK rTD rTG cpCell) (.seq (bwdK sIN rTD rTB) (.seq (bwdK sXS rTD rTB) (clr rTD)))))))

theorem cpCell_step (σ : St) (k : ℕ) (old src : List Bool) (hX : σ.st sIN = src) (v1 v2 : ℕ) :
    WXExec cap cpCell
      (((((σ.seth sIN k).sets sXS (wcopy old src k)).seth sXS k).setv rTD v1).setv rTG v2)
      (((((σ.seth sIN (k + 1)).sets sXS (wcopy old src (k + 1))).seth sXS (k + 1)).setv rTD v1).setv rTG v2) 6 := by
  set τ := ((((σ.seth sIN k).sets sXS (wcopy old src k)).seth sXS k).setv rTD v1).setv rTG v2 with hτ
  have hb : wbit τ sIN = readTapeBit src k := by simp [τ, wbit, Function.update_apply, hX]
  have hw : ∀ b : Bool, b = readTapeBit src k → WXExec cap (WMX.wr sXS b) τ
      (τ.sets sXS (wcopy old src (k + 1))) 1 := by
    intro b hb'
    refine (WXExec.wr cap sXS b τ).cast cap ?_ le_rfl
    simp [τ, wcopy, hb']
  have e1 : WXExec cap (.ifs sIN (WMX.wr sXS true) (WMX.wr sXS false)) τ (τ.sets sXS (wcopy old src (k + 1))) 2 := by
    cases h : readTapeBit src k
    · exact WXExec.ifsF (by rw [hb, h]) (hw false h.symm)
    · exact WXExec.ifsT (by rw [hb, h]) (hw true h.symm)
  refine (WXExec.seq e1 (WXExec.seq (WXExec.fwd cap sIN _) (WXExec.fwd cap sXS _))).cast cap ?_ (by omega)
  apply WState.eq
  · funext j; by_cases a1 : j = sIN
    · subst a1; simp [τ]
    · by_cases a2 : j = sXS
      · subst a2; simp [τ]
      · simp [τ, Function.update_apply, a1, a2]
  · funext j; by_cases a2 : j = sXS
    · subst a2; simp [τ]
    · simp [τ, Function.update_apply, a2]
  · rfl
  · rfl

set_option maxHeartbeats 400000 in
/-- **`XS := fr(x_{i+1})`** (proof of `cor:framed-refuter`). -/
theorem copyX_spec (σ : St) (L : List Bool) (N : ℕ) (hL : L.length = N) (hX : σ.st sIN = RepairOrdinary.frame L)
    (hXh : σ.sh sIN ≤ 2 * N) (hXS : (σ.st sXS).length = 2 * N + 1) (hXSh : σ.sh sXS = 0) (hE : σ.val rTE = N)
    (hD : σ.val rTD = 0) (hTA : σ.val rTA = 0) (hTB : σ.val rTB = 0) (hTG : σ.val rTG = 0) (hcap : 8 * N + 8 ≤ cap) :
    ∃ c, WXExec cap copyX σ ((σ.seth sIN 0).sets sXS (RepairOrdinary.frame L)) c ∧ c ≤ 200 * (N + 1) := by
  have hfl : (RepairOrdinary.frame L).length = 2 * N + 1 := by rw [frame_length, hL]
  obtain ⟨σ1, e1, h1⟩ := exEq cap (addR_spec cap (A := rTE) (B := rTD) (T := rTA) (by decide) (by decide) (by decide) σ hTA
    (by rw [hD, hE]; omega))
  obtain ⟨σ2, e2, h2⟩ := exEq cap (addR_spec cap (A := rTE) (B := rTD) (T := rTA) (by decide) (by decide) (by decide) σ1
    (by rw [h1]; simp [hTA]) (by rw [h1]; simp [hD, hE]; omega))
  obtain ⟨σ3, e3, h3⟩ := exEq cap (WXExec.inc cap rTD σ2 (by rw [h2, h1]; simp [hD, hE]; omega))
  have v3 : σ3.val rTD = 2 * N + 1 := by rw [h3, h2, h1]; simp [hD, hE]; omega
  obtain ⟨σ4, e4, h4⟩ := exEq cap (bwdK_spec cap (S := sIN) (K := rTD) (K2 := rTB) (by decide) σ3
    (by rw [h3, h2, h1]; simp [hTB]) (by rw [v3]; omega))
  have s4 : σ4 = (σ.seth sIN 0).setv rTD (2 * N + 1) := by
    rw [h4, v3, h3, h2, h1]
    apply WState.eq
    · funext j; by_cases a1 : j = sIN
      · subst a1; simp; lomega
      · simp [Function.update_apply, a1]
    · rfl
    · funext r; by_cases a1 : r = rTD
      · subst a1; simp [hD, hE]; omega
      · simp [Function.update_apply, a1]
    · rfl
  set σ' := (σ.seth sIN 0).setv rTD (2 * N + 1) with hσ'
  have e5 := Runs.repE (cap := cap) (K := rTD) (K2 := rTG) (body := cpCell) (by decide) 6 (2 * N + 1)
    (fun k => ((σ'.seth sIN k).sets sXS (wcopy (σ.st sXS) (RepairOrdinary.frame L) k)).seth sXS k) (by omega)
    (fun k => by simp) (fun k => by simp)
    (fun k _ v1 v2 => cpCell_step cap σ' k (σ.st sXS) (RepairOrdinary.frame L) (by simp [σ', hX]) v1 v2)
    (by simp [σ']) (by simp [σ', Function.update_apply, hTG])
  have st0 : ((σ'.seth sIN 0).sets sXS (wcopy (σ.st sXS) (RepairOrdinary.frame L) 0)).seth sXS 0 = σ4 := by
    rw [s4]
    apply WState.eq
    · funext j; by_cases a1 : j = sXS
      · subst a1; simp [σ', hXSh]
      · by_cases a2 : j = sIN
        · subst a2; simp [σ']
        · simp [σ', Function.update_apply, a1, a2]
    · funext j; by_cases a1 : j = sXS
      · subst a1; simp [σ', wcopy]
      · simp [σ', Function.update_apply, a1]
    · rfl
    · rfl
  rw [st0, ← hfl, wcopy_full _ _ (by rw [hXS, hfl]), hfl] at e5
  set σ5 := ((σ'.seth sIN (2 * N + 1)).sets sXS (RepairOrdinary.frame L)).seth sXS (2 * N + 1) with hσ5
  have v5 : σ5.val rTD = 2 * N + 1 := by simp [σ5, σ']
  obtain ⟨σ6, e6, h6⟩ := exEq cap (bwdK_spec cap (S := sIN) (K := rTD) (K2 := rTB) (by decide) σ5
    (by simp [σ5, σ', Function.update_apply, hTB]) (by rw [v5]; omega))
  obtain ⟨σ7, e7, h7⟩ := exEq cap (bwdK_spec cap (S := sXS) (K := rTD) (K2 := rTB) (by decide) σ6
    (by rw [h6]; simp [σ5, σ', Function.update_apply, hTB]) (by rw [h6]; simp [v5]; omega))
  obtain ⟨σ8, e8, h8⟩ := exEq cap (clr_spec cap rTD σ7 (by rw [h7, h6, v5]; simp [σ5, σ']; omega))
  refine ⟨_, (WXExec.seq e1 (WXExec.seq e2 (WXExec.seq e3 (WXExec.seq e4 (WXExec.seq e5 (WXExec.seq e6
    (WXExec.seq e7 e8))))))).cast cap ?_ le_rfl, ?_⟩
  · rw [h8, h7, h6]
    apply WState.eq
    · funext j; by_cases a1 : j = sXS
      · subst a1; simp [σ5, σ', hXSh]
      · by_cases a2 : j = sIN
        · subst a2; simp [σ5, σ']
        · simp [σ5, σ', Function.update_apply, a1, a2]
    · funext j; by_cases a1 : j = sXS
      · subst a1; simp [σ5, σ']
      · simp [σ5, σ', Function.update_apply, a1]
    · funext r; by_cases a1 : r = rTD
      · subst a1; simp [hD]
      · simp [σ5, σ', Function.update_apply, a1]
    · rfl
  · rw [h7, h6, h3, h2, h1]; simp [σ5, σ', hD, hE]; omega

/-! ## Reading `v` into `YS` -/

/-- `YS` after `k` guessed bits written as framed pairs over `old`. -/
def yv (old wD : List Bool) (e : ℕ) : ℕ → List Bool
  | 0 => old
  | k + 1 => writeTapeBit (writeTapeBit (yv old wD e k) (2 * k) true) (2 * k + 1) (gbit wD (e + k))

theorem yv_length (old wD : List Bool) (e : ℕ) : ∀ k, 2 * k ≤ old.length → (yv old wD e k).length = old.length
  | 0, _ => rfl
  | k + 1, h => by simp only [yv, wtb_length, yv_length old wD e k (by omega)]; omega

theorem yv_read (old wD : List Bool) (e : ℕ) : ∀ k p, p < 2 * k →
    readTapeBit (yv old wD e k) p = if p % 2 = 0 then true else gbit wD (e + p / 2)
  | 0, p, h => absurd h (by omega)
  | k + 1, p, h => by
    simp only [yv]
    rw [readTapeBit_writeTapeBit, readTapeBit_writeTapeBit]
    by_cases h1 : p = 2 * k + 1
    · subst h1; rw [if_pos rfl, if_neg (by omega), show (2 * k + 1) / 2 = k by omega]
    · by_cases h2 : p = 2 * k
      · subst h2; rw [if_neg (by omega), if_pos rfl, if_pos (by omega)]
      · rw [if_neg h1, if_neg h2, yv_read old wD e k p (by omega)]

theorem yv_frame (old wD : List Bool) (e g : ℕ) (h : old.length = 2 * g + 1) :
    writeTapeBit (yv old wD e g) (2 * g) false = RepairOrdinary.frame (gbits wD e g) := by
  have hl : (gbits wD e g).length = g := by simp [gbits]
  apply list_eq_of_read
  · rw [wtb_length, yv_length _ _ _ _ (by omega), frame_length, hl]; omega
  · intro p hp
    rw [wtb_length, yv_length _ _ _ _ (by omega)] at hp
    rw [readTapeBit_writeTapeBit, frame_eq_fpre]
    by_cases h1 : p = 2 * g
    · subst h1; rw [if_pos rfl, show 2 * g = 2 * (gbits wD e g).length + 0 by rw [hl]; ring, rd_fpre_after]; rfl
    · rw [if_neg h1, yv_read _ _ _ _ _ (by omega)]
      rcases Nat.even_or_odd' p with ⟨q, rfl | rfl⟩
      · rw [rd_fpre_mark _ _ (by rw [hl]; omega), if_pos (by omega)]
      · rw [rd_fpre_data _ _ (by rw [hl]; omega), if_neg (by omega), show (2 * q + 1) / 2 = q by omega]
        simp [gbits]

def vBody : Pg :=
  .seq (readG sWIT rBIT rWP) (.seq (WMX.wr sYS true) (.seq (WMX.fwd sYS) (.seq (.ifr rBIT (WMX.wr sYS true)
    (WMX.wr sYS false)) (.seq (WMX.fwd sYS) (clr rBIT)))))

def readV : Pg :=
  .seq (repK rS rTG vBody) (.seq (WMX.wr sYS false) (.seq (bwdK sYS rS rTB) (.seq (bwdK sYS rS rTB) (clr rWP))))

/-- The states of `readV`'s loop. -/
def vSt (σ : St) (wD : List Bool) (e k : ℕ) : St :=
  ((((σ.seth sWIT (2 * min (e + k) wD.length)).sets sYS (yv (σ.st sYS) wD e k)).seth sYS (2 * k)).setv rWP
    (witMoves wD e (e + k)))

set_option maxHeartbeats 400000 in
theorem vBody_step (σ : St) (wD : List Bool) (e k v1 v2 : ℕ) (hst : σ.st sWIT = RepairOrdinary.frame wD)
    (hB : σ.val rBIT = 0) (hcap : 4 * wD.length + 8 ≤ cap) :
    WXExec cap vBody (((vSt σ wD e k).setv rS v1).setv rTG v2) (((vSt σ wD e (k + 1)).setv rS v1).setv rTG v2) 32 := by
  set τ := ((vSt σ wD e k).setv rS v1).setv rTG v2 with hτ
  have hwm : witMoves wD e (e + k) ≤ 2 * wD.length := by unfold witMoves; omega
  have e1 := readG_spec cap (W := sWIT) (B := rBIT) (WP := rWP) (by decide) τ wD (e + k)
    (by simp [τ, vSt, hst]) (by simp [τ, vSt]) (by simp [τ, vSt, hB]; lomega) (by simp [τ, vSt]; unfold witMoves; lomega)
  obtain ⟨τ1, e1, h1⟩ := exEq cap e1
  have b1 : τ1.val rBIT = (gbit wD (e + k)).toNat := by rw [h1]; simp [τ, vSt, hB]
  have y1 : τ1.st sYS = yv (σ.st sYS) wD e k := by rw [h1]; simp [τ, vSt]
  have yh1 : τ1.sh sYS = 2 * k := by rw [h1]; simp [τ, vSt]
  obtain ⟨τ2, e2, h2⟩ := exEq cap (WXExec.wr cap sYS true τ1)
  obtain ⟨τ3, e3, h3⟩ := exEq cap (WXExec.fwd cap sYS τ2)
  have eIf : WXExec cap (.ifr rBIT (WMX.wr sYS true) (WMX.wr sYS false)) τ3
      (τ3.sets sYS (writeTapeBit (τ3.st sYS) (τ3.sh sYS) (gbit wD (e + k)))) 2 := by
    cases hg : gbit wD (e + k)
    · exact WXExec.ifrF (by rw [h3, h2]; simp [b1, hg]) (WXExec.wr cap sYS false τ3)
    · exact WXExec.ifrT (by rw [h3, h2]; simp [b1, hg]) (WXExec.wr cap sYS true τ3)
  obtain ⟨τ4, e4, h4⟩ := exEq cap eIf
  obtain ⟨τ5, e5, h5⟩ := exEq cap (WXExec.fwd cap sYS τ4)
  have b5 : τ5.val rBIT = (gbit wD (e + k)).toNat := by
    rw [h5, h4, h3, h2]; simp only [WState.setv_val, WState.seth_val, WState.sets_val]; exact b1
  obtain ⟨τ6, e6, h6⟩ := exEq cap (clr_spec cap rBIT τ5 (by rw [b5]; cases gbit wD (e + k) <;> simp <;> omega))
  refine (WXExec.seq e1 (WXExec.seq e2 (WXExec.seq e3 (WXExec.seq e4 (WXExec.seq e5 e6))))).cast cap ?_ ?_
  · rw [h6, h5, h4, h3, h2, h1]
    have hwm2 : witMoves wD e (e + k) + 2 * (min (e + k + 1) wD.length - min (e + k) wD.length) =
        witMoves wD e (e + (k + 1)) := by
      rw [show e + (k + 1) = e + k + 1 by ring]; unfold witMoves; omega
    apply WState.eq
    · funext j; by_cases a1 : j = sYS
      · subst a1; simp [τ, vSt]; ring
      · by_cases a2 : j = sWIT
        · subst a2; simp [τ, vSt]; ring_nf
        · simp [τ, vSt, Function.update_apply, a1, a2]
    · funext j; by_cases a1 : j = sYS
      · subst a1; simp [τ, vSt, yv]
      · simp [τ, vSt, Function.update_apply, a1]
    · funext r
      by_cases a1 : r = rBIT
      · subst a1; simp [τ, vSt, hB]
      · by_cases a2 : r = rWP
        · subst a2; simp [τ, vSt, hwm2]
        · simp [τ, vSt, Function.update_apply, a1, a2]
    · rfl
  · rw [b5]; cases gbit wD (e + k) <;> simp

set_option maxHeartbeats 400000 in
/-- **`YS := fr(v)`** for the `g` guessed bits `v` at logical witness position `e` (proof of `cor:framed-refuter`). -/
theorem readV_spec (σ : St) (wD : List Bool) (e g : ℕ) (hst : σ.st sWIT = RepairOrdinary.frame wD)
    (hwh : σ.sh sWIT = 2 * min e wD.length) (hY : (σ.st sYS).length = 2 * g + 1) (hYh : σ.sh sYS = 0)
    (hS : σ.val rS = g) (hB : σ.val rBIT = 0) (hWP : σ.val rWP = 0) (hTG : σ.val rTG = 0) (hTB : σ.val rTB = 0)
    (hcap : 4 * wD.length + 4 * g + 8 ≤ cap) :
    ∃ c, WXExec cap readV σ ((σ.seth sWIT (2 * min (e + g) wD.length)).sets sYS
      (RepairOrdinary.frame (gbits wD e g))) c ∧ c ≤ 100 * (g + 1) := by
  have h0 : vSt σ wD e 0 = σ := by
    apply WState.eq
    · funext j; by_cases a1 : j = sYS
      · subst a1; simp [vSt, hYh]
      · by_cases a2 : j = sWIT
        · subst a2; simp [vSt, hwh]
        · simp [vSt, Function.update_apply, a1, a2]
    · funext j; by_cases a1 : j = sYS
      · subst a1; simp [vSt, yv]
      · simp [vSt, Function.update_apply, a1]
    · funext r; by_cases a1 : r = rWP
      · subst a1; simp [vSt, witMoves, hWP]
      · simp [vSt, Function.update_apply, a1]
    · rfl
  have e1 := Runs.repE (cap := cap) (K := rS) (K2 := rTG) (body := vBody) (by decide) 32 g (vSt σ wD e)
    (by omega) (fun k => by simp [vSt]) (fun k => by simp [vSt])
    (fun k _ v1 v2 => vBody_step cap σ wD e k v1 v2 hst hB (by omega)) (by simp [vSt, hS]) (by simp [vSt, hTG])
  rw [h0] at e1
  obtain ⟨σ2, e2, h2⟩ := exEq cap (WXExec.wr cap sYS false (vSt σ wD e g))
  have y2 : σ2.st sYS = RepairOrdinary.frame (gbits wD e g) := by
    rw [h2]; simp [vSt]; exact yv_frame _ _ _ _ hY
  obtain ⟨σ3, e3, h3⟩ := exEq cap (bwdK_spec cap (S := sYS) (K := rS) (K2 := rTB) (by decide) σ2
    (by rw [h2]; simp [vSt, hTB]) (by rw [h2]; simp [vSt, hS]; omega))
  obtain ⟨σ4, e4, h4⟩ := exEq cap (bwdK_spec cap (S := sYS) (K := rS) (K2 := rTB) (by decide) σ3
    (by rw [h3, h2]; simp [vSt, hTB]) (by rw [h3, h2]; simp [vSt, hS]; omega))
  have hwm : witMoves wD e (e + g) ≤ 2 * g := by unfold witMoves; omega
  obtain ⟨σ5, e5, h5⟩ := exEq cap (clr_spec cap rWP σ4 (by rw [h4, h3, h2]; simp [vSt]; omega))
  refine ⟨_, (WXExec.seq e1 (WXExec.seq e2 (WXExec.seq e3 (WXExec.seq e4 e5)))).cast cap ?_ le_rfl, ?_⟩
  · rw [h5, h4, h3]
    apply WState.eq
    · funext j; by_cases a1 : j = sYS
      · subst a1; simp [h2, vSt, hYh, hS]; omega
      · by_cases a2 : j = sWIT
        · subst a2; simp [h2, vSt]
        · simp [h2, vSt, Function.update_apply, a1, a2]
    · funext j; by_cases a1 : j = sYS
      · subst a1; simp [y2]
      · simp [h2, vSt, Function.update_apply, a1]
    · funext r; by_cases a1 : r = rWP
      · subst a1; simp [hWP]
      · simp [h2, vSt, Function.update_apply, a1]
    · simp [h2, vSt]
  · rw [h4, h3, h2]; simp [vSt, hS]; omega

end NearCubicGates.Adapters.Refuter.Mach
