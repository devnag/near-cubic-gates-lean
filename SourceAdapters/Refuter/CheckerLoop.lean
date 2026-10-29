import SourceAdapters.Refuter.CheckerStepSpec

/-!
# The loop of one pass over the guessed trace (input 7, F01 machine layer, part 9)

The guessed trace (SFM78 l.222–224) is read from the witness as markers: `1` followed by a display
of `t` bits, repeated, and a final `0`. Bits beyond the witness read as `0`, so every witness parses
(`gtrace`, `gend`): a branch whose witness runs out simply ends its trace there.

`passLoop_spec`: from a pass state at logical witness position `p`, the loop runs `passRun` over the
parsed displays, in `n·(stepCost v + 40) + 40` steps for `n` parsed steps.
-/

namespace NearCubicGates.Adapters.Refuter.Mach

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairSource NearCubicWires.RepairSource.VerifierEncoding
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.WordPrograms
open NearCubicGates.Adapters.Refuter

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable (cap : ℕ)

/-! ## Parsing the guessed trace -/

/-- The displays guessed from position `p` (fuel `f`). -/
def gtrace (wD : List Bool) (t : ℕ) : ℕ → ℕ → List (Fin t → Bool)
  | 0, _ => []
  | f + 1, p => if gbit wD p then gdisp wD (p + 1) t :: gtrace wD t f (p + 1 + t) else []

/-- The position after the trace's final `0` marker. -/
def gend (wD : List Bool) (t : ℕ) : ℕ → ℕ → ℕ
  | 0, p => p + 1
  | f + 1, p => if gbit wD p then gend wD t f (p + 1 + t) else p + 1

theorem gbit_beyond (wD : List Bool) {p : ℕ} (h : wD.length ≤ p) : gbit wD p = false := by
  simp [gbit, List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem gend_ge (wD : List Bool) (t : ℕ) : ∀ f p, p < gend wD t f p
  | 0, p => by simp [gend]
  | f + 1, p => by
    simp only [gend]
    split
    · have := gend_ge wD t f (p + 1 + t); omega
    · omega

/-! ## Reading a marker -/

def readMarker : Pg := .seq (readG sWIT rBIT rWP) (.ifr rBIT (clr rBIT) (clr rCONT))

theorem readMarker_spec (σ : St) (wD : List Bool) (p : ℕ) (hst : σ.st sWIT = RepairOrdinary.frame wD)
    (hsh : σ.sh sWIT = 2 * min p wD.length) (hBIT : σ.val rBIT = 0) (hCONT : σ.val rCONT = 1)
    (hcap : σ.val rWP + 8 ≤ cap) :
    WXExec cap readMarker σ
      (((σ.setv rWP (σ.val rWP + witMoves wD p (p + 1))).seth sWIT (2 * min (p + 1) wD.length)).setv rCONT
        (if gbit wD p then 1 else 0)) 23 := by
  have e1 := readG_spec cap (W := sWIT) (B := rBIT) (WP := rWP) (by decide) σ wD p hst hsh (by lomega)
    (by lomega)
  cases hg : gbit wD p
  · have e2 := clr_spec cap rCONT (((σ.setv rBIT (σ.val rBIT + (false).toNat)).setv rWP
      (σ.val rWP + 2 * (min (p + 1) wD.length - min p wD.length))).seth sWIT (2 * min (p + 1) wD.length))
      (by simp [Function.update_apply, hCONT] <;> lomega)
    rw [hg] at e1
    refine (WXExec.seq e1 (WXExec.ifrF (by simp [Function.update_apply, hBIT]) e2)).cast cap ?_
      (by simp [Function.update_apply, hCONT])
    simp only [witMoves]
    wst
  · rw [hg] at e1
    have e2 := clr_spec cap rBIT (((σ.setv rBIT (σ.val rBIT + (true).toNat)).setv rWP
      (σ.val rWP + 2 * (min (p + 1) wD.length - min p wD.length))).seth sWIT (2 * min (p + 1) wD.length))
      (by simp [Function.update_apply, hBIT] <;> lomega)
    refine (WXExec.seq e1 (WXExec.ifrT (by simp [Function.update_apply, hBIT]) e2)).cast cap ?_
      (by simp [Function.update_apply, hBIT])
    simp only [witMoves]
    wst

/-! ## The loop -/

def passLoop : Pg := .whr rCONT (.seq readMarker (.ifr rCONT stepBody WMX.skip))

abbrev loopR : List (Fin NR) := [rOK, rQ, rH, rWP, rMK, rOFF, rQN, rW0, rW1, rM0, rM1, rCONT, rBIT]

/-- A pass state survives changes of the witness head, `WP` and `CONT`. -/
theorem PassEnc.frame {v : RepairOrdinary.Verifier} {r : ℕ} {i : Fin v.tapeCount} {wD : List Bool}
    {σ τ : St} {st : PassSt v.stateCount} (h : PassEnc v r i wD σ st)
    (hs : SameExcept σ τ [sWIT] [rWP, rCONT]) (hw : τ.st sWIT = σ.st sWIT) : PassEnc v r i wD τ st := by
  have fs : ∀ x, x ∉ [sWIT] → τ.st x = σ.st x := fun x hx => (hs.1 x hx).1
  have fsh : ∀ x, x ∉ [sWIT] → τ.sh x = σ.sh x := fun x hx => (hs.1 x hx).2
  have fv : ∀ x, x ∉ [rWP, rCONT] → τ.val x = σ.val x := fun x hx => hs.2.1 x hx
  exact {
    code := (by rw [fs _ (by decide)]; exact h.code),
    codeh := (by rw [fsh _ (by decide)]; exact h.codeh),
    t := (by rw [fv _ (by decide)]; exact h.t),
    wd := (by rw [fv _ (by decide)]; exact h.wd),
    ew := (by rw [fv _ (by decide)]; exact h.ew),
    hb := (by rw [fv _ (by decide)]; exact h.hb),
    tbl := (by rw [fv _ (by decide)]; exact h.tbl),
    bs := (by rw [fv _ (by decide)]; exact h.bs),
    ii := (by rw [fv _ (by decide)]; exact h.ii),
    ok := (by rw [fv _ (by decide)]; exact h.ok),
    q := (by rw [fv _ (by decide)]; exact h.q),
    h := (by rw [fv _ (by decide)]; exact h.h),
    sim := (by rw [fs _ (by decide)]; exact h.sim),
    simh := (by rw [fsh _ (by decide)]; exact h.simh),
    rs := (by rw [fs _ (by decide)]; exact h.rs),
    rsh := (by rw [fsh _ (by decide)]; exact h.rsh),
    wit := (by rw [hw]; exact h.wit),
    disph := (by rw [fsh _ (by decide)]; exact h.disph),
    zQN := (by rw [fv _ (by decide)]; exact h.zQN),
    zMK := (by rw [fv _ (by decide)]; exact h.zMK),
    zP := (by rw [fv _ (by decide)]; exact h.zP),
    zOFF := (by rw [fv _ (by decide)]; exact h.zOFF),
    zBIT := (by rw [fv _ (by decide)]; exact h.zBIT),
    zTA := (by rw [fv _ (by decide)]; exact h.zTA),
    zTB := (by rw [fv _ (by decide)]; exact h.zTB),
    zTC := (by rw [fv _ (by decide)]; exact h.zTC),
    zPT := (by rw [fv _ (by decide)]; exact h.zPT),
    zW0 := (by rw [fv _ (by decide)]; exact h.zW0),
    zW1 := (by rw [fv _ (by decide)]; exact h.zW1),
    zM0 := (by rw [fv _ (by decide)]; exact h.zM0),
    zM1 := (by rw [fv _ (by decide)]; exact h.zM1),
    zDI := (by rw [fv _ (by decide)]; exact h.zDI),
    zA2 := (by rw [fv _ (by decide)]; exact h.zA2) }

theorem passStep_head_le {t s : ℕ} (m : Machine t s) (r : ℕ) (i : Fin t) (st : PassSt s)
    (d : Fin t → Bool) : (passStep m r i st d).head ≤ st.head + 1 :=
  HeadMove.apply_le _ _

/-- **The pass loop** (fuel `f` with `|wD| < p + f`, so the trace ends within the fuel). -/
theorem passLoop_spec (v : RepairOrdinary.Verifier) (r : ℕ) (i : Fin v.tapeCount) (wD : List Bool)
    (p0 : ℕ) (hcap : 64 * ((VerifierEncoding.code v).length + 4 * wD.length + 8) ≤ cap) :
    ∀ (f p : ℕ) (σ : St) (st : PassSt v.stateCount), PassEnc v r i wD σ st → σ.val rCONT = 1 →
      σ.sh sWIT = 2 * min p wD.length → σ.val rWP = witMoves wD p0 p → p0 ≤ p →
      st.head ≤ min p wD.length - min p0 wD.length → wD.length < p + f →
      ∃ τ, WXExec cap passLoop σ τ ((gtrace wD v.tapeCount f p).length * (stepCost v + 40) + 40) ∧
        PassEnc v r i wD τ (passRun v.machine r i st (gtrace wD v.tapeCount f p)) ∧
        τ.val rCONT = 0 ∧ τ.sh sWIT = 2 * min (gend wD v.tapeCount f p) wD.length ∧
        τ.val rWP = witMoves wD p0 (gend wD v.tapeCount f p) ∧ SameExcept σ τ stepS loopR := by
  intro f
  induction f with
  | zero =>
    intro p σ st hE hC hsh hWP hp0 hhd hL
    have hwm : witMoves wD p0 p ≤ 2 * wD.length := by unfold witMoves; omega
    have e1 := readMarker_spec cap σ wD p hE.wit hsh hE.zBIT hC (by lomega)
    have hg : gbit wD p = false := gbit_beyond wD (by omega)
    rw [hg] at e1
    set σ1 := ((σ.setv rWP (σ.val rWP + witMoves wD p (p + 1))).seth sWIT
      (2 * min (p + 1) wD.length)).setv rCONT (if false = true then 1 else 0) with hσ1
    have h1 : σ1.val rCONT = 0 := by simp [σ1]
    have e2 : WXExec cap (.ifr rCONT stepBody WMX.skip) σ1 σ1 1 :=
      WXExec.ifrF h1 (WXExec.skip cap σ1)
    have e3 : WXExec cap passLoop σ1 σ1 1 := WXExec.whrF h1
    refine ⟨σ1, (WXExec.whrT (by rw [hC]; omega) (WXExec.seq e1 e2) e3).mono (by simp [gtrace]), ?_,
      h1, by simp [σ1, gend], ?_, ?_⟩
    · exact hE.frame (by simp only [σ1]; peel) (by simp [σ1])
    · simp only [σ1, gend]
      simp [Function.update_apply, hWP]
      exact witMoves_add wD hp0 (Nat.le_succ p)
    · simp only [σ1]; peel
  | succ f ih =>
    intro p σ st hE hC hsh hWP hp0 hhd hL
    have hwm : witMoves wD p0 p ≤ 2 * wD.length := by unfold witMoves; omega
    have e1 := readMarker_spec cap σ wD p hE.wit hsh hE.zBIT hC (by lomega)
    cases hg : gbit wD p
    · rw [hg] at e1
      set σ1 := ((σ.setv rWP (σ.val rWP + witMoves wD p (p + 1))).seth sWIT
        (2 * min (p + 1) wD.length)).setv rCONT (if false = true then 1 else 0) with hσ1
      have h1 : σ1.val rCONT = 0 := by simp [σ1]
      have e2 : WXExec cap (.ifr rCONT stepBody WMX.skip) σ1 σ1 1 :=
        WXExec.ifrF h1 (WXExec.skip cap σ1)
      have e3 : WXExec cap passLoop σ1 σ1 1 := WXExec.whrF h1
      refine ⟨σ1, (WXExec.whrT (by rw [hC]; omega) (WXExec.seq e1 e2) e3).mono (by simp [gtrace, hg]),
        ?_, h1, by simp [σ1, gend, hg], ?_, ?_⟩
      · simp only [gtrace, hg]
        exact hE.frame (by simp only [σ1]; peel) (by simp [σ1])
      · simp only [σ1, gend, hg]
        simp [Function.update_apply, hWP]
        exact witMoves_add wD hp0 (Nat.le_succ p)
      · simp only [σ1]; peel
    · rw [hg] at e1
      have hpL : p < wD.length := by
        by_contra hc; rw [gbit_beyond wD (by omega)] at hg; exact absurd hg (by decide)
      set σ1 := ((σ.setv rWP (σ.val rWP + witMoves wD p (p + 1))).seth sWIT
        (2 * min (p + 1) wD.length)).setv rCONT (if true = true then 1 else 0) with hσ1
      have h1 : σ1.val rCONT = 1 := by simp [σ1]
      have hE1 : PassEnc v r i wD σ1 st := hE.frame (by simp only [σ1]; peel) (by simp [σ1])
      have hwm1 : witMoves wD p0 (p + 1) ≤ 2 * wD.length := by unfold witMoves; omega
      obtain ⟨σ2, e2, hE2, hw2, hwp2, hf2⟩ := stepBody_spec cap v r i wD σ1 st (p + 1) hE1 (by simp [σ1])
        (by
          have : σ1.val rWP = witMoves wD p0 (p + 1) := by
            simp [σ1, Function.update_apply, hWP]; exact witMoves_add wD hp0 (Nat.le_succ p)
          rw [this]; omega)
      have hwp1 : σ1.val rWP = witMoves wD p0 (p + 1) := by
        simp [σ1, Function.update_apply, hWP]; exact witMoves_add wD hp0 (Nat.le_succ p)
      have hc2 : σ2.val rCONT = 1 := by rw [hf2.2.1 rCONT (by decide)]; exact h1
      obtain ⟨τ, e3, hE3, hc3, hw3, hwp3, hf3⟩ := ih (p + 1 + v.tapeCount) σ2 _ hE2 hc2 hw2
        (by rw [hwp2, hwp1]; exact witMoves_add wD (by omega) (by omega)) (by omega)
        (by
          have := passStep_head_le v.machine r i st (gdisp wD (p + 1) v.tapeCount)
          have : min p wD.length + 1 ≤ min (p + 1 + v.tapeCount) wD.length := by omega
          omega)
        (by omega)
      refine ⟨τ, (WXExec.whrT (by rw [hC]; omega) (WXExec.seq e1 (WXExec.ifrT (by rw [h1]; omega) e2))
        e3).mono ?_, ?_, hc3, ?_, ?_, ?_⟩
      · simp only [gtrace, hg, if_true, List.length_cons]
        ring_nf; omega
      · simp only [gtrace, hg, if_true]
        exact hE3
      · simp only [gend, hg, if_true]; exact hw3
      · simp only [gend, hg, if_true]; exact hwp3
      · have hs1 : SameExcept σ σ1 stepS loopR := by simp only [σ1]; peel
        exact (hs1.trans (hf2.weaken (by decide) (by decide))).trans hf3

end NearCubicGates.Adapters.Refuter.Mach
