import SourceAdapters.Refuter.CheckerLoop

/-!
# Copying the prefix of a simulated tape (input 7, F01 machine layer, part 10)

proof of `lem:multitape-refuter`: "copies cells `0,…,r−1` of both prepared tapes, including genuine blank cells when
necessary … The contents and flags are copied, not guessed." For pass `i` the work tape receives
cells `0,…,r−1` of the simulated tape `i`: the framed input (`XS`), the framed witness (`YS`) or
blank (`Z`, an always-empty stream). `wcopy_agree`: the result agrees below `r` with the copied
prefix, which is all `passes_iff` needs. Cost `O(r)`, independent of the simulated machine.
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

/-- The work tape after copying cells `0, …, k-1` of `src` over `old`. -/
def wcopy (old src : List Bool) : ℕ → List Bool
  | 0 => old
  | k + 1 => writeTapeBit (wcopy old src k) k (readTapeBit src k)

theorem wcopy_read (old src : List Bool) : ∀ k j, j < k → readTapeBit (wcopy old src k) j = readTapeBit src j
  | 0, j, h => absurd h (Nat.not_lt_zero _)
  | k + 1, j, h => by
    simp only [wcopy]
    rw [readTapeBit_writeTapeBit]
    by_cases hj : j = k
    · subst hj; simp
    · rw [if_neg hj]; exact wcopy_read old src k j (by omega)

theorem wcopy_agree (old src : List Bool) (r : ℕ) : AgreeBelow r (wcopy old src r) (prefixTape r src) := by
  intro j hj
  rw [wcopy_read old src r j hj]
  exact (agreeBelow_prefixTape r src j hj).symm

def copyCell (SRC : Fin (NS + 1)) : Pg :=
  .seq (.ifs SRC (WMX.wr sSIM true) (WMX.wr sSIM false)) (.seq (WMX.fwd SRC) (WMX.fwd sSIM))

theorem copyCell_spec (SRC : Fin (NS + 1)) (hS : SRC ≠ sSIM) (σ : St) :
    WXExec cap (copyCell SRC) σ
      (((σ.sets sSIM (writeTapeBit (σ.st sSIM) (σ.sh sSIM) (readTapeBit (σ.st SRC) (σ.sh SRC)))).seth SRC
        (σ.sh SRC + 1)).seth sSIM (σ.sh sSIM + 1)) 6 := by
  have hS' := Ne.symm hS
  cases hb : readTapeBit (σ.st SRC) (σ.sh SRC)
  · have e1 : WXExec cap (.ifs SRC (WMX.wr sSIM true) (WMX.wr sSIM false)) σ
        (σ.sets sSIM (writeTapeBit (σ.st sSIM) (σ.sh sSIM) false)) 2 :=
      WXExec.ifsF (by simp [wbit, hb]) (WXExec.wr cap sSIM false σ)
    have e2 := WXExec.fwd cap SRC (σ.sets sSIM (writeTapeBit (σ.st sSIM) (σ.sh sSIM) false))
    have e3 := WXExec.fwd cap sSIM ((σ.sets sSIM (writeTapeBit (σ.st sSIM) (σ.sh sSIM) false)).seth SRC
      ((σ.sets sSIM (writeTapeBit (σ.st sSIM) (σ.sh sSIM) false)).sh SRC + 1))
    refine (WXExec.seq e1 (WXExec.seq e2 e3)).cast cap ?_ (by omega)
    wst
  · have e1 : WXExec cap (.ifs SRC (WMX.wr sSIM true) (WMX.wr sSIM false)) σ
        (σ.sets sSIM (writeTapeBit (σ.st sSIM) (σ.sh sSIM) true)) 2 :=
      WXExec.ifsT (by simp [wbit, hb]) (WXExec.wr cap sSIM true σ)
    have e2 := WXExec.fwd cap SRC (σ.sets sSIM (writeTapeBit (σ.st sSIM) (σ.sh sSIM) true))
    have e3 := WXExec.fwd cap sSIM ((σ.sets sSIM (writeTapeBit (σ.st sSIM) (σ.sh sSIM) true)).seth SRC
      ((σ.sets sSIM (writeTapeBit (σ.st sSIM) (σ.sh sSIM) true)).sh SRC + 1))
    refine (WXExec.seq e1 (WXExec.seq e2 e3)).cast cap ?_ (by omega)
    wst

/-- Copy cells `0, …, R0-1` of `SRC` to the work tape; both heads return to `0`. -/
def copyFrom (SRC : Fin (NS + 1)) : Pg :=
  .seq (repK rR0 rTG (copyCell SRC)) (.seq (bwdK SRC rR0 rTB) (bwdK sSIM rR0 rTB))

theorem copyFrom_spec (SRC : Fin (NS + 1)) (hS : SRC ≠ sSIM) (σ : St) (hSh : σ.sh sSIM = 0)
    (hRh : σ.sh SRC = 0) (hTG : σ.val rTG = 0) (hTB : σ.val rTB = 0) (hcap : 2 * σ.val rR0 + 2 ≤ cap) :
    WXExec cap (copyFrom SRC) σ (σ.sets sSIM (wcopy (σ.st sSIM) (σ.st SRC) (σ.val rR0)))
      (σ.val rR0 * 21 + 32 * σ.val rR0 + 11) := by
  have hS' := Ne.symm hS
  let st : ℕ → St := fun k => ((σ.sets sSIM (wcopy (σ.st sSIM) (σ.st SRC) k)).seth SRC k).seth sSIM k
  have hst0 : st 0 = σ := by simp only [st, wcopy]; wst
  have hloop := Runs.repE (cap := cap) (K := rR0) (K2 := rTG) (body := copyCell SRC) (by decide) 6
    (σ.val rR0) st (by omega) (fun k => by simp [st]) (fun k => by simp [st])
    (fun k _ v1 v2 => by
      refine (copyCell_spec cap SRC hS _).cast cap ?_ le_rfl
      simp only [st, wcopy]
      wst)
    (by simp [st]) (by simp [st, hTG])
  rw [hst0] at hloop
  have e2 := bwdK_spec cap (S := SRC) (K := rR0) (K2 := rTB) (by decide) (st (σ.val rR0)) (by simp [st, hTB])
    (by simp [st, Function.update_apply, hS, hS']; lomega)
  have e3 := bwdK_spec cap (S := sSIM) (K := rR0) (K2 := rTB) (by decide)
    ((st (σ.val rR0)).seth SRC ((st (σ.val rR0)).sh SRC - (st (σ.val rR0)).val rR0))
    (by simp [st, hTB]) (by simp [st, Function.update_apply, hS, hS']; lomega)
  refine (WXExec.seq hloop (WXExec.seq e2 e3)).cast cap ?_
    (by simp [st, Function.update_apply, hS, hS']; ring_nf; lomega)
  simp only [st]
  wst

/-- Pass `i`'s copy: `XS` for tape `0`, `YS` for tape `1`, blank (`Z`) otherwise. -/
def copyPrefix : Pg :=
  .seq (addR rI rI1 rTA) (.seq (WMX.dec rI1)
    (.seq (.ifr rI (.ifr rI1 (copyFrom sZ) (copyFrom sYS)) (copyFrom sXS)) (clr rI1)))

/-- The source of pass `i`'s copy. -/
def srcOf (σ : St) (i : ℕ) : List Bool := if i = 0 then σ.st sXS else if i = 1 then σ.st sYS else σ.st sZ

theorem copyPrefix_spec (σ : St) (hSh : σ.sh sSIM = 0) (hX : σ.sh sXS = 0) (hY : σ.sh sYS = 0)
    (hZ : σ.sh sZ = 0) (hTG : σ.val rTG = 0) (hTB : σ.val rTB = 0) (hTA : σ.val rTA = 0)
    (hI1 : σ.val rI1 = 0) (hcap : 2 * (σ.val rR0 + σ.val rI) + 2 ≤ cap) :
    WXExec cap copyPrefix σ (σ.sets sSIM (wcopy (σ.st sSIM) (srcOf σ (σ.val rI)) (σ.val rR0)))
      (σ.val rR0 * 21 + 32 * σ.val rR0 + 25 * σ.val rI + 30) := by
  have e1 := addR_spec cap (A := rI) (B := rI1) (T := rTA) (by decide) (by decide) (by decide) σ hTA
    (by lomega)
  have e2 := WXExec.dec cap rI1 (σ.setv rI1 (σ.val rI1 + σ.val rI)) (by simp; lomega)
  set σ2 := (σ.setv rI1 (σ.val rI1 + σ.val rI)).setv rI1 ((σ.setv rI1 (σ.val rI1 + σ.val rI)).val rI1 - 1)
    with hσ2
  have hv : σ2.val rI1 = σ.val rI - 1 := by simp [σ2, hI1]
  by_cases h0 : σ.val rI = 0
  · have e3 := copyFrom_spec cap sXS (by decide) σ2 (by simp [σ2, hSh]) (by simp [σ2, hX])
      (by simp [σ2, Function.update_apply, hTG]) (by simp [σ2, Function.update_apply, hTB])
      (by simp [σ2, Function.update_apply]; lomega)
    have e4 := clr_spec cap rI1 (σ2.sets sSIM (wcopy (σ2.st sSIM) (σ2.st sXS) (σ2.val rR0)))
      (by simp [hv, h0])
    refine (WXExec.seq e1 (WXExec.seq e2 (WXExec.seq (WXExec.ifrF (by simp [σ2, Function.update_apply, h0])
      e3) e4))).cast cap ?_ (by simp [σ2, Function.update_apply, hI1, h0]; lomega)
    simp only [σ2, srcOf, h0, if_true]
    wst
  · by_cases h1 : σ.val rI = 1
    · have e3 := copyFrom_spec cap sYS (by decide) σ2 (by simp [σ2, hSh]) (by simp [σ2, hY])
        (by simp [σ2, Function.update_apply, hTG]) (by simp [σ2, Function.update_apply, hTB])
        (by simp [σ2, Function.update_apply]; lomega)
      have e4 := clr_spec cap rI1 (σ2.sets sSIM (wcopy (σ2.st sSIM) (σ2.st sYS) (σ2.val rR0)))
        (by simp [hv, h1])
      refine (WXExec.seq e1 (WXExec.seq e2 (WXExec.seq (WXExec.ifrT (by simp [σ2, Function.update_apply, h0])
        (WXExec.ifrF (by rw [hv, h1]) e3)) e4))).cast cap ?_
        (by simp [σ2, Function.update_apply, hI1, h1]; lomega)
      simp only [σ2, srcOf, h0, h1, if_true, if_false]
      wst
    · have e3 := copyFrom_spec cap sZ (by decide) σ2 (by simp [σ2, hSh]) (by simp [σ2, hZ])
        (by simp [σ2, Function.update_apply, hTG]) (by simp [σ2, Function.update_apply, hTB])
        (by simp [σ2, Function.update_apply]; lomega)
      have e4 := clr_spec cap rI1 (σ2.sets sSIM (wcopy (σ2.st sSIM) (σ2.st sZ) (σ2.val rR0)))
        (by simp [hv]; lomega)
      refine (WXExec.seq e1 (WXExec.seq e2 (WXExec.seq (WXExec.ifrT (by simp [σ2, Function.update_apply, h0])
        (WXExec.ifrT (by rw [hv]; omega) e3)) e4))).cast cap ?_
        (by simp [σ2, Function.update_apply, hI1]; lomega)
      simp only [σ2, srcOf, h0, h1, if_false]
      wst

end NearCubicGates.Adapters.Refuter.Mach
