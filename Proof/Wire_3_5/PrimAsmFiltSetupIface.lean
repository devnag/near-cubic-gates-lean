import Proof.Wire_3_5.PrimAsmCellState
import Proof.Wire_3_5.PrimAsmEnum

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.PrimAsm.FiltSetup
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.WireExponent3_5.PrimAsm.UnitReady NearCubicWires.WireExponent3_5.PrimAsm.FiltPipe
open NearCubicWires.WireExponent3_5.PrimAsm.FiltRec NearCubicWires.WireExponent3_5.PrimT.WalkBank
open NearCubicWires.WireExponent3_5.PrimAsm.CellState NearCubicWires.WireExponent3_5.PrimAsm.Emit
open NearCubicWires.WireExponent3_5.PrimAsm.PopPipe (sk_ne)

/-! ## The input registers -/

def fsLen : Fin LNR := ⟨400, by decide⟩
def fsCap : Fin LNR := ⟨401, by decide⟩
def fsErr : Fin LNR := ⟨402, by decide⟩
def fsSeed : Fin LNR := ⟨403, by decide⟩
def fsR4 : Fin LNR := ⟨404, by decide⟩
def fsG : Fin LNR := ⟨405, by decide⟩
def fsOff : Fin LNR := ⟨406, by decide⟩
def fsL : Fin LNR := ⟨407, by decide⟩

/-- **The FILTER setup's entry bank** (the cell `w`, `out`, `j`, data `u`; the eight values). -/
structure FsIn (x : ℕ) (σ : WState (LNS x) LNR) (w out : List Bool) (j : ℕ) (u : List Bool)
    (len cap err g r4 G off L : ℕ) : Prop where
  s0 : σ.st (sk x 0) = frame w
  s1 : σ.st (sk x 1) = out ++ [false]
  h1 : σ.sh (sk x 1) = out.length
  s2 : σ.st (sk x 2) = List.replicate j true
  h2 : σ.sh (sk x 2) = 0
  s113 : σ.st (sk x 113) = u
  blank : ∀ k : Fin 161, k.val ≠ 0 → k.val ≠ 1 → k.val ≠ 2 → k.val ≠ 113 → σ.st (sk x k) = [] ∧ σ.sh (sk x k) = 0
  blankT : ∀ k : Fin x, σ.st (sT x k) = [] ∧ σ.sh (sT x k) = 0
  cell : σ.cell = false
  vLen : σ.val fsLen = len
  vCap : σ.val fsCap = cap
  vErr : σ.val fsErr = err
  vSeed : σ.val fsSeed = g
  vR4 : σ.val fsR4 = r4
  vG : σ.val fsG = G
  vOff : σ.val fsOff = off
  vL : σ.val fsL = L
  zLow : ∀ r : Fin LNR, r.val < 250 → σ.val r = 0
  zHigh : ∀ r : Fin LNR, 408 ≤ r.val → σ.val r = 0

structure FiltSetupSpec (W : WalkBankProducer) where
  prog : WM (LNS W.x) LNR
  need : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ
  bound : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ
  Cn : ℕ
  Dn : ℕ
  need_poly : ∀ len cap err L r4 G off : ℕ,
    ValidatorPolynomialDomination.PolyBounded (need len cap err L r4 G off) (len + cap + err + L + r4 + G + off) Cn Dn
  Cb : ℕ
  Db : ℕ
  bound_poly : ∀ len cap err L r4 G off : ℕ,
    ValidatorPolynomialDomination.PolyBounded (bound len cap err L r4 G off) (len + cap + err + L + r4 + G + off) Cb Db
  run : ∀ (cap : ℕ) (P : GapParams) (g : ℕ) (hg : g < Fintype.card (GapSeed P)) (L r4 G off : ℕ)
    (w out u : List Bool) (j : ℕ) (σ : WState (LNS W.x) LNR),
    1 ≤ P.cap → (sliceLabs r4 G off L).length = 4 * L → need P.len P.cap P.errExp L r4 G off ≤ cap →
    FsIn W.x σ w out j u P.len P.cap P.errExp g r4 G off L →
    ∃ τ m, WExec cap prog σ τ m ∧ m ≤ bound P.len P.cap P.errExp L r4 G off ∧
      τ.st (sk W.x 0) = frame w ∧ τ.st (sk W.x 2) = List.replicate j true ∧ τ.sh (sk W.x 2) = 0 ∧
      τ.st (sk W.x 150) = [] ∧ τ.sh (sk W.x 150) = 0 ∧ τ.st (sk W.x 151) = [true] ∧ τ.sh (sk W.x 151) = 0 ∧
      ∃ (Mlab RW LW : ℕ) (sample : SupplierWalk.MargulisWalkSample
          (2 ^ (FinalPass.Filt.wOf P.fieldBits P.labelBits * 128)) (2 * (P.errExp / 4) + 1)),
        FiltReady cap W τ out P ((Enum.gapSeedEquiv P).symm ⟨g, hg⟩) L r4 G off Mlab RW LW sample ∧
        filtPipeBound P ((Enum.gapSeedEquiv P).symm ⟨g, hg⟩) L r4 G off RW LW ≤ bound P.len P.cap P.errExp L r4 G off

/-! ## The twin: the callers' bank -/

def fsBank (x : ℕ) (w out : List Bool) (j : ℕ) (u : List Bool) (len cap err g r4 G off L : ℕ) :
    WState (LNS x) LNR :=
  ((((((((((blankCell x w out j).sets (sk x 113) u).setv fsLen len).setv fsCap cap).setv fsErr err).setv fsSeed g).setv
    fsR4 r4).setv fsG G).setv fsOff off).setv fsL L)

theorem fsBank_val_other (x : ℕ) (w out : List Bool) (j : ℕ) (u : List Bool) (len cap err g r4 G off L : ℕ)
    (r : Fin LNR) (h : r.val < 400 ∨ 408 ≤ r.val) : (fsBank x w out j u len cap err g r4 G off L).val r = 0 := by
  have e0 : r ≠ fsLen := fun e => by subst e; simp [fsLen] at h
  have e1 : r ≠ fsCap := fun e => by subst e; simp [fsCap] at h
  have e2 : r ≠ fsErr := fun e => by subst e; simp [fsErr] at h
  have e3 : r ≠ fsSeed := fun e => by subst e; simp [fsSeed] at h
  have e4 : r ≠ fsR4 := fun e => by subst e; simp [fsR4] at h
  have e5 : r ≠ fsG := fun e => by subst e; simp [fsG] at h
  have e6 : r ≠ fsOff := fun e => by subst e; simp [fsOff] at h
  have e7 : r ≠ fsL := fun e => by subst e; simp [fsL] at h
  simp [fsBank, blankCell, Function.update_of_ne e0, Function.update_of_ne e1, Function.update_of_ne e2,
    Function.update_of_ne e3, Function.update_of_ne e4, Function.update_of_ne e5, Function.update_of_ne e6,
    Function.update_of_ne e7]

/-- **The twin**: `fsBank` meets `FsIn`. -/
theorem fsIn_fsBank (x : ℕ) (w out : List Bool) (j : ℕ) (u : List Bool) (len cap err g r4 G off L : ℕ) :
    FsIn x (fsBank x w out j u len cap err g r4 G off L) w out j u len cap err g r4 G off L := by
  have h01 : sk x 1 ≠ sk x 0 := sk_ne (x := x) 1 0 (by decide)
  have h02 : sk x 2 ≠ sk x 0 := sk_ne (x := x) 2 0 (by decide)
  have h12 : sk x 2 ≠ sk x 1 := sk_ne (x := x) 2 1 (by decide)
  have h113a : sk x 0 ≠ sk x 113 := sk_ne (x := x) 0 113 (by decide)
  have h113b : sk x 1 ≠ sk x 113 := sk_ne (x := x) 1 113 (by decide)
  have h113c : sk x 2 ≠ sk x 113 := sk_ne (x := x) 2 113 (by decide)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [fsBank, blankCell, Function.update_of_ne h113a]
  · simp [fsBank, blankCell, Function.update_of_ne h113b, h01]
  · simp [fsBank, blankCell]
  · simp [fsBank, blankCell, Function.update_of_ne h113c, h02, h12]
  · simp [fsBank, blankCell, h02, h12]
  · simp [fsBank]
  · intro k k0 k1 k2 k113
    have n0 : sk x k ≠ sk x 0 := sk_ne (x := x) k 0 (fun e => k0 (congrArg Fin.val e))
    have n1 : sk x k ≠ sk x 1 := sk_ne (x := x) k 1 (fun e => k1 (congrArg Fin.val e))
    have n2 : sk x k ≠ sk x 2 := sk_ne (x := x) k 2 (fun e => k2 (congrArg Fin.val e))
    have n113 : sk x k ≠ sk x 113 := sk_ne (x := x) k 113 (fun e => k113 (congrArg Fin.val e))
    simp [fsBank, blankCell, Function.update_of_ne n113, n0, n1, n2]
  · intro k
    have n0 : sT x k ≠ sk x 0 := fun e => sk_ne_sT x 0 k e.symm
    have n1 : sT x k ≠ sk x 1 := fun e => sk_ne_sT x 1 k e.symm
    have n2 : sT x k ≠ sk x 2 := fun e => sk_ne_sT x 2 k e.symm
    have n113 : sT x k ≠ sk x 113 := fun e => sk_ne_sT x 113 k e.symm
    simp [fsBank, blankCell, Function.update_of_ne n113, n0, n1, n2]
  · simp [fsBank, Function.update_apply, fsLen, fsCap, fsErr, fsSeed, fsR4, fsG, fsOff, fsL]
  · simp [fsBank, Function.update_apply, fsLen, fsCap, fsErr, fsSeed, fsR4, fsG, fsOff, fsL]
  · simp [fsBank, Function.update_apply, fsLen, fsCap, fsErr, fsSeed, fsR4, fsG, fsOff, fsL]
  · simp [fsBank, Function.update_apply, fsLen, fsCap, fsErr, fsSeed, fsR4, fsG, fsOff, fsL]
  · simp [fsBank, Function.update_apply, fsLen, fsCap, fsErr, fsSeed, fsR4, fsG, fsOff, fsL]
  · simp [fsBank, Function.update_apply, fsLen, fsCap, fsErr, fsSeed, fsR4, fsG, fsOff, fsL]
  · simp [fsBank, Function.update_apply, fsLen, fsCap, fsErr, fsSeed, fsR4, fsG, fsOff, fsL]
  · simp [fsBank]
  · intro r hr
    exact fsBank_val_other x w out j u len cap err g r4 G off L r (Or.inl (by omega))
  · intro r hr
    exact fsBank_val_other x w out j u len cap err g r4 G off L r (Or.inr hr)

end NearCubicWires.WireExponent3_5.PrimAsm.FiltSetup
