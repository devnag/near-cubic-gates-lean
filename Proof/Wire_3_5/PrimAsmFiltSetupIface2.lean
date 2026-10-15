import Proof.Wire_3_5.PrimAsmFiltSetupIface

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

/-- **The FILTER setup's entry bank, v2**: `FsIn` with the request's head at `0`. -/
structure FsIn2 (x : ℕ) (σ : WState (LNS x) LNR) (w out : List Bool) (j : ℕ) (u : List Bool)
    (len cap err g r4 G off L : ℕ) : Prop extends FsIn x σ w out j u len cap err g r4 G off L where
  h0 : σ.sh (sk x 0) = 0

/-- **The FILTER-setup machine, v2**: `FiltSetupSpec` from `FsIn2`, the request's head back at `0`. -/
structure FiltSetupSpec2 (W : WalkBankProducer) where
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
    FsIn2 W.x σ w out j u P.len P.cap P.errExp g r4 G off L →
    ∃ τ m, WExec cap prog σ τ m ∧ m ≤ bound P.len P.cap P.errExp L r4 G off ∧
      τ.st (sk W.x 0) = frame w ∧ τ.sh (sk W.x 0) = 0 ∧ τ.st (sk W.x 2) = List.replicate j true ∧
      τ.sh (sk W.x 2) = 0 ∧
      τ.st (sk W.x 150) = [] ∧ τ.sh (sk W.x 150) = 0 ∧ τ.st (sk W.x 151) = [true] ∧ τ.sh (sk W.x 151) = 0 ∧
      ∃ (Mlab RW LW : ℕ) (sample : SupplierWalk.MargulisWalkSample
          (2 ^ (FinalPass.Filt.wOf P.fieldBits P.labelBits * 128)) (2 * (P.errExp / 4) + 1)),
        FiltReady cap W τ out P ((Enum.gapSeedEquiv P).symm ⟨g, hg⟩) L r4 G off Mlab RW LW sample ∧
        filtPipeBound P ((Enum.gapSeedEquiv P).symm ⟨g, hg⟩) L r4 G off RW LW ≤ bound P.len P.cap P.errExp L r4 G off

/-- **The twin, v2**: `fsBank` meets `FsIn2`. -/
theorem fsIn2_fsBank (x : ℕ) (w out : List Bool) (j : ℕ) (u : List Bool) (len cap err g r4 G off L : ℕ) :
    FsIn2 x (fsBank x w out j u len cap err g r4 G off L) w out j u len cap err g r4 G off L :=
  { fsIn_fsBank x w out j u len cap err g r4 G off L with
    h0 := by
      have h01 : sk x 0 ≠ sk x 1 := sk_ne (x := x) 0 1 (by decide)
      simp [fsBank, blankCell, h01] }

end NearCubicWires.WireExponent3_5.PrimAsm.FiltSetup
