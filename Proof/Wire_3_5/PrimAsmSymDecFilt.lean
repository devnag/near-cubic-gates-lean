import Proof.Wire_3_5.UnionMachineFiltSetupIface5
import Proof.Wire_3_5.PrimAsmCellUnit

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.SymDecFilt
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.WireExponent3_5.PrimAsm.UnitReady NearCubicWires.WireExponent3_5.PrimAsm.FiltPipe
open NearCubicWires.WireExponent3_5.PrimAsm.FiltRec NearCubicWires.WireExponent3_5.PrimT.WalkBank
open NearCubicWires.WireExponent3_5.PrimAsm.CellState NearCubicWires.WireExponent3_5.PrimAsm.Emit
open NearCubicWires.WireExponent3_5.PrimAsm.CellUnit NearCubicWires.WireExponent3_5.PrimAsm.FiltSetup
open NearCubicWires.WireExponent3_5.ListMachine.Row NearCubicWires.WireExponent3_5.FinalPass.Filt

theorem filt_dock (W : WalkBankProducer) (F : FiltSetupSpec5 W) (cap : ℕ) (P : GapParams) (e : GapSeed P)
    (L r4 G off : ℕ) (w out u : List Bool) (j : ℕ) (σ : WState (LNS W.x) LNR) (hU : 1 ≤ P.cap)
    (hlab : (sliceLabs r4 G off L).length = 4 * L)
    (hneed : F.need P.len P.cap P.errExp L r4 G off (Fintype.card (GapSeed P)) ≤ cap)
    (hσ : FsIn2 W.x σ w out j u P.len P.cap P.errExp (Enum.gapSeedEquiv P e) r4 G off L) :
    ∃ τ m, WExec cap F.prog σ τ m ∧ m ≤ F.bound cap ∧
      DecOK cap W τ out ((filtRefC (filterTable P e L) (SupplierWalk.majorityThreshold P.walkLen) L true
        (sliceLabs r4 G off L)).flatMap (fun t => true :: ListMachine.Rec.termWord t))
        (filtPipeBound P e L r4 G off (rulerW P) (rulerW P)) ∧
      τ.st (sk W.x 0) = frame w ∧ τ.st (sk W.x 2) = List.replicate j true ∧ τ.sh (sk W.x 2) = 0 := by
  obtain ⟨τ, m, hx, hm, h0, -, h2, h2h, f150, f150h, f151, f151h, Mlab, RW, LW, sample, hRW, hLW, hR⟩ :=
    F.run cap P (Enum.gapSeedEquiv P e) (Enum.gapSeedEquiv P e).isLt L r4 G off w out u j σ hU hlab hneed hσ
  have he : (Enum.gapSeedEquiv P).symm ⟨(Enum.gapSeedEquiv P e : ℕ), (Enum.gapSeedEquiv P e).isLt⟩ = e := by simp
  rw [he] at hR
  subst hRW hLW
  exact ⟨τ, m, hx, hm, Or.inr (Or.inr ⟨f150, f150h, f151, f151h, P, e, L, r4, G, off, Mlab, _, _, sample, hR, rfl,
    le_rfl⟩), h0, h2, h2h⟩

end NearCubicWires.WireExponent3_5.PrimAsm.SymDecFilt
