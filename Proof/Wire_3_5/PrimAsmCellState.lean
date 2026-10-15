import Proof.Wire_3_5.PrimAsmUnitReady
import Proof.Wire_3_5.PrimAsmHashFlat

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.CellState
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.WireExponent3_5.PrimAsm.UnitReady NearCubicWires.WireExponent3_5.PrimAsm.FiltPipe
open NearCubicWires.WireExponent3_5.PrimT.WalkBank NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5.PrimAsm.PopPipe NearCubicWires.WireExponent3_5.Stars

/-- The request unit's registers: entry `QE`, printed row `QR`, target `QS`. -/
def QE : Fin LNR := ⟨300, by decide⟩
def QR : Fin LNR := ⟨301, by decide⟩
def QS : Fin LNR := ⟨302, by decide⟩

/-- **The blank cell state of unit `j`**. -/
def blankCell (x : ℕ) (w out : List Bool) (j : ℕ) : WState (LNS x) LNR :=
  ⟨fun i => if i = sk x 1 then out.length else 0,
    fun i => if i = sk x 0 then frame w else if i = sk x 1 then out ++ [false] else
      if i = sk x 2 then List.replicate j true else [],
    fun _ => 0, false⟩

/-- **The entry of a request unit**: `blankCell` with its entry, row and target in `QE`, `QR`, `QS`. -/
def reqCell (x : ℕ) (w out : List Bool) (j e r s : ℕ) : WState (LNS x) LNR :=
  (((blankCell x w out j).setv QE e).setv QR r).setv QS s

theorem blankCell_st0 (x : ℕ) (w out : List Bool) (j : ℕ) : (blankCell x w out j).st (sk x 0) = frame w := by
  simp [blankCell]

theorem blankCell_st1 (x : ℕ) (w out : List Bool) (j : ℕ) : (blankCell x w out j).st (sk x 1) = out ++ [false] := by
  simp [blankCell, sk_ne (x := x) 1 0 (by decide)]

theorem blankCell_st2 (x : ℕ) (w out : List Bool) (j : ℕ) :
    (blankCell x w out j).st (sk x 2) = List.replicate j true := by
  simp [blankCell, sk_ne (x := x) 2 0 (by decide), sk_ne (x := x) 2 1 (by decide)]

theorem blankCell_sh1 (x : ℕ) (w out : List Bool) (j : ℕ) : (blankCell x w out j).sh (sk x 1) = out.length := by
  simp [blankCell]

section Hash
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.PrimAsm.WriterIface NearCubicWires.WireExponent3_5.PrimAsm.HashFlat
open NearCubicWires.WireExponent3_5.PrimAsm.Records
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E}

def HashReqSpec (W : WalkBankProducer) (prog : WM (LNS W.x) LNR) (cap bound : ℕ)
    (alg : RepairRepresentation.DecompositionAlgorithm) (I : PrimitiveInputs B) {n : ℕ} (hs : I.StarAt n) {a : ℕ}
    (Cs : Fin a → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n)) (w : List Bool) : Prop :=
  ∀ e < nHash alg I hs Cs carriers, ∀ out : List Bool, ∃ τ m,
    WExec cap prog (reqCell W.x w out (5 * e + 2) e 0 0) τ m ∧ m ≤ bound ∧
    τ.st (sk W.x 0) = frame w ∧ τ.sh (sk W.x 0) = 0 ∧
    τ.st (sk W.x 2) = List.replicate (5 * e + 2) true ∧ τ.sh (sk W.x 2) = 0 ∧
    τ.st (sk W.x 150) = [] ∧ τ.sh (sk W.x 150) = 0 ∧ τ.st (sk W.x 151) = [true] ∧ τ.sh (sk W.x 151) = 0 ∧
    ∃ (Mlab RW LW : ℕ) (sample : SupplierWalk.MargulisWalkSample
        (2 ^ (FinalPass.Filt.wOf (auxP alg I hs Cs carriers).fieldBits (auxP alg I hs Cs carriers).labelBits * 128))
        (2 * ((auxP alg I hs Cs carriers).errExp / 4) + 1)),
      FiltReady cap W τ out (auxP alg I hs Cs carriers)
        (auxEnum alg I hs Cs carriers (e % nE alg I hs Cs carriers)) (2 * (carriers.map List.length).sum)
        (4 * (e / nE alg I hs Cs carriers)) (thrPool (I.starParams n hs) Cs carriers).length 0 Mlab RW LW sample ∧
      filtPipeBound (auxP alg I hs Cs carriers) (auxEnum alg I hs Cs carriers (e % nE alg I hs Cs carriers))
        (2 * (carriers.map List.length).sum) (4 * (e / nE alg I hs Cs carriers))
        (thrPool (I.starParams n hs) Cs carriers).length 0 RW LW ≤ bound

end Hash

end NearCubicWires.WireExponent3_5.PrimAsm.CellState
