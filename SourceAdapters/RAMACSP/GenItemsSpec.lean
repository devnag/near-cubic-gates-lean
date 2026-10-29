import SourceAdapters.RAMACSP.GenItemsBase
import SourceAdapters.RAMACSP.GenItemsSeam
import SourceAdapters.RAMACSP.GenCoordDock

/-!
# The numbers of the machine-items word

Paper: `lem:generator`. The item program writes the literal catalog stream;
its encoded number lengths, loop bounds and ordinary running time are polynomially
bounded by the request size.

`machineNums V irrPoly r` is the list of numbers whose `natWord`s are the seam's `machineItemsWord`
(`machineItemsWord_eq`): the items of `machineItems` with the constants as reduced masks (`termsMask`). `CoordV`: the
coordinate array of the request (`Joins.coordWord` at `GenCoordDock.coordRequest`) held in the program variable `vD`
as a number (its bits least significant first).
-/

set_option autoImplicit false

noncomputable section

namespace NearCubicGates.Adapters.RAMACSP.Gen.Items

open NearCubicGates.Adapters NearCubicGates.Adapters.RAMACSP NearCubicGates.Adapters.ACSP
open NearCubicGates.Adapters.ShortPCP.Machines NearCubicGates.Adapters.ShortPCP.Machines.FL
open NearCubicGates.Adapters.Joins NearCubicGates.Adapters.ShortPCP
open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open Polynomial

variable (V : Verifier) (irrPoly : ℕ → (ZMod 2)[X])

attribute [local irreducible] ownLayout baseIrr in
open Classical in
/-- **The numbers of the machine-items word** (the items of `machineItems`, as in `Gen.machineItemsWord`). -/
def machineNums (r : ClockRequest) : List ℕ :=
  if h : ModulusGood V irrPoly r then
    haveI : Fact (Irreducible (baseIrr V irrPoly r)) := ⟨h.1⟩
    (machineItems (ownLayout V r.2) (wordExp V r.2) (regCount V) (codeLen V) (ownRam V r) RAMTrace.mnKind
      (tau V r.2) (inRecExp V r) (termsLam V irrPoly r h)).flatMap
      (itemNums (Joins.termsMask (termsRequest V irrPoly r h) (termsRequest_ok V irrPoly r h)))
  else []

theorem flatMap_itemWord {F : Type} (mk : F → ℕ) {m : ℕ} (xs : List (Routing.Pattern m × Routing.Expr F)) :
    xs.flatMap (Joins.itemWord mk) = (xs.flatMap (itemNums mk)).flatMap natWord := by
  rw [List.flatMap_assoc]
  exact List.flatMap_congr (fun x _ => itemWord_eq mk x)

attribute [local irreducible] ownLayout baseIrr in
open Classical in
theorem machineItemsWord_eq (r : ClockRequest) :
    machineItemsWord V irrPoly r = (machineNums V irrPoly r).flatMap natWord := by
  unfold machineItemsWord machineNums
  split_ifs with h
  · exact flatMap_itemWord _ _
  · rfl

/-- The coordinate array of the request in `vD`. -/
def CoordV (hI : NearCubicGates.Published.Shoup.IrreducibleChoice irrPoly) (r : ClockRequest) (s : FS) : Prop :=
  s.env vD = CanonicalBinary.bitsValue (Joins.coordWord (coordRequest V irrPoly r) (coordRequest_ok V irrPoly hI r))

end NearCubicGates.Adapters.RAMACSP.Gen.Items
