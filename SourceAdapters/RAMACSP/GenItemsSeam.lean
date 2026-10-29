import SourceAdapters.RAMACSP.GenTermsDock

/-!
# Seam of the machine-items printer (the generator's stage G5, internal)

Paper: `def:event-trace`, `app:affine-embedding` and `lem:generator`.
The emitted item stream contains the machine catalog in order: time and
sorted equations, Booleanity, copies, and boundary equations (B1)–(B5).

- `machineItemsWord V irrPoly r`: the item words (`Joins.itemWord`, constants as reduced masks `Joins.termsMask`, reads
  raw) of `machineItems … (termsLam V irrPoly r h)` in catalog order, when `ModulusGood V irrPoly r` (else empty);
- `MachineItemsWF V irrPoly`: an ordinary machine printing `frame (machineItemsWord V irrPoly r)` on `ClockRequest.word r`
  within `K·(n + natBitLength t + 1)^e`.
-/

set_option autoImplicit false

noncomputable section

namespace NearCubicGates.Adapters.RAMACSP.Gen

open NearCubicGates.Adapters NearCubicGates.Adapters.RAMACSP NearCubicGates.Adapters.ACSP NearCubicWires
open NearCubicWires.RepairOrdinary
open NearCubicGates.Adapters.ShortPCP NearCubicGates.Adapters.Joins
open Polynomial

variable (V : Verifier) (irrPoly : ℕ → (ZMod 2)[X])

attribute [local irreducible] ownLayout baseIrr in
open Classical in
/-- The item words of the machine catalog at the clock request `r` (the `machineItems` part of `ownItems`). -/
def machineItemsWord (r : ClockRequest) : List Bool :=
  if h : ModulusGood V irrPoly r then
    haveI : Fact (Irreducible (baseIrr V irrPoly r)) := ⟨h.1⟩
    (machineItems (ownLayout V r.2) (wordExp V r.2) (regCount V) (codeLen V) (ownRam V r) RAMTrace.mnKind
      (tau V r.2) (inRecExp V r) (termsLam V irrPoly r h)).flatMap
      (Joins.itemWord (Joins.termsMask (termsRequest V irrPoly r h) (termsRequest_ok V irrPoly r h)))
  else []

/-- **The sub-seam**: an ordinary machine printing the machine catalog's item words (framed) on the request word,
within a polynomial budget (the shape of `ConsWF`). -/
def MachineItemsWF : Prop :=
  ∃ K e : ℕ, Nonempty (WordFunction ClockRequest ClockRequest.word
    (fun r => RepairSource.frame (machineItemsWord V irrPoly r))
    (fun r => K * (r.1.1 + natBitLength r.2 + 1) ^ e))

end NearCubicGates.Adapters.RAMACSP.Gen
