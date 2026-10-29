import SourceAdapters.RAMACSP.GenItemsWFB

/-!
# The printer of the machine-items stream

Paper: `lem:generator`. The main machine-item program emits every catalog
template at its active bit indices, as normalized guard and equation tokens.

`mainP V`: the eight blocks in the order of `machineItems`. `machineItems_blocks`: `machineItems` is the
concatenation of the blocks' item lists; `den_mainP`: under `Base`, `Room` and the coordinate array, the printer
prints exactly `machineNums` (the numbers of the seam's `machineItemsWord`).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

noncomputable section

namespace NearCubicGates.Adapters.RAMACSP.Gen.Items

open NearCubicGates.Adapters NearCubicGates.Adapters.RAMACSP NearCubicGates.Adapters.ACSP
open NearCubicGates.Adapters.ShortPCP NearCubicGates.Adapters.ShortPCP.Machines NearCubicGates.Adapters.ShortPCP.Machines.FL
open NearCubicGates.Adapters.RAMTrace NearCubicGates.Adapters.Joins
open NearCubicWires NearCubicWires.RepairOrdinary
open Polynomial

variable {G : Glob} (V : Verifier) (irrPoly : ℕ → (ZMod 2)[X])

/-- **The printer of the machine-items stream.** -/
def mainP : P := seqL [tBlockP V, tbBlockP V, cpBlockP V, b3P V, sBlockP, sbBlockP, b4P, b5P]

theorem WF_mainP : WF baseA (mainP V) := by
  apply WF_seqL
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact WF_tBlock V
  · exact WF_tbBlock V
  · exact WF_cpBlock V
  · exact WF_b3 V
  · exact WF_sBlock
  · exact WF_sbBlock
  · exact WF_b4
  · exact WF_b5

theorem Ok_mainP : Ok 0 (mainP V) := by
  apply Ok_seqL
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Ok_tBlock V
  · exact Ok_tbBlock V
  · exact Ok_cpBlock V
  · exact Ok_b3 V
  · exact Ok_sBlock
  · exact Ok_sbBlock
  · exact Ok_b4
  · exact Ok_b5

/-- **`machineItems` is the concatenation of the blocks' items.** -/
theorem machineItems_blocks {F : Type} [Field F] [CharP F 2] (r : ClockRequest) (lam : ℕ → Routing.Expr F) :
    machineItems (ownLayout V r.2) (wordExp V r.2) (regCount V) (codeLen V) (ownRam V r) RAMTrace.mnKind
      (tau V r.2) (inRecExp V r) lam =
    (timeEqList (dims (ownRam V r) (tau V r.2))).map (tItem V r) ++
    (timeSlotList (dims (ownRam V r) (tau V r.2))).map (tbItem V r) ++
    (copyList (dims (ownRam V r) (tau V r.2))).flatMap
      (fun cp => copyItems (ownLayout V r.2) (wordExp V r.2) (tau V r.2) (dstCell (regCount V) (codeLen V) cp)) ++
    b3Items V r ++
    (sortEqList (dims (ownRam V r) (tau V r.2))).map (sItem V r) ++
    (sortSlotList (dims (ownRam V r) (tau V r.2))).map (sbItem V r) ++
    (prevSlots (wordW V r.2) (tau V r.2)).flatMap
      (fun sl => sCopyItems (ownLayout V r.2) (wordExp V r.2) (2 * (ownLayout V r.2).k - 1) sl.1 sl.2) ++
    (recSlotList (dims (ownRam V r) (tau V r.2))).flatMap
      (inItems (ownLayout V r.2) (wordExp V r.2) (tau V r.2) (inRecExp V r) lam) := by
  unfold machineItems
  refine congrArg₂ (· ++ ·) (congrArg₂ (· ++ ·) (congrArg₂ (· ++ ·) (congrArg₂ (· ++ ·) (congrArg₂ (· ++ ·)
    (congrArg₂ (· ++ ·) (congrArg₂ (· ++ ·) ?_ ?_) ?_) ?_) ?_) ?_) ?_) ?_
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · have e1 : (dims (ownRam V r) (tau V r.2)).w = wordW V r.2 := dims_w V r
    have e2 : (dims (ownRam V r) (tau V r.2)).τ = tau V r.2 := dims_tau V r
    rw [e1, e2]
    apply List.flatMap_congr
    intro sl _
    rfl
  · rfl

/-- **The printer prints the item numbers of `machineItems`** (for any field, masks with `0 ↦ 0`, `1 ↦ 1`, and rows
`lam` whose (B5) block is printed). -/
theorem den_mainP_gen {F : Type} [Field F] [CharP F 2] (mk : F → ℕ) (hm0 : mk 0 = 0) (hm1 : mk 1 = 1)
    (r : ClockRequest) (hR : Room V r G) {s : FS} (hb : Base V r s) (lam : ℕ → Routing.Expr F)
    (h5 : den G s b5P = (recSlotList (dims (ownRam V r) (tau V r.2))).flatMap (fun sl =>
      (inItems (ownLayout V r.2) (wordExp V r.2) (tau V r.2) (inRecExp V r) lam sl).flatMap (itemNums mk))) :
    den G s (mainP V) = (machineItems (ownLayout V r.2) (wordExp V r.2) (regCount V) (codeLen V) (ownRam V r)
      RAMTrace.mnKind (tau V r.2) (inRecExp V r) lam).flatMap (itemNums mk) := by
  rw [machineItems_blocks]
  simp only [mainP, den_seqL, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.flatMap_append,
    List.flatMap_map, List.flatMap_assoc, List.append_assoc]
  rw [den_tBlock V mk hm0 hm1 r hR hb, den_tbBlock V mk r hR hb, den_cpBlock V mk r hR hb, den_b3 V mk hm0 hm1 r hR hb,
    den_sBlock V mk hm0 hm1 r hR hb, den_sbBlock V mk r hR hb, den_b4 V mk hm0 hm1 r hR hb, h5]

end NearCubicGates.Adapters.RAMACSP.Gen.Items
