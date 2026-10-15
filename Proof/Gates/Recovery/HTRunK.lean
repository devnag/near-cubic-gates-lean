import Proof.Gates.Recovery.HTRunC
import Proof.Gates.Setup.CompSpec

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicGates.Close.Recovery.HT

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.CheckedPCPP NearCubicGates.Close.Gadget
open NearCubicGates.PublishedSources.PCPP NearCubicWires.SourceInterfaces NearCubicWires.RepairSource
open NearCubicGates.Close

theorem compMap_other (tK tE tH : ℕ) (hIn dIn j : Fin tK) (h1 : j ≠ hIn) (h2 : j ≠ dIn) :
    compMap tK tE tH hIn dIn j = bK tK tE tH j := by simp [compMap, h1, h2]

/-- **Phase K.** -/
theorem comp_exec {s : GateSources} {P : ThreeQueryPCPP} {g : Transfer.GateParams}
    (cx : Setup.CompFull s P g) (tE tH cap : ℕ) {N : ℕ} (x : BitInput N)
    (B : Outer.OuterGuess (Outer.width s.mw (g.sv s) N)) (hq : 2 ≤ Outer.width s.mw (g.sv s) N)
    (σ : WState (NS cx.t tE tH) 64)
    (hP0 : σ.st (P0 cx.t tE tH) = mwWord s g N B.src) (hP0h : σ.sh (P0 cx.t tE tH) = 0)
    (hDS : σ.st (DS cx.t tE tH) = PCPPNative.descriptor B.pf) (hDSh : σ.sh (DS cx.t tE tH) = 0)
    (hbK : ∀ j, σ.st (bK cx.t tE tH j) = []) (hbKh : ∀ j, σ.sh (bK cx.t tE tH j) = 0) :
    ∃ τ, WXExec cap (.mach cx.M (compMap cx.t tE tH cx.cIn cx.dIn)) σ τ
        (cx.C * ((mwWord s g N B.src).length + (PCPPNative.descriptor B.pf).length +
          Outer.width s.mw (g.sv s) N + 1) ^ cx.e) ∧
      τ.st (bK cx.t tE tH cx.cOut) = RepairOrdinary.frame (checkedCircuit P.code (substitutedAt s g x B)).word ∧
      τ.st (bK cx.t tE tH cx.wOut) = (P.output (checkedCircuit P.code (substitutedAt s g x B))).word ∧
      τ.st (bK cx.t tE tH cx.pOut) =
        RepairOrdinary.frame (P.output (checkedCircuit P.code (substitutedAt s g x B))).proofBits.bits ∧
      τ.st (bK cx.t tE tH cx.rOut) =
        RepairOrdinary.frame (P.output (checkedCircuit P.code (substitutedAt s g x B))).randomBits.bits ∧
      (∀ j, τ.sh (compMap cx.t tE tH cx.cIn cx.dIn j) = 0) ∧ τ.val = σ.val ∧ τ.cell = σ.cell ∧
      (∀ y, (∀ j, compMap cx.t tE tH cx.cIn cx.dIn j ≠ y) → τ.st y = σ.st y ∧ τ.sh y = σ.sh y) := by
  obtain ⟨out, hrun, hc, hw, -, hp, hr⟩ := cx.run x B hq
  have nd := cx.nd
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true,
    not_false_eq_true] at nd
  obtain ⟨⟨hd, hc1, hw1, -, hp1, hr1⟩, ⟨dc, dw, -, dp, dr⟩, -, -, -, -⟩ := nd
  have hin : ∀ j, σ.st (compMap cx.t tE tH cx.cIn cx.dIn j) = portBank cx.t cx.cIn cx.dIn
      (mwWord s g N B.src) (PCPPNative.descriptor B.pf) j := by
    intro j
    by_cases j1 : j = cx.cIn
    · subst j1; simp [compMap, portBank, hP0]
    · by_cases j2 : j = cx.dIn
      · subst j2; simp [compMap, portBank, j1, hDS]
      · simp [compMap, portBank, j1, j2, hbK]
  have h0 : ∀ j, σ.sh (compMap cx.t tE tH cx.cIn cx.dIn j) = 0 := by
    intro j
    by_cases j1 : j = cx.cIn
    · subst j1; simp [compMap, hP0h]
    · by_cases j2 : j = cx.dIn
      · subst j2; simp [compMap, j1, hDSh]
      · simp [compMap, j1, j2, hbKh]
  obtain ⟨τ, e, hdk⟩ := Dock.ready_mach cap hrun (compMap_inj cx.t tE tH cx.cIn cx.dIn) σ h0 hin
  refine ⟨τ, e, ?_, ?_, ?_, ?_, fun j => hdk.sh j, hdk.val, hdk.cell, fun y hy => hdk.other y hy⟩
  · rw [← compMap_other cx.t tE tH cx.cIn cx.dIn cx.cOut (Ne.symm hc1) (Ne.symm dc), hdk.st, hc]
  · rw [← compMap_other cx.t tE tH cx.cIn cx.dIn cx.wOut (Ne.symm hw1) (Ne.symm dw), hdk.st, hw]
  · rw [← compMap_other cx.t tE tH cx.cIn cx.dIn cx.pOut (Ne.symm hp1) (Ne.symm dp), hdk.st, hp]
  · rw [← compMap_other cx.t tE tH cx.cIn cx.dIn cx.rOut (Ne.symm hr1) (Ne.symm dr), hdk.st, hr]

end NearCubicGates.Close.Recovery.HT
