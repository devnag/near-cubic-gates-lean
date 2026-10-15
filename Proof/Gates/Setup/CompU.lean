import Proof.Gates.Setup.UniformSpec
import Proof.Gates.CheckedPCPP.CompositeInstance

set_option autoImplicit false

namespace NearCubicGates.Close.Setup

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.SourceInterfaces NearCubicWires.RepairSource NearCubicWires.RepairSource.ProjectionNormalization
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicGates.PublishedSources.PCPP NearCubicGates.Close.Gadget NearCubicWires.Bindings.CLW20Lemma311
open NearCubicGates.Close NearCubicGates.Close.WordPrograms NearCubicGates.Close.CheckedPCPP NearCubicGates.Close.Transfer

open Comp Comp.SubstFront in
open NearCubicWires.WireExponent3_5 NearCubicWires.ExtDecompositionBatch in

theorem compFull_of_objs {P : ThreeQueryPCPP} (o : Objs P) {C e : ℕ}
    (hC : ∀ i : Inst, costOf o i ≤ C * (Sz i + 1) ^ e) (s : GateSources) (g : GateParams) :
    ∃ cf : CompFull s P g, cf.e ≤ e := by
  refine ⟨⟨_, _, Rewind.machine (prog o).compile,
    (sTape (nr := 64) (HS o.t2 o.wf.program.tapeCount CloseoutCaseTwo.RequestInput.tapes o.p5.tapeCount)).castAdd 1,
    (sTape (nr := 64) (DS o.t2 o.wf.program.tapeCount CloseoutCaseTwo.RequestInput.tapes o.p5.tapeCount)).castAdd 1,
    (sTape (nr := 64) (b4 o.t2 o.wf.program.tapeCount CloseoutCaseTwo.RequestInput.tapes
      o.p5.tapeCount CloseoutCaseTwo.RequestInput.outputSlot)).castAdd 1,
    (sTape (nr := 64) (b5 o.t2 o.wf.program.tapeCount CloseoutCaseTwo.RequestInput.tapes
      o.p5.tapeCount o.p5.outputTape)).castAdd 1,
    (sTape (nr := 64) (SUP o.t2 o.wf.program.tapeCount CloseoutCaseTwo.RequestInput.tapes o.p5.tapeCount)).castAdd 1,
    (sTape (nr := 64) (PO o.t2 o.wf.program.tapeCount CloseoutCaseTwo.RequestInput.tapes o.p5.tapeCount)).castAdd 1,
    (sTape (nr := 64) (RO o.t2 o.wf.program.tapeCount CloseoutCaseTwo.RequestInput.tapes o.p5.tapeCount)).castAdd 1,
    2 * C + 2, e, ?_, ?_⟩, le_rfl⟩
  · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true,
      not_false_eq_true]
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩ <;>
    · intro h; have := congrArg Fin.val h; simp [sTape_v] at this; try omega
  · intro N x B hq
    let i : Inst := ⟨Outer.outC s.mw (g.sv s) (Nat.log 2 N) B.src, Outer.width s.mw (g.sv s) N, B.pf, hq⟩
    obtain ⟨τ, eτ, h1, h2, h3, h4, h5⟩ := inst_run o i
    obtain ⟨out, hrun, hout⟩ := WXExec.readyRewound eτ (fun _ => rfl) (fun _ => rfl) rfl
    have hb : costOf o i ≤ C * ((mwWord s g N B.src).length + (PCPPNative.descriptor B.pf).length +
        Outer.width s.mw (g.sv s) N + 1) ^ e := hC i
    have hpow : 1 ≤ ((mwWord s g N B.src).length + (PCPPNative.descriptor B.pf).length +
        Outer.width s.mw (g.sv s) N + 1) ^ e := Nat.one_le_pow _ _ (by omega)
    refine ⟨out, ?_, (hout _).trans h1, (hout _).trans h2, (hout _).trans h3, (hout _).trans h4, (hout _).trans h5⟩
    have hrun' : ClockJoin.ReadyRun (Rewind.machine (prog o).compile) (2 * costOf o i + 2)
        (portBank (NS o.t2 o.wf.program.tapeCount CloseoutCaseTwo.RequestInput.tapes o.p5.tapeCount + 2 + 64 + 1)
          ((sTape (nr := 64) (HS o.t2 o.wf.program.tapeCount CloseoutCaseTwo.RequestInput.tapes
            o.p5.tapeCount)).castAdd 1)
          ((sTape (nr := 64) (DS o.t2 o.wf.program.tapeCount CloseoutCaseTwo.RequestInput.tapes
            o.p5.tapeCount)).castAdd 1) (hx i) (dx i)) out := by
      rw [← bank_eq']; exact hrun
    refine ClockJoin.enlarge _ _ _ _ _ hrun' ?_
    nlinarith

theorem compU_of (h : Succinct.SubstMachine.SubstReadySpec) (s : GateSources) (P : ThreeQueryPCPP) : CompU s P := by
  obtain ⟨o⟩ := Comp.SubstFront.objs_exist h P
  obtain ⟨C, e, hC⟩ := Comp.SubstFront.cost_poly o
  exact ⟨e, fun g => compFull_of_objs o hC s g⟩

theorem composite_of (h : Succinct.SubstMachine.SubstReadySpec) : CompositeSpec := by
  intro s P g
  obtain ⟨E, hE⟩ := compU_of h s P
  obtain ⟨cf, -⟩ := hE g
  refine ⟨cf.t, cf.st, cf.M, cf.cIn, cf.dIn, cf.cOut, cf.wOut, cf.sOut, cf.pOut, cf.rOut, cf.C, cf.e, ?_, ?_⟩
  · have := cf.nd
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at this
    exact this.1.1
  · intro N x B hq
    obtain ⟨out, hr, h1, h2, h3, h4, h5⟩ := cf.run x B hq
    exact ⟨out, hr, by rw [h1]; exact RdEq.refl _, by rw [h2]; exact RdEq.refl _, by rw [h3]; exact RdEq.refl _,
      by rw [h4]; exact RdEq.refl _, by rw [h5]; exact RdEq.refl _⟩

end NearCubicGates.Close.Setup
