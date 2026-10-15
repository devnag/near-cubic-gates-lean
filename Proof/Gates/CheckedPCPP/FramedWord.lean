import Proof.Gates.CheckedPCPP.PCPPWord
import Proof.Gates.CheckedPCPP.Framed.Budget

set_option autoImplicit false

namespace NearCubicGates.Close.CheckedPCPP

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Gadget

theorem tm2_ready_framed {α β : Type} {ea : α → List Bool} {eb : β → List Bool} {f : α → β}
    (h : Turing.TM2ComputableInPolyTime ea eb f) (X : α → ℕ) (K₀ a₀ : ℕ)
    (hlen : ∀ a, (ea a).length ≤ K₀ * (X a + 1) ^ a₀) :
    ∃ (p : Program) (K e : ℕ), ∀ a, ∃ out,
      ClockJoin.ReadyRun p.machine (K * (X a + 1) ^ e) (p.inputTapes (ea a)) out ∧
        out p.outputTape = FramedSim.pairs (eb (f a)) := by
  obtain ⟨K, e, ⟨wf⟩⟩ := FramedSim.tm2Poly_ordinary h X K₀ a₀ hlen
  refine ⟨Rewind.program wf.program, 2 * K + 2, e, fun a => ?_⟩
  obtain ⟨out, hrun, hout⟩ := wordFunction_ready wf a
  refine ⟨out, ClockJoin.enlarge _ _ _ _ _ hrun ?_, hout⟩
  have h1 : 1 ≤ (X a + 1) ^ e := Nat.one_le_pow _ _ (Nat.succ_pos _)
  nlinarith

theorem encFramed_ready (P : ThreeQueryPCPP) :
    ∃ (p : Program) (K e : ℕ), ∀ m : NearCubicGates.PublishedSources.PCPP.MessageRequest, ∃ out,
      ClockJoin.ReadyRun p.machine
        (K * ((NearCubicGates.PublishedSources.PCPP.messageWord m).length + 1) ^ e)
        (p.inputTapes (NearCubicGates.PublishedSources.PCPP.messageWord m)) out ∧
        out p.outputTape = FramedSim.pairs (List.ofFn (P.code.enc m.1 m.2.val)) := by
  obtain ⟨h⟩ := P.encPoly
  exact tm2_ready_framed h (fun m => (NearCubicGates.PublishedSources.PCPP.messageWord m).length) 1 1
    (fun m => by simp)

theorem honestFramed_ready (P : ThreeQueryPCPP) :
    ∃ (p : Program) (K e : ℕ), ∀ a : NearCubicGates.PublishedSources.PCPP.AcceptedCircuitInput, ∃ out,
      ClockJoin.ReadyRun p.machine
        (K * ((NearCubicGates.PublishedSources.PCPP.acceptedCircuitInputWord a).length + 1) ^ e)
        (p.inputTapes (NearCubicGates.PublishedSources.PCPP.acceptedCircuitInputWord a)) out ∧
        out p.outputTape = FramedSim.pairs (List.ofFn (P.honest a)) := by
  obtain ⟨h⟩ := P.honestPoly
  exact tm2_ready_framed h (fun a => (NearCubicGates.PublishedSources.PCPP.acceptedCircuitInputWord a).length)
    1 1 (fun a => by simp)

end NearCubicGates.Close.CheckedPCPP
