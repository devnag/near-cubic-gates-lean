import Proof.Gates.CheckedPCPP.Word
import Proof.Gates.Gadget.ThreeQuery

set_option autoImplicit false

namespace NearCubicGates.Close.CheckedPCPP

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.Bindings.CLW20Lemma311 NearCubicGates.Close.Gadget

theorem pcppWord_ready (P : ThreeQueryPCPP) :
    ∃ (p : Program) (K e : ℕ), ∀ C : Circuit, ∃ out,
      ClockJoin.ReadyRun p.machine (K * (C.word.length + 1) ^ e) (p.inputTapes C.word) out ∧
        out p.outputTape = (P.output C).word := by
  obtain ⟨h⟩ := P.outputPoly
  exact tm2_ready h (fun C : Circuit => C.word.length) 1 1 (fun C => by simp)

theorem honestWord_ready (P : ThreeQueryPCPP) :
    ∃ (p : Program) (K e : ℕ), ∀ a : NearCubicGates.PublishedSources.PCPP.AcceptedCircuitInput, ∃ out,
      ClockJoin.ReadyRun p.machine
        (K * ((NearCubicGates.PublishedSources.PCPP.acceptedCircuitInputWord a).length + 1) ^ e)
        (p.inputTapes (NearCubicGates.PublishedSources.PCPP.acceptedCircuitInputWord a)) out ∧
        out p.outputTape = List.ofFn (P.honest a) := by
  obtain ⟨h⟩ := P.honestPoly
  exact tm2_ready h (fun a => (NearCubicGates.PublishedSources.PCPP.acceptedCircuitInputWord a).length) 1 1
    (fun a => by simp)

theorem encWord_ready (P : ThreeQueryPCPP) :
    ∃ (p : Program) (K e : ℕ), ∀ m : NearCubicGates.PublishedSources.PCPP.MessageRequest, ∃ out,
      ClockJoin.ReadyRun p.machine
        (K * ((NearCubicGates.PublishedSources.PCPP.messageWord m).length + 1) ^ e)
        (p.inputTapes (NearCubicGates.PublishedSources.PCPP.messageWord m)) out ∧
        out p.outputTape = List.ofFn (P.code.enc m.1 m.2.val) := by
  obtain ⟨h⟩ := P.encPoly
  exact tm2_ready h (fun m => (NearCubicGates.PublishedSources.PCPP.messageWord m).length) 1 1 (fun m => by simp)

end NearCubicGates.Close.CheckedPCPP
