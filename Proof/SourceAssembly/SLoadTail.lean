import Proof.SourceAssembly.SLoadSuffixFrame

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace SLoad.Tail
open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairRepresentation SupplierEstimator SupplierPipeline SourceInterfaces
open FixedLivePackets PacketProduction MaskedFamilySource
noncomputable section

/-- The mask producer's `∀ B` is a singleton: `MaskProducer.correct` supplies a
compatible bank, and determinism of `Step` forces every other one to be it. -/
theorem mask_bank (mask : MaskProducer) (d : MaskData) :
    ∃ B0 : Fin (5 + mask.work) → List Bool,
      Step mask.machine (maskBudget mask.coefficient mask.degree d) (fun _ => 0)
        (d.input mask.work) (fun _ => 0) B0 ∧
      B0 ⟨4, by omega⟩ = d.word ∧
      ∀ B : Fin (5 + mask.work) → List Bool,
        Step mask.machine (maskBudget mask.coefficient mask.degree d) (fun _ => 0)
          (d.input mask.work) (fun _ => 0) B → B = B0 := by
  obtain ⟨B0, hrun, hword⟩ := mask.correct d
  exact ⟨B0, hrun, hword, fun B hB => (SuffixFrame.step_det hB hrun).2⟩

/-- The packet producer's `∀ B` is a singleton, for the same reason. No private
tape of the packet worker has to be cleared by the tail. -/
theorem packet_bank {selector : CyclicChoice.Laws} {a : DecompositionAlgorithm}
    (packet : PacketWriter selector a) (r : Request) :
    ∃ B0 : Fin packet.ordinary.program.tapeCount → List Bool,
      B0 packet.ordinary.program.outputTape = r.raw selector a ∧
      ∀ B : Fin packet.ordinary.program.tapeCount → List Bool,
        Step packet.ordinary.program.machine (packetBudget a packet.coefficient packet.degree r)
          (fun _ => 0) (packet.ordinary.program.inputTapes (r.input a)) (fun _ => 0) B →
        B = B0 := by
  obtain ⟨B0, hrun, hout⟩ := packet.run selector a r
  exact ⟨B0, hout, fun B hB => (SuffixFrame.step_det hB hrun).2⟩

/-- The tail program: the existing raw framer, docked at the packet's own
certified output slot, a retained unary length driver, a zero-backed
destination slot and a paid rewind log. Five states, four slots, no request
in scope. -/
noncomputable def machine {U : Nat} (src drv dst log : Fin U) : Machine U 5 :=
  MaskFrame.machine src drv dst log

/-- Fuel for the tail, in the actual physical length of the raw packet word. -/
def cost (n : Nat) : Nat := 4 * n + 4

/-- The tail's physical run, from an arbitrary certified packet bank. Only the
output slot is read; the packet worker's private slots are neither read nor
written, and no ambient head moves. -/
theorem tail_step {U : Nat} {selector : CyclicChoice.Laws} {a : DecompositionAlgorithm}
    (packet : PacketWriter selector a) (r : Request)
    (slots : Fin packet.ordinary.program.tapeCount → Fin U)
    (hsinj : Function.Injective slots) (drv dst log : Fin U)
    (hd : ∀ j, slots j ≠ drv) (ht : ∀ j, slots j ≠ dst) (hl : ∀ j, slots j ≠ log)
    (hdt : drv ≠ dst) (hdl : drv ≠ log) (htl : dst ≠ log)
    (reserve : Fin packet.ordinary.program.tapeCount → Nat)
    (ambientH : Fin U → Nat) (ambientA : Fin U → List Bool)
    (capD cap capL : Nat) (hcapL : 2 * (r.raw selector a).length + 1 ≤ capL)
    (hHd : ambientH drv = 0) (hHt : ambientH dst = 0) (hHl : ambientH log = 0)
    (hAd : ambientA drv = ZeroPadding.pad capD (List.replicate (r.raw selector a).length true))
    (hAt : ambientA dst = List.replicate cap false)
    (hAl : ambientA log = List.replicate capL false)
    (B : Fin packet.ordinary.program.tapeCount → List Bool)
    (hB : B packet.ordinary.program.outputTape = r.raw selector a) :
    Step (machine (slots packet.ordinary.program.outputTape) drv dst log)
      (cost (r.raw selector a).length)
      (dockH slots ambientH (fun _ => 0))
      (install slots ambientA (fun i => ZeroPadding.pad (reserve i) (B i)))
      (dockH slots ambientH (fun _ => 0))
      (Function.update (install slots ambientA (fun i => ZeroPadding.pad (reserve i) (B i)))
        dst (ZeroPadding.pad cap (frame (r.raw selector a)))) := by
  classical
  have hsrc := hd packet.ordinary.program.outputTape
  exact MaskFrame.mask_frame_step (slots packet.ordinary.program.outputTape) drv dst log
    hsrc (ht packet.ordinary.program.outputTape) (hl packet.ordinary.program.outputTape)
    hdt hdl htl (reserve packet.ordinary.program.outputTape) capD cap capL
    (r.raw selector a) hcapL _ _
    (dockH_slot slots hsinj ambientH (fun _ => 0) packet.ordinary.program.outputTape)
    (by rw [dockH_other slots ambientH (fun _ => 0) drv hd]; exact hHd)
    (by rw [dockH_other slots ambientH (fun _ => 0) dst ht]; exact hHt)
    (by rw [dockH_other slots ambientH (fun _ => 0) log hl]; exact hHl)
    (by rw [install_slot slots hsinj, hB])
    (by rw [install_other slots ambientA _ drv hd]; exact hAd)
    (by rw [install_other slots ambientA _ dst ht]; exact hAt)
    (by rw [install_other slots ambientA _ log hl]; exact hAl)

end
end SLoad.Tail
