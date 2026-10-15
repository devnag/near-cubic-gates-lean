import Proof.SourceAssembly.SLoadMaskInput
import Proof.SourceAssembly.SLoadRequestFrames

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace SLoad.RequestLead
open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairRepresentation SupplierEstimator SupplierPipeline SourceInterfaces
open RepairSource.VerifierDecoding
open FixedLivePackets PacketProduction MaskedFamilySource
noncomputable section

/-- The prefix fuel, in the request's own physical dimensions. -/
def prefixFuel (a : DecompositionAlgorithm) (r : Request) : Nat :=
  Lead.cost (r.supportWord a).length r.q (normalizedLiveCount r.q r.liveScale)
    (r.family a).occurrences.length

theorem request_lead_step {U : Nat} (mask : MaskProducer)
    (maskSlots : Fin (5 + mask.work) → Fin U) (hinj : Function.Injective maskSlots)
    (ret : Fin 4 → Fin U) (log : Fin U)
    (hrm : ∀ (i : Fin 4) (j : Fin (5 + mask.work)), ret i ≠ maskSlots j)
    (hrl : ∀ i, ret i ≠ log) (hlm : ∀ j, log ≠ maskSlots j)
    (a : DecompositionAlgorithm) (r : Request) (cap : Nat) (uq uK um : List Bool)
    (hq : uq.length = r.q) (hk : uK.length = normalizedLiveCount r.q r.liveScale)
    (hmm : um.length = (r.family a).occurrences.length)
    (cs : (r.supportWord a).length ≤ cap) (cq : 4 * uq.length + 3 ≤ cap)
    (ck : 4 * uK.length + 3 ≤ cap) (cm : 4 * um.length + 3 ≤ cap)
    (blank : Fin (5 + mask.work) → Nat)
    (H : Fin U → Nat) (A : Fin U → List Bool)
    (hHr : ∀ i, H (ret i) = 0) (hHm : ∀ j, H (maskSlots j) = 0) (hHl : H log = 0)
    (hA0 : A (ret 0) = ZeroPadding.pad cap (frame (r.supportWord a)))
    (hA1 : A (ret 1) = ZeroPadding.pad cap (frame uq))
    (hA2 : A (ret 2) = ZeroPadding.pad cap (frame uK))
    (hA3 : A (ret 3) = ZeroPadding.pad cap (frame um))
    (hLive : ∀ j : Fin (5 + mask.work), j.val < 4 → A (maskSlots j) = [])
    (hPriv : ∀ j : Fin (5 + mask.work), 4 ≤ j.val →
      A (maskSlots j) = List.replicate (blank j) false)
    (hAl : A log = List.replicate cap false) :
    Step (Lead.machine ret (MaskInput.live maskSlots) log) (prefixFuel a r) H A
      (dockH maskSlots H (fun _ => 0))
      (install maskSlots A (fun i => ZeroPadding.pad (MaskInput.reserve blank i)
        ((maskData a r).input mask.work i))) := by
  have hsupport := RequestFrames.support_eq a r
  have h := MaskInput.mask_input_step maskSlots hinj ret log hrm hrl hlm
    (maskData a r) cap uq uK um hq hk hmm (by rw [hsupport]; exact cs) cq ck cm
    blank H A hHr hHm hHl (by rw [hsupport]; exact hA0) hA1 hA2 hA3 hLive hPriv hAl
  have hcost : Lead.cost (maskData a r).supportWord.length (maskData a r).q
      (maskData a r).K (maskData a r).m = prefixFuel a r := by
    rw [prefixFuel, hsupport]
    rfl
  rw [hcost] at h
  exact h

end
end SLoad.RequestLead
