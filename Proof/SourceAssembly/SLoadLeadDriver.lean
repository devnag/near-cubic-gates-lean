import Proof.SourceAssembly.SLoadRequestLead

/-! The one open input obligation of the accepted second conjunct.

`RequestFrames.request_frames_step` consumes the suffix's unary domain driver
as a BARE word, `A drv = ZeroPadding.pad capD (List.replicate (B 4).length true)`,
while every retained ambient field of this loader family is framed. The gap is
paid on the LEAD side, by one extra call of the already docked unframing
producer `SLoad.Lead.bareStage` (`Streaming.machine`, all heads zero in and
out) against a retained `frame (List.replicate r.q true)`. No new machine and
no new local program: the prefix simply gains a fifth stage, and its fuel the
corresponding `4 * r.q + 2 + 1`.

The physical length of the driver is read off the retained framed word, and
`(maskData a r).word.length = r.q` (`word_length`) is what makes it the
driver the framing pass demands. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace SLoad.LeadDriver
open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairRepresentation SupplierEstimator SupplierPipeline SourceInterfaces
open RepairSource.VerifierDecoding
open FixedLivePackets PacketProduction MaskedFamilySource
noncomputable section

/-- The mask worker's promised output word is exactly `r.q` bits long. -/
theorem word_length (a : DecompositionAlgorithm) (r : Request) :
    (maskData a r).word.length = r.q := by
  simp [MaskData.word, maskData]

/-- The extended prefix: the retained unary domain driver is unframed onto the
suffix's driver slot, then the accepted four-stage mask input load runs. -/
noncomputable def machine {U work : Nat} (retDrv drv : Fin U) (ret : Fin 4 → Fin U)
    (maskSlots : Fin (5 + work) → Fin U) (log : Fin U) : Machine U 34 :=
  Composition.machine (Lead.bareStage retDrv drv log)
    (Lead.machine ret (MaskInput.live maskSlots) log)

/-- Fuel for the extended prefix. -/
def prefixFuel (a : DecompositionAlgorithm) (r : Request) : Nat :=
  4 * r.q + 2 + 1 + RequestLead.prefixFuel a r

/-- The first conjunct of `MaskSeedCode.Ready`, with the suffix's bare unary
driver additionally resident. -/
theorem lead_driver_step {U : Nat} (mask : MaskProducer)
    (maskSlots : Fin (5 + mask.work) → Fin U) (hinj : Function.Injective maskSlots)
    (ret : Fin 4 → Fin U) (retDrv drv log : Fin U)
    (hrm : ∀ (i : Fin 4) (j : Fin (5 + mask.work)), ret i ≠ maskSlots j)
    (hrl : ∀ i, ret i ≠ log) (hlm : ∀ j, log ≠ maskSlots j)
    (hdm : ∀ j, drv ≠ maskSlots j) (hdr : ∀ i, drv ≠ ret i) (hdl : drv ≠ log)
    (hDd : retDrv ≠ drv) (hDl : retDrv ≠ log)
    (a : DecompositionAlgorithm) (r : Request) (cap : Nat) (uq uK um : List Bool)
    (hq : uq.length = r.q) (hk : uK.length = normalizedLiveCount r.q r.liveScale)
    (hmm : um.length = (r.family a).occurrences.length)
    (cs : (r.supportWord a).length ≤ cap) (cq : 4 * uq.length + 3 ≤ cap)
    (ck : 4 * uK.length + 3 ≤ cap) (cm : 4 * um.length + 3 ≤ cap)
    (blank : Fin (5 + mask.work) → Nat)
    (H : Fin U → Nat) (A : Fin U → List Bool)
    (hHr : ∀ i, H (ret i) = 0) (hHm : ∀ j, H (maskSlots j) = 0) (hHl : H log = 0)
    (hHD : H retDrv = 0) (hHd : H drv = 0)
    (hAD : A retDrv = ZeroPadding.pad cap (frame (List.replicate r.q true)))
    (hAd : A drv = [])
    (hA0 : A (ret 0) = ZeroPadding.pad cap (frame (r.supportWord a)))
    (hA1 : A (ret 1) = ZeroPadding.pad cap (frame uq))
    (hA2 : A (ret 2) = ZeroPadding.pad cap (frame uK))
    (hA3 : A (ret 3) = ZeroPadding.pad cap (frame um))
    (hLive : ∀ j : Fin (5 + mask.work), j.val < 4 → A (maskSlots j) = [])
    (hPriv : ∀ j : Fin (5 + mask.work), 4 ≤ j.val →
      A (maskSlots j) = List.replicate (blank j) false)
    (hAl : A log = List.replicate cap false) :
    Step (machine retDrv drv ret maskSlots log) (prefixFuel a r) H A
      (dockH maskSlots H (fun _ => 0))
      (install maskSlots (Function.update A drv (List.replicate r.q true))
        (fun i => ZeroPadding.pad (MaskInput.reserve blank i)
          ((maskData a r).input mask.work i))) := by
  classical
  have hlen : (List.replicate r.q true).length = r.q := List.length_replicate
  have hcap : (List.replicate r.q true).length ≤ cap := by rw [hlen]; omega
  have e0 := Lead.bare_stage_step retDrv drv log hDd hDl hdl cap (List.replicate r.q true)
    hcap H A hHD hHd hHl hAD hAd hAl
  have e1 := RequestLead.request_lead_step mask maskSlots hinj ret log hrm hrl hlm a r cap
    uq uK um hq hk hmm cs cq ck cm blank H (Function.update A drv (List.replicate r.q true))
    hHr hHm hHl
    (by rw [Function.update_of_ne (Ne.symm (hdr 0))]; exact hA0)
    (by rw [Function.update_of_ne (Ne.symm (hdr 1))]; exact hA1)
    (by rw [Function.update_of_ne (Ne.symm (hdr 2))]; exact hA2)
    (by rw [Function.update_of_ne (Ne.symm (hdr 3))]; exact hA3)
    (fun j hj => by rw [Function.update_of_ne (Ne.symm (hdm j))]; exact hLive j hj)
    (fun j hj => by rw [Function.update_of_ne (Ne.symm (hdm j))]; exact hPriv j hj)
    (by rw [Function.update_of_ne (Ne.symm hdl)]; exact hAl)
  have joined := e0.seq e1
  rw [hlen] at joined
  exact joined

end
end SLoad.LeadDriver
