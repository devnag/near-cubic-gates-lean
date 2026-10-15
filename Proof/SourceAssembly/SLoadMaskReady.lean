import Proof.SourceAssembly.SLoadLeadDriver
import Proof.SourceAssembly.SLoadRequestSuffix
import Proof.SourceAssembly.SLoadTail

/-! The deliverable: an actual `MaskSeedCode` and its `Ready` certificate.

The three conjuncts are the three accepted physical runs of this source
loader, with the fuel `Ready`'s last conjunct asks for, as an equality rather
than an estimate:

```
(prefixFuel+1+(maskBudget+1+suffixFuel))+1+(packetBudget+1+tailFuel)
```

Neither `∀ B` costs a clearing scan. Both producers' final banks are pinned by
determinism of `Step` (`Tail.mask_bank`, `Tail.packet_bank`), so the
quantifiers range over the single bank the producer's own correctness field
supplies, and the mask worker's and the packet worker's private tapes are
carried out of the loader exactly as they were returned. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace SLoad.MaskReady
open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairRepresentation SupplierEstimator SupplierPipeline SourceInterfaces
open RepairSource.VerifierDecoding
open FixedLivePackets PacketProduction MaskedFamilySource
noncomputable section

theorem entry_one (capS capD cap : Nat) (mw nw sw iw tw : List Bool) :
    SuffixFrame.entry capS capD cap mw nw sw iw tw 1
      = ZeroPadding.pad capD (List.replicate mw.length true) := rfl

/-- The physical source loader: an extended prefix, the docked mask worker's
own suffix and the raw framer, on one ambient layout. Every state count is a
numeral and no request is in scope. -/
noncomputable def code {U : Nat} (mask : MaskProducer) {selector : CyclicChoice.Laws}
    {a : DecompositionAlgorithm} (packet : PacketWriter selector a)
    (maskSlots : Fin (5 + mask.work) → Fin U) (hminj : Function.Injective maskSlots)
    (slots : Fin packet.ordinary.program.tapeCount → Fin U) (hsinj : Function.Injective slots)
    (slot : Fin 13 → Fin U) (ret : Fin 4 → Fin U)
    (retDrv log rawDrv rawDst rawLog : Fin U) : MaskSeedCode mask packet U where
  slots := slots
  injective := hsinj
  maskSlots := maskSlots
  maskInjective := hminj
  prefixStates := 34
  lead := LeadDriver.machine retDrv (slot 1) ret maskSlots log
  suffixStates := 34
  suffix := SuffixFrame.machine slot
  tailStates := 5
  tail := Tail.machine (slots packet.ordinary.program.outputTape) rawDrv rawDst rawLog

/-- The loader's total fuel, exactly the sum `Ready` requires. -/
def fuel (mask : MaskProducer) {selector : CyclicChoice.Laws} {a : DecompositionAlgorithm}
    (packet : PacketWriter selector a) (r : Request) : Nat :=
  (LeadDriver.prefixFuel a r + 1 +
      (maskBudget mask.coefficient mask.degree (maskData a r) + 1 +
        SuffixFrame.cost r.q r.nativeWord.length (r.supportWord a).length
          (r.indexWord a).length (r.topWord a).length)) + 1 +
    (packetBudget a packet.coefficient packet.degree r + 1 +
      Tail.cost (r.raw selector a).length)

/-- `MaskSeedCode.Ready` for the physical loader. -/
theorem mask_ready {U : Nat} (mask : MaskProducer) {selector : CyclicChoice.Laws}
    {a : DecompositionAlgorithm} (packet : PacketWriter selector a)
    (maskSlots : Fin (5 + mask.work) → Fin U) (hminj : Function.Injective maskSlots)
    (slots : Fin packet.ordinary.program.tapeCount → Fin U) (hsinj : Function.Injective slots)
    (slot : Fin 13 → Fin U) (hinj : Function.Injective slot)
    (ret : Fin 4 → Fin U) (retDrv log rawDrv rawDst rawLog : Fin U)
    (r : Request) (cap capR capD capL : Nat) (uK um : List Bool)
    (hk : uK.length = normalizedLiveCount r.q r.liveScale)
    (hmm : um.length = (r.family a).occurrences.length)
    (hmsk : slot 0 = maskSlots ⟨4, by omega⟩)
    (hoffm : ∀ j : Fin 13, j ≠ 0 → ∀ i, maskSlots i ≠ slot j)
    (hslot0 : ∀ j : Fin packet.ordinary.program.tapeCount, j.val = 0 → slots j = slot 11)
    (hoffp : ∀ j : Fin packet.ordinary.program.tapeCount, j.val ≠ 0 → ∀ k, slot k ≠ slots j)
    (hmp : ∀ (j : Fin packet.ordinary.program.tapeCount) (i : Fin (5 + mask.work)),
      maskSlots i ≠ slots j)
    (hrm : ∀ (i : Fin 4) (j : Fin (5 + mask.work)), ret i ≠ maskSlots j)
    (hrl : ∀ i, ret i ≠ log) (hlm : ∀ j, log ≠ maskSlots j)
    (hdr : ∀ i, slot 1 ≠ ret i) (hdl : slot 1 ≠ log)
    (hDd : retDrv ≠ slot 1) (hDl : retDrv ≠ log)
    (htd : ∀ j : Fin 13, slot j ≠ rawDrv) (htt : ∀ j : Fin 13, slot j ≠ rawDst)
    (htg : ∀ j : Fin 13, slot j ≠ rawLog)
    (hmd : ∀ i, maskSlots i ≠ rawDrv) (hmt : ∀ i, maskSlots i ≠ rawDst)
    (hmg : ∀ i, maskSlots i ≠ rawLog)
    (hpd : ∀ j, slots j ≠ rawDrv) (hpt : ∀ j, slots j ≠ rawDst) (hpg : ∀ j, slots j ≠ rawLog)
    (hdt2 : rawDrv ≠ rawDst) (hdl2 : rawDrv ≠ rawLog) (htl2 : rawDst ≠ rawLog)
    (cs : (r.supportWord a).length ≤ cap) (cq : 4 * r.q + 3 ≤ cap)
    (ck : 4 * uK.length + 3 ≤ cap) (cm : 4 * um.length + 3 ≤ cap)
    (cq2 : 2 * r.q + 1 ≤ cap) (cn : 2 * r.nativeWord.length + 1 ≤ cap)
    (cs2 : 2 * (r.supportWord a).length + 1 ≤ cap) (ci : 2 * (r.indexWord a).length + 1 ≤ cap)
    (ct : 2 * (r.topWord a).length + 1 ≤ cap)
    (cL : 2 * (r.raw selector a).length + 1 ≤ capL)
    (blank : Fin (5 + mask.work) → Nat)
    (blankP : Fin packet.ordinary.program.tapeCount → Nat)
    (H : Fin U → Nat) (A : Fin U → List Bool)
    (hHr : ∀ i, H (ret i) = 0) (hHm : ∀ j, H (maskSlots j) = 0) (hHl : H log = 0)
    (hHD : H retDrv = 0) (hHsl : ∀ j, H (slot j) = 0) (hHs : ∀ j, H (slots j) = 0)
    (hHrd : H rawDrv = 0) (hHrt : H rawDst = 0) (hHrg : H rawLog = 0)
    (hAD : A retDrv = ZeroPadding.pad cap (frame (List.replicate r.q true)))
    (hA0 : A (ret 0) = ZeroPadding.pad cap (frame (r.supportWord a)))
    (hA1 : A (ret 1) = ZeroPadding.pad cap (frame (List.replicate r.q true)))
    (hA2 : A (ret 2) = ZeroPadding.pad cap (frame uK))
    (hA3 : A (ret 3) = ZeroPadding.pad cap (frame um))
    (hLive : ∀ j : Fin (5 + mask.work), j.val < 4 → A (maskSlots j) = [])
    (hPriv : ∀ j : Fin (5 + mask.work), 4 ≤ j.val →
      A (maskSlots j) = List.replicate (blank j) false)
    (hAl : A log = List.replicate cap false)
    (hAd : A (slot 1) = [])
    (hAsuf : ∀ j : Fin 13, j ≠ 0 → j ≠ 1 → A (slot j)
      = SuffixFrame.entry (MaskInput.reserve blank ⟨4, by omega⟩) 0 cap (maskData a r).word
          r.nativeWord (r.supportWord a) (r.indexWord a) (r.topWord a) j)
    (hblankP : ∀ j : Fin packet.ordinary.program.tapeCount, j.val ≠ 0 →
      A (slots j) = List.replicate (blankP j) false)
    (hArd : A rawDrv = ZeroPadding.pad capD (List.replicate (r.raw selector a).length true))
    (hArt : A rawDst = List.replicate capR false)
    (hArg : A rawLog = List.replicate capL false) :
    ∃ A' : Fin U → List Bool,
      (code mask packet maskSlots hminj slots hsinj slot ret retDrv log rawDrv rawDst rawLog).Ready
        r (fuel mask packet r) H (dockH slots H (fun _ => 0)) A A' ∧
      A' rawDst = ZeroPadding.pad capR (frame (r.raw selector a)) := by
  classical
  have hdm : ∀ j, slot 1 ≠ maskSlots j := fun j => (hoffm 1 (by decide) j).symm
  have hlenq : (List.replicate r.q true).length = r.q := List.length_replicate
  -- the first conjunct, with the suffix's bare unary driver additionally resident
  have e1 := LeadDriver.lead_driver_step mask maskSlots hminj ret retDrv (slot 1) log
    hrm hrl hlm hdm hdr hdl hDd hDl a r cap (List.replicate r.q true) uK um
    hlenq hk hmm cs (by rw [hlenq]; exact cq) ck cm blank H A hHr hHm hHl hHD (hHsl 1)
    hAD hAd hA0 hA1 hA2 hA3 hLive hPriv hAl
  -- the mask producer's final bank is pinned
  obtain ⟨B0, hrun0, hword0, huniq0⟩ := Tail.mask_bank mask (maskData a r)
  have hql : (B0 ⟨4, by omega⟩).length = r.q := by
    rw [hword0]; exact LeadDriver.word_length a r
  -- the second conjunct
  obtain ⟨ambientA, hsuf, hkeep⟩ := RequestSuffix.request_suffix_step slot hinj maskSlots hminj
    packet.ordinary.program slots hsinj a r B0 hword0 (MaskInput.reserve blank) blankP 0 cap
    (by rw [hql]; exact cq2) cn cs2 ci ct H (Function.update A (slot 1) (List.replicate r.q true))
    hmsk hoffm hslot0 hoffp hmp hHm hHsl hHs
    (by
      intro j hj
      by_cases h1 : j = 1
      · subst h1
        rw [Function.update_self, hword0, entry_one, ZeroPadding.pad_zero,
          LeadDriver.word_length]
      · rw [Function.update_of_ne (fun h => h1 (hinj h)), hAsuf j hj h1, hword0])
    (by
      intro j hj
      rw [Function.update_of_ne (Ne.symm (hoffp j hj 1))]
      exact hblankP j hj)
  rw [hql] at hsuf
  -- the ambient bank outside the suffix's own slots is the caller's bank
  have hAmb : ∀ x, (∀ j : Fin 13, slot j ≠ x) → (∀ i, maskSlots i ≠ x) → ambientA x = A x := by
    intro x h13 hmk
    rw [hkeep x h13, install_other maskSlots _ _ x hmk,
      Function.update_of_ne (Ne.symm (h13 1))]
  -- the packet producer's final bank is pinned
  obtain ⟨Bp, houtp, huniqp⟩ := Tail.packet_bank packet r
  -- the third conjunct
  have htail := Tail.tail_step packet r slots hsinj rawDrv rawDst rawLog hpd hpt hpg
    hdt2 hdl2 htl2 (RequestSuffix.reserve blankP) H ambientA capD capR capL cL
    hHrd hHrt hHrg
    (by rw [hAmb rawDrv htd hmd]; exact hArd)
    (by rw [hAmb rawDst htt hmt]; exact hArt)
    (by rw [hAmb rawLog htg hmg]; exact hArg)
    Bp houtp
  refine ⟨Function.update (install slots ambientA
      (fun i => ZeroPadding.pad (RequestSuffix.reserve blankP i) (Bp i))) rawDst
      (ZeroPadding.pad capR (frame (r.raw selector a))),
    ⟨MaskInput.reserve blank, H, Function.update A (slot 1) (List.replicate r.q true),
    RequestSuffix.reserve blankP, H, ambientA, LeadDriver.prefixFuel a r,
    SuffixFrame.cost r.q r.nativeWord.length (r.supportWord a).length (r.indexWord a).length
      (r.topWord a).length,
    Tail.cost (r.raw selector a).length, e1, ?_, ?_, Nat.le_refl _⟩, Function.update_self _ _ _⟩
  · intro B hB hword
    have : B = B0 := huniq0 B hB
    subst this
    exact hsuf
  · intro B hB hraw
    have : B = Bp := huniqp B hB
    subst this
    exact htail

/-- The same certificate at the interface the caller consumes: the accepted
`MaskSeedCode.project` turns it into `SeedCode.Ready` for the composed loader
`MaskSeedCode.base`, whose `load` is the prefix, the docked mask worker and
the suffix. -/
theorem seed_ready {U : Nat} (mask : MaskProducer) {selector : CyclicChoice.Laws}
    {a : DecompositionAlgorithm} (packet : PacketWriter selector a)
    (maskSlots : Fin (5 + mask.work) → Fin U) (hminj : Function.Injective maskSlots)
    (slots : Fin packet.ordinary.program.tapeCount → Fin U) (hsinj : Function.Injective slots)
    (slot : Fin 13 → Fin U) (ret : Fin 4 → Fin U)
    (retDrv log rawDrv rawDst rawLog : Fin U) (r : Request) (capR : Nat)
    (H : Fin U → Nat) (A A' : Fin U → List Bool)
    (h : (code mask packet maskSlots hminj slots hsinj slot ret retDrv log
        rawDrv rawDst rawLog).Ready r (fuel mask packet r) H (dockH slots H (fun _ => 0)) A A') :
    (code mask packet maskSlots hminj slots hsinj slot ret retDrv log
      rawDrv rawDst rawLog).base.Ready r (fuel mask packet r) H
      (dockH slots H (fun _ => 0)) A A' :=
  MaskSeedCode.project _ r _ _ _ _ _ h

end
end SLoad.MaskReady
