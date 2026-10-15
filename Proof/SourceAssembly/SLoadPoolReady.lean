import Proof.SourceAssembly.SLoadPool

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace SLoad.PoolReady
open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairRepresentation SupplierEstimator SupplierPipeline SourceInterfaces
open RepairSource.VerifierDecoding
open NearCubicWires.P1Closure
open FixedLivePackets PacketProduction MaskedFamilySource
noncomputable section

/-- `MaskSeedCode.Ready` for the physical loader, at the pool-shaped exit that
`MaskFamilyCode.Prepared` demands. -/
theorem pool_seed_ready {U : Nat} (mask : MaskProducer) {selector : CyclicChoice.Laws}
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
    (hArg : A rawLog = List.replicate capL false)
    (poolSlots : Fin 373 → Fin U) (poolReserve : Fin 373 → Nat)
    (hpS : ∀ (j : Fin 13) (i : Fin 373), slot j ≠ poolSlots i)
    (hpM : ∀ (j : Fin (5 + mask.work)) (i : Fin 373), maskSlots j ≠ poolSlots i)
    (hpP : ∀ (j : Fin packet.ordinary.program.tapeCount) (i : Fin 373), slots j ≠ poolSlots i)
    (hpR : ∀ i : Fin 373, poolSlots i ≠ rawDst)
    (hpH : ∀ i, H (poolSlots i) = 0)
    (hpA : ∀ i, A (poolSlots i) = ZeroPadding.pad (poolReserve i)
      (BinaryCacheColdRun.input (CachedFamilyLoader.cacheArgs a (r.family a)) i)) :
    ∃ (poolH : Fin U → Nat) (poolA : Fin U → List Bool),
      (MaskReady.code mask packet maskSlots hminj slots hsinj slot ret retDrv log
          rawDrv rawDst rawLog).Ready r (MaskReady.fuel mask packet r) H
        (dockH poolSlots poolH (fun _ => 0)) A
        (install poolSlots poolA (fun i => ZeroPadding.pad (poolReserve i)
          (BinaryCacheColdRun.input (CachedFamilyLoader.cacheArgs a (r.family a)) i))) := by
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
        rw [Function.update_self, hword0, MaskReady.entry_one, ZeroPadding.pad_zero,
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
  have ready : (MaskReady.code mask packet maskSlots hminj slots hsinj slot ret retDrv log
      rawDrv rawDst rawLog).Ready r (MaskReady.fuel mask packet r) H
      (dockH slots H (fun _ => 0)) A
      (Function.update (install slots ambientA
        (fun i => ZeroPadding.pad (RequestSuffix.reserve blankP i) (Bp i))) rawDst
        (ZeroPadding.pad capR (frame (r.raw selector a)))) := by
    refine ⟨MaskInput.reserve blank, H, Function.update A (slot 1) (List.replicate r.q true),
      RequestSuffix.reserve blankP, H, ambientA, LeadDriver.prefixFuel a r,
      SuffixFrame.cost r.q r.nativeWord.length (r.supportWord a).length (r.indexWord a).length
        (r.topWord a).length,
      Tail.cost (r.raw selector a).length, e1, ?_, ?_, Nat.le_refl _⟩
    · intro B hB hword
      have hbb : B = B0 := huniq0 B hB
      subst hbb
      exact hsuf
    · intro B hB hraw
      have hbb : B = Bp := huniqp B hB
      subst hbb
      exact htail
  -- the pool slots are outside every working family, so the loader left them alone
  have hframe : ∀ i : Fin 373,
      Function.update (install slots ambientA
        (fun i => ZeroPadding.pad (RequestSuffix.reserve blankP i) (Bp i))) rawDst
        (ZeroPadding.pad capR (frame (r.raw selector a))) (poolSlots i)
      = ZeroPadding.pad (poolReserve i)
        (BinaryCacheColdRun.input (CachedFamilyLoader.cacheArgs a (r.family a)) i) := by
    intro i
    rw [Function.update_of_ne (hpR i),
      install_other slots ambientA _ (poolSlots i) (fun j => hpP j i),
      hAmb (poolSlots i) (fun j => hpS j i) (fun j => hpM j i)]
    exact hpA i
  refine ⟨dockH slots H (fun _ => 0), _,
    Pool.reindex _ r _ H _ A _ poolSlots poolReserve ?_ hframe ready⟩
  intro i
  rw [dockH_other slots H (fun _ => 0) (poolSlots i) (fun j => hpP j i)]
  exact hpH i

/-- The same at the concrete ambient layout of `SLoad.Geometry`: no slot
geometry is left as a hypothesis, and `SLoad.Pool.residency` reduces `hpA` to
four resident words plus a zero backing. -/
theorem pool_ready_at (mask : MaskProducer) {selector : CyclicChoice.Laws}
    {a : DecompositionAlgorithm} (packet : PacketWriter selector a)
    (r : Request) (cap capR capD capL : Nat) (uK um : List Bool)
    (hk : uK.length = normalizedLiveCount r.q r.liveScale)
    (hmm : um.length = (r.family a).occurrences.length)
    (cs : (r.supportWord a).length ≤ cap) (cq : 4 * r.q + 3 ≤ cap)
    (ck : 4 * uK.length + 3 ≤ cap) (cm : 4 * um.length + 3 ≤ cap)
    (cq2 : 2 * r.q + 1 ≤ cap) (cn : 2 * r.nativeWord.length + 1 ≤ cap)
    (cs2 : 2 * (r.supportWord a).length + 1 ≤ cap) (ci : 2 * (r.indexWord a).length + 1 ≤ cap)
    (ct : 2 * (r.topWord a).length + 1 ≤ cap)
    (cL : 2 * (r.raw selector a).length + 1 ≤ capL)
    (blank : Fin (5 + mask.work) → Nat)
    (blankP : Fin packet.ordinary.program.tapeCount → Nat)
    (H : Fin (Geometry.univ mask.work packet.ordinary.program.tapeCount) → Nat)
    (A : Fin (Geometry.univ mask.work packet.ordinary.program.tapeCount) → List Bool)
    (hHr : ∀ i, H (Geometry.ret mask.work packet.ordinary.program.tapeCount i) = 0)
    (hHm : ∀ j, H (Geometry.maskSlots mask.work packet.ordinary.program.tapeCount j) = 0)
    (hHl : H (Geometry.log mask.work packet.ordinary.program.tapeCount) = 0)
    (hHD : H (Geometry.retDrv mask.work packet.ordinary.program.tapeCount) = 0)
    (hHsl : ∀ j, H (Geometry.slot mask.work packet.ordinary.program.tapeCount j) = 0)
    (hHs : ∀ j, H (Geometry.slots mask.work packet.ordinary.program.tapeCount j) = 0)
    (hHrd : H (Geometry.rawDrv mask.work packet.ordinary.program.tapeCount) = 0)
    (hHrt : H (Geometry.rawDst mask.work packet.ordinary.program.tapeCount) = 0)
    (hHrg : H (Geometry.rawLog mask.work packet.ordinary.program.tapeCount) = 0)
    (hAD : A (Geometry.retDrv mask.work packet.ordinary.program.tapeCount)
      = ZeroPadding.pad cap (frame (List.replicate r.q true)))
    (hA0 : A (Geometry.ret mask.work packet.ordinary.program.tapeCount 0)
      = ZeroPadding.pad cap (frame (r.supportWord a)))
    (hA1 : A (Geometry.ret mask.work packet.ordinary.program.tapeCount 1)
      = ZeroPadding.pad cap (frame (List.replicate r.q true)))
    (hA2 : A (Geometry.ret mask.work packet.ordinary.program.tapeCount 2)
      = ZeroPadding.pad cap (frame uK))
    (hA3 : A (Geometry.ret mask.work packet.ordinary.program.tapeCount 3)
      = ZeroPadding.pad cap (frame um))
    (hLive : ∀ j : Fin (5 + mask.work), j.val < 4 →
      A (Geometry.maskSlots mask.work packet.ordinary.program.tapeCount j) = [])
    (hPriv : ∀ j : Fin (5 + mask.work), 4 ≤ j.val →
      A (Geometry.maskSlots mask.work packet.ordinary.program.tapeCount j)
        = List.replicate (blank j) false)
    (hAl : A (Geometry.log mask.work packet.ordinary.program.tapeCount) = List.replicate cap false)
    (hAd : A (Geometry.slot mask.work packet.ordinary.program.tapeCount 1) = [])
    (hAsuf : ∀ j : Fin 13, j ≠ 0 → j ≠ 1 →
      A (Geometry.slot mask.work packet.ordinary.program.tapeCount j)
        = SuffixFrame.entry (MaskInput.reserve blank ⟨4, by omega⟩) 0 cap (maskData a r).word
            r.nativeWord (r.supportWord a) (r.indexWord a) (r.topWord a) j)
    (hblankP : ∀ j : Fin packet.ordinary.program.tapeCount, j.val ≠ 0 →
      A (Geometry.slots mask.work packet.ordinary.program.tapeCount j) = List.replicate (blankP j) false)
    (hArd : A (Geometry.rawDrv mask.work packet.ordinary.program.tapeCount)
      = ZeroPadding.pad capD (List.replicate (r.raw selector a).length true))
    (hArt : A (Geometry.rawDst mask.work packet.ordinary.program.tapeCount) = List.replicate capR false)
    (hArg : A (Geometry.rawLog mask.work packet.ordinary.program.tapeCount) = List.replicate capL false)
    (poolReserve : Fin 373 → Nat)
    (hpH : ∀ i, H (Geometry.pool mask.work packet.ordinary.program.tapeCount i) = 0)
    (hpA : ∀ i, A (Geometry.pool mask.work packet.ordinary.program.tapeCount i) = ZeroPadding.pad (poolReserve i)
      (BinaryCacheColdRun.input (CachedFamilyLoader.cacheArgs a (r.family a)) i)) :
    ∃ (poolH : Fin (Geometry.univ mask.work packet.ordinary.program.tapeCount) → Nat)
      (poolA : Fin (Geometry.univ mask.work packet.ordinary.program.tapeCount) → List Bool),
      (Geometry.layout mask packet).Ready r (MaskReady.fuel mask packet r) H
        (dockH (Geometry.pool mask.work packet.ordinary.program.tapeCount) poolH (fun _ => 0)) A
        (install (Geometry.pool mask.work packet.ordinary.program.tapeCount) poolA (fun i => ZeroPadding.pad (poolReserve i)
          (BinaryCacheColdRun.input (CachedFamilyLoader.cacheArgs a (r.family a)) i))) :=
  pool_seed_ready mask packet _ (Geometry.mask_injective _ _) _ (Geometry.slots_injective _ _) _
    (Geometry.slot_injective _ _) _ _ _ _ _ _ r cap capR capD capL uK um hk hmm
    (Geometry.mask_output _ _) (Geometry.mask_off _ _) (Geometry.packet_frame _ _)
    (Geometry.slot_off _ _) (Geometry.mask_packet _ _)
    (Geometry.ret_mask _ _) (Geometry.ret_log _ _) (Geometry.log_mask _ _)
    (Geometry.slot_ret _ _) (Geometry.slot_log _ _)
    (Geometry.drv_slot _ _) (Geometry.drv_log _ _)
    (Geometry.slot_rawDrv _ _) (Geometry.slot_rawDst _ _) (Geometry.slot_rawLog _ _)
    (Geometry.mask_rawDrv _ _) (Geometry.mask_rawDst _ _) (Geometry.mask_rawLog _ _)
    (Geometry.slots_rawDrv _ _) (Geometry.slots_rawDst _ _) (Geometry.slots_rawLog _ _)
    (Geometry.rawDrv_rawDst _ _) (Geometry.rawDrv_rawLog _ _) (Geometry.rawDst_rawLog _ _)
    cs cq ck cm cq2 cn cs2 ci ct cL blank blankP H A
    hHr hHm hHl hHD hHsl hHs hHrd hHrt hHrg hAD hA0 hA1 hA2 hA3 hLive hPriv hAl hAd hAsuf
    hblankP hArd hArt hArg (Geometry.pool mask.work packet.ordinary.program.tapeCount) poolReserve
    (Geometry.slot_pool _ _) (Geometry.mask_pool _ _) (Geometry.slots_pool _ _)
    (fun i => (Geometry.rawDst_pool _ _ i).symm) hpH hpA

end
end SLoad.PoolReady
