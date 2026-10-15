import Proof.SourceAssembly.SLoadPoolReady
import Proof.SourceAssembly.SLoadPrepared
import Proof.SourceAssembly.SourceReuse

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace NearCubicWires.SourceRequest
open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairRepresentation SupplierEstimator SupplierPipeline SourceInterfaces
open RepairSource.VerifierDecoding
open NearCubicWires.P1Closure
open FixedLivePackets PacketProduction MaskedFamilySource
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
noncomputable section
attribute [local irreducible] NearCubicWires.P1TopDownPaidPayload.tapes

/-! ## 0. The request of one monomial -/

def monomialRequest (L target : Nat) (mode : Bool) {q : Nat} {circuit : BooleanCircuit q}
    {pcpp : PointwisePCPP circuit} (atoms : List (C10TotalDecode.Atom pcpp))
    (four : atoms.length ≤ 4) : Request :=
  if mode then
    .sym ⟨q, atoms.map C10NaturalModeAtoms.nativeSymmetricAtom⟩
      (by simp only [List.length_map]; exact four) L target
  else
    .thr ⟨q, atoms.map C10NaturalModeAtoms.nativeThresholdAtom⟩
      (by simp only [List.length_map]; exact four) L target

/-- SYM branch: the monomial's request family is `Packets.request` (definitionally). -/
theorem monomialRequest_family_sym (sources : EightSources) (L target : Nat)
    {q : Nat} {circuit : BooleanCircuit q} {pcpp : PointwisePCPP circuit}
    (atoms : List (C10TotalDecode.Atom pcpp)) (four : atoms.length ≤ 4) :
    (monomialRequest L target true atoms four).family (decompositionOf sources)
      = Packets.request sources L target true atoms := rfl

/-- THR branch: the monomial's request family is `Packets.request` (definitionally). -/
theorem monomialRequest_family_thr (sources : EightSources) (L target : Nat)
    {q : Nat} {circuit : BooleanCircuit q} {pcpp : PointwisePCPP circuit}
    (atoms : List (C10TotalDecode.Atom pcpp)) (four : atoms.length ≤ 4) :
    (monomialRequest L target false atoms four).family (decompositionOf sources)
      = Packets.request sources L target false atoms := rfl

theorem monomialRequest_q (L target : Nat) (mode : Bool)
    {q : Nat} {circuit : BooleanCircuit q} {pcpp : PointwisePCPP circuit}
    (atoms : List (C10TotalDecode.Atom pcpp)) (four : atoms.length ≤ 4) :
    (monomialRequest L target mode atoms four).q = q := by
  cases mode <;> exact rfl

theorem monomialRequest_liveScale (L target : Nat) (mode : Bool)
    {q : Nat} {circuit : BooleanCircuit q} {pcpp : PointwisePCPP circuit}
    (atoms : List (C10TotalDecode.Atom pcpp)) (four : atoms.length ≤ 4) :
    (monomialRequest L target mode atoms four).liveScale = L := by
  cases mode <;> exact rfl

/-! ## 1. The resident set at the prologue's exit -/

structure Resident {U : Nat} (mask : MaskProducer) {selector : CyclicChoice.Laws}
    {a : DecompositionAlgorithm} {printer : WilliamsAlgorithm}
    (packet : PacketWriter selector a) (rows : RowProducer selector a printer)
    (maskSlots : Fin (5 + mask.work) → Fin U)
    (pslots : Fin packet.ordinary.program.tapeCount → Fin U)
    (slot : Fin 13 → Fin U) (ret : Fin 4 → Fin U) (retDrv log : Fin U)
    (familySlots : Fin (rowTapes printer rows.privateWork + 1) → Fin U)
    (poolSlots : Fin 373 → Fin U) (rewindSlots : Fin 3 → Fin U)
    (s1 d1 l1 s2 d2 l2 lenTape : Fin U)
    (r : Request) (layout : Packets.Layout a (r.family a) (geometryOf selector a r))
    (caps : RowCaps) (H : Fin U → Nat) (A : Fin U → List Bool) where
  /-- shared pad of the lead/suffix words and of the lead's log -/
  cap : Nat
  uK : List Bool
  um : List Bool
  blank : Fin (5 + mask.work) → Nat
  blankP : Fin packet.ordinary.program.tapeCount → Nat
  poolReserve : Fin 373 → Nat
  familyReserve : Fin (rowTapes printer rows.privateWork + 1) → Nat
  capS1 : Nat
  capD1 : Nat
  capL1 : Nat
  capS2 : Nat
  capD2 : Nat
  capL2 : Nat
  capLen : Nat

  /-- lead: unary `q`, framed (unframed by the lead onto the suffix driver `slot 1`) -/
  w_retDrv : A retDrv = ZeroPadding.pad cap (RepairOrdinary.frame (List.replicate r.q true))
  /-- lead → mask input 0: the support bitmaps, framed per occurrence, framed -/
  w_ret0 : A (ret 0) = ZeroPadding.pad cap (RepairOrdinary.frame (r.supportWord a))
  /-- lead → mask input 1: unary `q` -/
  w_ret1 : A (ret 1) = ZeroPadding.pad cap (RepairOrdinary.frame (List.replicate r.q true))
  /-- lead → mask input 2: any word of length `K = normalizedLiveCount q L` -/
  w_ret2 : A (ret 2) = ZeroPadding.pad cap (RepairOrdinary.frame uK)
  len_uK : uK.length = normalizedLiveCount r.q r.liveScale
  /-- lead → mask input 3: any word of length `m = #occurrences` -/
  w_ret3 : A (ret 3) = ZeroPadding.pad cap (RepairOrdinary.frame um)
  len_um : um.length = (r.family a).occurrences.length
  /-- suffix field 3: the native word -/
  w_native : A (slot 3) = ZeroPadding.pad cap (RepairOrdinary.frame r.nativeWord)
  /-- suffix field 4: the support word -/
  w_support : A (slot 4) = ZeroPadding.pad cap (RepairOrdinary.frame (r.supportWord a))
  /-- suffix field 5: the child-count index word -/
  w_index : A (slot 5) = ZeroPadding.pad cap (RepairOrdinary.frame (r.indexWord a))
  /-- suffix field 6: the TOP word (`[]` for SYM) -/
  w_top : A (slot 6) = ZeroPadding.pad cap (RepairOrdinary.frame (r.topWord a))
  /-- cold-cache input: 98 child list, 224 `UnaryTemplate q`, 225 `UnaryTemplate K`,
  226 membership bits, zero backing elsewhere (`SLoad.Pool.residency`) -/
  w_pool : ∀ i, A (poolSlots i) = ZeroPadding.pad (poolReserve i)
    (BinaryCacheColdRun.input (CachedFamilyLoader.cacheArgs a (r.family a)) i)
  /-- setup source 1: the BARE packet input word (mask field included) -/
  w_input : A s1 = ZeroPadding.pad capS1 (r.input a)
  /-- setup driver 1: its unary length -/
  w_inputLen : A d1 = ZeroPadding.pad capD1 (List.replicate (r.input a).length true)
  /-- setup source 2: the bare row metadata bits `[w, degree, C] ++ caps` -/
  w_meta : A s2 = ZeroPadding.pad capS2 (SLoad.Setup.metaBits layout.w layout.degree layout.C caps)
  /-- setup driver 2: its unary length -/
  w_metaLen : A d2 = ZeroPadding.pad capD2
    (List.replicate (SLoad.Setup.metaBits layout.w layout.degree layout.C caps).length true)
  /-- S's driver calc: `1^L`, `L` the child-list word's length -/
  w_len : A lenTape = ZeroPadding.pad capLen (List.replicate
    (exactListWord (CachedFamilyLoader.cacheArgs a (r.family a)).gs).length true)
  -- (H1) zero backing --------------------------------------------------------------------------
  b_log : A log = List.replicate cap false
  b_maskLive : ∀ j : Fin (5 + mask.work), j.val < 4 → A (maskSlots j) = []
  b_maskPriv : ∀ j : Fin (5 + mask.work), 4 ≤ j.val → A (maskSlots j) = List.replicate (blank j) false
  b_slot1 : A (slot 1) = []
  b_slot2 : A (slot 2) = List.replicate cap false
  b_slot7 : A (slot 7) = []
  b_slot8 : A (slot 8) = List.replicate cap false
  b_slotTail : ∀ j : Fin 13, 9 ≤ j.val → A (slot j) = []
  b_packet : ∀ j : Fin packet.ordinary.program.tapeCount, j.val ≠ 0 →
    A (pslots j) = List.replicate (blankP j) false
  b_l1 : A l1 = List.replicate capL1 false
  b_l2 : A l2 = List.replicate capL2 false
  b_family : ∀ i : Fin (rowTapes printer rows.privateWork + 1), i.val ≠ 0 → i.val ≠ 262 →
    A (familySlots i) = List.replicate (familyReserve i) false
  -- (S) rewind driver and log (read by `Prepared`'s rewind conjuncts) ---------------------------
  s_rewind1 : A (rewindSlots 1) = List.replicate caps.descriptorReserve true
  s_rewind2 : A (rewindSlots 2) = List.replicate caps.descriptorReserve false
  -- heads ----------------------------------------------------------------------------------------
  hH_ret : ∀ i, H (ret i) = 0
  hH_mask : ∀ j, H (maskSlots j) = 0
  hH_log : H log = 0
  hH_retDrv : H retDrv = 0
  hH_slot : ∀ j, H (slot j) = 0
  hH_packet : ∀ j, H (pslots j) = 0
  hH_pool : ∀ i, H (poolSlots i) = 0
  hH_family : ∀ i, H (familySlots i) = 0
  hH_s1 : H s1 = 0
  hH_d1 : H d1 = 0
  hH_l1 : H l1 = 0
  hH_s2 : H s2 = 0
  hH_d2 : H d2 = 0
  hH_l2 : H l2 = 0
  hH_len : H lenTape = 0
  hH_rewind1 : H (rewindSlots 1) = 0
  hH_rewind2 : H (rewindSlots 2) = 0
  -- capacities -----------------------------------------------------------------------------------
  cs : (r.supportWord a).length ≤ cap
  cq : 4 * r.q + 3 ≤ cap
  ck : 4 * uK.length + 3 ≤ cap
  cm : 4 * um.length + 3 ≤ cap
  cq2 : 2 * r.q + 1 ≤ cap
  cn : 2 * r.nativeWord.length + 1 ≤ cap
  cs2 : 2 * (r.supportWord a).length + 1 ≤ cap
  ci : 2 * (r.indexWord a).length + 1 ≤ cap
  ct : 2 * (r.topWord a).length + 1 ≤ cap
  cl1 : 2 * (r.input a).length + 1 ≤ capL1
  cl2 : 2 * (SLoad.Setup.metaBits layout.w layout.degree layout.C caps).length + 1 ≤ capL2

/-! ## 2. The seed conjunct -/

/-- The seed code: the loader's lead/suffix with the identity tail. -/
def seedCode {U : Nat} (mask : MaskProducer) {selector : CyclicChoice.Laws}
    {a : DecompositionAlgorithm} (packet : PacketWriter selector a)
    (maskSlots : Fin (5 + mask.work) → Fin U) (hminj : Function.Injective maskSlots)
    (pslots : Fin packet.ordinary.program.tapeCount → Fin U) (hsinj : Function.Injective pslots)
    (slot : Fin 13 → Fin U) (ret : Fin 4 → Fin U) (retDrv log rawDrv rawDst rawLog : Fin U) :
    MaskSeedCode mask packet U :=
  SourceAssemblyReuse.identityTail
    (SLoad.MaskReady.code mask packet maskSlots hminj pslots hsinj slot ret retDrv log
      rawDrv rawDst rawLog)

/-- The seed fuel: exactly the sum `Ready` asks for, tail fuel `0`. -/
def seedFuel (mask : MaskProducer) {selector : CyclicChoice.Laws} {a : DecompositionAlgorithm}
    (packet : PacketWriter selector a) (r : Request) : Nat :=
  (SLoad.LeadDriver.prefixFuel a r + 1 +
    (maskBudget mask.coefficient mask.degree (maskData a r) + 1 +
      SLoad.SuffixFrame.cost r.q r.nativeWord.length (r.supportWord a).length
        (r.indexWord a).length (r.topWord a).length)) + 1 +
    (packetBudget a packet.coefficient packet.degree r + 1 + 0)

section seed
variable {U : Nat} {mask : MaskProducer} {selector : CyclicChoice.Laws}
  {a : DecompositionAlgorithm} {printer : WilliamsAlgorithm}
  {packet : PacketWriter selector a} {rows : RowProducer selector a printer}
  {maskSlots : Fin (5 + mask.work) → Fin U}
  {pslots : Fin packet.ordinary.program.tapeCount → Fin U}
  {slot : Fin 13 → Fin U} {ret : Fin 4 → Fin U} {retDrv log : Fin U}
  {familySlots : Fin (rowTapes printer rows.privateWork + 1) → Fin U}
  {poolSlots : Fin 373 → Fin U} {rewindSlots : Fin 3 → Fin U}
  {s1 d1 l1 s2 d2 l2 lenTape : Fin U}
  {r : Request} {layout : Packets.Layout a (r.family a) (geometryOf selector a r)}
  {caps : RowCaps} {H : Fin U → Nat} {A : Fin U → List Bool}

/-- The verbatim suffix-entry premise of `pool_seed_ready` (`hAsuf`), from the explicit fields. -/
theorem Resident.suffix_entry
    (res : Resident mask packet rows maskSlots pslots slot ret retDrv log familySlots poolSlots
      rewindSlots s1 d1 l1 s2 d2 l2 lenTape r layout caps H A) :
    ∀ j : Fin 13, j ≠ 0 → j ≠ 1 → A (slot j)
      = SLoad.SuffixFrame.entry (SLoad.MaskInput.reserve res.blank ⟨4, by omega⟩) 0 res.cap
          (maskData a r).word r.nativeWord (r.supportWord a) (r.indexWord a) (r.topWord a) j := by
  intro j h0 h1
  fin_cases j
  · exact absurd rfl h0
  · exact absurd rfl h1
  · exact res.b_slot2
  · exact res.w_native
  · exact res.w_support
  · exact res.w_index
  · exact res.w_top
  · exact res.b_slot7
  · exact res.b_slot8
  · exact res.b_slotTail _ (by decide)
  · exact res.b_slotTail _ (by decide)
  · exact res.b_slotTail _ (by decide)
  · exact res.b_slotTail _ (by decide)

end seed

theorem pad_replicate_false (m n : Nat) :
    ZeroPadding.pad m (List.replicate n false) = List.replicate (max m n) false := by
  rw [← SLoad.Words.pad_nil n, SourceAssemblyReuse.pad_pad, SLoad.Words.pad_nil]

/-- **Conjunct 1 at the exact bank.** `Resident` suffices for the seed's `Ready`, landing on
`Prepared`'s pool-shaped exit; the exit bank keeps the raw packet word at the packet's output tape
and every tape outside the loader's slots (`slot`, `maskSlots`, `pslots`). -/
theorem seed_ready_exact {U : Nat} (mask : MaskProducer) {selector : CyclicChoice.Laws}
    {a : DecompositionAlgorithm} {printer : WilliamsAlgorithm}
    (packet : PacketWriter selector a) (rows : RowProducer selector a printer)
    (maskSlots : Fin (5 + mask.work) → Fin U) (hminj : Function.Injective maskSlots)
    (pslots : Fin packet.ordinary.program.tapeCount → Fin U) (hsinj : Function.Injective pslots)
    (slot : Fin 13 → Fin U) (hinj : Function.Injective slot)
    (ret : Fin 4 → Fin U) (retDrv log rawDrv rawDst rawLog : Fin U)
    (familySlots : Fin (rowTapes printer rows.privateWork + 1) → Fin U)
    (poolSlots : Fin 373 → Fin U) (rewindSlots : Fin 3 → Fin U)
    (s1 d1 l1 s2 d2 l2 lenTape : Fin U)
    (hmsk : slot 0 = maskSlots ⟨4, by omega⟩)
    (hoffm : ∀ j : Fin 13, j ≠ 0 → ∀ i, maskSlots i ≠ slot j)
    (hslot0 : ∀ j : Fin packet.ordinary.program.tapeCount, j.val = 0 → pslots j = slot 11)
    (hoffp : ∀ j : Fin packet.ordinary.program.tapeCount, j.val ≠ 0 → ∀ k, slot k ≠ pslots j)
    (hmp : ∀ (j : Fin packet.ordinary.program.tapeCount) (i : Fin (5 + mask.work)),
      maskSlots i ≠ pslots j)
    (hrm : ∀ (i : Fin 4) (j : Fin (5 + mask.work)), ret i ≠ maskSlots j)
    (hrl : ∀ i, ret i ≠ log) (hlm : ∀ j, log ≠ maskSlots j)
    (hdr : ∀ i, slot 1 ≠ ret i) (hdl : slot 1 ≠ log)
    (hDd : retDrv ≠ slot 1) (hDl : retDrv ≠ log)
    (hpS : ∀ (j : Fin 13) (i : Fin 373), slot j ≠ poolSlots i)
    (hpM : ∀ (j : Fin (5 + mask.work)) (i : Fin 373), maskSlots j ≠ poolSlots i)
    (hpP : ∀ (j : Fin packet.ordinary.program.tapeCount) (i : Fin 373), pslots j ≠ poolSlots i)
    (r : Request) (layout : Packets.Layout a (r.family a) (geometryOf selector a r))
    (caps : RowCaps) (H : Fin U → Nat) (A : Fin U → List Bool)
    (res : Resident mask packet rows maskSlots pslots slot ret retDrv log familySlots poolSlots
      rewindSlots s1 d1 l1 s2 d2 l2 lenTape r layout caps H A) :
    ∃ poolA : Fin U → List Bool,
      (seedCode mask packet maskSlots hminj pslots hsinj slot ret retDrv log rawDrv rawDst
          rawLog).Ready r (seedFuel mask packet r) H (dockH poolSlots H (fun _ => 0)) A
        (install poolSlots poolA (fun i => ZeroPadding.pad (res.poolReserve i)
          (BinaryCacheColdRun.input (CachedFamilyLoader.cacheArgs a (r.family a)) i))) ∧
      poolA (pslots packet.ordinary.program.outputTape)
        = ZeroPadding.pad (SLoad.RequestSuffix.reserve res.blankP packet.ordinary.program.outputTape)
          (r.raw selector a) ∧
      (∀ x, (∀ j, slot j ≠ x) → (∀ i, maskSlots i ≠ x) → (∀ j, pslots j ≠ x) → poolA x = A x) := by
  classical
  have hdm : ∀ j, slot 1 ≠ maskSlots j := fun j => (hoffm 1 (by decide) j).symm
  have hlenq : (List.replicate r.q true).length = r.q := List.length_replicate
  -- the lead
  have e1 := SLoad.LeadDriver.lead_driver_step mask maskSlots hminj ret retDrv (slot 1) log
    hrm hrl hlm hdm hdr hdl hDd hDl a r res.cap (List.replicate r.q true) res.uK res.um
    hlenq res.len_uK res.len_um res.cs (by rw [hlenq]; exact res.cq) res.ck res.cm res.blank H A
    res.hH_ret res.hH_mask res.hH_log res.hH_retDrv (res.hH_slot 1)
    res.w_retDrv res.b_slot1 res.w_ret0 res.w_ret1 res.w_ret2 res.w_ret3
    res.b_maskLive res.b_maskPriv res.b_log
  -- the mask producer's bank is pinned
  obtain ⟨B0, _hrun0, hword0, huniq0⟩ := SLoad.Tail.mask_bank mask (maskData a r)
  have hql : (B0 ⟨4, by omega⟩).length = r.q := by
    rw [hword0]; exact SLoad.LeadDriver.word_length a r
  -- the suffix
  obtain ⟨ambientA, hsuf, hkeep⟩ := SLoad.RequestSuffix.request_suffix_step slot hinj maskSlots
    hminj packet.ordinary.program pslots hsinj a r B0 hword0 (SLoad.MaskInput.reserve res.blank)
    res.blankP 0 res.cap (by rw [hql]; exact res.cq2) res.cn res.cs2 res.ci res.ct H
    (Function.update A (slot 1) (List.replicate r.q true)) hmsk hoffm hslot0 hoffp hmp
    res.hH_mask res.hH_slot res.hH_packet
    (by
      intro j hj
      by_cases h1 : j = 1
      · subst h1
        rw [Function.update_self, hword0, SLoad.MaskReady.entry_one, ZeroPadding.pad_zero,
          SLoad.LeadDriver.word_length]
      · rw [Function.update_of_ne (fun h => h1 (hinj h)), res.suffix_entry j hj h1, hword0])
    (by
      intro j hj
      rw [Function.update_of_ne (Ne.symm (hoffp j hj 1))]
      exact res.b_packet j hj)
  rw [hql] at hsuf
  have hAmb : ∀ x, (∀ j : Fin 13, slot j ≠ x) → (∀ i, maskSlots i ≠ x) → ambientA x = A x := by
    intro x h13 hmk
    rw [hkeep x h13, install_other maskSlots _ _ x hmk,
      Function.update_of_ne (Ne.symm (h13 1))]
  -- the packet bank is pinned
  obtain ⟨Bp, houtp, huniqp⟩ := SLoad.Tail.packet_bank packet r
  let endA : Fin U → List Bool :=
    install pslots ambientA (fun i => ZeroPadding.pad (SLoad.RequestSuffix.reserve res.blankP i) (Bp i))
  have hHp : dockH pslots H (fun _ => 0) = H := SLoad.dockH_existing pslots H _ res.hH_packet
  have hpoolH : dockH poolSlots H (fun _ => 0) = H := SLoad.dockH_existing poolSlots H _ res.hH_pool
  have hpoolA : install poolSlots endA (fun i => ZeroPadding.pad (res.poolReserve i)
      (BinaryCacheColdRun.input (CachedFamilyLoader.cacheArgs a (r.family a)) i)) = endA := by
    apply install_existing
    intro j
    show install pslots ambientA _ (poolSlots j) = _
    rw [install_other pslots ambientA _ (poolSlots j) (fun i => hpP i j),
      hAmb (poolSlots j) (fun i => hpS i j) (fun i => hpM i j)]
    exact res.w_pool j
  refine ⟨endA, ?_, ?_, ?_⟩
  · rw [hpoolH, hpoolA]
    refine ⟨SLoad.MaskInput.reserve res.blank, H,
      Function.update A (slot 1) (List.replicate r.q true),
      SLoad.RequestSuffix.reserve res.blankP, H, ambientA, SLoad.LeadDriver.prefixFuel a r,
      SLoad.SuffixFrame.cost r.q r.nativeWord.length (r.supportWord a).length
        (r.indexWord a).length (r.topWord a).length, 0, e1, ?_, ?_, le_refl _⟩
    · intro B hB hword
      have hbb : B = B0 := huniq0 B hB
      subst hbb
      exact hsuf
    · intro B hB hraw
      have hbb : B = Bp := huniqp B hB
      subst hbb
      show Step (SourceAssemblyReuse.haltMachine U) 0 (dockH pslots H (fun _ => 0))
        endA H endA
      rw [hHp]
      exact SourceAssemblyReuse.halt_step H endA
  · show install pslots ambientA _ (pslots packet.ordinary.program.outputTape) = _
    rw [install_slot pslots hsinj, houtp]
  · intro x h13 hmk hps
    show install pslots ambientA _ x = A x
    rw [install_other pslots ambientA _ x hps]
    exact hAmb x h13 hmk

/-! ## 3. At any zero padding (the refill's clear backing) -/

/-- **Conjunct 1, padded.** For any per-tape padding `R` of the prologue's exit bank (the refill's
`replicate R false` backing), the seed is `Ready` at `Prepared`'s pool-shaped exit, with pool
reserve `max (R ∘ poolSlots) poolReserve`, the raw packet word at the packet output tape, and every
tape outside the loader's slots equal to its padded prologue-exit word. -/
theorem seed_ready {U : Nat} (mask : MaskProducer) {selector : CyclicChoice.Laws}
    {a : DecompositionAlgorithm} {printer : WilliamsAlgorithm}
    (packet : PacketWriter selector a) (rows : RowProducer selector a printer)
    (maskSlots : Fin (5 + mask.work) → Fin U) (hminj : Function.Injective maskSlots)
    (pslots : Fin packet.ordinary.program.tapeCount → Fin U) (hsinj : Function.Injective pslots)
    (slot : Fin 13 → Fin U) (hinj : Function.Injective slot)
    (ret : Fin 4 → Fin U) (retDrv log rawDrv rawDst rawLog : Fin U)
    (familySlots : Fin (rowTapes printer rows.privateWork + 1) → Fin U)
    (poolSlots : Fin 373 → Fin U) (rewindSlots : Fin 3 → Fin U)
    (s1 d1 l1 s2 d2 l2 lenTape : Fin U)
    (hmsk : slot 0 = maskSlots ⟨4, by omega⟩)
    (hoffm : ∀ j : Fin 13, j ≠ 0 → ∀ i, maskSlots i ≠ slot j)
    (hslot0 : ∀ j : Fin packet.ordinary.program.tapeCount, j.val = 0 → pslots j = slot 11)
    (hoffp : ∀ j : Fin packet.ordinary.program.tapeCount, j.val ≠ 0 → ∀ k, slot k ≠ pslots j)
    (hmp : ∀ (j : Fin packet.ordinary.program.tapeCount) (i : Fin (5 + mask.work)),
      maskSlots i ≠ pslots j)
    (hrm : ∀ (i : Fin 4) (j : Fin (5 + mask.work)), ret i ≠ maskSlots j)
    (hrl : ∀ i, ret i ≠ log) (hlm : ∀ j, log ≠ maskSlots j)
    (hdr : ∀ i, slot 1 ≠ ret i) (hdl : slot 1 ≠ log)
    (hDd : retDrv ≠ slot 1) (hDl : retDrv ≠ log)
    (hpS : ∀ (j : Fin 13) (i : Fin 373), slot j ≠ poolSlots i)
    (hpM : ∀ (j : Fin (5 + mask.work)) (i : Fin 373), maskSlots j ≠ poolSlots i)
    (hpP : ∀ (j : Fin packet.ordinary.program.tapeCount) (i : Fin 373), pslots j ≠ poolSlots i)
    (r : Request) (layout : Packets.Layout a (r.family a) (geometryOf selector a r))
    (caps : RowCaps) (H : Fin U → Nat) (A : Fin U → List Bool)
    (res : Resident mask packet rows maskSlots pslots slot ret retDrv log familySlots poolSlots
      rewindSlots s1 d1 l1 s2 d2 l2 lenTape r layout caps H A) (R : Fin U → Nat) :
    ∃ poolA : Fin U → List Bool,
      (seedCode mask packet maskSlots hminj pslots hsinj slot ret retDrv log rawDrv rawDst
          rawLog).Ready r (seedFuel mask packet r) H (dockH poolSlots H (fun _ => 0))
        (fun x => ZeroPadding.pad (R x) (A x))
        (install poolSlots poolA (fun i => ZeroPadding.pad (max (R (poolSlots i)) (res.poolReserve i))
          (BinaryCacheColdRun.input (CachedFamilyLoader.cacheArgs a (r.family a)) i))) ∧
      poolA (pslots packet.ordinary.program.outputTape)
        = ZeroPadding.pad (max (R (pslots packet.ordinary.program.outputTape))
            (SLoad.RequestSuffix.reserve res.blankP packet.ordinary.program.outputTape))
          (r.raw selector a) ∧
      (∀ x, (∀ j, slot j ≠ x) → (∀ i, maskSlots i ≠ x) → (∀ j, pslots j ≠ x) →
        poolA x = ZeroPadding.pad (R x) (A x)) := by
  obtain ⟨poolA0, hready, hraw, hframe⟩ := seed_ready_exact mask packet rows maskSlots hminj
    pslots hsinj slot hinj ret retDrv log rawDrv rawDst rawLog familySlots poolSlots rewindSlots
    s1 d1 l1 s2 d2 l2 lenTape hmsk hoffm hslot0 hoffp hmp hrm hrl hlm hdr hdl hDd hDl hpS hpM hpP
    r layout caps H A res
  have hp := SourceAssemblyReuse.ready_pad _ r _ H _ A _ R hready
  rw [SourceAssemblyReuse.pad_install] at hp
  simp only [SourceAssemblyReuse.pad_pad] at hp
  refine ⟨fun x => ZeroPadding.pad (R x) (poolA0 x), hp, ?_, ?_⟩
  · show ZeroPadding.pad _ (poolA0 _) = _
    rw [hraw, SourceAssemblyReuse.pad_pad]
  · intro x h13 hmk hps
    show ZeroPadding.pad (R x) (poolA0 x) = _
    rw [hframe x h13 hmk hps]

/-! ## 4. The setup conjunct -/

/-- A tape the seed loader and the cold run never touch. -/
def Outside {U tc w : Nat} (slot : Fin 13 → Fin U) (maskSlots : Fin (5 + w) → Fin U)
    (pslots : Fin tc → Fin U) (poolSlots : Fin 373 → Fin U) (x : Fin U) : Prop :=
  (∀ j, slot j ≠ x) ∧ (∀ i, maskSlots i ≠ x) ∧ (∀ j, pslots j ≠ x) ∧ (∀ i, poolSlots i ≠ x)

/-- The family reserve the setup conjunct lands on: the cold cache's own reserve at family port 0
(aliased to pool 34), the raw word's pad at port 262 (aliased to the packet output), and the padded
prologue backing elsewhere. -/
def famReserve {U : Nat} {mask : MaskProducer} {selector : CyclicChoice.Laws}
    {a : DecompositionAlgorithm} {printer : WilliamsAlgorithm}
    {packet : PacketWriter selector a} {rows : RowProducer selector a printer}
    {maskSlots : Fin (5 + mask.work) → Fin U}
    {pslots : Fin packet.ordinary.program.tapeCount → Fin U}
    {slot : Fin 13 → Fin U} {ret : Fin 4 → Fin U} {retDrv log : Fin U}
    {familySlots : Fin (rowTapes printer rows.privateWork + 1) → Fin U}
    {poolSlots : Fin 373 → Fin U} {rewindSlots : Fin 3 → Fin U}
    {s1 d1 l1 s2 d2 l2 lenTape : Fin U}
    {r : Request} {layout : Packets.Layout a (r.family a) (geometryOf selector a r)}
    {caps : RowCaps} {H : Fin U → Nat} {A : Fin U → List Bool}
    (res : Resident mask packet rows maskSlots pslots slot ret retDrv log familySlots poolSlots
      rewindSlots s1 d1 l1 s2 d2 l2 lenTape r layout caps H A) (R : Fin U → Nat) :
    Fin (rowTapes printer rows.privateWork + 1) → Nat := fun i =>
  if i.val = 0 then max (R (poolSlots 34)) (res.poolReserve 34)
  else if i.val = 262 then max (R (pslots packet.ordinary.program.outputTape))
    (SLoad.RequestSuffix.reserve res.blankP packet.ordinary.program.outputTape)
  else max (R (familySlots i)) (res.familyReserve i)

/-- **Conjunct 2.** From the seed's exit (any `poolA` with the raw word at the packet output and the
padded prologue words outside the loader), after the cold run (pool slots now `output`), the
setup loader frames `r.input a` and the metadata onto the row family's request/caps ports, with the
family bank at `rowPublicInput`. Every premise that is not the seed's exit or the cold run's output
is a `Resident` field. -/
theorem setup_ready {U : Nat} (mask : MaskProducer) {selector : CyclicChoice.Laws}
    {a : DecompositionAlgorithm} {printer : WilliamsAlgorithm}
    (packet : PacketWriter selector a) (rows : RowProducer selector a printer)
    (maskSlots : Fin (5 + mask.work) → Fin U)
    (pslots : Fin packet.ordinary.program.tapeCount → Fin U)
    (slot : Fin 13 → Fin U) (ret : Fin 4 → Fin U) (retDrv log : Fin U)
    (familySlots : Fin (rowTapes printer rows.privateWork + 1) → Fin U)
    (hfinj : Function.Injective familySlots)
    (poolSlots : Fin 373 → Fin U) (hpinj : Function.Injective poolSlots)
    (rewindSlots : Fin 3 → Fin U)
    (s1 d1 l1 s2 d2 l2 lenTape : Fin U)
    (hpP : ∀ (j : Fin packet.ordinary.program.tapeCount) (i : Fin 373), pslots j ≠ poolSlots i)
    (hpool0 : ∀ i : Fin (rowTapes printer rows.privateWork + 1), i.val = 0 →
      familySlots i = poolSlots 34)
    (hraw262 : ∀ i : Fin (rowTapes printer rows.privateWork + 1), i.val = 262 →
      familySlots i = pslots packet.ordinary.program.outputTape)
    (hfamOut : ∀ i : Fin (rowTapes printer rows.privateWork + 1), i.val ≠ 0 → i.val ≠ 262 →
      Outside slot maskSlots pslots poolSlots (familySlots i))
    (os1 : Outside slot maskSlots pslots poolSlots s1) (od1 : Outside slot maskSlots pslots poolSlots d1)
    (ol1 : Outside slot maskSlots pslots poolSlots l1) (os2 : Outside slot maskSlots pslots poolSlots s2)
    (od2 : Outside slot maskSlots pslots poolSlots d2) (ol2 : Outside slot maskSlots pslots poolSlots l2)
    (e1 : s1 ≠ d1) (e2 : s1 ≠ familySlots (rowRequestPort printer rows.privateWork))
    (e3 : s1 ≠ l1) (e4 : d1 ≠ familySlots (rowRequestPort printer rows.privateWork))
    (e5 : d1 ≠ l1) (e6 : familySlots (rowRequestPort printer rows.privateWork) ≠ l1)
    (k1 : s2 ≠ d2) (k2 : s2 ≠ familySlots (rowCapsPort printer rows.privateWork))
    (k3 : s2 ≠ l2) (k4 : d2 ≠ familySlots (rowCapsPort printer rows.privateWork))
    (k5 : d2 ≠ l2) (k6 : familySlots (rowCapsPort printer rows.privateWork) ≠ l2)
    (m1 : familySlots (rowRequestPort printer rows.privateWork) ≠ s2)
    (m2 : familySlots (rowRequestPort printer rows.privateWork) ≠ d2)
    (m4 : familySlots (rowRequestPort printer rows.privateWork) ≠ l2)
    (r : Request) (layout : Packets.Layout a (r.family a) (geometryOf selector a r))
    (caps : RowCaps) (H : Fin U → Nat) (A : Fin U → List Bool)
    (res : Resident mask packet rows maskSlots pslots slot ret retDrv log familySlots poolSlots
      rewindSlots s1 d1 l1 s2 d2 l2 lenTape r layout caps H A) (R : Fin U → Nat)
    (poolA : Fin U → List Bool)
    (hraw : poolA (pslots packet.ordinary.program.outputTape)
      = ZeroPadding.pad (max (R (pslots packet.ordinary.program.outputTape))
          (SLoad.RequestSuffix.reserve res.blankP packet.ordinary.program.outputTape))
        (r.raw selector a))
    (hframe : ∀ x, (∀ j, slot j ≠ x) → (∀ i, maskSlots i ≠ x) → (∀ j, pslots j ≠ x) →
      poolA x = ZeroPadding.pad (R x) (A x)) :
    Step (SLoad.Setup.machine s1 d1 (familySlots (rowRequestPort printer rows.privateWork)) l1
        s2 d2 (familySlots (rowCapsPort printer rows.privateWork)) l2)
      (SLoad.Setup.cost (r.input a).length
        (SLoad.Setup.metaBits layout.w layout.degree layout.C caps).length)
      (dockH poolSlots H (fun _ => 0))
      (install poolSlots poolA (fun i => ZeroPadding.pad (max (R (poolSlots i)) (res.poolReserve i))
        (BinaryCacheColdRun.output (CachedFamilyLoader.cacheArgs a (r.family a)) i)))
      (dockH familySlots H (fun _ => 0))
      (install familySlots
        (SLoad.Prepared.setupExit selector a printer rows.privateWork r layout caps familySlots
          (famReserve res R)
          (install poolSlots poolA (fun i => ZeroPadding.pad (max (R (poolSlots i)) (res.poolReserve i))
            (BinaryCacheColdRun.output (CachedFamilyLoader.cacheArgs a (r.family a)) i))))
        (fun i => ZeroPadding.pad (famReserve res R i)
          (rowPublicInput selector a printer rows.privateWork r layout caps i))) := by
  classical
  set cold : Fin U → List Bool :=
    install poolSlots poolA (fun i => ZeroPadding.pad (max (R (poolSlots i)) (res.poolReserve i))
      (BinaryCacheColdRun.output (CachedFamilyLoader.cacheArgs a (r.family a)) i)) with hcold
  have hout : ∀ x, Outside slot maskSlots pslots poolSlots x → cold x = ZeroPadding.pad (R x) (A x) := by
    intro x ⟨h1, h2, h3, h4⟩
    rw [hcold, install_other poolSlots poolA _ x h4]
    exact hframe x h1 h2 h3
  have hreq0 : (rowRequestPort printer rows.privateWork).val ≠ 0 := by
    simp only [rowRequestPort]; omega
  have hreq262 : (rowRequestPort printer rows.privateWork).val ≠ 262 := by
    simp only [rowRequestPort]; omega
  have hcap0 : (rowCapsPort printer rows.privateWork).val ≠ 0 := by
    simp only [rowCapsPort]; omega
  have hcap262 : (rowCapsPort printer rows.privateWork).val ≠ 262 := by
    simp only [rowCapsPort]; omega
  have hfr : ∀ i : Fin (rowTapes printer rows.privateWork + 1), i.val ≠ 0 → i.val ≠ 262 →
      famReserve res R i = max (R (familySlots i)) (res.familyReserve i) := by
    intro i h0 h262
    simp only [famReserve, if_neg h0, if_neg h262]
  have hfb : ∀ i : Fin (rowTapes printer rows.privateWork + 1), i.val ≠ 0 → i.val ≠ 262 →
      cold (familySlots i) = List.replicate (famReserve res R i) false := by
    intro i h0 h262
    rw [hout _ (hfamOut i h0 h262), res.b_family i h0 h262, pad_replicate_false, hfr i h0 h262]
  have step := SLoad.Prepared.setup_exit_step (selector := selector) printer rows.privateWork layout caps poolSlots
    (fun i => max (R (poolSlots i)) (res.poolReserve i)) familySlots hfinj (famReserve res R)
    s1 d1 l1 s2 d2 l2 H cold
    (max (R s1) res.capS1) (max (R d1) res.capD1) (max (R l1) res.capL1)
    (max (R s2) res.capS2) (max (R d2) res.capD2) (max (R l2) res.capL2)
    (le_trans res.cl1 (le_max_right _ _)) (le_trans res.cl2 (le_max_right _ _))
    res.hH_pool
    (fun i => by rw [hcold]; exact install_slot poolSlots hpinj poolA _ i)
    res.hH_family e1 e2 e3 e4 e5 e6 k1 k2 k3 k4 k5 k6 m1 m2 m4
    res.hH_s1 res.hH_d1 res.hH_l1 res.hH_s2 res.hH_d2 res.hH_l2
    (by rw [hout s1 os1, res.w_input, SourceAssemblyReuse.pad_pad])
    (by rw [hout d1 od1, res.w_inputLen, SourceAssemblyReuse.pad_pad])
    (by rw [hout l1 ol1, res.b_l1, pad_replicate_false])
    (by rw [hout s2 os2, res.w_meta, SourceAssemblyReuse.pad_pad])
    (by rw [hout d2 od2, res.w_metaLen, SourceAssemblyReuse.pad_pad])
    (by rw [hout l2 ol2, res.b_l2, pad_replicate_false])
    (hfb _ hreq0 hreq262) (hfb _ hcap0 hcap262)
    (by
      intro i hi
      rw [hpool0 i hi, hcold, install_slot poolSlots hpinj,
        CachedFamilyLoader.cache_word a (r.family a) (geometryOf selector a r)]
      simp only [famReserve, if_pos hi])
    (by
      intro i hi
      have h0 : i.val ≠ 0 := by omega
      rw [hraw262 i hi, hcold,
        install_other poolSlots poolA _ _ (fun j => (hpP packet.ordinary.program.outputTape j).symm), hraw]
      simp only [famReserve, if_neg h0, if_pos hi])
    (fun i h0 h262 _ _ => hfb i h0 h262)
  have hcc : install poolSlots cold (fun i => ZeroPadding.pad (max (R (poolSlots i)) (res.poolReserve i))
      (BinaryCacheColdRun.output (CachedFamilyLoader.cacheArgs a (r.family a)) i)) = cold := by
    apply install_existing
    intro j
    rw [hcold]
    exact install_slot poolSlots hpinj poolA _ j
  rw [hcc] at step
  exact step

/-- **`lenTape` and every other untouched tape survive to the setup's exit**: outside the loader,
the pool and the family bank, the setup's exit bank is the padded prologue word. -/
theorem setup_frame {U : Nat} {selector : CyclicChoice.Laws} {a : DecompositionAlgorithm}
    {printer : WilliamsAlgorithm} (privateWork : Nat) (r : Request)
    (layout : Packets.Layout a (r.family a) (geometryOf selector a r)) (caps : RowCaps)
    {tc w : Nat} (slot : Fin 13 → Fin U) (maskSlots : Fin (5 + w) → Fin U) (pslots : Fin tc → Fin U)
    (familySlots : Fin (rowTapes printer privateWork + 1) → Fin U)
    (poolSlots : Fin 373 → Fin U) (familyRes : Fin (rowTapes printer privateWork + 1) → Nat)
    (poolRes : Fin 373 → Nat) (poolA A : Fin U → List Bool) (R : Fin U → Nat)
    (hframe : ∀ x, (∀ j, slot j ≠ x) → (∀ i, maskSlots i ≠ x) → (∀ j, pslots j ≠ x) →
      poolA x = ZeroPadding.pad (R x) (A x))
    (x : Fin U) (hx : Outside slot maskSlots pslots poolSlots x) (hf : ∀ i, familySlots i ≠ x) :
    install familySlots
        (SLoad.Prepared.setupExit selector a printer privateWork r layout caps familySlots familyRes
          (install poolSlots poolA (fun i => ZeroPadding.pad (poolRes i)
            (BinaryCacheColdRun.output (CachedFamilyLoader.cacheArgs a (r.family a)) i))))
        (fun i => ZeroPadding.pad (familyRes i)
          (rowPublicInput selector a printer privateWork r layout caps i)) x
      = ZeroPadding.pad (R x) (A x) := by
  obtain ⟨h1, h2, h3, h4⟩ := hx
  rw [install_other familySlots _ _ x hf, SLoad.Prepared.setupExit,
    Function.update_of_ne (fun h => hf _ h.symm), Function.update_of_ne (fun h => hf _ h.symm),
    install_other poolSlots poolA _ x h4]
  exact hframe x h1 h2 h3

/-- The child-list length `1^L` on `lenTape` at the setup's exit. -/
theorem len_at_setup {U : Nat} {mask : MaskProducer} {selector : CyclicChoice.Laws}
    {a : DecompositionAlgorithm} {printer : WilliamsAlgorithm}
    {packet : PacketWriter selector a} {rows : RowProducer selector a printer}
    {maskSlots : Fin (5 + mask.work) → Fin U}
    {pslots : Fin packet.ordinary.program.tapeCount → Fin U}
    {slot : Fin 13 → Fin U} {ret : Fin 4 → Fin U} {retDrv log : Fin U}
    {familySlots : Fin (rowTapes printer rows.privateWork + 1) → Fin U}
    {poolSlots : Fin 373 → Fin U} {rewindSlots : Fin 3 → Fin U}
    {s1 d1 l1 s2 d2 l2 lenTape : Fin U}
    {r : Request} {layout : Packets.Layout a (r.family a) (geometryOf selector a r)}
    {caps : RowCaps} {H : Fin U → Nat} {A : Fin U → List Bool}
    (res : Resident mask packet rows maskSlots pslots slot ret retDrv log familySlots poolSlots
      rewindSlots s1 d1 l1 s2 d2 l2 lenTape r layout caps H A)
    (familyRes : Fin (rowTapes printer rows.privateWork + 1) → Nat)
    (poolRes : Fin 373 → Nat) (poolA : Fin U → List Bool) (R : Fin U → Nat)
    (hframe : ∀ x, (∀ j, slot j ≠ x) → (∀ i, maskSlots i ≠ x) → (∀ j, pslots j ≠ x) →
      poolA x = ZeroPadding.pad (R x) (A x))
    (hx : Outside slot maskSlots pslots poolSlots lenTape) (hf : ∀ i, familySlots i ≠ lenTape) :
    install familySlots
        (SLoad.Prepared.setupExit selector a printer rows.privateWork r layout caps familySlots familyRes
          (install poolSlots poolA (fun i => ZeroPadding.pad (poolRes i)
            (BinaryCacheColdRun.output (CachedFamilyLoader.cacheArgs a (r.family a)) i))))
        (fun i => ZeroPadding.pad (familyRes i)
          (rowPublicInput selector a printer rows.privateWork r layout caps i)) lenTape
      = ZeroPadding.pad (max (R lenTape) res.capLen) (List.replicate
          (exactListWord (CachedFamilyLoader.cacheArgs a (r.family a)).gs).length true) := by
  rw [setup_frame rows.privateWork r layout caps slot maskSlots pslots familySlots poolSlots familyRes
    poolRes poolA A R hframe lenTape hx hf, res.w_len, SourceAssemblyReuse.pad_pad]

end
end NearCubicWires.SourceRequest
