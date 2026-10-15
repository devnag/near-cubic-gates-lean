import Proof.SourceAssembly.SLoadFinal

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace SLoad.Prepared
open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairRepresentation SupplierEstimator SupplierPipeline SourceInterfaces
open NearCubicWires.P1Closure
open RepairSource.VerifierDecoding
open FixedLivePackets PacketProduction MaskedFamilySource
noncomputable section

variable {mask : MaskProducer} {selector : CyclicChoice.Laws} {a : DecompositionAlgorithm}
  {printer : WilliamsAlgorithm} {packet : PacketWriter selector a}
  {rows : RowProducer selector a printer} {U : Nat}

/-- The rewind source word: the appended descriptor stream under the reserve
`Prepared` names, which is the larger of the family bank's own reserve at the
descriptor tape and the row package's `caps.descriptorReserve`. -/
abbrev srcWord (printer : WilliamsAlgorithm) (rows : RowProducer selector a printer)
    {r : Request} (layout : Packets.Layout a (r.family a) (geometryOf selector a r))
    (facts : ∀ row ∈ (r.family a).rows,
      Packets.PacketFacts a (r.family a) (geometryOf selector a r) row) (caps : RowCaps)
    (familyReserve : Fin (rowTapes printer rows.privateWork + 1) → Nat) : List Bool :=
  ZeroPadding.pad (max (familyReserve (Final.port printer rows)) caps.descriptorReserve)
    (CachedFamilyLoader.descriptorWord printer
      (dataList a (r.family a) (geometryOf selector a r) layout facts))

def code {U : Nat} (mask : MaskProducer) {selector : CyclicChoice.Laws}
    {a : DecompositionAlgorithm} {printer : WilliamsAlgorithm}
    (packet : PacketWriter selector a) (rows : RowProducer selector a printer)
    (maskSlots : Fin (5 + mask.work) → Fin U) (hminj : Function.Injective maskSlots)
    (pslots : Fin packet.ordinary.program.tapeCount → Fin U)
    (hsinj : Function.Injective pslots)
    (slot : Fin 13 → Fin U) (ret : Fin 4 → Fin U)
    (retDrv log rawDrv rawDst rawLog : Fin U)
    (familySlots : Fin (rowTapes printer rows.privateWork + 1) → Fin U)
    (hfinj : Function.Injective familySlots)
    (poolSlots : Fin 373 → Fin U) (hpinj : Function.Injective poolSlots)
    (rewindSlots : Fin 3 → Fin U) (hrinj : Function.Injective rewindSlots)
    (hraw : pslots packet.ordinary.program.outputTape = familySlots
      ((SharedRowLayout.headerSlots printer (rowWork rows.privateWork) 262).castAdd 1))
    (hpool : poolSlots 34 = familySlots
      ((SharedRowLayout.headerSlots printer (rowWork rows.privateWork) 0).castAdd 1))
    (hsrc : rewindSlots 0 = familySlots
      ((SharedRowLayout.descriptor printer (rowWork rows.privateWork)).castAdd 1))
    (s1 d1 l1 s2 d2 l2 : Fin U)
    (finishStates : Nat) (finish : Machine U finishStates) :
    MaskFamilyCode mask packet rows U where
  familySlots := familySlots
  familyInjective := hfinj
  poolSlots := poolSlots
  poolInjective := hpinj
  rewindSlots := rewindSlots
  rewindInjective := hrinj
  seed := MaskReady.code mask packet maskSlots hminj pslots hsinj slot ret retDrv log
    rawDrv rawDst rawLog
  rawAlias := hraw
  poolAlias := hpool
  sourceAlias := hsrc
  setupLoadStates := _
  setupLoad := Setup.machine s1 d1 (familySlots (rowRequestPort printer rows.privateWork)) l1
    s2 d2 (familySlots (rowCapsPort printer rows.privateWork)) l2
  finishStates := finishStates
  finish := finish

/-- `MaskFamilyCode.Prepared`, at the exact assembled fuel. -/
theorem prepared (p : MaskFamilyCode mask packet rows U) {r : Request}
    (layout : Packets.Layout a (r.family a) (geometryOf selector a r))
    (facts : ∀ row ∈ (r.family a).rows,
      Packets.PacketFacts a (r.family a) (geometryOf selector a r) row)
    (caps : RowCaps) (good : RowCaps.Good selector a printer r layout facts caps)
    (poolReserve : Fin 373 → Nat)
    (familyReserve : Fin (rowTapes printer rows.privateWork + 1) → Nat)
    (poolH ambientH H H' : Fin U → Nat) (poolA ambientA A A' : Fin U → List Bool)
    (seedFuel setupLoadFuel finishFuel : Nat)
    (h1 : ∀ j, p.familySlots j ≠ p.rewindSlots 1)
    (h2 : ∀ j, p.familySlots j ≠ p.rewindSlots 2)
    (hH1 : ambientH (p.rewindSlots 1) = 0) (hH2 : ambientH (p.rewindSlots 2) = 0)
    (hA1 : ambientA (p.rewindSlots 1) = List.replicate caps.descriptorReserve true)
    (hA2 : ambientA (p.rewindSlots 2) = List.replicate caps.descriptorReserve false)
    (hseed : p.seed.Ready r seedFuel H
      (dockH p.poolSlots poolH (fun _ => 0)) A
      (install p.poolSlots poolA (fun i => ZeroPadding.pad (poolReserve i)
        (BinaryCacheColdRun.input (CachedFamilyLoader.cacheArgs a (r.family a)) i))))
    (hsetup : Step p.setupLoad setupLoadFuel
      (dockH p.poolSlots poolH (fun _ => 0))
      (install p.poolSlots poolA (fun i => ZeroPadding.pad (poolReserve i)
        (BinaryCacheColdRun.output (CachedFamilyLoader.cacheArgs a (r.family a)) i)))
      (dockH p.familySlots ambientH (fun _ => 0))
      (install p.familySlots ambientA (fun i => ZeroPadding.pad (familyReserve i)
        (rowPublicInput selector a printer rows.privateWork r layout caps i))))
    (hfinish : Step p.finish finishFuel
      (dockH p.rewindSlots
        (dockH p.familySlots ambientH (Final.exitCfg printer rows layout facts caps).heads)
        (CompetitorRecordRewind.cfg 2 (srcWord printer rows layout facts caps familyReserve) 0
          caps.descriptorReserve 0 0 (List.replicate caps.descriptorReserve false)).heads)
      (install p.rewindSlots
        (install p.familySlots ambientA (fun i => ZeroPadding.pad (familyReserve i)
          ((Final.exitCfg printer rows layout facts caps).tapes i)))
        (fun i => ZeroPadding.pad ((![0, 0, caps.descriptorReserve] : Fin 3 → Nat) i)
          ((CompetitorRecordRewind.cfg 2 (srcWord printer rows layout facts caps familyReserve) 0
            caps.descriptorReserve 0 0 (List.replicate caps.descriptorReserve false)).tapes i)))
      H' A') :
    p.Prepared (dataList a (r.family a) (geometryOf selector a r) layout facts)
      (seedFuel + 1 +
        (BinaryCacheColdRun.budget (CachedFamilyLoader.cacheArgs a (r.family a)) + 1 +
          (setupLoadFuel + 1 + rowInitBudget a rows.coefficient rows.degree r
            layout.w layout.degree layout.C caps)) + 1 +
        (ExternalRowFamily.budget printer (r.family a) (rows.state r layout facts caps) +
          1 + (2 * caps.descriptorReserve + 2 + 1 + finishFuel)))
      H H' A A' :=
  ⟨r, layout, facts, caps, good, rfl, poolReserve, familyReserve, poolH, poolA,
    ambientH, ambientA, seedFuel, setupLoadFuel, finishFuel, caps.descriptorReserve,
    max (familyReserve (Final.port printer rows)) caps.descriptorReserve,
    hseed, hsetup, Setup.descriptor_fits layout facts caps good,
    Final.rewind_heads p layout facts caps good ambientH
      (srcWord printer rows layout facts caps familyReserve) caps.descriptorReserve h1 h2 hH1 hH2,
    Final.rewind_tapes p layout facts caps good ambientA familyReserve
      (CachedFamilyLoader.descriptorWord printer
        (dataList a (r.family a) (geometryOf selector a r) layout facts)).length
      caps.descriptorReserve h1 h2 hA1 hA2,
    hfinish, Nat.le_refl _⟩

/-- The same, projected to the native `FamilyCode.Prepared` the source
assembly consumes. -/
theorem base_prepared (p : MaskFamilyCode mask packet rows U) {r : Request}
    (layout : Packets.Layout a (r.family a) (geometryOf selector a r))
    (facts : ∀ row ∈ (r.family a).rows,
      Packets.PacketFacts a (r.family a) (geometryOf selector a r) row)
    (caps : RowCaps) (good : RowCaps.Good selector a printer r layout facts caps)
    (poolReserve : Fin 373 → Nat)
    (familyReserve : Fin (rowTapes printer rows.privateWork + 1) → Nat)
    (poolH ambientH H H' : Fin U → Nat) (poolA ambientA A A' : Fin U → List Bool)
    (seedFuel setupLoadFuel finishFuel : Nat)
    (h1 : ∀ j, p.familySlots j ≠ p.rewindSlots 1)
    (h2 : ∀ j, p.familySlots j ≠ p.rewindSlots 2)
    (hH1 : ambientH (p.rewindSlots 1) = 0) (hH2 : ambientH (p.rewindSlots 2) = 0)
    (hA1 : ambientA (p.rewindSlots 1) = List.replicate caps.descriptorReserve true)
    (hA2 : ambientA (p.rewindSlots 2) = List.replicate caps.descriptorReserve false)
    (hseed : p.seed.Ready r seedFuel H
      (dockH p.poolSlots poolH (fun _ => 0)) A
      (install p.poolSlots poolA (fun i => ZeroPadding.pad (poolReserve i)
        (BinaryCacheColdRun.input (CachedFamilyLoader.cacheArgs a (r.family a)) i))))
    (hsetup : Step p.setupLoad setupLoadFuel
      (dockH p.poolSlots poolH (fun _ => 0))
      (install p.poolSlots poolA (fun i => ZeroPadding.pad (poolReserve i)
        (BinaryCacheColdRun.output (CachedFamilyLoader.cacheArgs a (r.family a)) i)))
      (dockH p.familySlots ambientH (fun _ => 0))
      (install p.familySlots ambientA (fun i => ZeroPadding.pad (familyReserve i)
        (rowPublicInput selector a printer rows.privateWork r layout caps i))))
    (hfinish : Step p.finish finishFuel
      (dockH p.rewindSlots
        (dockH p.familySlots ambientH (Final.exitCfg printer rows layout facts caps).heads)
        (CompetitorRecordRewind.cfg 2 (srcWord printer rows layout facts caps familyReserve) 0
          caps.descriptorReserve 0 0 (List.replicate caps.descriptorReserve false)).heads)
      (install p.rewindSlots
        (install p.familySlots ambientA (fun i => ZeroPadding.pad (familyReserve i)
          ((Final.exitCfg printer rows layout facts caps).tapes i)))
        (fun i => ZeroPadding.pad ((![0, 0, caps.descriptorReserve] : Fin 3 → Nat) i)
          ((CompetitorRecordRewind.cfg 2 (srcWord printer rows layout facts caps familyReserve) 0
            caps.descriptorReserve 0 0 (List.replicate caps.descriptorReserve false)).tapes i)))
      H' A') :
    p.base.Prepared (dataList a (r.family a) (geometryOf selector a r) layout facts)
      (seedFuel + 1 +
        (BinaryCacheColdRun.budget (CachedFamilyLoader.cacheArgs a (r.family a)) + 1 +
          (setupLoadFuel + 1 + rowInitBudget a rows.coefficient rows.degree r
            layout.w layout.degree layout.C caps)) + 1 +
        (ExternalRowFamily.budget printer (r.family a) (rows.state r layout facts caps) +
          1 + (2 * caps.descriptorReserve + 2 + 1 + finishFuel)))
      H H' A A' :=
  p.project _ _ _ _ _ _
    (prepared p layout facts caps good poolReserve familyReserve poolH ambientH H H'
      poolA ambientA A A' seedFuel setupLoadFuel finishFuel h1 h2 hH1 hH2 hA1 hA2
      hseed hsetup hfinish)

/-! ### Closing the seam: the setup loader's exit bank, explicitly

`SLoad.Setup.setup_load_step` reports its exit bank existentially, which is
enough for the second conjunct alone but not for the rewind bank, since
`Prepared` shares one `ambientA` between the two. `SLoad.Setup.setup_frames`
already reports the exit bank EXPLICITLY, so the same assembly is redone here
against that explicit bank. No machine and no new run is introduced. -/

/-- The setup loader's exit bank: the entry bank with the framed request at
`rowRequestPort` and the framed metadata word at `rowCapsPort`. -/
def setupExit {U : Nat} (selector : CyclicChoice.Laws) (a : DecompositionAlgorithm)
    (printer : WilliamsAlgorithm) (privateWork : Nat) (r : Request)
    (layout : Packets.Layout a (r.family a) (geometryOf selector a r)) (caps : RowCaps)
    (familySlots : Fin (rowTapes printer privateWork + 1) → Fin U)
    (familyReserve : Fin (rowTapes printer privateWork + 1) → Nat)
    (A : Fin U → List Bool) : Fin U → List Bool :=
  Function.update (Function.update A (familySlots (rowRequestPort printer privateWork))
      (ZeroPadding.pad (familyReserve (rowRequestPort printer privateWork))
        (RepairOrdinary.frame (r.input a))))
    (familySlots (rowCapsPort printer privateWork))
    (ZeroPadding.pad (familyReserve (rowCapsPort printer privateWork))
      (RepairOrdinary.frame (Setup.metaBits layout.w layout.degree layout.C caps)))

/-- `MaskFamilyCode.Prepared`'s SECOND conjunct against the explicit exit bank. -/
theorem setup_exit_step {U : Nat} {selector : CyclicChoice.Laws} {a : DecompositionAlgorithm}
    (printer : WilliamsAlgorithm) (privateWork : Nat) {r : Request}
    (layout : Packets.Layout a (r.family a) (geometryOf selector a r)) (caps : RowCaps)
    (poolSlots : Fin 373 → Fin U) (poolReserve : Fin 373 → Nat)
    (familySlots : Fin (rowTapes printer privateWork + 1) → Fin U)
    (hfinj : Function.Injective familySlots)
    (familyReserve : Fin (rowTapes printer privateWork + 1) → Nat)
    (s1 d1 l1 s2 d2 l2 : Fin U)
    (H : Fin U → Nat) (A : Fin U → List Bool)
    (capS1 capD1 capL1 capS2 capD2 capL2 : Nat)
    (hl1 : 2 * (r.input a).length + 1 ≤ capL1)
    (hl2 : 2 * (Setup.metaBits layout.w layout.degree layout.C caps).length + 1 ≤ capL2)
    (hpH : ∀ i, H (poolSlots i) = 0)
    (hpA : ∀ i, A (poolSlots i) = ZeroPadding.pad (poolReserve i)
      (BinaryCacheColdRun.output (CachedFamilyLoader.cacheArgs a (r.family a)) i))
    (hfH : ∀ i, H (familySlots i) = 0)
    (h1 : s1 ≠ d1) (h2 : s1 ≠ familySlots (rowRequestPort printer privateWork))
    (h3 : s1 ≠ l1) (h4 : d1 ≠ familySlots (rowRequestPort printer privateWork))
    (h5 : d1 ≠ l1) (h6 : familySlots (rowRequestPort printer privateWork) ≠ l1)
    (k1 : s2 ≠ d2) (k2 : s2 ≠ familySlots (rowCapsPort printer privateWork))
    (k3 : s2 ≠ l2) (k4 : d2 ≠ familySlots (rowCapsPort printer privateWork))
    (k5 : d2 ≠ l2) (k6 : familySlots (rowCapsPort printer privateWork) ≠ l2)
    (m1 : familySlots (rowRequestPort printer privateWork) ≠ s2)
    (m2 : familySlots (rowRequestPort printer privateWork) ≠ d2)
    (m4 : familySlots (rowRequestPort printer privateWork) ≠ l2)
    (hH1s : H s1 = 0) (hH1d : H d1 = 0) (hH1l : H l1 = 0)
    (hH2s : H s2 = 0) (hH2d : H d2 = 0) (hH2l : H l2 = 0)
    (hA1s : A s1 = ZeroPadding.pad capS1 (r.input a))
    (hA1d : A d1 = ZeroPadding.pad capD1 (List.replicate (r.input a).length true))
    (hA1l : A l1 = List.replicate capL1 false)
    (hA2s : A s2 = ZeroPadding.pad capS2 (Setup.metaBits layout.w layout.degree layout.C caps))
    (hA2d : A d2 = ZeroPadding.pad capD2
      (List.replicate (Setup.metaBits layout.w layout.degree layout.C caps).length true))
    (hA2l : A l2 = List.replicate capL2 false)
    (hA1t : A (familySlots (rowRequestPort printer privateWork))
      = List.replicate (familyReserve (rowRequestPort printer privateWork)) false)
    (hA2t : A (familySlots (rowCapsPort printer privateWork))
      = List.replicate (familyReserve (rowCapsPort printer privateWork)) false)
    (hfam0 : ∀ i : Fin (rowTapes printer privateWork + 1), i.val = 0 →
      A (familySlots i) = ZeroPadding.pad (familyReserve i)
        (exactListWord (Packets.pool a (r.family a) (geometryOf selector a r))))
    (hfam262 : ∀ i : Fin (rowTapes printer privateWork + 1), i.val = 262 →
      A (familySlots i) = ZeroPadding.pad (familyReserve i) (r.raw selector a))
    (hfamBlank : ∀ i : Fin (rowTapes printer privateWork + 1), i.val ≠ 0 → i.val ≠ 262 →
      i ≠ rowRequestPort printer privateWork → i ≠ rowCapsPort printer privateWork →
      A (familySlots i) = List.replicate (familyReserve i) false) :
    Step (Setup.machine s1 d1 (familySlots (rowRequestPort printer privateWork)) l1
            s2 d2 (familySlots (rowCapsPort printer privateWork)) l2)
      (Setup.cost (r.input a).length
        (Setup.metaBits layout.w layout.degree layout.C caps).length)
      (dockH poolSlots H (fun _ => 0))
      (install poolSlots A (fun i => ZeroPadding.pad (poolReserve i)
        (BinaryCacheColdRun.output (CachedFamilyLoader.cacheArgs a (r.family a)) i)))
      (dockH familySlots H (fun _ => 0))
      (install familySlots (setupExit selector a printer privateWork r layout caps familySlots familyReserve A)
        (fun i => ZeroPadding.pad (familyReserve i)
          (rowPublicInput selector a printer privateWork r layout caps i))) := by
  classical
  have hne : familySlots (rowRequestPort printer privateWork)
      ≠ familySlots (rowCapsPort printer privateWork) := fun h =>
    (RowInput.capsPort_ne_requestPort printer privateWork) (hfinj h).symm
  have step := Setup.setup_frames s1 d1 (familySlots (rowRequestPort printer privateWork)) l1
    s2 d2 (familySlots (rowCapsPort printer privateWork)) l2
    h1 h2 h3 h4 h5 h6 k1 k2 k3 k4 k5 k6 m1 m2 hne m4
    capS1 capD1 (familyReserve (rowRequestPort printer privateWork)) capL1
    capS2 capD2 (familyReserve (rowCapsPort printer privateWork)) capL2
    (r.input a) (Setup.metaBits layout.w layout.degree layout.C caps) hl1 hl2 H A
    hH1s hH1d (hfH _) hH1l hH2s hH2d (hfH _) hH2l
    hA1s hA1d hA1t hA1l hA2s hA2d hA2t hA2l
  have hres : ∀ i, setupExit selector a printer privateWork r layout caps familySlots familyReserve A
      (familySlots i) = ZeroPadding.pad (familyReserve i)
      (rowPublicInput selector a printer privateWork r layout caps i) := by
    refine RowInput.residency familySlots layout caps _ familyReserve ?_ ?_ ?_ ?_ ?_
    · intro i hi
      have e1 : familySlots i ≠ familySlots (rowRequestPort printer privateWork) := by
        intro h
        exact RowInput.requestPort_ne_zero printer privateWork (by rw [← hfinj h]; exact hi)
      have e2 : familySlots i ≠ familySlots (rowCapsPort printer privateWork) := by
        intro h
        exact RowInput.capsPort_ne_zero printer privateWork (by rw [← hfinj h]; exact hi)
      rw [setupExit, Function.update_of_ne e2, Function.update_of_ne e1]
      exact hfam0 i hi
    · intro i hi
      have e1 : familySlots i ≠ familySlots (rowRequestPort printer privateWork) := by
        intro h
        exact RowInput.requestPort_ne_262 printer privateWork (by rw [← hfinj h]; exact hi)
      have e2 : familySlots i ≠ familySlots (rowCapsPort printer privateWork) := by
        intro h
        exact RowInput.capsPort_ne_262 printer privateWork (by rw [← hfinj h]; exact hi)
      rw [setupExit, Function.update_of_ne e2, Function.update_of_ne e1]
      exact hfam262 i hi
    · rw [setupExit, Function.update_of_ne hne, Function.update_self]
    · rw [setupExit, Function.update_self, Setup.meta_frame]
    · intro i h0 h262 hq hc
      have e1 : familySlots i ≠ familySlots (rowRequestPort printer privateWork) :=
        fun h => hq (hfinj h)
      have e2 : familySlots i ≠ familySlots (rowCapsPort printer privateWork) :=
        fun h => hc (hfinj h)
      rw [setupExit, Function.update_of_ne e2, Function.update_of_ne e1]
      exact hfamBlank i h0 h262 hq hc
  rw [SLoad.dockH_existing poolSlots H (fun _ => 0) hpH,
    install_existing poolSlots A _ hpA,
    SLoad.dockH_existing familySlots H (fun _ => 0) hfH,
    RowInput.install_row familySlots layout caps _ familyReserve hres]
  exact step

/-- The heads at the cold run's exit: the pool slots rewound, the rest ambient. -/
abbrev coldHeads {U : Nat} (poolSlots : Fin 373 → Fin U) (poolH : Fin U → Nat) : Fin U → Nat :=
  dockH poolSlots poolH (fun _ => 0)

/-- The bank at the cold run's exit: the 373 pool words, the rest ambient. -/
abbrev coldBank {U : Nat} (alg : DecompositionAlgorithm) (r : Request)
    (poolSlots : Fin 373 → Fin U) (poolReserve : Fin 373 → Nat)
    (poolA : Fin U → List Bool) : Fin U → List Bool :=
  install poolSlots poolA (fun i => ZeroPadding.pad (poolReserve i)
    (BinaryCacheColdRun.output (CachedFamilyLoader.cacheArgs alg (r.family alg)) i))

theorem prepared_code {U : Nat} (mask : MaskProducer) {selector : CyclicChoice.Laws}
    {a : DecompositionAlgorithm} {printer : WilliamsAlgorithm}
    (packet : PacketWriter selector a) (rows : RowProducer selector a printer)
    (maskSlots : Fin (5 + mask.work) → Fin U) (hminj : Function.Injective maskSlots)
    (pslots : Fin packet.ordinary.program.tapeCount → Fin U)
    (hsinj : Function.Injective pslots)
    (slot : Fin 13 → Fin U) (ret : Fin 4 → Fin U)
    (retDrv log rawDrv rawDst rawLog : Fin U)
    (familySlots : Fin (rowTapes printer rows.privateWork + 1) → Fin U)
    (hfinj : Function.Injective familySlots)
    (poolSlots : Fin 373 → Fin U) (hpinj : Function.Injective poolSlots)
    (rewindSlots : Fin 3 → Fin U) (hrinj : Function.Injective rewindSlots)
    (hraw : pslots packet.ordinary.program.outputTape = familySlots
      ((SharedRowLayout.headerSlots printer (rowWork rows.privateWork) 262).castAdd 1))
    (hpool : poolSlots 34 = familySlots
      ((SharedRowLayout.headerSlots printer (rowWork rows.privateWork) 0).castAdd 1))
    (hsrc : rewindSlots 0 = familySlots
      ((SharedRowLayout.descriptor printer (rowWork rows.privateWork)).castAdd 1))
    (s1 d1 l1 s2 d2 l2 : Fin U)
    (finishStates : Nat) (finish : Machine U finishStates)
    {r : Request} (layout : Packets.Layout a (r.family a) (geometryOf selector a r))
    (facts : ∀ row ∈ (r.family a).rows,
      Packets.PacketFacts a (r.family a) (geometryOf selector a r) row)
    (caps : RowCaps) (good : RowCaps.Good selector a printer r layout facts caps)
    (poolReserve : Fin 373 → Nat)
    (familyReserve : Fin (rowTapes printer rows.privateWork + 1) → Nat)
    (poolH H H' : Fin U → Nat) (poolA A A' : Fin U → List Bool)
    (seedFuel finishFuel capS1 capD1 capL1 capS2 capD2 capL2 : Nat)
    (hl1 : 2 * (r.input a).length + 1 ≤ capL1)
    (hl2 : 2 * (Setup.metaBits layout.w layout.degree layout.C caps).length + 1 ≤ capL2)
    -- the three rewind tapes outside the family bank
    (hf1 : ∀ j, familySlots j ≠ rewindSlots 1)
    (hf2 : ∀ j, familySlots j ≠ rewindSlots 2)
    (hq1 : ∀ i, poolSlots i ≠ rewindSlots 1)
    (hq2 : ∀ i, poolSlots i ≠ rewindSlots 2)
    (hpH1 : poolH (rewindSlots 1) = 0) (hpH2 : poolH (rewindSlots 2) = 0)
    (hpA1 : poolA (rewindSlots 1) = List.replicate caps.descriptorReserve true)
    (hpA2 : poolA (rewindSlots 2) = List.replicate caps.descriptorReserve false)
    -- FIRST conjunct: the physical seed loader at the pool-shaped exit
    (hseed : (MaskReady.code mask packet maskSlots hminj pslots hsinj slot ret retDrv log
        rawDrv rawDst rawLog).Ready r seedFuel H
      (coldHeads poolSlots poolH) A
      (install poolSlots poolA (fun i => ZeroPadding.pad (poolReserve i)
        (BinaryCacheColdRun.input (CachedFamilyLoader.cacheArgs a (r.family a)) i))))
    -- SECOND conjunct: the setup loader's resources at the cold run's exit
    (hfH : ∀ i, coldHeads poolSlots poolH (familySlots i) = 0)
    (e1 : s1 ≠ d1) (e2 : s1 ≠ familySlots (rowRequestPort printer rows.privateWork))
    (e3 : s1 ≠ l1) (e4 : d1 ≠ familySlots (rowRequestPort printer rows.privateWork))
    (e5 : d1 ≠ l1) (e6 : familySlots (rowRequestPort printer rows.privateWork) ≠ l1)
    (k1 : s2 ≠ d2) (k2 : s2 ≠ familySlots (rowCapsPort printer rows.privateWork))
    (k3 : s2 ≠ l2) (k4 : d2 ≠ familySlots (rowCapsPort printer rows.privateWork))
    (k5 : d2 ≠ l2) (k6 : familySlots (rowCapsPort printer rows.privateWork) ≠ l2)
    (m1 : familySlots (rowRequestPort printer rows.privateWork) ≠ s2)
    (m2 : familySlots (rowRequestPort printer rows.privateWork) ≠ d2)
    (m4 : familySlots (rowRequestPort printer rows.privateWork) ≠ l2)
    (hH1s : coldHeads poolSlots poolH s1 = 0) (hH1d : coldHeads poolSlots poolH d1 = 0)
    (hH1l : coldHeads poolSlots poolH l1 = 0) (hH2s : coldHeads poolSlots poolH s2 = 0)
    (hH2d : coldHeads poolSlots poolH d2 = 0) (hH2l : coldHeads poolSlots poolH l2 = 0)
    (hA1s : coldBank a r poolSlots poolReserve poolA s1
      = ZeroPadding.pad capS1 (r.input a))
    (hA1d : coldBank a r poolSlots poolReserve poolA d1
      = ZeroPadding.pad capD1 (List.replicate (r.input a).length true))
    (hA1l : coldBank a r poolSlots poolReserve poolA l1 = List.replicate capL1 false)
    (hA2s : coldBank a r poolSlots poolReserve poolA s2
      = ZeroPadding.pad capS2 (Setup.metaBits layout.w layout.degree layout.C caps))
    (hA2d : coldBank a r poolSlots poolReserve poolA d2 = ZeroPadding.pad capD2
      (List.replicate (Setup.metaBits layout.w layout.degree layout.C caps).length true))
    (hA2l : coldBank a r poolSlots poolReserve poolA l2 = List.replicate capL2 false)
    (hA1t : coldBank a r poolSlots poolReserve poolA
        (familySlots (rowRequestPort printer rows.privateWork))
      = List.replicate (familyReserve (rowRequestPort printer rows.privateWork)) false)
    (hA2t : coldBank a r poolSlots poolReserve poolA
        (familySlots (rowCapsPort printer rows.privateWork))
      = List.replicate (familyReserve (rowCapsPort printer rows.privateWork)) false)
    (hfam0 : ∀ i : Fin (rowTapes printer rows.privateWork + 1), i.val = 0 →
      coldBank a r poolSlots poolReserve poolA (familySlots i)
        = ZeroPadding.pad (familyReserve i)
          (exactListWord (Packets.pool a (r.family a) (geometryOf selector a r))))
    (hfam262 : ∀ i : Fin (rowTapes printer rows.privateWork + 1), i.val = 262 →
      coldBank a r poolSlots poolReserve poolA (familySlots i)
        = ZeroPadding.pad (familyReserve i) (r.raw selector a))
    (hfamBlank : ∀ i : Fin (rowTapes printer rows.privateWork + 1), i.val ≠ 0 → i.val ≠ 262 →
      i ≠ rowRequestPort printer rows.privateWork → i ≠ rowCapsPort printer rows.privateWork →
      coldBank a r poolSlots poolReserve poolA (familySlots i)
        = List.replicate (familyReserve i) false)
    
    (hfinish : Step finish finishFuel
      (dockH rewindSlots
        (dockH familySlots (coldHeads poolSlots poolH)
          (Final.exitCfg printer rows layout facts caps).heads)
        (CompetitorRecordRewind.cfg 2 (srcWord printer rows layout facts caps familyReserve) 0
          caps.descriptorReserve 0 0 (List.replicate caps.descriptorReserve false)).heads)
      (install rewindSlots
        (install familySlots
          (setupExit selector a printer rows.privateWork r layout caps familySlots familyReserve
            (coldBank a r poolSlots poolReserve poolA))
          (fun i => ZeroPadding.pad (familyReserve i)
            ((Final.exitCfg printer rows layout facts caps).tapes i)))
        (fun i => ZeroPadding.pad ((![0, 0, caps.descriptorReserve] : Fin 3 → Nat) i)
          ((CompetitorRecordRewind.cfg 2 (srcWord printer rows layout facts caps familyReserve) 0
            caps.descriptorReserve 0 0 (List.replicate caps.descriptorReserve false)).tapes i)))
      H' A') :
    (code mask packet rows maskSlots hminj pslots hsinj slot ret retDrv log rawDrv rawDst rawLog
        familySlots hfinj poolSlots hpinj rewindSlots hrinj hraw hpool hsrc
        s1 d1 l1 s2 d2 l2 finishStates finish).Prepared
      (dataList a (r.family a) (geometryOf selector a r) layout facts)
      (seedFuel + 1 +
        (BinaryCacheColdRun.budget (CachedFamilyLoader.cacheArgs a (r.family a)) + 1 +
          (Setup.cost (r.input a).length
              (Setup.metaBits layout.w layout.degree layout.C caps).length + 1 +
            rowInitBudget a rows.coefficient rows.degree r
              layout.w layout.degree layout.C caps)) + 1 +
        (ExternalRowFamily.budget printer (r.family a) (rows.state r layout facts caps) +
          1 + (2 * caps.descriptorReserve + 2 + 1 + finishFuel)))
      H H' A A' := by
  have hsetup := setup_exit_step printer rows.privateWork layout caps poolSlots poolReserve
    familySlots hfinj familyReserve s1 d1 l1 s2 d2 l2
    (coldHeads poolSlots poolH) (coldBank a r poolSlots poolReserve poolA)
    capS1 capD1 capL1 capS2 capD2 capL2 hl1 hl2
    (fun i => dockH_slot poolSlots hpinj poolH (fun _ => 0) i)
    (fun i => install_slot poolSlots hpinj poolA _ i)
    hfH e1 e2 e3 e4 e5 e6 k1 k2 k3 k4 k5 k6 m1 m2 m4
    hH1s hH1d hH1l hH2s hH2d hH2l hA1s hA1d hA1l hA2s hA2d hA2l hA1t hA2t
    hfam0 hfam262 hfamBlank
  rw [SLoad.dockH_existing poolSlots (coldHeads poolSlots poolH) (fun _ => 0)
      (fun i => dockH_slot poolSlots hpinj poolH (fun _ => 0) i),
    install_existing poolSlots (coldBank a r poolSlots poolReserve poolA) _
      (fun i => install_slot poolSlots hpinj poolA _ i)] at hsetup
  have hH1 : coldHeads poolSlots poolH (rewindSlots 1) = 0 :=
    (dockH_other poolSlots poolH (fun _ => 0) _ hq1).trans hpH1
  have hH2 : coldHeads poolSlots poolH (rewindSlots 2) = 0 :=
    (dockH_other poolSlots poolH (fun _ => 0) _ hq2).trans hpH2
  have hkeep : ∀ x : Fin U, x ≠ familySlots (rowRequestPort printer rows.privateWork) →
      x ≠ familySlots (rowCapsPort printer rows.privateWork) →
      setupExit selector a printer rows.privateWork r layout caps familySlots familyReserve
        (coldBank a r poolSlots poolReserve poolA) x
      = coldBank a r poolSlots poolReserve poolA x := by
    intro x hx1 hx2
    rw [setupExit, Function.update_of_ne hx2, Function.update_of_ne hx1]
  have hA1 : setupExit selector a printer rows.privateWork r layout caps familySlots familyReserve
      (coldBank a r poolSlots poolReserve poolA) (rewindSlots 1)
      = List.replicate caps.descriptorReserve true :=
    ((hkeep (rewindSlots 1) (Ne.symm (hf1 _)) (Ne.symm (hf1 _))).trans
      (install_other poolSlots poolA _ _ hq1)).trans hpA1
  have hA2 : setupExit selector a printer rows.privateWork r layout caps familySlots familyReserve
      (coldBank a r poolSlots poolReserve poolA) (rewindSlots 2)
      = List.replicate caps.descriptorReserve false :=
    ((hkeep (rewindSlots 2) (Ne.symm (hf2 _)) (Ne.symm (hf2 _))).trans
      (install_other poolSlots poolA _ _ hq2)).trans hpA2
  exact prepared _ layout facts caps good poolReserve familyReserve poolH
    (coldHeads poolSlots poolH) H H' poolA
    (setupExit selector a printer rows.privateWork r layout caps familySlots familyReserve
      (coldBank a r poolSlots poolReserve poolA)) A A'
    seedFuel _ finishFuel hf1 hf2 hH1 hH2 hA1 hA2 hseed hsetup hfinish

end
end SLoad.Prepared
