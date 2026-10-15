import Proof.SourceAssembly.SLoadSetup
import Proof.SourceAssembly.MaskFamily

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace SLoad.Final
open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairRepresentation SupplierEstimator SupplierPipeline SourceInterfaces
open NearCubicWires.P1Closure
open RepairSource.VerifierDecoding
open FixedLivePackets PacketProduction MaskedFamilySource
noncomputable section

/-! ### Two padding identities -/

/-- Re-padding a padded word is padding to the larger reserve. -/
theorem pad_pad (u v : Nat) (w : List Bool) :
    ZeroPadding.pad u (ZeroPadding.pad v w) = ZeroPadding.pad (max u v) w := by
  have hl : (ZeroPadding.pad v w).length = max v w.length := ZeroPadding.pad_length v w
  show (w ++ List.replicate (v - w.length) false)
      ++ List.replicate (u - (ZeroPadding.pad v w).length) false
    = w ++ List.replicate (max u v - w.length) false
  rw [hl, List.append_assoc, ← List.replicate_add]
  congr 2
  omega

/-- A zero-backed tape is the padding of the empty word. -/
theorem pad_nil (u : Nat) : ZeroPadding.pad u ([] : List Bool) = List.replicate u false := by
  simp [ZeroPadding.pad]

variable {mask : MaskProducer} {selector : CyclicChoice.Laws} {a : DecompositionAlgorithm}
  {printer : WilliamsAlgorithm} {packet : PacketWriter selector a}
  {rows : RowProducer selector a printer} {U : Nat}

/-- The descriptor port of the accepted row package, as a family-bank index. -/
abbrev port (printer : WilliamsAlgorithm) (rows : RowProducer selector a printer) :
    Fin (rowTapes printer rows.privateWork + 1) :=
  (SharedRowLayout.descriptor printer (rowWork rows.privateWork)).castAdd 1

/-- The family exit configuration `MaskFamilyCode.Prepared` names. -/
abbrev exitCfg (printer : WilliamsAlgorithm) (rows : RowProducer selector a printer) {r : Request}
    (layout : Packets.Layout a (r.family a) (geometryOf selector a r))
    (facts : ∀ row ∈ (r.family a).rows,
      Packets.PacketFacts a (r.family a) (geometryOf selector a r) row) (caps : RowCaps) :=
  ExternalRowFamily.exit printer (SharedRowLayout.code rows.program)
    a (r.family a) (geometryOf selector a r) layout facts (rows.state r layout facts caps)

/-! ### The family exit at the descriptor port -/

theorem exit_heads {r : Request}
    (layout : Packets.Layout a (r.family a) (geometryOf selector a r))
    (facts : ∀ row ∈ (r.family a).rows,
      Packets.PacketFacts a (r.family a) (geometryOf selector a r) row) (caps : RowCaps) :
    (exitCfg printer rows layout facts caps).heads (port printer rows)
      = (rows.state r layout facts caps).heads (r.family a).rows.attach.length
          (CachedFamilyLoader.descriptorWord printer
            (dataList a (r.family a) (geometryOf selector a r) layout facts))
          (SharedRowLayout.descriptor printer (rowWork rows.privateWork)) := by
  simp [exitCfg, ExternalRowFamily.exit, RepeatMachine.cfg, controlConfig,
    TapeEmbedding.config, ExternalRowFamily.rowConfig,
    CachedFamilyLoader.descriptorWord]

theorem exit_tapes {r : Request}
    (layout : Packets.Layout a (r.family a) (geometryOf selector a r))
    (facts : ∀ row ∈ (r.family a).rows,
      Packets.PacketFacts a (r.family a) (geometryOf selector a r) row) (caps : RowCaps) :
    (exitCfg printer rows layout facts caps).tapes (port printer rows)
      = (rows.state r layout facts caps).tapes (r.family a).rows.attach.length
          (CachedFamilyLoader.descriptorWord printer
            (dataList a (r.family a) (geometryOf selector a r) layout facts))
          (SharedRowLayout.descriptor printer (rowWork rows.privateWork)) := by
  simp [exitCfg, ExternalRowFamily.exit, RepeatMachine.cfg, controlConfig,
    TapeEmbedding.config, ExternalRowFamily.rowConfig,
    CachedFamilyLoader.descriptorWord]

/-- The supplied row package's descriptor contract, read at the family exit. -/
theorem descriptor_head {r : Request}
    (layout : Packets.Layout a (r.family a) (geometryOf selector a r))
    (facts : ∀ row ∈ (r.family a).rows,
      Packets.PacketFacts a (r.family a) (geometryOf selector a r) row) (caps : RowCaps)
    (good : RowCaps.Good selector a printer r layout facts caps) :
    (exitCfg printer rows layout facts caps).heads (port printer rows)
      = (CachedFamilyLoader.descriptorWord printer
            (dataList a (r.family a) (geometryOf selector a r) layout facts)).length := by
  rw [exit_heads]
  exact (rows.descriptor r layout facts caps good (r.family a).rows.attach.length
    (le_of_eq (List.length_attach))
    (CachedFamilyLoader.descriptorWord printer
      (dataList a (r.family a) (geometryOf selector a r) layout facts))).1

theorem descriptor_tape {r : Request}
    (layout : Packets.Layout a (r.family a) (geometryOf selector a r))
    (facts : ∀ row ∈ (r.family a).rows,
      Packets.PacketFacts a (r.family a) (geometryOf selector a r) row) (caps : RowCaps)
    (good : RowCaps.Good selector a printer r layout facts caps) :
    (exitCfg printer rows layout facts caps).tapes (port printer rows)
      = ZeroPadding.pad caps.descriptorReserve (CachedFamilyLoader.descriptorWord printer
            (dataList a (r.family a) (geometryOf selector a r) layout facts)) := by
  rw [exit_tapes]
  exact (rows.descriptor r layout facts caps good (r.family a).rows.attach.length
    (le_of_eq (List.length_attach))
    (CachedFamilyLoader.descriptorWord printer
      (dataList a (r.family a) (geometryOf selector a r) layout facts))).2

/-! ### The rewind bank

`MaskFamilyCode.Prepared`'s fourth and fifth conjuncts. Tape `0` is the family's
own descriptor tape, by `sourceAlias`; tapes `1` and `2` are outside the family
bank and carry the ambient driver and log unchanged. -/

theorem fin3 (i : Fin 3) : i = 0 ∨ i = 1 ∨ i = 2 := by
  fin_cases i
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

/-- Fourth conjunct: the rewind entry HEADS at `p.rewindSlots`. The source head
is the accumulated descriptor length, straight from `RowProducer.descriptor`;
the driver and log heads are the ambient zeros. -/
theorem rewind_heads (p : MaskFamilyCode mask packet rows U) {r : Request}
    (layout : Packets.Layout a (r.family a) (geometryOf selector a r))
    (facts : ∀ row ∈ (r.family a).rows,
      Packets.PacketFacts a (r.family a) (geometryOf selector a r) row) (caps : RowCaps)
    (good : RowCaps.Good selector a printer r layout facts caps)
    (ambientH : Fin U → Nat) (word : List Bool) (rewindCap : Nat)
    (h1 : ∀ j, p.familySlots j ≠ p.rewindSlots 1)
    (h2 : ∀ j, p.familySlots j ≠ p.rewindSlots 2)
    (hH1 : ambientH (p.rewindSlots 1) = 0) (hH2 : ambientH (p.rewindSlots 2) = 0) :
    ∀ i, dockH p.familySlots ambientH (exitCfg printer rows layout facts caps).heads
        (p.rewindSlots i)
      = (CompetitorRecordRewind.cfg 0 word
          (CachedFamilyLoader.descriptorWord printer
            (dataList a (r.family a) (geometryOf selector a r) layout facts)).length
          rewindCap 0 0 []).heads i := by
  intro i
  rcases fin3 i with rfl | rfl | rfl
  · rw [p.sourceAlias, dockH_slot p.familySlots p.familyInjective,
      descriptor_head layout facts caps good]
    simp [CompetitorRecordRewind.cfg]
  · rw [dockH_other p.familySlots ambientH _ _ h1, hH1]
    simp [CompetitorRecordRewind.cfg]
  · rw [dockH_other p.familySlots ambientH _ _ h2, hH2]
    simp [CompetitorRecordRewind.cfg]

/-- Fifth conjunct: the rewind entry TAPES at `p.rewindSlots`, with
`descriptorReserve` fixed to the larger of the family's own reserve at the
descriptor tape and the row package's `caps.descriptorReserve`. That choice is
an equality of tapes, not a new bound on the position. -/
theorem rewind_tapes (p : MaskFamilyCode mask packet rows U) {r : Request}
    (layout : Packets.Layout a (r.family a) (geometryOf selector a r))
    (facts : ∀ row ∈ (r.family a).rows,
      Packets.PacketFacts a (r.family a) (geometryOf selector a r) row) (caps : RowCaps)
    (good : RowCaps.Good selector a printer r layout facts caps)
    (ambientA : Fin U → List Bool)
    (familyReserve : Fin (rowTapes printer rows.privateWork + 1) → Nat)
    (pos rewindCap : Nat)
    (h1 : ∀ j, p.familySlots j ≠ p.rewindSlots 1)
    (h2 : ∀ j, p.familySlots j ≠ p.rewindSlots 2)
    (hA1 : ambientA (p.rewindSlots 1) = List.replicate rewindCap true)
    (hA2 : ambientA (p.rewindSlots 2) = List.replicate rewindCap false) :
    ∀ i, install p.familySlots ambientA
        (fun j => ZeroPadding.pad (familyReserve j)
          ((exitCfg printer rows layout facts caps).tapes j)) (p.rewindSlots i)
      = ZeroPadding.pad ((![0, 0, rewindCap] : Fin 3 → Nat) i)
          ((CompetitorRecordRewind.cfg 0
            (ZeroPadding.pad (max (familyReserve (port printer rows)) caps.descriptorReserve)
              (CachedFamilyLoader.descriptorWord printer
                (dataList a (r.family a) (geometryOf selector a r) layout facts)))
            pos rewindCap 0 0 []).tapes i) := by
  intro i
  rcases fin3 i with rfl | rfl | rfl
  · rw [p.sourceAlias, install_slot p.familySlots p.familyInjective]
    simp only [descriptor_tape layout facts caps good, pad_pad]
    simp [CompetitorRecordRewind.cfg]
  · rw [install_other p.familySlots ambientA _ _ h1, hA1]
    simp [CompetitorRecordRewind.cfg]
  · rw [install_other p.familySlots ambientA _ _ h2, hA2]
    simp [CompetitorRecordRewind.cfg, pad_nil]

end
end SLoad.Final
