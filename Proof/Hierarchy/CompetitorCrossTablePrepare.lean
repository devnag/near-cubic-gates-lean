import Proof.Hierarchy.CompetitorCrossTablePrepareLayout

/-! All native cross-table dimension words and padding are now physically
prepared from four raw fields and the packet source, with every head reset. -/
namespace NearCubicWires.RepairOrdinary.CompetitorCrossTablePrepare
open LocalBitMultitape RecoveryRootRound CompetitorRationalProducts
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def scalars := RecoveryFocus.machine scalarSlots CompetitorCrossScalarDrivers.machine
noncomputable def capacity := RecoveryFocus.machine capacitySlots CompetitorCrossCapacity.machine
noncomputable def padding := RecoveryFocus.machine paddingSlots (CompetitorPlaneTablePadding.machine 4)
noncomputable def machine := Composition.machine scalars (Composition.machine capacity padding)
def budget (b w n p : ℕ) := CompetitorCrossScalarDrivers.budget w b n p+1+
  (CompetitorCrossCapacity.budget w n+1+(2*CompetitorPlanePacketPass.capacity w n+4))

theorem prepare_run (b w n p : ℕ) (source : List Bool) : ∃ out,
    ClockJoin.ReadyRun machine (budget b w n p) (input b w n p source) out ∧
      (∀ i : Fin 35,out (i.castAdd 85)=CompetitorPlaneTableCold.input b w n p source i) ∧
      out 35=List.replicate n true ∧ out 36=List.replicate p true := by
  obtain ⟨a,ha,hkeep,h4,h23,h26,h30⟩ := CompetitorCrossScalarDrivers.drivers_run w b n p
  have hs := bounded_focus scalarSlots scalar_injective _ _ _ ha (input b w n p source)
    (scalar_input b w n p source)
  let atapes := install scalarSlots (input b w n p source) a
  have af := scalar_fields b w n p source a hkeep h4 h23 h26 h30
  obtain ⟨c,hc,hc0,hc1,hc51⟩ := CompetitorCrossCapacity.capacity_run w n
  have hd := bounded_focus capacitySlots capacity_injective _ _ _ hc atapes
    (capacity_input b w n p source a af)
  let ctapes := install capacitySlots atapes c
  have cf := capacity_fields (CompetitorPlanePacketPass.capacity w n) b w n p source atapes c af hc0 hc1 hc51
  have fresh : ctapes 119=[] := by
    apply (install_other capacitySlots _ _ _ (by
      intro j hj
      have hv := congrArg Fin.val hj
      rw [capacity_value] at hv
      split_ifs at hv <;> omega)).trans
    exact scalar_fresh b w n p source a 119 (by decide)
  obtain ⟨pad,hp,hpt,hph,hps⟩ := CompetitorPlaneTablePadding.padding_ready
    (CompetitorPlanePacketPass.capacity w n) (padFields b w n)
  have hpad : ClockJoin.ReadyRun (CompetitorPlaneTablePadding.machine 4)
      (2*CompetitorPlanePacketPass.capacity w n+4)
      (CompetitorPlaneTablePadding.input (CompetitorPlanePacketPass.capacity w n) (padFields b w n))
      (CompetitorPlaneTablePadding.output (CompetitorPlanePacketPass.capacity w n) (padFields b w n)) :=
    ⟨pad,hp,hpt,hph,hps.le⟩
  have hpadded := bounded_focus paddingSlots padding_injective _ _ _ hpad ctapes
    (padding_input b w n p source ctapes cf fresh)
  let out := install paddingSlots ctapes
    (CompetitorPlaneTablePadding.output (CompetitorPlanePacketPass.capacity w n) (padFields b w n))
  refine ⟨out,ClockJoin.join _ _ _ _ _ _ _ hs (ClockJoin.join _ _ _ _ _ _ _ hd hpadded),
    padding_fields b w n p source ctapes cf,?_,?_⟩
  · exact (install_other paddingSlots _ _ _ (by decide)).trans (cf 35)
  · exact (install_other paddingSlots _ _ _ (by decide)).trans (cf 36)

end NearCubicWires.RepairOrdinary.CompetitorCrossTablePrepare
