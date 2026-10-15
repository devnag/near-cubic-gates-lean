import Proof.MachineModel.OrdinaryMatrixScoreWeightSelect
import Proof.MachineModel.OrdinaryMatrixScoreDimensions

/-! Whole streamed weight entry: execute assignment/sign selection, then load
the following magnitude into reusable framed storage. The source advances
one full sign-magnitude field; the assignment advances exactly one bit. -/
namespace NearCubicWires.RepairOrdinary.MatrixScoreWeightSelect
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def loadSlots : Fin 3 → Fin 6 := ![0,4,5]
noncomputable def load := RecoveryFocus.machine loadSlots FrameLoad.machine
noncomputable def fieldMachine : Machine 6 7 := Composition.machine machine load

theorem field_run (pre suffix apre asuffix positive negative magnitude bits : List Bool)
    (cap : ℕ) (sign bit : Bool) (hp : positive.length≤1) (hn : negative.length≤1)
    (hm : magnitude.length≤2*bits.length+1) :
    ∃ actual : ExecutionReceipt 6 7,
      runFrom fieldMachine (4*bits.length+6) (cfg 0 (pre++frame (sign::bits)++suffix) pre.length
        (apre++[true,bit]++asuffix) apre.length positive negative magnitude cap)=some actual ∧
      actual.final=cfg 6 (pre++frame (sign::bits)++suffix) (pre.length+2*bits.length+3)
        (apre++[true,bit]++asuffix) (apre.length+2) [bit && !sign] [bit && sign]
        (frame bits) (max cap (2*bits.length+1)) ∧ actual.steps=4*bits.length+6 := by
  let source := pre++frame (sign::bits)++suffix
  let assignment := apre++[true,bit]++asuffix
  obtain ⟨first,hf,hff,hfs⟩ := select_run pre suffix apre asuffix positive negative magnitude bits cap sign bit hp hn
  obtain ⟨base,hb,hbf,hbs,_⟩ := FrameLoad.load_run (pre++[true,sign]) bits suffix magnitude hm
  have hsource : (pre++[true,sign])++frame bits++suffix=source := by
    simp [source,frame,List.append_assoc]
  have hpre : (pre++[true,sign]).length=pre.length+2 := by simp
  rw [hsource,hpre] at hb hbf
  obtain ⟨padded,hpad,hpadf,hpads,_⟩ := ZeroPadding.run_config FrameLoad.machine ![0,0,cap] _ _ base hb
  let entry := ZeroPadding.config ![0,0,cap]
    (FrameLoad.scan 0 source (pre.length+2) [] magnitude)
  have hi : RecoveryFocus.config loadSlots first.final.heads first.final.tapes entry=
      Composition.restart first.final load.start := by
    apply WilliamsSourceCrop.focus_same
    · intro i
      rw [hff]
      fin_cases i <;> simp [loadSlots,cfg,entry,ZeroPadding.config,FrameLoad.scan]
    · intro i
      rw [hff]
      fin_cases i <;> simp [loadSlots,cfg,entry,ZeroPadding.config,ZeroPadding.pad,FrameLoad.scan,
        StablePartition.Workspace.overlay,source]
  obtain ⟨last,hl,hlf,hls⟩ := RecoveryFocus.run_config loadSlots (by decide) FrameLoad.machine
    first.final.heads first.final.tapes _ entry padded hpad
  rw [hi] at hl
  have hj := Composition.run_join machine load 2 (4*bits.length+3)
    (cfg 0 source pre.length assignment apre.length positive negative magnitude cap) first last hf hl
  have htime : 2+1+(4*bits.length+3)=4*bits.length+6 := by omega
  rw [htime] at hj
  have pick (i : Fin 6) : RecoveryFocus.pick loadSlots i=
      (![some 0,none,none,none,some 1,some 2] : Fin 6 → Option (Fin 3)) i := by
    fin_cases i
    · exact RecoveryFocus.pick_slot loadSlots (by decide) 0
    · decide
    · decide
    · decide
    · exact RecoveryFocus.pick_slot loadSlots (by decide) 1
    · exact RecoveryFocus.pick_slot loadSlots (by decide) 2
  refine ⟨Composition.joinedReceipt first last,hj,?_,?_⟩
  · change Composition.rightConfig 3 last.final=_
    rw [hlf,hpadf,hbf,hff]
    apply configuration_ext
    · rfl
    · funext i
      fin_cases i <;> simp [Composition.rightConfig,RecoveryFocus.config,pick,ZeroPadding.config,
        FrameLoad.reset,cfg]
      omega
    · funext i
      fin_cases i <;> simp [Composition.rightConfig,RecoveryFocus.config,pick,ZeroPadding.config,
        FrameLoad.reset,cfg,ZeroPadding.pad,source]
      simpa [ZeroPadding.pad] using Rewind.Workspace.pad_zeros cap (2*bits.length+1)
  · change first.steps+1+last.steps=_
    rw [hfs,hls,hpads,hbs]
    omega

end NearCubicWires.RepairOrdinary.MatrixScoreWeightSelect
