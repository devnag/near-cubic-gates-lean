import Proof.MachineModel.OrdinaryMatrixCoefficientBitLeaf

/-! Paid prefix and tail scans around a selected coefficient bit. The
physical byte-offset sentinel is retained at head one, the sign flag is
retained, and neither global stream is rewound inside this coefficient. -/
namespace NearCubicWires.RepairOrdinary.MatrixCoefficientBitScans
open LocalBitMultitape
open MatrixCoefficientBitLeaf (cfg)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def skipSlots : Fin 3 → Fin 4 := ![1,0,3]
def tailSlots : Fin 3 → Fin 4 := ![0,1,3]
theorem skip_injective : Function.Injective skipSlots := by decide
theorem tail_injective : Function.Injective tailSlots := by decide
noncomputable def skip := RecoveryFocus.machine skipSlots (MatrixRawBlock.machine false)
noncomputable def tail := RecoveryFocus.machine tailSlots MatrixCoefficientFields.threshold

theorem skip_run (bits pre suffix out : List Bool) (flag : Bool) : ∃ actual,
    runFrom skip (2*bits.length+4) (cfg skip.start (pre++bits++suffix) pre.length bits.length flag out)=some actual ∧
    actual.final=cfg actual.final.control (pre++bits++suffix) (pre.length+bits.length) bits.length flag out ∧
    actual.steps=2*bits.length+4 := by
  obtain ⟨base,hb,bf,bs,_⟩ := MatrixRawBlock.block_run false pre bits suffix out
  let entry := cfg skip.start (pre++bits++suffix) pre.length bits.length flag out
  have hi : RecoveryFocus.config skipSlots entry.heads entry.tapes
      (MatrixRawBlock.config 0 (UnaryTemplate.tape bits.length) 1 (pre++bits++suffix) pre.length out)=entry := by
    apply WilliamsSourceCrop.focus_same
    · intro j; fin_cases j <;> rfl
    · intro j; fin_cases j <;> rfl
  obtain ⟨actual,ha,af,as⟩ := RecoveryFocus.run_config skipSlots skip_injective (MatrixRawBlock.machine false)
    entry.heads entry.tapes _ _ base hb
  rw [hi] at ha
  refine ⟨actual,ha,?_,as.trans bs⟩
  rw [af,bf]
  have hp (i : Fin 4) : RecoveryFocus.pick skipSlots i=(![some 1,some 0,none,some 2] : Fin 4 → Option (Fin 3)) i := by
    fin_cases i
    · exact RecoveryFocus.pick_slot skipSlots skip_injective 1
    · exact RecoveryFocus.pick_slot skipSlots skip_injective 0
    · decide
    · exact RecoveryFocus.pick_slot skipSlots skip_injective 2
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [RecoveryFocus.config,hp,entry,cfg,MatrixRawBlock.config,MatrixRawBlock.selected]
  · funext i; fin_cases i <;> simp [RecoveryFocus.config,hp,entry,cfg,MatrixRawBlock.config,MatrixRawBlock.selected]

theorem tail_run (bits pre suffix out : List Bool) (offset : ℕ) (flag : Bool) : ∃ actual,
    runFrom tail (2*bits.length+1) (cfg tail.start (pre++frame bits++suffix) pre.length offset flag out)=some actual ∧
    actual.final=cfg actual.final.control (pre++frame bits++suffix) (pre.length+(frame bits).length) offset flag out ∧
    actual.steps=2*bits.length+1 := by
  obtain ⟨base,hb,bf,bs⟩ := MatrixCoefficientFields.threshold_run bits pre suffix out offset
  let entry := cfg tail.start (pre++frame bits++suffix) pre.length offset flag out
  have hi : RecoveryFocus.config tailSlots entry.heads entry.tapes
      (MatrixCoefficientFields.cfg MatrixCoefficientFields.threshold.start (pre++frame bits++suffix) pre.length offset out)=entry := by
    apply WilliamsSourceCrop.focus_same
    · intro j; fin_cases j <;> rfl
    · intro j; fin_cases j <;> rfl
  obtain ⟨actual,ha,af,as⟩ := RecoveryFocus.run_config tailSlots tail_injective MatrixCoefficientFields.threshold
    entry.heads entry.tapes _ _ base hb
  rw [hi] at ha
  refine ⟨actual,ha,?_,as.trans bs⟩
  rw [af,bf]
  have hp (i : Fin 4) : RecoveryFocus.pick tailSlots i=(![some 0,some 1,none,some 2] : Fin 4 → Option (Fin 3)) i := by
    fin_cases i
    · exact RecoveryFocus.pick_slot tailSlots tail_injective 0
    · exact RecoveryFocus.pick_slot tailSlots tail_injective 1
    · decide
    · exact RecoveryFocus.pick_slot tailSlots tail_injective 2
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [RecoveryFocus.config,hp,entry,cfg,MatrixCoefficientFields.cfg]
  · funext i; fin_cases i <;> simp [RecoveryFocus.config,hp,entry,cfg,MatrixCoefficientFields.cfg]

end NearCubicWires.RepairOrdinary.MatrixCoefficientBitScans
