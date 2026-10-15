import Proof.Amplification.RecoveryTablesState

/-! The second counted copy consumes the parsed inner suffix at the actual
row-skip cursor, leaving both literal table buffers and both counts present. -/
namespace NearCubicWires.RepairOrdinary.RecoveryColdTables
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open RepairSource.VerifierDecoding
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def outerSlots : Fin 6→Fin 11 := ![3,7,2,8,9,10]
theorem outerSlots_injective : Function.Injective outerSlots := by decide
noncomputable def outerProgram := RecoveryFocus.machine outerSlots RecoveryColdTableSlice.machine
noncomputable def outer {s : Nat} (q : Fin s) (word innerBits outerBits : List Bool)
    (n m width cap : Nat) : Configuration 11 s :=
  RecoveryFocus.config outerSlots (skipped q word innerBits n width cap).heads
    (skipped q word innerBits n width cap).tapes (sliceDone q innerBits outerBits m cap)

open private focus_configuration from Proof.Amplification.RecoveryValuationStreamTapes

theorem outer_input (word bits : List Bool) (n width cap : Nat) :
    RecoveryFocus.config outerSlots (skipped outerProgram.start word bits n width cap).heads
      (skipped outerProgram.start word bits n width cap).tapes
      (RecoveryColdTableSlice.cfg RecoveryColdTableSlice.machine.start bits (2*(4*width*n)) 0 cap)=
      skipped outerProgram.start word bits n width cap := by
  apply focus_configuration outerSlots outerSlots_injective
  · rfl
  · intro j; fin_cases j
    · change 2*(4*width*n)=8*width*n
      ring
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
  · intro j; fin_cases j <;> rfl
  · intro i _; rfl
  · intro i _; rfl

theorem outer_run (word bits : List Bool) (n width cap : Nat) :
    ∃ r,runFrom outerProgram (RecoveryColdTableSlice.budget cap bits)
        (skipped outerProgram.start word bits n width cap)=some r ∧
      r.steps ≤ RecoveryColdTableSlice.budget cap bits ∧ r.final.heads 10=0 ∧
      r.final.tapes 10=[(readCount cap (bits.drop (4*width*n))).isSome] ∧
      ∀ m rest,readCount cap (bits.drop (4*width*n))=some (m,rest) → m ≤ cap ∧
        r.final=outer r.final.control word bits rest n m width cap := by
  obtain ⟨base,hr,hb,hh,ht,hready⟩ := RecoveryColdTableSlice.slice_run cap bits (4*width*n)
  obtain ⟨r,h,hfinal,hsteps⟩ := RecoveryFocus.run_config outerSlots outerSlots_injective
    RecoveryColdTableSlice.machine (skipped outerProgram.start word bits n width cap).heads
      (skipped outerProgram.start word bits n width cap).tapes _ _ base hr
  rw [outer_input] at h
  have hpick : RecoveryFocus.pick outerSlots (10 : Fin 11)=some 5 :=
    RecoveryFocus.pick_slot outerSlots outerSlots_injective 5
  refine ⟨r,h,hsteps.le.trans hb,?_,?_,?_⟩
  · rw [hfinal]; simpa only [RecoveryFocus.config,hpick] using hh
  · rw [hfinal]; simpa only [RecoveryFocus.config,hpick] using ht
  · intro m rest hp
    obtain ⟨hm,hh',ht'⟩ := hready m rest hp
    have he : base.final=sliceDone base.final.control bits rest m cap := by
      apply configuration_ext
      · rfl
      · exact hh'
      · exact ht'
    refine ⟨hm,?_⟩
    rw [hfinal,he]
    rfl

end NearCubicWires.RepairOrdinary.RecoveryColdTables
