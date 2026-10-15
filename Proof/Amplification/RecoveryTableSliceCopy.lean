import Proof.Amplification.RecoveryTableSliceCount

/-! The table slice copies its actual remaining framed suffix, paying the
output rewind and preserving the produced count/cap drivers. -/
namespace NearCubicWires.RepairOrdinary.RecoveryColdTableSlice
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open RepairSource.VerifierDecoding
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def copySlots : Fin 3→Fin 6 := ![0,3,4]
theorem copySlots_injective : Function.Injective copySlots := by decide
noncomputable def copyProgram := RecoveryFocus.machine copySlots PCPFieldMoves.advanceMachine
def copied {s : Nat} (q : Fin s) (word rest : List Bool) (n cap : Nat) : Configuration 6 s :=
  ⟨q,![2*word.length+1,1,1,0,0,0],![frame word,CompareMachine.word n,CompareMachine.word cap,
    frame rest,List.replicate (2*rest.length+1) false,[false]]⟩

open private focus_configuration from Proof.Amplification.RecoveryValuationStreamTapes

theorem copy_input (word rest : List Bool) (k n cap : Nat)
    (hp : readCount cap (word.drop k)=some (n,rest)) :
    RecoveryFocus.config copySlots (cfg (0 : Fin 5) word (2*k+2*n+2) n cap).heads
      (cfg (0 : Fin 5) word (2*k+2*n+2) n cap).tapes
      (PCPFieldMoves.entry (before word k n) rest [] 0 0)=
      cfg copyProgram.start word (2*k+2*n+2) n cap := by
  obtain ⟨hs,hl,_⟩ := suffix_geometry cap n k word rest hp
  apply focus_configuration copySlots copySlots_injective
  · rfl
  · intro j; fin_cases j
    · exact hl
    · rfl
    · rfl
  · intro j; fin_cases j
    · change ZeroPadding.pad 0 (before word k n++frame rest++[])=frame word
      simpa [ZeroPadding.pad] using hs
    · rfl
    · rfl
  · intro i _; rfl
  · intro i _; rfl

theorem copy_output (word rest : List Bool) (k n cap : Nat)
    (hp : readCount cap (word.drop k)=some (n,rest)) (q : Fin 5) :
    RecoveryFocus.config copySlots (cfg q word (2*k+2*n+2) n cap).heads
      (cfg q word (2*k+2*n+2) n cap).tapes
      (⟨q,![(before word k n).length+2*rest.length+1,0,0],
        PCPFieldMoves.output (before word k n) rest [] 0 0⟩ : Configuration 3 5)=
      copied q word rest n cap := by
  obtain ⟨hs,_,_⟩ := suffix_geometry cap n k word rest hp
  have hl : (before word k n).length+2*rest.length+1=2*word.length+1 := by
    have he := congrArg List.length hs
    simp only [List.length_append,frame_length] at he
    omega
  apply focus_configuration copySlots copySlots_injective
  · rfl
  · intro j; fin_cases j
    · exact hl
    · rfl
    · rfl
  · intro j; fin_cases j
    · change before word k n++frame rest++[]=frame word
      simpa only [List.append_nil] using hs
    · simp [PCPFieldMoves.output,ZeroPadding.pad]
      rfl
    · simp [PCPFieldMoves.output]
      rfl
  · intro i hi; fin_cases i <;> try rfl
    exact False.elim (hi 0 rfl)
  · intro i hi; fin_cases i <;> try rfl
    · exact False.elim (hi 1 rfl)
    · exact False.elim (hi 2 rfl)

theorem copy_run (word rest : List Bool) (k n cap : Nat)
    (hp : readCount cap (word.drop k)=some (n,rest)) :
    ∃ r,runFrom copyProgram (4*rest.length+4)
        (cfg copyProgram.start word (2*k+2*n+2) n cap)=some r ∧
      r.final=copied r.final.control word rest n cap ∧ r.steps=4*rest.length+4 := by
  obtain ⟨base,hr,ht,hh,hb⟩ := PCPFieldMoves.advance_run (before word k n) rest [] 0 0
  obtain ⟨r,h,hfinal,hsteps⟩ := RecoveryFocus.run_config copySlots copySlots_injective
    PCPFieldMoves.advanceMachine (cfg (0 : Fin 5) word (2*k+2*n+2) n cap).heads
      (cfg (0 : Fin 5) word (2*k+2*n+2) n cap).tapes _ _ base hr
  rw [copy_input word rest k n cap hp] at h
  refine ⟨r,h,?_,hsteps.trans hb⟩
  have he : base.final=(⟨base.final.control,
      ![(before word k n).length+2*rest.length+1,0,0],
      PCPFieldMoves.output (before word k n) rest [] 0 0⟩ : Configuration 3 5) := by
    apply configuration_ext
    · rfl
    · exact hh
    · exact ht
  rw [hfinal,he]
  exact copy_output word rest k n cap hp _

end NearCubicWires.RepairOrdinary.RecoveryColdTableSlice
