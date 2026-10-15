import Proof.Amplification.RecoveryTableSkip

/-! The two table buffers share the already produced width/cap drivers.
The first counted copy and the row skipper execute on eleven fixed tapes. -/
namespace NearCubicWires.RepairOrdinary.RecoveryColdTables
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open RepairSource.VerifierDecoding
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def tailHeads : Fin 5→Nat := ![1,1,0,0,0]
def tailTapes (width : Nat) : Fin 5→List Bool := ![CompareMachine.word (2*width),CompareMachine.word 0,[],[],[false]]
def initial {s : Nat} (q : Fin s) (word : List Bool) (k width cap : Nat) : Configuration 11 s :=
  TapeEmbedding.config tailHeads (tailTapes width) (RecoveryColdTableSlice.cfg q word (2*k) 0 cap)
def sliceDone {s : Nat} (q : Fin s) (word rest : List Bool) (n cap : Nat) : Configuration 6 s :=
  {RecoveryColdTableSlice.copied q word rest n cap with
    tapes:=Function.update (RecoveryColdTableSlice.copied q word rest n cap).tapes 5 [true]}
def inner {s : Nat} (q : Fin s) (word rest : List Bool) (n width cap : Nat) : Configuration 11 s :=
  TapeEmbedding.config tailHeads (tailTapes width) (sliceDone q word rest n cap)
def skipped {s : Nat} (q : Fin s) (word rest : List Bool) (n width cap : Nat) : Configuration 11 s :=
  {inner q word rest n width cap with
    heads:=Function.update (inner q word rest n width cap).heads 3 (8*width*n)}
noncomputable def firstProgram := TapeEmbedding.machine 5 RecoveryColdTableSlice.machine

theorem first_run (cap width : Nat) (word : List Bool) (k : Nat) :
    ∃ r,runFrom firstProgram (RecoveryColdTableSlice.budget cap word)
        (initial firstProgram.start word k width cap)=some r ∧
      r.steps ≤ RecoveryColdTableSlice.budget cap word ∧
      r.final.heads 5=0 ∧ r.final.tapes 5=[(readCount cap (word.drop k)).isSome] ∧
      r.final.heads 10=0 ∧ r.final.tapes 10=[false] ∧
      ∀ n rest,readCount cap (word.drop k)=some (n,rest) → n ≤ cap ∧
        r.final=inner r.final.control word rest n width cap := by
  obtain ⟨base,hr,hb,hh,ht,hready⟩ := RecoveryColdTableSlice.slice_run cap word k
  let r := TapeEmbedding.receipt tailHeads (tailTapes width) base
  have h := TapeEmbedding.run_embed RecoveryColdTableSlice.machine tailHeads (tailTapes width) _ _ base hr
  refine ⟨r,h,hb,hh,ht,rfl,rfl,?_⟩
  intro n rest hp
  obtain ⟨hn,hh',ht'⟩ := hready n rest hp
  have he : base.final=sliceDone base.final.control word rest n cap := by
    apply configuration_ext
    · rfl
    · exact hh'
    · exact ht'
  refine ⟨hn,?_⟩
  change TapeEmbedding.config tailHeads (tailTapes width) base.final=_
  rw [he]
  rfl

def skipSlots : Fin 3→Fin 11 := ![3,6,1]
theorem skipSlots_injective : Function.Injective skipSlots := by decide
noncomputable def skipProgram := RecoveryFocus.machine skipSlots RecoveryColdTableSkip.machine

open private focus_configuration from Proof.Amplification.RecoveryValuationStreamTapes

theorem skip_input (word rest : List Bool) (n width cap : Nat) :
    RecoveryFocus.config skipSlots (inner skipProgram.start word rest n width cap).heads
      (inner skipProgram.start word rest n width cap).tapes
      (RepeatMachine.cfg 0 (RecoveryColdTableSkip.source (frame rest) width 0) n 1)=
      inner skipProgram.start word rest n width cap := by
  apply focus_configuration skipSlots skipSlots_injective
  · rfl
  · intro j; fin_cases j <;> rfl
  · intro j; fin_cases j <;> rfl
  · intro i _; rfl
  · intro i _; rfl

theorem skip_output (word rest : List Bool) (n width cap : Nat) :
    RecoveryFocus.config skipSlots (inner skipProgram.start word rest n width cap).heads
      (inner skipProgram.start word rest n width cap).tapes
      (RepeatMachine.cfg 3 (RecoveryColdTableSkip.source (frame rest) width (8*width*n)) n 1)=
      skipped (RepeatMachine.phaseCode 8 3) word rest n width cap := by
  apply focus_configuration skipSlots skipSlots_injective
  · rfl
  · intro j; fin_cases j <;> rfl
  · intro j; fin_cases j <;> rfl
  · intro i hi
    change (inner _ word rest n width cap).heads i=
      Function.update (inner _ word rest n width cap).heads 3 (8*width*n) i
    exact (Function.update_of_ne (Ne.symm (hi 0)) _ _).symm
  · intro i _; rfl

theorem skip_run (word rest : List Bool) (n width cap : Nat) :
    ∃ r,runFrom skipProgram (RecoveryColdTableSkip.budget width n)
        (inner skipProgram.start word rest n width cap)=some r ∧
      r.steps ≤ RecoveryColdTableSkip.budget width n ∧
      r.final=skipped r.final.control word rest n width cap := by
  obtain ⟨base,hr,hb,hf⟩ := RecoveryColdTableSkip.skip_run (frame rest) width n 0
  simp only [Nat.zero_add] at hf
  obtain ⟨r,h,hfinal,hsteps⟩ := RecoveryFocus.run_config skipSlots skipSlots_injective
    RecoveryColdTableSkip.machine (inner skipProgram.start word rest n width cap).heads
      (inner skipProgram.start word rest n width cap).tapes _ _ base hr
  rw [skip_input] at h
  refine ⟨r,h,hsteps.le.trans hb,?_⟩
  rw [hfinal,hf]
  exact skip_output word rest n width cap

end NearCubicWires.RepairOrdinary.RecoveryColdTables
