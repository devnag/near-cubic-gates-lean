import Proof.Amplification.RecoveryAssignmentCounterErase

/-! The sixteen-tape reusable assignment boundary: fifteen lookup tapes and
one retained erase driver. Only the old counter backing is arbitrary. -/
namespace NearCubicWires.RepairOrdinary.RecoveryAssignment
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryValuationStream
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def reuseTapes (d : Data) (count cap : Nat) (binaryCount committed : List Bool) (guard : Bool)
    (sourceCapacity total resetCapacity : Nat) : Fin 16→List Bool :=
  fun i=>Fin.addCases (readyTapes d count cap binaryCount committed guard sourceCapacity total resetCapacity)
    (fun _ : Fin 1=>List.replicate total true) i
noncomputable def reuseInput (d : Data) (cap : Nat) (binaryCount committed : List Bool) (guard : Bool)
    (sourceCapacity total resetCapacity : Nat) (backing : List Bool) : Fin 16→List Bool :=
  Function.update (reuseTapes d 0 cap binaryCount committed guard sourceCapacity total resetCapacity) 8 backing

theorem reuse_counter_zero (d : Data) (cap : Nat) (binaryCount committed : List Bool) (guard : Bool)
    (sourceCapacity total resetCapacity : Nat) (h : 1≤total) :
    reuseTapes d 0 cap binaryCount committed guard sourceCapacity total resetCapacity 8=List.replicate total false := by
  simp [reuseTapes,Fin.addCases,readyTapes,paddedTapes,padding,cfg_tapes,CompareMachine.word,ZeroPadding.pad]
  rw [← List.replicate_succ,Nat.sub_add_cancel h]

theorem reuse_counter_length (d : Data) (count cap : Nat) (binaryCount committed : List Bool) (guard : Bool)
    (sourceCapacity total resetCapacity : Nat) (h : count+1≤total) :
    (reuseTapes d count cap binaryCount committed guard sourceCapacity total resetCapacity 8).length=total := by
  simp [reuseTapes,Fin.addCases,readyTapes,paddedTapes,padding,cfg_tapes,ZeroPadding.pad_length,CompareMachine.word,
    Nat.max_eq_left h]

theorem reuse_clear (d : Data) (cap : Nat) (binaryCount committed : List Bool) (guard : Bool)
    (sourceCapacity total resetCapacity : Nat) (backing : List Bool)
    (hb : backing.length≤total) (ht : 1≤total) (hr : total+1≤resetCapacity) :
    ReadyRun eraseMachine (2*total+4)
      (reuseInput d cap binaryCount committed guard sourceCapacity total resetCapacity backing)
      (reuseTapes d 0 cap binaryCount committed guard sourceCapacity total resetCapacity) := by
  have h := erase_counter_ready (reuseInput d cap binaryCount committed guard sourceCapacity total resetCapacity backing)
    total resetCapacity (by simpa [reuseInput] using hb)
    (by simp [reuseInput,reuseTapes,Fin.addCases]) (by simp [reuseInput,reuseTapes,readyTapes,Fin.addCases]) hr
  have he : Function.update
      (reuseInput d cap binaryCount committed guard sourceCapacity total resetCapacity backing) 8
      (List.replicate total false)=reuseTapes d 0 cap binaryCount committed guard sourceCapacity total resetCapacity := by
    rw [reuseInput,Function.update_idem]
    rw [← reuse_counter_zero d cap binaryCount committed guard sourceCapacity total resetCapacity ht]
    exact Function.update_eq_self _ _
  rw [he] at h
  exact h

noncomputable def scanMachine := TapeEmbedding.machine 1 rewindMachine
noncomputable def reusableMachine := Composition.machine eraseMachine scanMachine

end NearCubicWires.RepairOrdinary.RecoveryAssignment
