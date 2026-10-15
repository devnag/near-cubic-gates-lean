import Proof.Amplification.RecoveryTseitinColdStream

/-! Retain the actual cold kernel state at the enclosing node consumer.
Its physically generated capacity and cleared log remain available. -/
namespace NearCubicWires.RepairSource.RecoveryTseitinTautology.Cold
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

private theorem join_state {s t : Nat} (driver : Machine 262 s) (stream : Machine 242 t)
    (startData : Fin 262→List Bool) (cap count driverBudget streamBudget : Nat)
    (hd : ∃ out,ClockJoin.ReadyRun driver driverBudget startData out ∧
      out 3=List.replicate cap true ∧ out 241=CompareMachine.word count ∧ out 242=List.replicate count true ∧
      (∀ i : Fin 242,i≠3 → i≠241 → out (i.castAdd 20)=[]))
    (base : ExecutionReceipt 242 t)
    (hb : runFrom stream streamBudget ⟨stream.start,fun _=>0,bankInput cap count []⟩=some base)
    (bs : base.steps ≤ streamBudget) :
    ∃ r,run (Composition.machine driver (RecoveryFocus.machine streamSlots stream))
      (driverBudget+1+streamBudget) startData=some r ∧
      (∀ i,r.final.tapes (streamSlots i)=base.final.tapes i ∧ r.final.heads (streamSlots i)=base.final.heads i) ∧
      r.steps≤driverBudget+1+streamBudget := by
  obtain ⟨data,⟨first,hf,ft,fh,fs⟩,d3,d241,_d242,db⟩:=hd
  obtain ⟨last,hl,_lc,ls,lh,lt,_lo⟩:=RecoveryFocus.dock streamSlots stream_injective stream streamBudget
    first.final.heads first.final.tapes _ (by intro i; exact fh _)
    (by
      intro i
      rw [ft]
      by_cases h3 : i=3
      · subst i; exact d3
      by_cases h241 : i=241
      · subst i; exact d241
      simpa [bankInput,h3,h241,streamSlots] using db i h3 h241) base hb
  exact ⟨_,Composition.run_join driver (RecoveryFocus.machine streamSlots stream) _ _ _ first last hf hl,
    fun i=>⟨lt i,lh i⟩,Nat.add_le_add (Nat.add_le_add_right fs 1) (ls.le.trans bs)⟩

theorem state_run (count : Nat) : ∃ after : Fin 239→List Bool,∃ r,
    run machine (budget count) (driversInput count)=some r ∧
      (∀ i : Fin 239,r.final.tapes (i.castAdd 23)=after i ∧ r.final.heads (i.castAdd 23)=0) ∧
      Valid (driverCapacity count) count after ∧ r.steps≤budget count := by
  obtain ⟨after,base,hb,bh,bt,bv,bs⟩:=prepared_run (driverCapacity count) count [] (driver_capacity count)
  have he : bankHeads []=(fun _ : Fin 242=>0) := by funext i; simp [bankHeads]
  rw [he] at hb
  obtain ⟨r,hr,ho,rs⟩:=join_state driversMachine preparedMachine (driversInput count)
    (driverCapacity count) count (driversBudget count) (preparedBudget (driverCapacity count) count)
    (drivers_run count) base hb bs
  refine ⟨after,r,hr,?_,bv,rs⟩
  intro i
  have h:=ho ((i.castAdd 2).castAdd 1)
  rw [bt,bh] at h
  have hi : streamSlots ((i.castAdd 2).castAdd 1)=i.castAdd 23 := Fin.ext rfl
  rw [hi] at h
  simpa only [loopCfg,RepeatMachine.cfg,controlConfig,TapeEmbedding.config,Fin.addCases_left,input,heads] using h

theorem reference_driver_run (count : Nat) : ∃ r,
    run machine (budget count) (driversInput count)=some r ∧
      r.final.tapes 0=ZeroPadding.pad (driverCapacity count) (RepairOrdinary.frame count.bits) ∧
      r.final.tapes 3=List.replicate (driverCapacity count) true ∧
      r.final.tapes 4=List.replicate (driverCapacity count+1) false ∧
      r.final.heads 0=0 ∧ r.final.heads 3=0 ∧ r.final.heads 4=0 ∧ r.steps≤budget count := by
  obtain ⟨after,r,hr,ho,hv,hs⟩:=state_run count
  exact ⟨r,hr,(ho 0).1.trans hv.indexTape,(ho 3).1.trans hv.driver,(ho 4).1.trans hv.log,
    (ho 0).2,(ho 3).2,(ho 4).2,hs⟩

end NearCubicWires.RepairSource.RecoveryTseitinTautology.Cold
