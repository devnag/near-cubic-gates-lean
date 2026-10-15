import Proof.Amplification.RecoveryTseitinColdStream

/-! Reuse the checked cold binary-index production at the actual node
reference consumer. It handles zero as well as positive values and exposes
the physically incremented canonical framed reference, with the same budget. -/
namespace NearCubicWires.RepairSource.RecoveryTseitinTautology.Cold
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem prepared_reference (cap count : Nat) (hc : uniformCapacity count≤cap) : ∃ r,
    runFrom preparedMachine (preparedBudget cap count)
      ⟨preparedMachine.start,fun _=>0,bankInput cap count []⟩=some r ∧
      r.final.tapes 0=ZeroPadding.pad cap (RepairOrdinary.frame count.bits) ∧
      r.final.heads 0=0 ∧ r.steps≤preparedBudget cap count := by
  obtain ⟨after,r,hr,rh,rt,rv,rs⟩ := prepared_run cap count [] hc
  have he : bankHeads []=(fun _ : Fin 242=>0) := by funext i; simp [bankHeads]
  rw [he] at hr
  refine ⟨r,hr,?_,?_,rs⟩
  · rw [rt]
    exact rv.indexTape
  · rw [rh]
    rfl

private theorem reference_join {s t : Nat} (driver : Machine 262 s) (stream : Machine 242 t)
    (startData : Fin 262→List Bool) (cap count driverBudget streamBudget : Nat) (reference : List Bool)
    (hd : ∃ out,ClockJoin.ReadyRun driver driverBudget startData out ∧
      out 3=List.replicate cap true ∧ out 241=VerifierDecoding.CompareMachine.word count ∧
      out 242=List.replicate count true ∧
      (∀ i : Fin 242,i≠3 → i≠241 → out (i.castAdd 20)=[]))
    (ho : ∃ r,runFrom stream streamBudget
      ⟨stream.start,fun _=>0,bankInput cap count []⟩=some r ∧
      r.final.tapes 0=reference ∧ r.final.heads 0=0 ∧ r.steps ≤ streamBudget) : ∃ r,
    run (Composition.machine driver (RecoveryFocus.machine streamSlots stream))
      (driverBudget+1+streamBudget) startData=some r ∧
      r.final.tapes 0=reference ∧ r.final.heads 0=0 ∧ r.steps≤driverBudget+1+streamBudget := by
  obtain ⟨data,⟨first,hf,ft,fh,fs⟩,d3,d241,_d242,db⟩ := hd
  obtain ⟨base,hb,bt,bh,bs⟩ := ho
  obtain ⟨last,hl,_lc,ls,lh,lt,_lo⟩ := RecoveryFocus.dock streamSlots stream_injective
    stream streamBudget first.final.heads first.final.tapes _ (by intro i; exact fh _)
    (by
      intro i
      rw [ft]
      by_cases h3 : i=3
      · subst i; exact d3
      by_cases h241 : i=241
      · subst i; exact d241
      simpa [bankInput,h3,h241,streamSlots] using db i h3 h241) base hb
  have hwhole := Composition.run_join driver (RecoveryFocus.machine streamSlots stream) _ _ _ first last hf hl
  refine ⟨_,hwhole,(lt 0).trans bt,(lh 0).trans bh,?_⟩
  exact Nat.add_le_add (Nat.add_le_add_right fs 1) (ls.le.trans bs)

theorem reference_run (count : Nat) : ∃ r,
    run machine (budget count) (driversInput count)=some r ∧
      r.final.tapes 0=ZeroPadding.pad (driverCapacity count) (RepairOrdinary.frame count.bits) ∧
      r.final.heads 0=0 ∧ r.steps≤budget count :=
  reference_join driversMachine preparedMachine (driversInput count) (driverCapacity count) count
    (driversBudget count) (preparedBudget (driverCapacity count) count)
    (ZeroPadding.pad (driverCapacity count) (RepairOrdinary.frame count.bits))
    (drivers_run count) (prepared_reference (driverCapacity count) count (driver_capacity count))

end NearCubicWires.RepairSource.RecoveryTseitinTautology.Cold
