import Proof.Amplification.RecoveryTseitinReadOnly

/-! Both actual raw input counters survive all four physical reference banks. -/
namespace NearCubicWires.RepairSource.RecoveryTseitinReferences
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryTseitinReadOnly
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem raw_sum_readonly (i : Fin 2) : NoWrite ClockUnarySum.raw (i.castAdd 1) := by
  intro q bs a ha
  fin_cases q <;> fin_cases i <;> simp [ClockUnarySum.raw] at ha
  all_goals split at ha <;> cases ha <;> rfl
theorem sum_readonly (i : Fin 2) : NoWrite ClockUnarySum.machine ((i.castAdd 1).castAdd 1) :=
  rewind ClockUnarySum.raw (i.castAdd 1) (raw_sum_readonly i)
theorem sums_readonly (i : Fin 2) : NoWrite sumsMachine (i.castAdd 8) := by
  fin_cases i
  · apply composition
    · apply composition
      · exact focus (slots 0) (injective 0) ClockUnarySum.machine 0 (sum_readonly 0)
      · exact focus (slots 1) (injective 1) ClockUnarySum.machine 0 (sum_readonly 0)
    · exact focus (slots 2) (injective 2) ClockUnarySum.machine 0 (sum_readonly 0)
  · apply composition
    · apply composition
      · exact focus (slots 0) (injective 0) ClockUnarySum.machine 1 (sum_readonly 1)
      · exact unselected (slots 1) _ 1 (by decide)
    · exact unselected (slots 2) _ 1 (by decide)
theorem bank_counter_away (k : Fin 4) (i : Fin 2) : ∀ j,bankSlots k j≠i.castAdd 1060 := by
  intro j he
  have hv:=congrArg Fin.val he
  have hi:=i.isLt
  dsimp only [bankSlots,referenceSlot] at hv
  split_ifs at hv
  · change 10+k.val=i.val at hv
    omega
  · fin_cases k <;> dsimp [countSlot] at hv <;> omega
  · change 14+262*k.val+j.val=i.val at hv
    omega
theorem banks_readonly {s : Nat} (parts : Fin 4→Machine 1062 s) (i : Fin 1062)
    (hp : ∀ k,NoWrite (parts k) i) (ks : List (Fin 4)) : NoWrite (Sequence.bankMachine parts ks) i := by
  induction ks with
  | nil => intro q bs a ha; contradiction
  | cons k ks ih => exact composition (parts k) (Sequence.bankMachine parts ks) i (hp k) ih
theorem cold_readonly (i : Fin 2) : NoWrite coldMachine (i.castAdd 1060) := by
  apply composition
  · exact focus scalarSlot scalar_injective sumsMachine (i.castAdd 8) (sums_readonly i)
  · exact banks_readonly referencePart (i.castAdd 1060)
      (fun k=>unselected (bankSlots k) _ _ (bank_counter_away k i)) order

end NearCubicWires.RepairSource.RecoveryTseitinReferences
