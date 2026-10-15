import Proof.Amplification.RecoveryViewBank

/-! Complete seven-copy raw-view bank preparation, with all heads retained
and every finite-control call return included in the exact step count. -/
namespace NearCubicWires.RepairOrdinary.RecoveryColdView
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem width_call (bits : List Bool) (pos : Nat) (a : Fin 100→List Bool) (ha : Sources bits a) :
    AtRun doubleProgram (4*width bits+6) (bankHeads pos) (stage3 bits a) (stage4 bits a) := by
  have h := double_at doubleSlots doubleSlots_injective (bankHeads pos) (stage3 bits a)
    (width bits) (reset1 bits)
    (by
      intro j
      fin_cases j <;> simp [doubleSlots,stage3,stage2,stage1,put]
      · exact ha.width
      · exact ha.empty 62 (by decide))
    (by intro j; fin_cases j <;> rfl)
  rw [max_eq_left (show 2*width bits+2≤reset1 bits by unfold reset1; omega)] at h
  simpa [doubleProgram,doubleSlots,stage4,put] using h

theorem cap_call (bits : List Bool) (pos : Nat) (a : Fin 100→List Bool) (ha : Sources bits a) :
    AtRun unaryProgram (2*limit bits+6) (bankHeads pos) (stage4 bits a) (stage5 bits a) := by
  have h := unary_at unarySlots unarySlots_injective (bankHeads pos) (stage4 bits a)
    (limit bits) (reset1 bits)
    (by
      intro j
      fin_cases j <;> simp [unarySlots,stage4,stage3,stage2,stage1,put]
      · exact ha.cap
      · exact ha.empty 96 (by decide))
    (by intro j; fin_cases j <;> rfl)
  simpa [unaryProgram,unarySlots,stage5,put,reset5] using h

theorem inner_erase_call (bits : List Bool) (pos : Nat) (a : Fin 100→List Bool) (ha : Sources bits a) :
    AtRun (eraseProgram 0) (2*erase bits+6) (bankHeads pos) (stage5 bits a) (stage6 bits a) := by
  have h := erase_at (eraseSlots 0) (eraseSlots_injective 0) (bankHeads pos) (stage5 bits a)
    (erase bits) (reset5 bits)
    (by
      intro j
      fin_cases j <;> simp [eraseSlots,stage5,stage4,stage3,stage2,stage1,put]
      · exact ha.erase
      · exact ha.empty 99 (by decide)
      · exact ha.empty 53 (by decide))
    (by intro j; fin_cases j <;> rfl)
  simpa [eraseProgram,eraseSlots,stage6,put,reset6] using h

theorem outer_erase_call (bits : List Bool) (pos : Nat) (a : Fin 100→List Bool) (ha : Sources bits a) :
    AtRun (eraseProgram 1) (2*erase bits+6) (bankHeads pos) (stage6 bits a) (stage7 bits a) := by
  have h := erase_at (eraseSlots 1) (eraseSlots_injective 1) (bankHeads pos) (stage6 bits a)
    (erase bits) (reset6 bits)
    (by
      intro j
      fin_cases j <;> simp [eraseSlots,stage6,stage5,stage4,stage3,stage2,stage1,put]
      · exact ha.erase
      · exact ha.empty 99 (by decide)
      · exact ha.empty 89 (by decide))
    (by intro j; fin_cases j <;> rfl)
  rw [max_eq_left (show erase bits+2≤reset6 bits from Nat.le_max_right _ _)] at h
  simpa [eraseProgram,eraseSlots,stage7,put] using h

theorem bank_run (bits : List Bool) (pos : Nat) (a : Fin 100→List Bool) (ha : Sources bits a) :
    AtRun bankProgram (bankBudget bits) (bankHeads pos) a (stage7 bits a) := by
  have h := ((((((zero_call bits pos a ha).seq (bound_call bits pos a ha)).seq
    (code_call bits pos a ha)).seq (width_call bits pos a ha)).seq
    (cap_call bits pos a ha)).seq (inner_erase_call bits pos a ha)).seq (outer_erase_call bits pos a ha)
  have he : ((((((4*width bits+8)+1+(4*width bits+8))+1+(4*width bits+8))+1+
      (4*width bits+6))+1+(2*limit bits+6))+1+(2*erase bits+6))+1+(2*erase bits+6)=bankBudget bits := by
    unfold bankBudget
    omega
  rw [he] at h
  exact h

end NearCubicWires.RepairOrdinary.RecoveryColdView
