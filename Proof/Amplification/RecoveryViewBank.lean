import Proof.Amplification.RecoveryViewCopyCalls

/-! Fixed physical raw-view bank: seven copies use the scalar header and
one reusable log. Tape23 remains the shared certificate stream. -/
namespace NearCubicWires.RepairOrdinary.RecoveryColdView
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def width (bits : List Bool) := RecoveryColdValuation.width bits
def limit (bits : List Bool) := RecoveryColdValuation.cap bits
def erase (bits : List Bool) := RecoveryColdValuation.capacity bits
def bankHeads (pos : Nat) := Function.update (fun _ : Fin 100=>0) 23 pos
def put (a : Fin 100→List Bool) (i : Fin 100) (word : List Bool) (reset : Nat) :=
  Function.update (Function.update a i word) 98 (List.replicate reset false)
def reset1 (bits : List Bool) := 2*width bits+3
def reset5 (bits : List Bool) := max (reset1 bits) (limit bits+2)
def reset6 (bits : List Bool) := max (reset5 bits) (erase bits+2)
def stage1 (bits : List Bool) (a : Fin 100→List Bool) := put a 32 (frame (RecoveryColdHeader.zeroWord bits)) (reset1 bits)
def stage2 (bits : List Bool) (a : Fin 100→List Bool) := put (stage1 bits a) 63 (frame (RecoveryColdHeader.boundWord bits)) (reset1 bits)
def stage3 (bits : List Bool) (a : Fin 100→List Bool) := put (stage2 bits a) 68 (frame (RecoveryColdHeader.codeWord bits)) (reset1 bits)
def stage4 (bits : List Bool) (a : Fin 100→List Bool) := put (stage3 bits a) 62 (CompareMachine.word (2*width bits)) (reset1 bits)
def stage5 (bits : List Bool) (a : Fin 100→List Bool) := put (stage4 bits a) 96 (CompareMachine.word (limit bits)) (reset5 bits)
def stage6 (bits : List Bool) (a : Fin 100→List Bool) := put (stage5 bits a) 53 (List.replicate (erase bits) true) (reset6 bits)
def stage7 (bits : List Bool) (a : Fin 100→List Bool) := put (stage6 bits a) 89 (List.replicate (erase bits) true) (reset6 bits)

structure Sources (bits : List Bool) (a : Fin 100→List Bool) : Prop where
  width : a 2=CompareMachine.word (width bits)
  code : a 6=frame (RecoveryColdHeader.codeWord bits)
  bound : a 8=frame (RecoveryColdHeader.boundWord bits)
  zero : a 10=frame (RecoveryColdHeader.zeroWord bits)
  erase : a 16=List.replicate (erase bits) true
  cap : a 21=CompareMachine.word (limit bits)
  empty : ∀ (i : Fin 100), (32 : Nat) ≤ i.val → a i = []

def fieldSlots (j : Fin 3) : Fin 4→Fin 100 := ![![10,32,2,98],![8,63,2,98],![6,68,2,98]] j
def doubleSlots : Fin 3→Fin 100 := ![2,62,98]
def unarySlots : Fin 3→Fin 100 := ![21,96,98]
def eraseSlots (j : Fin 2) : Fin 4→Fin 100 := ![![16,99,53,98],![16,99,89,98]] j
theorem fieldSlots_injective (j : Fin 3) : Function.Injective (fieldSlots j) := by fin_cases j <;> decide
theorem doubleSlots_injective : Function.Injective doubleSlots := by decide
theorem unarySlots_injective : Function.Injective unarySlots := by decide
theorem eraseSlots_injective (j : Fin 2) : Function.Injective (eraseSlots j) := by fin_cases j <;> decide

noncomputable def fieldProgram (j : Fin 3) := RecoveryFocus.machine (fieldSlots j) RecoveryColdPaddedCopy.machine
noncomputable def doubleProgram := RecoveryFocus.machine doubleSlots doubleMachine
noncomputable def unaryProgram := RecoveryFocus.machine unarySlots unaryMachine
noncomputable def eraseProgram (j : Fin 2) := RecoveryFocus.machine (eraseSlots j) ClockUnarySum.machine
noncomputable def fieldsProgram := Composition.machine (Composition.machine (fieldProgram 0) (fieldProgram 1)) (fieldProgram 2)
noncomputable def countsProgram := Composition.machine (Composition.machine fieldsProgram doubleProgram) unaryProgram
noncomputable def bankProgram := Composition.machine (Composition.machine countsProgram (eraseProgram 0)) (eraseProgram 1)
def bankBudget (bits : List Bool) := 16*width bits+2*limit bits+4*erase bits+54

theorem zero_call (bits : List Bool) (pos : Nat) (a : Fin 100→List Bool) (ha : Sources bits a) :
    AtRun (fieldProgram 0) (4*width bits+8) (bankHeads pos) a (stage1 bits a) := by
  have h := field_at (fieldSlots 0) (fieldSlots_injective 0) (bankHeads pos) a
    (RecoveryColdHeader.zeroWord bits) (width bits) 0 (RecoveryColdHeader.zero_length bits)
    (by
      intro j
      fin_cases j
      · exact ha.zero
      · exact ha.empty 32 (by decide)
      · exact ha.width
      · exact ha.empty 98 (by decide))
    (by intro j; fin_cases j <;> rfl)
  simpa [fieldProgram,fieldSlots,stage1,put,reset1] using h

theorem bound_call (bits : List Bool) (pos : Nat) (a : Fin 100→List Bool) (ha : Sources bits a) :
    AtRun (fieldProgram 1) (4*width bits+8) (bankHeads pos) (stage1 bits a) (stage2 bits a) := by
  have h := field_at (fieldSlots 1) (fieldSlots_injective 1) (bankHeads pos) (stage1 bits a)
    (RecoveryColdHeader.boundWord bits) (width bits) (reset1 bits) (RecoveryColdHeader.bound_length bits)
    (by
      intro j
      fin_cases j <;> simp [fieldSlots,stage1,put]
      · exact ha.bound
      · exact ha.empty 63 (by decide)
      · exact ha.width)
    (by intro j; fin_cases j <;> rfl)
  simpa [fieldProgram,fieldSlots,stage2,put,reset1] using h

theorem code_call (bits : List Bool) (pos : Nat) (a : Fin 100→List Bool) (ha : Sources bits a) :
    AtRun (fieldProgram 2) (4*width bits+8) (bankHeads pos) (stage2 bits a) (stage3 bits a) := by
  have h := field_at (fieldSlots 2) (fieldSlots_injective 2) (bankHeads pos) (stage2 bits a)
    (RecoveryColdHeader.codeWord bits) (width bits) (reset1 bits) (RecoveryColdHeader.code_length bits)
    (by
      intro j
      fin_cases j <;> simp [fieldSlots,stage2,stage1,put]
      · exact ha.code
      · exact ha.empty 68 (by decide)
      · exact ha.width)
    (by intro j; fin_cases j <;> rfl)
  simpa [fieldProgram,fieldSlots,stage3,put,reset1] using h

end NearCubicWires.RepairOrdinary.RecoveryColdView
