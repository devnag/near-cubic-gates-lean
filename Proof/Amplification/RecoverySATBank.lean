import Proof.Amplification.RecoverySATState

/-! Nine paid copies produce the RawSAT bank while retaining every original
raw-view tape and head. Only one reset log and one empty sum input are added. -/
namespace NearCubicWires.RepairOrdinary.RecoveryColdSAT
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open RepairSource.VerifierDecoding
open RecoveryColdView
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def lift (a : Fin 100→List Bool) : Fin 172→List Bool := Fin.addCases (m:=100) (n:=72) (motive:=fun _=>List Bool) a (fun _=>[])
def heads (pos : Nat) : Fin 172→Nat := Fin.addCases (m:=100) (n:=72) (motive:=fun _=>Nat) (bootHeads pos) (fun _=>0)
def put (a : Fin 172→List Bool) (i : Fin 172) (word : List Bool) (reset : Nat) :=
  Function.update (Function.update a i word) 170 (List.replicate reset false)
structure Sources (bits word : List Bool) (a : Fin 172→List Bool) : Prop where
  source : a 1=frame word
  width : a 2=CompareMachine.word (width bits)
  code : a 6=frame (RecoveryColdHeader.codeWord bits)
  zero : a 10=frame (RecoveryColdHeader.zeroWord bits)
  increment : a 14=CompareMachine.word (RecoveryColdView.width bits+1)
  erase : a 16=List.replicate (erase bits) true
  cap : a 21=CompareMachine.word (limit bits)
  length : a 24=CompareMachine.word word.length
  empty : ∀ (i : Fin 172), (100 : Nat) ≤ i.val → a i=[]

def reset1 (_bits word : List Bool) := max (0) (2*word.length+3)
def stage1 (bits word : List Bool) (a : Fin 172→List Bool) :=
  put (a) 128 (frame (word)) (reset1 bits word)
def slots1 : Fin 4→Fin 172 := ![1,128,24,170]
theorem slots1_injective : Function.Injective slots1 := by decide
noncomputable def program1 := RecoveryFocus.machine slots1 RecoveryColdPaddedCopy.machine

def reset2 (bits word : List Bool) := max (reset1 bits word) (2*width bits+3)
def stage2 (bits word : List Bool) (a : Fin 172→List Bool) :=
  put (stage1 bits word a) 100 (frame (RecoveryColdHeader.zeroWord bits)) (reset2 bits word)
def slots2 : Fin 4→Fin 172 := ![10,100,2,170]
theorem slots2_injective : Function.Injective slots2 := by decide
noncomputable def program2 := RecoveryFocus.machine slots2 RecoveryColdPaddedCopy.machine

def reset3 (bits word : List Bool) := max (reset2 bits word) (2*width bits+3)
def stage3 (bits word : List Bool) (a : Fin 172→List Bool) :=
  put (stage2 bits word a) 137 (frame (RecoveryColdHeader.zeroWord bits)) (reset3 bits word)
def slots3 : Fin 4→Fin 172 := ![10,137,2,170]
theorem slots3_injective : Function.Injective slots3 := by decide
noncomputable def program3 := RecoveryFocus.machine slots3 RecoveryColdPaddedCopy.machine

def reset4 (bits word : List Bool) := max (reset3 bits word) (2*width bits+3)
def stage4 (bits word : List Bool) (a : Fin 172→List Bool) :=
  put (stage3 bits word a) 138 (frame (RecoveryColdHeader.zeroWord bits)) (reset4 bits word)
def slots4 : Fin 4→Fin 172 := ![10,138,2,170]
theorem slots4_injective : Function.Injective slots4 := by decide
noncomputable def program4 := RecoveryFocus.machine slots4 RecoveryColdPaddedCopy.machine

def reset5 (bits word : List Bool) := max (reset4 bits word) (2*width bits+3)
def stage5 (bits word : List Bool) (a : Fin 172→List Bool) :=
  put (stage4 bits word a) 142 (frame (RecoveryColdHeader.codeWord bits)) (reset5 bits word)
def slots5 : Fin 4→Fin 172 := ![6,142,2,170]
theorem slots5_injective : Function.Injective slots5 := by decide
noncomputable def program5 := RecoveryFocus.machine slots5 RecoveryColdPaddedCopy.machine

def reset6 (bits word : List Bool) := max (reset5 bits word) (width bits+1+2)
def stage6 (bits word : List Bool) (a : Fin 172→List Bool) :=
  put (stage5 bits word a) 130 (CompareMachine.word (width bits+1)) (reset6 bits word)
def slots6 : Fin 3→Fin 172 := ![14,130,170]
theorem slots6_injective : Function.Injective slots6 := by decide
noncomputable def program6 := RecoveryFocus.machine slots6 unaryMachine

def reset7 (bits word : List Bool) := max (reset6 bits word) (limit bits+2)
def stage7 (bits word : List Bool) (a : Fin 172→List Bool) :=
  put (stage6 bits word a) 136 (CompareMachine.word (limit bits)) (reset7 bits word)
def slots7 : Fin 3→Fin 172 := ![21,136,170]
theorem slots7_injective : Function.Injective slots7 := by decide
noncomputable def program7 := RecoveryFocus.machine slots7 unaryMachine

def reset8 (bits word : List Bool) := max (reset7 bits word) (erase bits+2)
def stage8 (bits word : List Bool) (a : Fin 172→List Bool) :=
  put (stage7 bits word a) 121 (List.replicate (erase bits) true) (reset8 bits word)
def slots8 : Fin 4→Fin 172 := ![16,171,121,170]
theorem slots8_injective : Function.Injective slots8 := by decide
noncomputable def program8 := RecoveryFocus.machine slots8 ClockUnarySum.machine

def reset9 (bits word : List Bool) := max (reset8 bits word) (erase bits+2)
def stage9 (bits word : List Bool) (a : Fin 172→List Bool) :=
  put (stage8 bits word a) 163 (List.replicate (erase bits) true) (reset9 bits word)
def slots9 : Fin 4→Fin 172 := ![16,171,163,170]
theorem slots9_injective : Function.Injective slots9 := by decide
noncomputable def program9 := RecoveryFocus.machine slots9 ClockUnarySum.machine

theorem call1 (bits word : List Bool) (pos : Nat) (a : Fin 172→List Bool)
    (ha : Sources bits word a) :
    AtRun program1 (4*word.length+8) (heads pos) a (stage1 bits word a) := by
  have h := field_at slots1 slots1_injective (heads pos) a (word) (word.length) 0 (rfl)
    (by
      intro k
      fin_cases k <;> simp [slots1]
      all_goals first
        | exact ha.source
        | exact ha.width
        | exact ha.code
        | exact ha.zero
        | exact ha.increment
        | exact ha.erase
        | exact ha.cap
        | exact ha.length
        | exact ha.empty _ (by decide))
    (by intro k; fin_cases k <;> rfl)
  simpa [program1,slots1,stage1,put,reset1] using h

theorem call2 (bits word : List Bool) (pos : Nat) (a : Fin 172→List Bool)
    (ha : Sources bits word a) :
    AtRun program2 (4*width bits+8) (heads pos) (stage1 bits word a) (stage2 bits word a) := by
  have h := field_at slots2 slots2_injective (heads pos) (stage1 bits word a) (RecoveryColdHeader.zeroWord bits) (width bits) (reset1 bits word) (RecoveryColdHeader.zero_length bits)
    (by
      intro k
      fin_cases k <;> simp [slots2,stage1,put]
      all_goals first
        | exact ha.source
        | exact ha.width
        | exact ha.code
        | exact ha.zero
        | exact ha.increment
        | exact ha.erase
        | exact ha.cap
        | exact ha.length
        | exact ha.empty _ (by decide))
    (by intro k; fin_cases k <;> rfl)
  simpa [program2,slots2,stage2,put,reset2] using h

theorem call3 (bits word : List Bool) (pos : Nat) (a : Fin 172→List Bool)
    (ha : Sources bits word a) :
    AtRun program3 (4*width bits+8) (heads pos) (stage2 bits word a) (stage3 bits word a) := by
  have h := field_at slots3 slots3_injective (heads pos) (stage2 bits word a) (RecoveryColdHeader.zeroWord bits) (width bits) (reset2 bits word) (RecoveryColdHeader.zero_length bits)
    (by
      intro k
      fin_cases k <;> simp [slots3,stage2,stage1,put]
      all_goals first
        | exact ha.source
        | exact ha.width
        | exact ha.code
        | exact ha.zero
        | exact ha.increment
        | exact ha.erase
        | exact ha.cap
        | exact ha.length
        | exact ha.empty _ (by decide))
    (by intro k; fin_cases k <;> rfl)
  simpa [program3,slots3,stage3,put,reset3] using h

theorem call4 (bits word : List Bool) (pos : Nat) (a : Fin 172→List Bool)
    (ha : Sources bits word a) :
    AtRun program4 (4*width bits+8) (heads pos) (stage3 bits word a) (stage4 bits word a) := by
  have h := field_at slots4 slots4_injective (heads pos) (stage3 bits word a) (RecoveryColdHeader.zeroWord bits) (width bits) (reset3 bits word) (RecoveryColdHeader.zero_length bits)
    (by
      intro k
      fin_cases k <;> simp [slots4,stage3,stage2,stage1,put]
      all_goals first
        | exact ha.source
        | exact ha.width
        | exact ha.code
        | exact ha.zero
        | exact ha.increment
        | exact ha.erase
        | exact ha.cap
        | exact ha.length
        | exact ha.empty _ (by decide))
    (by intro k; fin_cases k <;> rfl)
  simpa [program4,slots4,stage4,put,reset4] using h

theorem call5 (bits word : List Bool) (pos : Nat) (a : Fin 172→List Bool)
    (ha : Sources bits word a) :
    AtRun program5 (4*width bits+8) (heads pos) (stage4 bits word a) (stage5 bits word a) := by
  have h := field_at slots5 slots5_injective (heads pos) (stage4 bits word a) (RecoveryColdHeader.codeWord bits) (width bits) (reset4 bits word) (RecoveryColdHeader.code_length bits)
    (by
      intro k
      fin_cases k <;> simp [slots5,stage4,stage3,stage2,stage1,put]
      all_goals first
        | exact ha.source
        | exact ha.width
        | exact ha.code
        | exact ha.zero
        | exact ha.increment
        | exact ha.erase
        | exact ha.cap
        | exact ha.length
        | exact ha.empty _ (by decide))
    (by intro k; fin_cases k <;> rfl)
  simpa [program5,slots5,stage5,put,reset5] using h

theorem call6 (bits word : List Bool) (pos : Nat) (a : Fin 172→List Bool)
    (ha : Sources bits word a) :
    AtRun program6 (2*(width bits+1)+6) (heads pos) (stage5 bits word a) (stage6 bits word a) := by
  have h := unary_at slots6 slots6_injective (heads pos) (stage5 bits word a) (width bits+1) (reset5 bits word)
    (by
      intro k
      fin_cases k <;> simp [slots6,stage5,stage4,stage3,stage2,stage1,put]
      all_goals first
        | exact ha.source
        | exact ha.width
        | exact ha.code
        | exact ha.zero
        | exact ha.increment
        | exact ha.erase
        | exact ha.cap
        | exact ha.length
        | exact ha.empty _ (by decide))
    (by intro k; fin_cases k <;> rfl)
  simpa [program6,slots6,stage6,put,reset6] using h

theorem call7 (bits word : List Bool) (pos : Nat) (a : Fin 172→List Bool)
    (ha : Sources bits word a) :
    AtRun program7 (2*limit bits+6) (heads pos) (stage6 bits word a) (stage7 bits word a) := by
  have h := unary_at slots7 slots7_injective (heads pos) (stage6 bits word a) (limit bits) (reset6 bits word)
    (by
      intro k
      fin_cases k <;> simp [slots7,stage6,stage5,stage4,stage3,stage2,stage1,put]
      all_goals first
        | exact ha.source
        | exact ha.width
        | exact ha.code
        | exact ha.zero
        | exact ha.increment
        | exact ha.erase
        | exact ha.cap
        | exact ha.length
        | exact ha.empty _ (by decide))
    (by intro k; fin_cases k <;> rfl)
  simpa [program7,slots7,stage7,put,reset7] using h

theorem call8 (bits word : List Bool) (pos : Nat) (a : Fin 172→List Bool)
    (ha : Sources bits word a) :
    AtRun program8 (2*erase bits+6) (heads pos) (stage7 bits word a) (stage8 bits word a) := by
  have h := erase_at slots8 slots8_injective (heads pos) (stage7 bits word a) (erase bits) (reset7 bits word)
    (by
      intro k
      fin_cases k <;> simp [slots8,stage7,stage6,stage5,stage4,stage3,stage2,stage1,put]
      all_goals first
        | exact ha.source
        | exact ha.width
        | exact ha.code
        | exact ha.zero
        | exact ha.increment
        | exact ha.erase
        | exact ha.cap
        | exact ha.length
        | exact ha.empty _ (by decide))
    (by intro k; fin_cases k <;> rfl)
  simpa [program8,slots8,stage8,put,reset8] using h

theorem call9 (bits word : List Bool) (pos : Nat) (a : Fin 172→List Bool)
    (ha : Sources bits word a) :
    AtRun program9 (2*erase bits+6) (heads pos) (stage8 bits word a) (stage9 bits word a) := by
  have h := erase_at slots9 slots9_injective (heads pos) (stage8 bits word a) (erase bits) (reset8 bits word)
    (by
      intro k
      fin_cases k <;> simp [slots9,stage8,stage7,stage6,stage5,stage4,stage3,stage2,stage1,put]
      all_goals first
        | exact ha.source
        | exact ha.width
        | exact ha.code
        | exact ha.zero
        | exact ha.increment
        | exact ha.erase
        | exact ha.cap
        | exact ha.length
        | exact ha.empty _ (by decide))
    (by intro k; fin_cases k <;> rfl)
  simpa [program9,slots9,stage9,put,reset9] using h

noncomputable def bankProgram := (Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine program1 program2) program3) program4) program5) program6) program7) program8) program9)
def bankBudget (bits word : List Bool) := 4*word.length+18*width bits+2*limit bits+4*erase bits+74

theorem bank_run (bits word : List Bool) (pos : Nat) (a : Fin 172→List Bool)
    (ha : Sources bits word a) :
    AtRun bankProgram (bankBudget bits word) (heads pos) a (stage9 bits word a) := by
  have h := (((((((((call1 bits word pos a ha).seq (call2 bits word pos a ha)).seq (call3 bits word pos a ha)).seq (call4 bits word pos a ha)).seq (call5 bits word pos a ha)).seq (call6 bits word pos a ha)).seq (call7 bits word pos a ha)).seq (call8 bits word pos a ha)).seq (call9 bits word pos a ha))
  have he : ((((((((4*word.length+8)+1+(4*width bits+8))+1+(4*width bits+8))+1+(4*width bits+8))+1+(4*width bits+8))+1+(2*(width bits+1)+6))+1+(2*limit bits+6))+1+(2*erase bits+6))+1+(2*erase bits+6)=bankBudget bits word := by
    unfold bankBudget
    omega
  rw [he] at h
  exact h

end NearCubicWires.RepairOrdinary.RecoveryColdSAT
