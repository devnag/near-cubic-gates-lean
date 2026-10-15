import Proof.Amplification.RecoveryMarkerState

/-! Six paid broadcasts produce the native marker bank, retaining all279
cold-front tapes and every streaming head. One reset log is reused. -/
namespace NearCubicWires.RepairOrdinary.RecoveryColdMarker
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryColdView
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def lift (a : Fin 279→List Bool) : Fin 338→List Bool :=
  Fin.addCases (m:=279) (n:=59) (motive:=fun _=>List Bool) a (fun _=>[])
def heads (h : Fin 279→Nat) : Fin 338→Nat :=
  Fin.addCases (m:=279) (n:=59) (motive:=fun _=>Nat) h (fun _=>0)
def put (a : Fin 338→List Bool) (i : Fin 338) (word : List Bool) (reset : Nat) :=
  Function.update (Function.update a i word) 336 (List.replicate reset false)
structure Sources (bits : List Bool) (h : Fin 279→Nat) (a : Fin 279→List Bool) : Prop where
  width : a 2=CompareMachine.word (width bits)
  code : a 6=frame (RecoveryColdHeader.codeWord bits)
  zero : a 10=frame (RecoveryColdHeader.zeroWord bits)
  erase : a 16=List.replicate (erase bits) true
  width_head : h 2=0
  code_head : h 6=0
  zero_head : h 10=0
  erase_head : h 16=0

def reset1 (bits : List Bool) := max (0) (2*width bits+3)
def stage1 (bits : List Bool) (a : Fin 279→List Bool) :=
  put (lift a) 279 (frame (RecoveryColdHeader.zeroWord bits)) (reset1 bits)
def slots1 : Fin 4→Fin 338 := ![10,279,2,336]
theorem slots1_injective : Function.Injective slots1 := by decide
noncomputable def program1 := RecoveryFocus.machine slots1 RecoveryColdPaddedCopy.machine
theorem call1 (bits : List Bool) (h : Fin 279→Nat) (a : Fin 279→List Bool)
    (ha : Sources bits h a) :
    AtRun program1 (4*width bits+8) (heads h) (lift a) (stage1 bits a) := by
  have h := field_at slots1 slots1_injective (heads h) (lift a)
    (RecoveryColdHeader.zeroWord bits) (width bits) (0) (RecoveryColdHeader.zero_length bits)
    (by
      intro k
      fin_cases k <;> simp [slots1,lift,Fin.addCases]
      all_goals first | exact ha.width | exact ha.zero)
    (by
      intro k
      fin_cases k <;> simp [slots1,heads,Fin.addCases]
      all_goals first | exact ha.width_head | exact ha.zero_head)
  simpa [program1,slots1,stage1,put,reset1] using h

def reset2 (bits : List Bool) := max (reset1 bits) (2*width bits+3)
def stage2 (bits : List Bool) (a : Fin 279→List Bool) :=
  put (stage1 bits a) 304 (frame (RecoveryColdHeader.zeroWord bits)) (reset2 bits)
def slots2 : Fin 4→Fin 338 := ![10,304,2,336]
theorem slots2_injective : Function.Injective slots2 := by decide
noncomputable def program2 := RecoveryFocus.machine slots2 RecoveryColdPaddedCopy.machine
theorem call2 (bits : List Bool) (h : Fin 279→Nat) (a : Fin 279→List Bool)
    (ha : Sources bits h a) :
    AtRun program2 (4*width bits+8) (heads h) (stage1 bits a) (stage2 bits a) := by
  have h := field_at slots2 slots2_injective (heads h) (stage1 bits a)
    (RecoveryColdHeader.zeroWord bits) (width bits) (reset1 bits) (RecoveryColdHeader.zero_length bits)
    (by
      intro k
      fin_cases k <;> simp [slots2,stage1,put,lift,Fin.addCases]
      all_goals first | exact ha.width | exact ha.zero)
    (by
      intro k
      fin_cases k <;> simp [slots2,heads,Fin.addCases]
      all_goals first | exact ha.width_head | exact ha.zero_head)
  simpa [program2,slots2,stage2,put,reset2] using h

def reset3 (bits : List Bool) := max (reset2 bits) (2*width bits+3)
def stage3 (bits : List Bool) (a : Fin 279→List Bool) :=
  put (stage2 bits a) 334 (frame (RecoveryColdHeader.zeroWord bits)) (reset3 bits)
def slots3 : Fin 4→Fin 338 := ![10,334,2,336]
theorem slots3_injective : Function.Injective slots3 := by decide
noncomputable def program3 := RecoveryFocus.machine slots3 RecoveryColdPaddedCopy.machine
theorem call3 (bits : List Bool) (h : Fin 279→Nat) (a : Fin 279→List Bool)
    (ha : Sources bits h a) :
    AtRun program3 (4*width bits+8) (heads h) (stage2 bits a) (stage3 bits a) := by
  have h := field_at slots3 slots3_injective (heads h) (stage2 bits a)
    (RecoveryColdHeader.zeroWord bits) (width bits) (reset2 bits) (RecoveryColdHeader.zero_length bits)
    (by
      intro k
      fin_cases k <;> simp [slots3,stage2,stage1,put,lift,Fin.addCases]
      all_goals first | exact ha.width | exact ha.zero)
    (by
      intro k
      fin_cases k <;> simp [slots3,heads,Fin.addCases]
      all_goals first | exact ha.width_head | exact ha.zero_head)
  simpa [program3,slots3,stage3,put,reset3] using h

def reset4 (bits : List Bool) := max (reset3 bits) (2*width bits+3)
def stage4 (bits : List Bool) (a : Fin 279→List Bool) :=
  put (stage3 bits a) 308 (frame (RecoveryColdHeader.codeWord bits)) (reset4 bits)
def slots4 : Fin 4→Fin 338 := ![6,308,2,336]
theorem slots4_injective : Function.Injective slots4 := by decide
noncomputable def program4 := RecoveryFocus.machine slots4 RecoveryColdPaddedCopy.machine
theorem call4 (bits : List Bool) (h : Fin 279→Nat) (a : Fin 279→List Bool)
    (ha : Sources bits h a) :
    AtRun program4 (4*width bits+8) (heads h) (stage3 bits a) (stage4 bits a) := by
  have h := field_at slots4 slots4_injective (heads h) (stage3 bits a)
    (RecoveryColdHeader.codeWord bits) (width bits) (reset3 bits) (RecoveryColdHeader.code_length bits)
    (by
      intro k
      fin_cases k <;> simp [slots4,stage3,stage2,stage1,put,lift,Fin.addCases]
      all_goals first | exact ha.width | exact ha.code)
    (by
      intro k
      fin_cases k <;> simp [slots4,heads,Fin.addCases]
      all_goals first | exact ha.width_head | exact ha.code_head)
  simpa [program4,slots4,stage4,put,reset4] using h

def reset5 (bits : List Bool) := max (reset4 bits) (erase bits+2)
def stage5 (bits : List Bool) (a : Fin 279→List Bool) :=
  put (stage4 bits a) 300 (List.replicate (erase bits) true) (reset5 bits)
def slots5 : Fin 4→Fin 338 := ![16,337,300,336]
theorem slots5_injective : Function.Injective slots5 := by decide
noncomputable def program5 := RecoveryFocus.machine slots5 ClockUnarySum.machine
theorem call5 (bits : List Bool) (h : Fin 279→Nat) (a : Fin 279→List Bool)
    (ha : Sources bits h a) :
    AtRun program5 (2*erase bits+6) (heads h) (stage4 bits a) (stage5 bits a) := by
  have h := erase_at slots5 slots5_injective (heads h) (stage4 bits a)
    (erase bits) (reset4 bits)
    (by
      intro k
      fin_cases k <;> simp [slots5,stage4,stage3,stage2,stage1,put,lift,Fin.addCases]
      all_goals exact ha.erase)
    (by
      intro k
      fin_cases k <;> simp [slots5,heads,Fin.addCases]
      all_goals exact ha.erase_head)
  simpa [program5,slots5,stage5,put,reset5] using h

def reset6 (bits : List Bool) := max (reset5 bits) (erase bits+2)
def stage6 (bits : List Bool) (a : Fin 279→List Bool) :=
  put (stage5 bits a) 329 (List.replicate (erase bits) true) (reset6 bits)
def slots6 : Fin 4→Fin 338 := ![16,337,329,336]
theorem slots6_injective : Function.Injective slots6 := by decide
noncomputable def program6 := RecoveryFocus.machine slots6 ClockUnarySum.machine
theorem call6 (bits : List Bool) (h : Fin 279→Nat) (a : Fin 279→List Bool)
    (ha : Sources bits h a) :
    AtRun program6 (2*erase bits+6) (heads h) (stage5 bits a) (stage6 bits a) := by
  have h := erase_at slots6 slots6_injective (heads h) (stage5 bits a)
    (erase bits) (reset5 bits)
    (by
      intro k
      fin_cases k <;> simp [slots6,stage5,stage4,stage3,stage2,stage1,put,lift,Fin.addCases]
      all_goals exact ha.erase)
    (by
      intro k
      fin_cases k <;> simp [slots6,heads,Fin.addCases]
      all_goals exact ha.erase_head)
  simpa [program6,slots6,stage6,put,reset6] using h

noncomputable def bankProgram := (Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine program1 program2) program3) program4) program5) program6)
def bankBudget (bits : List Bool) := 16*width bits+4*erase bits+49
theorem bank_run (bits : List Bool) (h : Fin 279→Nat) (a : Fin 279→List Bool)
    (ha : Sources bits h a) :
    AtRun bankProgram (bankBudget bits) (heads h) (lift a) (stage6 bits a) := by
  have hr := (((((call1 bits h a ha).seq (call2 bits h a ha)).seq (call3 bits h a ha)).seq (call4 bits h a ha)).seq (call5 bits h a ha)).seq (call6 bits h a ha)
  have he : (((((4*width bits+8)+1+(4*width bits+8))+1+(4*width bits+8))+1+(4*width bits+8))+1+(2*erase bits+6))+1+(2*erase bits+6)=bankBudget bits := by unfold bankBudget; omega
  rw [he] at hr
  exact hr

end NearCubicWires.RepairOrdinary.RecoveryColdMarker
