import Proof.Amplification.RecoveryCompactEntry

/-! All34 actual compact-bank broadcasts from the produced sources.
Framed copies use the retained original witness/width drivers. The same
reset log is reused; all ambient streaming heads stay at their positions. -/
namespace NearCubicWires.RepairOrdinary.RecoveryColdCompact
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryColdView
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def put (a : Fin 493→List Bool) (i : Fin 493) (word : List Bool) (reset : Nat) :=
  Function.update (Function.update a i word) 336 (List.replicate reset false)
def reset0 (bits _word : List Bool) (_n _m : Nat) := RecoveryColdMarker.reset6 bits
def stage0 (_bits _word _innerBits _outerBits : List Bool) (_n _m : Nat) (a : Fin 493→List Bool) := a

def reset1 (bits word : List Bool) (n m : Nat) := max (reset0 bits word n m) (2*(width bits)+3)
def stage1 (bits word innerBits outerBits : List Bool) (n m : Nat) (a : Fin 493→List Bool) :=
  put (stage0 bits word innerBits outerBits n m a) 338 (frame (RecoveryColdHeader.zeroWord bits)) (reset1 bits word n m)
def slots1 : Fin 4→Fin 493 := ![10,338,2,336]
theorem slots1_injective : Function.Injective slots1 := by decide
noncomputable def program1 := RecoveryFocus.machine slots1 RecoveryColdPaddedCopy.machine
theorem call1 (bits word innerBits outerBits : List Bool) (n m : Nat)
    (h : Fin 493→Nat) (a : Fin 493→List Bool) (ha : Sources bits word innerBits outerBits n m h a) :
    AtRun program1 (4*(width bits)+8) h (stage0 bits word innerBits outerBits n m a) (stage1 bits word innerBits outerBits n m a) := by
  have hr := field_at slots1 slots1_injective h (stage0 bits word innerBits outerBits n m a)
    (RecoveryColdHeader.zeroWord bits) (width bits) (reset0 bits word n m) (RecoveryColdHeader.zero_length bits)
    (by
      intro k
      fin_cases k
      · simpa [slots1,stage0,bankSlot,sourceSlots,sourceTapes] using (ha.source 0)
      · simpa [slots1,stage0] using (ha.fresh 338 (by decide))
      · simpa [slots1,stage0,bankSlot,sourceSlots,sourceTapes] using (ha.source 1)
      · simpa [slots1,stage0,reset0] using (ha.reset)
    )
    (by
      intro k
      fin_cases k
      · exact ha.source_head 0
      · exact ha.fresh_head 338 (by decide)
      · exact ha.source_head 1
      · exact ha.reset_head
    )
  simpa [program1,slots1,stage1,put,reset1] using hr

def reset2 (bits word : List Bool) (n m : Nat) := max (reset1 bits word n m) (2*(width bits)+3)
def stage2 (bits word innerBits outerBits : List Bool) (n m : Nat) (a : Fin 493→List Bool) :=
  put (stage1 bits word innerBits outerBits n m a) 375 (frame (RecoveryColdHeader.zeroWord bits)) (reset2 bits word n m)
def slots2 : Fin 4→Fin 493 := ![10,375,2,336]
theorem slots2_injective : Function.Injective slots2 := by decide
noncomputable def program2 := RecoveryFocus.machine slots2 RecoveryColdPaddedCopy.machine
theorem call2 (bits word innerBits outerBits : List Bool) (n m : Nat)
    (h : Fin 493→Nat) (a : Fin 493→List Bool) (ha : Sources bits word innerBits outerBits n m h a) :
    AtRun program2 (4*(width bits)+8) h (stage1 bits word innerBits outerBits n m a) (stage2 bits word innerBits outerBits n m a) := by
  have hr := field_at slots2 slots2_injective h (stage1 bits word innerBits outerBits n m a)
    (RecoveryColdHeader.zeroWord bits) (width bits) (reset1 bits word n m) (RecoveryColdHeader.zero_length bits)
    (by
      intro k
      fin_cases k
      · simpa [slots2,stage1,stage0,put,bankSlot,sourceSlots,sourceTapes] using (ha.source 0)
      · simpa [slots2,stage1,stage0,put] using (ha.fresh 375 (by decide))
      · simpa [slots2,stage1,stage0,put,bankSlot,sourceSlots,sourceTapes] using (ha.source 1)
      · simp [slots2,stage1,stage0,put]
    )
    (by
      intro k
      fin_cases k
      · exact ha.source_head 0
      · exact ha.fresh_head 375 (by decide)
      · exact ha.source_head 1
      · exact ha.reset_head
    )
  simpa [program2,slots2,stage2,put,reset2] using hr

def reset3 (bits word : List Bool) (n m : Nat) := max (reset2 bits word n m) (2*(width bits)+3)
def stage3 (bits word innerBits outerBits : List Bool) (n m : Nat) (a : Fin 493→List Bool) :=
  put (stage2 bits word innerBits outerBits n m a) 376 (frame (RecoveryColdHeader.zeroWord bits)) (reset3 bits word n m)
def slots3 : Fin 4→Fin 493 := ![10,376,2,336]
theorem slots3_injective : Function.Injective slots3 := by decide
noncomputable def program3 := RecoveryFocus.machine slots3 RecoveryColdPaddedCopy.machine
theorem call3 (bits word innerBits outerBits : List Bool) (n m : Nat)
    (h : Fin 493→Nat) (a : Fin 493→List Bool) (ha : Sources bits word innerBits outerBits n m h a) :
    AtRun program3 (4*(width bits)+8) h (stage2 bits word innerBits outerBits n m a) (stage3 bits word innerBits outerBits n m a) := by
  have hr := field_at slots3 slots3_injective h (stage2 bits word innerBits outerBits n m a)
    (RecoveryColdHeader.zeroWord bits) (width bits) (reset2 bits word n m) (RecoveryColdHeader.zero_length bits)
    (by
      intro k
      fin_cases k
      · simpa [slots3,stage2,stage1,stage0,put,bankSlot,sourceSlots,sourceTapes] using (ha.source 0)
      · simpa [slots3,stage2,stage1,stage0,put] using (ha.fresh 376 (by decide))
      · simpa [slots3,stage2,stage1,stage0,put,bankSlot,sourceSlots,sourceTapes] using (ha.source 1)
      · simp [slots3,stage2,stage1,stage0,put]
    )
    (by
      intro k
      fin_cases k
      · exact ha.source_head 0
      · exact ha.fresh_head 376 (by decide)
      · exact ha.source_head 1
      · exact ha.reset_head
    )
  simpa [program3,slots3,stage3,put,reset3] using hr

def reset4 (bits word : List Bool) (n m : Nat) := max (reset3 bits word n m) (2*(width bits)+3)
def stage4 (bits word innerBits outerBits : List Bool) (n m : Nat) (a : Fin 493→List Bool) :=
  put (stage3 bits word innerBits outerBits n m a) 397 (frame (RecoveryColdHeader.zeroWord bits)) (reset4 bits word n m)
def slots4 : Fin 4→Fin 493 := ![10,397,2,336]
theorem slots4_injective : Function.Injective slots4 := by decide
noncomputable def program4 := RecoveryFocus.machine slots4 RecoveryColdPaddedCopy.machine
theorem call4 (bits word innerBits outerBits : List Bool) (n m : Nat)
    (h : Fin 493→Nat) (a : Fin 493→List Bool) (ha : Sources bits word innerBits outerBits n m h a) :
    AtRun program4 (4*(width bits)+8) h (stage3 bits word innerBits outerBits n m a) (stage4 bits word innerBits outerBits n m a) := by
  have hr := field_at slots4 slots4_injective h (stage3 bits word innerBits outerBits n m a)
    (RecoveryColdHeader.zeroWord bits) (width bits) (reset3 bits word n m) (RecoveryColdHeader.zero_length bits)
    (by
      intro k
      fin_cases k
      · simpa [slots4,stage3,stage2,stage1,stage0,put,bankSlot,sourceSlots,sourceTapes] using (ha.source 0)
      · simpa [slots4,stage3,stage2,stage1,stage0,put] using (ha.fresh 397 (by decide))
      · simpa [slots4,stage3,stage2,stage1,stage0,put,bankSlot,sourceSlots,sourceTapes] using (ha.source 1)
      · simp [slots4,stage3,stage2,stage1,stage0,put]
    )
    (by
      intro k
      fin_cases k
      · exact ha.source_head 0
      · exact ha.fresh_head 397 (by decide)
      · exact ha.source_head 1
      · exact ha.reset_head
    )
  simpa [program4,slots4,stage4,put,reset4] using hr

def reset5 (bits word : List Bool) (n m : Nat) := max (reset4 bits word n m) (2*(width bits)+3)
def stage5 (bits word innerBits outerBits : List Bool) (n m : Nat) (a : Fin 493→List Bool) :=
  put (stage4 bits word innerBits outerBits n m a) 398 (frame (RecoveryColdHeader.zeroWord bits)) (reset5 bits word n m)
def slots5 : Fin 4→Fin 493 := ![10,398,2,336]
theorem slots5_injective : Function.Injective slots5 := by decide
noncomputable def program5 := RecoveryFocus.machine slots5 RecoveryColdPaddedCopy.machine
theorem call5 (bits word innerBits outerBits : List Bool) (n m : Nat)
    (h : Fin 493→Nat) (a : Fin 493→List Bool) (ha : Sources bits word innerBits outerBits n m h a) :
    AtRun program5 (4*(width bits)+8) h (stage4 bits word innerBits outerBits n m a) (stage5 bits word innerBits outerBits n m a) := by
  have hr := field_at slots5 slots5_injective h (stage4 bits word innerBits outerBits n m a)
    (RecoveryColdHeader.zeroWord bits) (width bits) (reset4 bits word n m) (RecoveryColdHeader.zero_length bits)
    (by
      intro k
      fin_cases k
      · simpa [slots5,stage4,stage3,stage2,stage1,stage0,put,bankSlot,sourceSlots,sourceTapes] using (ha.source 0)
      · simpa [slots5,stage4,stage3,stage2,stage1,stage0,put] using (ha.fresh 398 (by decide))
      · simpa [slots5,stage4,stage3,stage2,stage1,stage0,put,bankSlot,sourceSlots,sourceTapes] using (ha.source 1)
      · simp [slots5,stage4,stage3,stage2,stage1,stage0,put]
    )
    (by
      intro k
      fin_cases k
      · exact ha.source_head 0
      · exact ha.fresh_head 398 (by decide)
      · exact ha.source_head 1
      · exact ha.reset_head
    )
  simpa [program5,slots5,stage5,put,reset5] using hr

def reset6 (bits word : List Bool) (n m : Nat) := max (reset5 bits word n m) (2*(width bits)+3)
def stage6 (bits word innerBits outerBits : List Bool) (n m : Nat) (a : Fin 493→List Bool) :=
  put (stage5 bits word innerBits outerBits n m a) 407 (frame (RecoveryColdHeader.zeroWord bits)) (reset6 bits word n m)
def slots6 : Fin 4→Fin 493 := ![10,407,2,336]
theorem slots6_injective : Function.Injective slots6 := by decide
noncomputable def program6 := RecoveryFocus.machine slots6 RecoveryColdPaddedCopy.machine
theorem call6 (bits word innerBits outerBits : List Bool) (n m : Nat)
    (h : Fin 493→Nat) (a : Fin 493→List Bool) (ha : Sources bits word innerBits outerBits n m h a) :
    AtRun program6 (4*(width bits)+8) h (stage5 bits word innerBits outerBits n m a) (stage6 bits word innerBits outerBits n m a) := by
  have hr := field_at slots6 slots6_injective h (stage5 bits word innerBits outerBits n m a)
    (RecoveryColdHeader.zeroWord bits) (width bits) (reset5 bits word n m) (RecoveryColdHeader.zero_length bits)
    (by
      intro k
      fin_cases k
      · simpa [slots6,stage5,stage4,stage3,stage2,stage1,stage0,put,bankSlot,sourceSlots,sourceTapes] using (ha.source 0)
      · simpa [slots6,stage5,stage4,stage3,stage2,stage1,stage0,put] using (ha.fresh 407 (by decide))
      · simpa [slots6,stage5,stage4,stage3,stage2,stage1,stage0,put,bankSlot,sourceSlots,sourceTapes] using (ha.source 1)
      · simp [slots6,stage5,stage4,stage3,stage2,stage1,stage0,put]
    )
    (by
      intro k
      fin_cases k
      · exact ha.source_head 0
      · exact ha.fresh_head 407 (by decide)
      · exact ha.source_head 1
      · exact ha.reset_head
    )
  simpa [program6,slots6,stage6,put,reset6] using hr

def reset7 (bits word : List Bool) (n m : Nat) := max (reset6 bits word n m) (2*(width bits)+3)
def stage7 (bits word innerBits outerBits : List Bool) (n m : Nat) (a : Fin 493→List Bool) :=
  put (stage6 bits word innerBits outerBits n m a) 444 (frame (RecoveryColdHeader.zeroWord bits)) (reset7 bits word n m)
def slots7 : Fin 4→Fin 493 := ![10,444,2,336]
theorem slots7_injective : Function.Injective slots7 := by decide
noncomputable def program7 := RecoveryFocus.machine slots7 RecoveryColdPaddedCopy.machine
theorem call7 (bits word innerBits outerBits : List Bool) (n m : Nat)
    (h : Fin 493→Nat) (a : Fin 493→List Bool) (ha : Sources bits word innerBits outerBits n m h a) :
    AtRun program7 (4*(width bits)+8) h (stage6 bits word innerBits outerBits n m a) (stage7 bits word innerBits outerBits n m a) := by
  have hr := field_at slots7 slots7_injective h (stage6 bits word innerBits outerBits n m a)
    (RecoveryColdHeader.zeroWord bits) (width bits) (reset6 bits word n m) (RecoveryColdHeader.zero_length bits)
    (by
      intro k
      fin_cases k
      · simpa [slots7,stage6,stage5,stage4,stage3,stage2,stage1,stage0,put,bankSlot,sourceSlots,sourceTapes] using (ha.source 0)
      · simpa [slots7,stage6,stage5,stage4,stage3,stage2,stage1,stage0,put] using (ha.fresh 444 (by decide))
      · simpa [slots7,stage6,stage5,stage4,stage3,stage2,stage1,stage0,put,bankSlot,sourceSlots,sourceTapes] using (ha.source 1)
      · simp [slots7,stage6,stage5,stage4,stage3,stage2,stage1,stage0,put]
    )
    (by
      intro k
      fin_cases k
      · exact ha.source_head 0
      · exact ha.fresh_head 444 (by decide)
      · exact ha.source_head 1
      · exact ha.reset_head
    )
  simpa [program7,slots7,stage7,put,reset7] using hr

def reset8 (bits word : List Bool) (n m : Nat) := max (reset7 bits word n m) (2*(width bits)+3)
def stage8 (bits word innerBits outerBits : List Bool) (n m : Nat) (a : Fin 493→List Bool) :=
  put (stage7 bits word innerBits outerBits n m a) 445 (frame (RecoveryColdHeader.zeroWord bits)) (reset8 bits word n m)
def slots8 : Fin 4→Fin 493 := ![10,445,2,336]
theorem slots8_injective : Function.Injective slots8 := by decide
noncomputable def program8 := RecoveryFocus.machine slots8 RecoveryColdPaddedCopy.machine
theorem call8 (bits word innerBits outerBits : List Bool) (n m : Nat)
    (h : Fin 493→Nat) (a : Fin 493→List Bool) (ha : Sources bits word innerBits outerBits n m h a) :
    AtRun program8 (4*(width bits)+8) h (stage7 bits word innerBits outerBits n m a) (stage8 bits word innerBits outerBits n m a) := by
  have hr := field_at slots8 slots8_injective h (stage7 bits word innerBits outerBits n m a)
    (RecoveryColdHeader.zeroWord bits) (width bits) (reset7 bits word n m) (RecoveryColdHeader.zero_length bits)
    (by
      intro k
      fin_cases k
      · simpa [slots8,stage7,stage6,stage5,stage4,stage3,stage2,stage1,stage0,put,bankSlot,sourceSlots,sourceTapes] using (ha.source 0)
      · simpa [slots8,stage7,stage6,stage5,stage4,stage3,stage2,stage1,stage0,put] using (ha.fresh 445 (by decide))
      · simpa [slots8,stage7,stage6,stage5,stage4,stage3,stage2,stage1,stage0,put,bankSlot,sourceSlots,sourceTapes] using (ha.source 1)
      · simp [slots8,stage7,stage6,stage5,stage4,stage3,stage2,stage1,stage0,put]
    )
    (by
      intro k
      fin_cases k
      · exact ha.source_head 0
      · exact ha.fresh_head 445 (by decide)
      · exact ha.source_head 1
      · exact ha.reset_head
    )
  simpa [program8,slots8,stage8,put,reset8] using hr

def reset9 (bits word : List Bool) (n m : Nat) := max (reset8 bits word n m) (2*(width bits)+3)
def stage9 (bits word innerBits outerBits : List Bool) (n m : Nat) (a : Fin 493→List Bool) :=
  put (stage8 bits word innerBits outerBits n m a) 466 (frame (RecoveryColdHeader.zeroWord bits)) (reset9 bits word n m)
def slots9 : Fin 4→Fin 493 := ![10,466,2,336]
theorem slots9_injective : Function.Injective slots9 := by decide
noncomputable def program9 := RecoveryFocus.machine slots9 RecoveryColdPaddedCopy.machine
theorem call9 (bits word innerBits outerBits : List Bool) (n m : Nat)
    (h : Fin 493→Nat) (a : Fin 493→List Bool) (ha : Sources bits word innerBits outerBits n m h a) :
    AtRun program9 (4*(width bits)+8) h (stage8 bits word innerBits outerBits n m a) (stage9 bits word innerBits outerBits n m a) := by
  have hr := field_at slots9 slots9_injective h (stage8 bits word innerBits outerBits n m a)
    (RecoveryColdHeader.zeroWord bits) (width bits) (reset8 bits word n m) (RecoveryColdHeader.zero_length bits)
    (by
      intro k
      fin_cases k
      · simpa [slots9,stage8,stage7,stage6,stage5,stage4,stage3,stage2,stage1,stage0,put,bankSlot,sourceSlots,sourceTapes] using (ha.source 0)
      · simpa [slots9,stage8,stage7,stage6,stage5,stage4,stage3,stage2,stage1,stage0,put] using (ha.fresh 466 (by decide))
      · simpa [slots9,stage8,stage7,stage6,stage5,stage4,stage3,stage2,stage1,stage0,put,bankSlot,sourceSlots,sourceTapes] using (ha.source 1)
      · simp [slots9,stage8,stage7,stage6,stage5,stage4,stage3,stage2,stage1,stage0,put]
    )
    (by
      intro k
      fin_cases k
      · exact ha.source_head 0
      · exact ha.fresh_head 466 (by decide)
      · exact ha.source_head 1
      · exact ha.reset_head
    )
  simpa [program9,slots9,stage9,put,reset9] using hr

def reset10 (bits word : List Bool) (n m : Nat) := max (reset9 bits word n m) (2*(width bits)+3)
def stage10 (bits word innerBits outerBits : List Bool) (n m : Nat) (a : Fin 493→List Bool) :=
  put (stage9 bits word innerBits outerBits n m a) 467 (frame (RecoveryColdHeader.zeroWord bits)) (reset10 bits word n m)
def slots10 : Fin 4→Fin 493 := ![10,467,2,336]
theorem slots10_injective : Function.Injective slots10 := by decide
noncomputable def program10 := RecoveryFocus.machine slots10 RecoveryColdPaddedCopy.machine
theorem call10 (bits word innerBits outerBits : List Bool) (n m : Nat)
    (h : Fin 493→Nat) (a : Fin 493→List Bool) (ha : Sources bits word innerBits outerBits n m h a) :
    AtRun program10 (4*(width bits)+8) h (stage9 bits word innerBits outerBits n m a) (stage10 bits word innerBits outerBits n m a) := by
  have hr := field_at slots10 slots10_injective h (stage9 bits word innerBits outerBits n m a)
    (RecoveryColdHeader.zeroWord bits) (width bits) (reset9 bits word n m) (RecoveryColdHeader.zero_length bits)
    (by
      intro k
      fin_cases k
      · simpa [slots10,stage9,stage8,stage7,stage6,stage5,stage4,stage3,stage2,stage1,stage0,put,bankSlot,sourceSlots,sourceTapes] using (ha.source 0)
      · simpa [slots10,stage9,stage8,stage7,stage6,stage5,stage4,stage3,stage2,stage1,stage0,put] using (ha.fresh 467 (by decide))
      · simpa [slots10,stage9,stage8,stage7,stage6,stage5,stage4,stage3,stage2,stage1,stage0,put,bankSlot,sourceSlots,sourceTapes] using (ha.source 1)
      · simp [slots10,stage9,stage8,stage7,stage6,stage5,stage4,stage3,stage2,stage1,stage0,put]
    )
    (by
      intro k
      fin_cases k
      · exact ha.source_head 0
      · exact ha.fresh_head 467 (by decide)
      · exact ha.source_head 1
      · exact ha.reset_head
    )
  simpa [program10,slots10,stage10,put,reset10] using hr

def reset11 (bits word : List Bool) (n m : Nat) := max (reset10 bits word n m) (2*(width bits)+3)
def stage11 (bits word innerBits outerBits : List Bool) (n m : Nat) (a : Fin 493→List Bool) :=
  put (stage10 bits word innerBits outerBits n m a) 482 (frame (RecoveryColdHeader.zeroWord bits)) (reset11 bits word n m)
def slots11 : Fin 4→Fin 493 := ![10,482,2,336]
theorem slots11_injective : Function.Injective slots11 := by decide
noncomputable def program11 := RecoveryFocus.machine slots11 RecoveryColdPaddedCopy.machine
theorem call11 (bits word innerBits outerBits : List Bool) (n m : Nat)
    (h : Fin 493→Nat) (a : Fin 493→List Bool) (ha : Sources bits word innerBits outerBits n m h a) :
    AtRun program11 (4*(width bits)+8) h (stage10 bits word innerBits outerBits n m a) (stage11 bits word innerBits outerBits n m a) := by
  have hr := field_at slots11 slots11_injective h (stage10 bits word innerBits outerBits n m a)
    (RecoveryColdHeader.zeroWord bits) (width bits) (reset10 bits word n m) (RecoveryColdHeader.zero_length bits)
    (by
      intro k
      fin_cases k
      · simpa [slots11,stage10,stage9,stage8,stage7,stage6,stage5,stage4,stage3,stage2,stage1,stage0,put,bankSlot,sourceSlots,sourceTapes] using (ha.source 0)
      · simpa [slots11,stage10,stage9,stage8,stage7,stage6,stage5,stage4,stage3,stage2,stage1,stage0,put] using (ha.fresh 482 (by decide))
      · simpa [slots11,stage10,stage9,stage8,stage7,stage6,stage5,stage4,stage3,stage2,stage1,stage0,put,bankSlot,sourceSlots,sourceTapes] using (ha.source 1)
      · simp [slots11,stage10,stage9,stage8,stage7,stage6,stage5,stage4,stage3,stage2,stage1,stage0,put]
    )
    (by
      intro k
      fin_cases k
      · exact ha.source_head 0
      · exact ha.fresh_head 482 (by decide)
      · exact ha.source_head 1
      · exact ha.reset_head
    )
  simpa [program11,slots11,stage11,put,reset11] using hr

def reset12 (bits word : List Bool) (n m : Nat) := max (reset11 bits word n m) (2*(width bits)+3)
def stage12 (bits word innerBits outerBits : List Bool) (n m : Nat) (a : Fin 493→List Bool) :=
  put (stage11 bits word innerBits outerBits n m a) 483 (frame (RecoveryColdHeader.zeroWord bits)) (reset12 bits word n m)
def slots12 : Fin 4→Fin 493 := ![10,483,2,336]
theorem slots12_injective : Function.Injective slots12 := by decide
noncomputable def program12 := RecoveryFocus.machine slots12 RecoveryColdPaddedCopy.machine
theorem call12 (bits word innerBits outerBits : List Bool) (n m : Nat)
    (h : Fin 493→Nat) (a : Fin 493→List Bool) (ha : Sources bits word innerBits outerBits n m h a) :
    AtRun program12 (4*(width bits)+8) h (stage11 bits word innerBits outerBits n m a) (stage12 bits word innerBits outerBits n m a) := by
  have hr := field_at slots12 slots12_injective h (stage11 bits word innerBits outerBits n m a)
    (RecoveryColdHeader.zeroWord bits) (width bits) (reset11 bits word n m) (RecoveryColdHeader.zero_length bits)
    (by
      intro k
      fin_cases k
      · simpa [slots12,stage11,stage10,stage9,stage8,stage7,stage6,stage5,stage4,stage3,stage2,stage1,stage0,put,bankSlot,sourceSlots,sourceTapes] using (ha.source 0)
      · simpa [slots12,stage11,stage10,stage9,stage8,stage7,stage6,stage5,stage4,stage3,stage2,stage1,stage0,put] using (ha.fresh 483 (by decide))
      · simpa [slots12,stage11,stage10,stage9,stage8,stage7,stage6,stage5,stage4,stage3,stage2,stage1,stage0,put,bankSlot,sourceSlots,sourceTapes] using (ha.source 1)
      · simp [slots12,stage11,stage10,stage9,stage8,stage7,stage6,stage5,stage4,stage3,stage2,stage1,stage0,put]
    )
    (by
      intro k
      fin_cases k
      · exact ha.source_head 0
      · exact ha.fresh_head 483 (by decide)
      · exact ha.source_head 1
      · exact ha.reset_head
    )
  simpa [program12,slots12,stage12,put,reset12] using hr

def reset13 (bits word : List Bool) (n m : Nat) := max (reset12 bits word n m) (2*(width bits)+3)
def stage13 (bits word innerBits outerBits : List Bool) (n m : Nat) (a : Fin 493→List Bool) :=
  put (stage12 bits word innerBits outerBits n m a) 492 (frame (RecoveryColdHeader.zeroWord bits)) (reset13 bits word n m)
def slots13 : Fin 4→Fin 493 := ![10,492,2,336]
theorem slots13_injective : Function.Injective slots13 := by decide
noncomputable def program13 := RecoveryFocus.machine slots13 RecoveryColdPaddedCopy.machine
theorem call13 (bits word innerBits outerBits : List Bool) (n m : Nat)
    (h : Fin 493→Nat) (a : Fin 493→List Bool) (ha : Sources bits word innerBits outerBits n m h a) :
    AtRun program13 (4*(width bits)+8) h (stage12 bits word innerBits outerBits n m a) (stage13 bits word innerBits outerBits n m a) := by
  have hr := field_at slots13 slots13_injective h (stage12 bits word innerBits outerBits n m a)
    (RecoveryColdHeader.zeroWord bits) (width bits) (reset12 bits word n m) (RecoveryColdHeader.zero_length bits)
    (by
      intro k
      fin_cases k
      · simpa [slots13,stage12,stage11,stage10,stage9,stage8,stage7,stage6,stage5,stage4,stage3,stage2,stage1,stage0,put,bankSlot,sourceSlots,sourceTapes] using (ha.source 0)
      · simpa [slots13,stage12,stage11,stage10,stage9,stage8,stage7,stage6,stage5,stage4,stage3,stage2,stage1,stage0,put] using (ha.fresh 492 (by decide))
      · simpa [slots13,stage12,stage11,stage10,stage9,stage8,stage7,stage6,stage5,stage4,stage3,stage2,stage1,stage0,put,bankSlot,sourceSlots,sourceTapes] using (ha.source 1)
      · simp [slots13,stage12,stage11,stage10,stage9,stage8,stage7,stage6,stage5,stage4,stage3,stage2,stage1,stage0,put]
    )
    (by
      intro k
      fin_cases k
      · exact ha.source_head 0
      · exact ha.fresh_head 492 (by decide)
      · exact ha.source_head 1
      · exact ha.reset_head
    )
  simpa [program13,slots13,stage13,put,reset13] using hr

def reset14 (bits word : List Bool) (n m : Nat) := max (reset13 bits word n m) (2*(word.length)+3)
def stage14 (bits word innerBits outerBits : List Bool) (n m : Nat) (a : Fin 493→List Bool) :=
  put (stage13 bits word innerBits outerBits n m a) 366 (frame (word)) (reset14 bits word n m)
def slots14 : Fin 4→Fin 493 := ![1,366,24,336]
theorem slots14_injective : Function.Injective slots14 := by decide
noncomputable def program14 := RecoveryFocus.machine slots14 RecoveryColdPaddedCopy.machine
theorem call14 (bits word innerBits outerBits : List Bool) (n m : Nat)
    (h : Fin 493→Nat) (a : Fin 493→List Bool) (ha : Sources bits word innerBits outerBits n m h a) :
    AtRun program14 (4*(word.length)+8) h (stage13 bits word innerBits outerBits n m a) (stage14 bits word innerBits outerBits n m a) := by
  have hr := field_at slots14 slots14_injective h (stage13 bits word innerBits outerBits n m a)
    (word) (word.length) (reset13 bits word n m) (rfl)
    (by
      intro k
      fin_cases k
      · simpa [slots14,stage13,stage12,stage11,stage10,stage9,stage8,stage7,stage6,stage5,stage4,stage3,stage2,stage1,stage0,put,bankSlot,sourceSlots,sourceTapes] using (ha.source 2)
      · simpa [slots14,stage13,stage12,stage11,stage10,stage9,stage8,stage7,stage6,stage5,stage4,stage3,stage2,stage1,stage0,put] using (ha.fresh 366 (by decide))
      · simpa [slots14,stage13,stage12,stage11,stage10,stage9,stage8,stage7,stage6,stage5,stage4,stage3,stage2,stage1,stage0,put,bankSlot,sourceSlots,sourceTapes] using (ha.source 3)
      · simp [slots14,stage13,stage12,stage11,stage10,stage9,stage8,stage7,stage6,stage5,stage4,stage3,stage2,stage1,stage0,put]
    )
    (by
      intro k
      fin_cases k
      · exact ha.source_head 2
      · exact ha.fresh_head 366 (by decide)
      · exact ha.source_head 3
      · exact ha.reset_head
    )
  simpa [program14,slots14,stage14,put,reset14] using hr

def reset15 (bits word : List Bool) (n m : Nat) := max (reset14 bits word n m) (2*(word.length)+3)
def stage15 (bits word innerBits outerBits : List Bool) (n m : Nat) (a : Fin 493→List Bool) :=
  put (stage14 bits word innerBits outerBits n m a) 435 (frame (word)) (reset15 bits word n m)
def slots15 : Fin 4→Fin 493 := ![1,435,24,336]
theorem slots15_injective : Function.Injective slots15 := by decide
noncomputable def program15 := RecoveryFocus.machine slots15 RecoveryColdPaddedCopy.machine
theorem call15 (bits word innerBits outerBits : List Bool) (n m : Nat)
    (h : Fin 493→Nat) (a : Fin 493→List Bool) (ha : Sources bits word innerBits outerBits n m h a) :
    AtRun program15 (4*(word.length)+8) h (stage14 bits word innerBits outerBits n m a) (stage15 bits word innerBits outerBits n m a) := by
  have hr := field_at slots15 slots15_injective h (stage14 bits word innerBits outerBits n m a)
    (word) (word.length) (reset14 bits word n m) (rfl)
    (by
      intro k
      fin_cases k
      · simpa [slots15,stage14,stage13,stage12,stage11,stage10,stage9,stage8,stage7,stage6,stage5,stage4,stage3,stage2,stage1,stage0,put,bankSlot,sourceSlots,sourceTapes] using (ha.source 2)
      · simpa [slots15,stage14,stage13,stage12,stage11,stage10,stage9,stage8,stage7,stage6,stage5,stage4,stage3,stage2,stage1,stage0,put] using (ha.fresh 435 (by decide))
      · simpa [slots15,stage14,stage13,stage12,stage11,stage10,stage9,stage8,stage7,stage6,stage5,stage4,stage3,stage2,stage1,stage0,put,bankSlot,sourceSlots,sourceTapes] using (ha.source 3)
      · simp [slots15,stage14,stage13,stage12,stage11,stage10,stage9,stage8,stage7,stage6,stage5,stage4,stage3,stage2,stage1,stage0,put]
    )
    (by
      intro k
      fin_cases k
      · exact ha.source_head 2
      · exact ha.fresh_head 435 (by decide)
      · exact ha.source_head 3
      · exact ha.reset_head
    )
  simpa [program15,slots15,stage15,put,reset15] using hr

def reset16 (bits word : List Bool) (n m : Nat) := max (reset15 bits word n m) (2*(word.length)+3)
def stage16 (bits word innerBits outerBits : List Bool) (n m : Nat) (a : Fin 493→List Bool) :=
  put (stage15 bits word innerBits outerBits n m a) 386 (frame (buffer innerBits word)) (reset16 bits word n m)
def slots16 : Fin 4→Fin 493 := ![271,386,24,336]
theorem slots16_injective : Function.Injective slots16 := by decide
noncomputable def program16 := RecoveryFocus.machine slots16 RecoveryColdPaddedCopy.machine
theorem call16 (bits word innerBits outerBits : List Bool) (n m : Nat)
    (h : Fin 493→Nat) (a : Fin 493→List Bool) (ha : Sources bits word innerBits outerBits n m h a) :
    AtRun program16 (4*(word.length)+8) h (stage15 bits word innerBits outerBits n m a) (stage16 bits word innerBits outerBits n m a) := by
  have hr := padded_at slots16 slots16_injective h (stage15 bits word innerBits outerBits n m a)
    (innerBits) (word.length) (reset15 bits word n m)
    (by
      intro k
      fin_cases k
      · simpa [slots16,stage15,stage14,stage13,stage12,stage11,stage10,stage9,stage8,stage7,stage6,stage5,stage4,stage3,stage2,stage1,stage0,put,bankSlot,sourceSlots,sourceTapes] using (ha.source 4)
      · simpa [slots16,stage15,stage14,stage13,stage12,stage11,stage10,stage9,stage8,stage7,stage6,stage5,stage4,stage3,stage2,stage1,stage0,put] using (ha.fresh 386 (by decide))
      · simpa [slots16,stage15,stage14,stage13,stage12,stage11,stage10,stage9,stage8,stage7,stage6,stage5,stage4,stage3,stage2,stage1,stage0,put,bankSlot,sourceSlots,sourceTapes] using (ha.source 3)
      · simp [slots16,stage15,stage14,stage13,stage12,stage11,stage10,stage9,stage8,stage7,stage6,stage5,stage4,stage3,stage2,stage1,stage0,put]
    )
    (by
      intro k
      fin_cases k
      · exact ha.source_head 4
      · exact ha.fresh_head 386 (by decide)
      · exact ha.source_head 3
      · exact ha.reset_head
    )
  simpa [program16,slots16,stage16,put,reset16,buffer] using hr

def reset17 (bits word : List Bool) (n m : Nat) := max (reset16 bits word n m) (2*(word.length)+3)
def stage17 (bits word innerBits outerBits : List Bool) (n m : Nat) (a : Fin 493→List Bool) :=
  put (stage16 bits word innerBits outerBits n m a) 390 (frame (buffer innerBits word)) (reset17 bits word n m)
def slots17 : Fin 4→Fin 493 := ![271,390,24,336]
theorem slots17_injective : Function.Injective slots17 := by decide
noncomputable def program17 := RecoveryFocus.machine slots17 RecoveryColdPaddedCopy.machine
theorem call17 (bits word innerBits outerBits : List Bool) (n m : Nat)
    (h : Fin 493→Nat) (a : Fin 493→List Bool) (ha : Sources bits word innerBits outerBits n m h a) :
    AtRun program17 (4*(word.length)+8) h (stage16 bits word innerBits outerBits n m a) (stage17 bits word innerBits outerBits n m a) := by
  have hr := padded_at slots17 slots17_injective h (stage16 bits word innerBits outerBits n m a)
    (innerBits) (word.length) (reset16 bits word n m)
    (by
      intro k
      fin_cases k
      · simpa [slots17,stage16,stage15,stage14,stage13,stage12,stage11,stage10,stage9,stage8,stage7,stage6,stage5,stage4,stage3,stage2,stage1,stage0,put,bankSlot,sourceSlots,sourceTapes] using (ha.source 4)
      · simpa [slots17,stage16,stage15,stage14,stage13,stage12,stage11,stage10,stage9,stage8,stage7,stage6,stage5,stage4,stage3,stage2,stage1,stage0,put] using (ha.fresh 390 (by decide))
      · simpa [slots17,stage16,stage15,stage14,stage13,stage12,stage11,stage10,stage9,stage8,stage7,stage6,stage5,stage4,stage3,stage2,stage1,stage0,put,bankSlot,sourceSlots,sourceTapes] using (ha.source 3)
      · simp [slots17,stage16,stage15,stage14,stage13,stage12,stage11,stage10,stage9,stage8,stage7,stage6,stage5,stage4,stage3,stage2,stage1,stage0,put]
    )
    (by
      intro k
      fin_cases k
      · exact ha.source_head 4
      · exact ha.fresh_head 390 (by decide)
      · exact ha.source_head 3
      · exact ha.reset_head
    )
  simpa [program17,slots17,stage17,put,reset17,buffer] using hr

def reset18 (bits word : List Bool) (n m : Nat) := max (reset17 bits word n m) (2*(word.length)+3)
def stage18 (bits word innerBits outerBits : List Bool) (n m : Nat) (a : Fin 493→List Bool) :=
  put (stage17 bits word innerBits outerBits n m a) 475 (frame (buffer innerBits word)) (reset18 bits word n m)
def slots18 : Fin 4→Fin 493 := ![271,475,24,336]
theorem slots18_injective : Function.Injective slots18 := by decide
noncomputable def program18 := RecoveryFocus.machine slots18 RecoveryColdPaddedCopy.machine
theorem call18 (bits word innerBits outerBits : List Bool) (n m : Nat)
    (h : Fin 493→Nat) (a : Fin 493→List Bool) (ha : Sources bits word innerBits outerBits n m h a) :
    AtRun program18 (4*(word.length)+8) h (stage17 bits word innerBits outerBits n m a) (stage18 bits word innerBits outerBits n m a) := by
  have hr := padded_at slots18 slots18_injective h (stage17 bits word innerBits outerBits n m a)
    (innerBits) (word.length) (reset17 bits word n m)
    (by
      intro k
      fin_cases k
      · simpa [slots18,stage17,stage16,stage15,stage14,stage13,stage12,stage11,stage10,stage9,stage8,stage7,stage6,stage5,stage4,stage3,stage2,stage1,stage0,put,bankSlot,sourceSlots,sourceTapes] using (ha.source 4)
      · simpa [slots18,stage17,stage16,stage15,stage14,stage13,stage12,stage11,stage10,stage9,stage8,stage7,stage6,stage5,stage4,stage3,stage2,stage1,stage0,put] using (ha.fresh 475 (by decide))
      · simpa [slots18,stage17,stage16,stage15,stage14,stage13,stage12,stage11,stage10,stage9,stage8,stage7,stage6,stage5,stage4,stage3,stage2,stage1,stage0,put,bankSlot,sourceSlots,sourceTapes] using (ha.source 3)
      · simp [slots18,stage17,stage16,stage15,stage14,stage13,stage12,stage11,stage10,stage9,stage8,stage7,stage6,stage5,stage4,stage3,stage2,stage1,stage0,put]
    )
    (by
      intro k
      fin_cases k
      · exact ha.source_head 4
      · exact ha.fresh_head 475 (by decide)
      · exact ha.source_head 3
      · exact ha.reset_head
    )
  simpa [program18,slots18,stage18,put,reset18,buffer] using hr

def reset19 (bits word : List Bool) (n m : Nat) := max (reset18 bits word n m) (2*(word.length)+3)
def stage19 (bits word innerBits outerBits : List Bool) (n m : Nat) (a : Fin 493→List Bool) :=
  put (stage18 bits word innerBits outerBits n m a) 455 (frame (buffer outerBits word)) (reset19 bits word n m)
def slots19 : Fin 4→Fin 493 := ![275,455,24,336]
theorem slots19_injective : Function.Injective slots19 := by decide
noncomputable def program19 := RecoveryFocus.machine slots19 RecoveryColdPaddedCopy.machine
theorem call19 (bits word innerBits outerBits : List Bool) (n m : Nat)
    (h : Fin 493→Nat) (a : Fin 493→List Bool) (ha : Sources bits word innerBits outerBits n m h a) :
    AtRun program19 (4*(word.length)+8) h (stage18 bits word innerBits outerBits n m a) (stage19 bits word innerBits outerBits n m a) := by
  have hr := padded_at slots19 slots19_injective h (stage18 bits word innerBits outerBits n m a)
    (outerBits) (word.length) (reset18 bits word n m)
    (by
      intro k
      fin_cases k
      · simpa [slots19,stage18,stage17,stage16,stage15,stage14,stage13,stage12,stage11,stage10,stage9,stage8,stage7,stage6,stage5,stage4,stage3,stage2,stage1,stage0,put,bankSlot,sourceSlots,sourceTapes] using (ha.source 5)
      · simpa [slots19,stage18,stage17,stage16,stage15,stage14,stage13,stage12,stage11,stage10,stage9,stage8,stage7,stage6,stage5,stage4,stage3,stage2,stage1,stage0,put] using (ha.fresh 455 (by decide))
      · simpa [slots19,stage18,stage17,stage16,stage15,stage14,stage13,stage12,stage11,stage10,stage9,stage8,stage7,stage6,stage5,stage4,stage3,stage2,stage1,stage0,put,bankSlot,sourceSlots,sourceTapes] using (ha.source 3)
      · simp [slots19,stage18,stage17,stage16,stage15,stage14,stage13,stage12,stage11,stage10,stage9,stage8,stage7,stage6,stage5,stage4,stage3,stage2,stage1,stage0,put]
    )
    (by
      intro k
      fin_cases k
      · exact ha.source_head 5
      · exact ha.fresh_head 455 (by decide)
      · exact ha.source_head 3
      · exact ha.reset_head
    )
  simpa [program19,slots19,stage19,put,reset19,buffer] using hr

def reset20 (bits word : List Bool) (n m : Nat) := max (reset19 bits word n m) (2*(word.length)+3)
def stage20 (bits word innerBits outerBits : List Bool) (n m : Nat) (a : Fin 493→List Bool) :=
  put (stage19 bits word innerBits outerBits n m a) 459 (frame (buffer outerBits word)) (reset20 bits word n m)
def slots20 : Fin 4→Fin 493 := ![275,459,24,336]
theorem slots20_injective : Function.Injective slots20 := by decide
noncomputable def program20 := RecoveryFocus.machine slots20 RecoveryColdPaddedCopy.machine
theorem call20 (bits word innerBits outerBits : List Bool) (n m : Nat)
    (h : Fin 493→Nat) (a : Fin 493→List Bool) (ha : Sources bits word innerBits outerBits n m h a) :
    AtRun program20 (4*(word.length)+8) h (stage19 bits word innerBits outerBits n m a) (stage20 bits word innerBits outerBits n m a) := by
  have hr := padded_at slots20 slots20_injective h (stage19 bits word innerBits outerBits n m a)
    (outerBits) (word.length) (reset19 bits word n m)
    (by
      intro k
      fin_cases k
      · simpa [slots20,stage19,stage18,stage17,stage16,stage15,stage14,stage13,stage12,stage11,stage10,stage9,stage8,stage7,stage6,stage5,stage4,stage3,stage2,stage1,stage0,put,bankSlot,sourceSlots,sourceTapes] using (ha.source 5)
      · simpa [slots20,stage19,stage18,stage17,stage16,stage15,stage14,stage13,stage12,stage11,stage10,stage9,stage8,stage7,stage6,stage5,stage4,stage3,stage2,stage1,stage0,put] using (ha.fresh 459 (by decide))
      · simpa [slots20,stage19,stage18,stage17,stage16,stage15,stage14,stage13,stage12,stage11,stage10,stage9,stage8,stage7,stage6,stage5,stage4,stage3,stage2,stage1,stage0,put,bankSlot,sourceSlots,sourceTapes] using (ha.source 3)
      · simp [slots20,stage19,stage18,stage17,stage16,stage15,stage14,stage13,stage12,stage11,stage10,stage9,stage8,stage7,stage6,stage5,stage4,stage3,stage2,stage1,stage0,put]
    )
    (by
      intro k
      fin_cases k
      · exact ha.source_head 5
      · exact ha.fresh_head 459 (by decide)
      · exact ha.source_head 3
      · exact ha.reset_head
    )
  simpa [program20,slots20,stage20,put,reset20,buffer] using hr

def reset21 (bits word : List Bool) (n m : Nat) := max (reset20 bits word n m) ((width bits)+2)
def stage21 (bits word innerBits outerBits : List Bool) (n m : Nat) (a : Fin 493→List Bool) :=
  put (stage20 bits word innerBits outerBits n m a) 387 (CompareMachine.word (width bits)) (reset21 bits word n m)
def slots21 : Fin 3→Fin 493 := ![2,387,336]
theorem slots21_injective : Function.Injective slots21 := by decide
noncomputable def program21 := RecoveryFocus.machine slots21 unaryMachine
theorem call21 (bits word innerBits outerBits : List Bool) (n m : Nat)
    (h : Fin 493→Nat) (a : Fin 493→List Bool) (ha : Sources bits word innerBits outerBits n m h a) :
    AtRun program21 (2*(width bits)+6) h (stage20 bits word innerBits outerBits n m a) (stage21 bits word innerBits outerBits n m a) := by
  have hr := unary_at slots21 slots21_injective h (stage20 bits word innerBits outerBits n m a)
    (width bits) (reset20 bits word n m)
    (by
      intro k
      fin_cases k
      · simpa [slots21,stage20,stage19,stage18,stage17,stage16,stage15,stage14,stage13,stage12,stage11,stage10,stage9,stage8,stage7,stage6,stage5,stage4,stage3,stage2,stage1,stage0,put,bankSlot,sourceSlots,sourceTapes] using (ha.source 1)
      · simpa [slots21,stage20,stage19,stage18,stage17,stage16,stage15,stage14,stage13,stage12,stage11,stage10,stage9,stage8,stage7,stage6,stage5,stage4,stage3,stage2,stage1,stage0,put] using (ha.fresh 387 (by decide))
      · simp [slots21,stage20,stage19,stage18,stage17,stage16,stage15,stage14,stage13,stage12,stage11,stage10,stage9,stage8,stage7,stage6,stage5,stage4,stage3,stage2,stage1,stage0,put]
    )
    (by
      intro k
      fin_cases k
      · exact ha.source_head 1
      · exact ha.fresh_head 387 (by decide)
      · exact ha.reset_head
    )
  simpa [program21,slots21,stage21,put,reset21] using hr

def reset22 (bits word : List Bool) (n m : Nat) := max (reset21 bits word n m) ((width bits)+2)
def stage22 (bits word innerBits outerBits : List Bool) (n m : Nat) (a : Fin 493→List Bool) :=
  put (stage21 bits word innerBits outerBits n m a) 395 (CompareMachine.word (width bits)) (reset22 bits word n m)
def slots22 : Fin 3→Fin 493 := ![2,395,336]
theorem slots22_injective : Function.Injective slots22 := by decide
noncomputable def program22 := RecoveryFocus.machine slots22 unaryMachine
theorem call22 (bits word innerBits outerBits : List Bool) (n m : Nat)
    (h : Fin 493→Nat) (a : Fin 493→List Bool) (ha : Sources bits word innerBits outerBits n m h a) :
    AtRun program22 (2*(width bits)+6) h (stage21 bits word innerBits outerBits n m a) (stage22 bits word innerBits outerBits n m a) := by
  have hr := unary_at slots22 slots22_injective h (stage21 bits word innerBits outerBits n m a)
    (width bits) (reset21 bits word n m)
    (by
      intro k
      fin_cases k
      · simpa [slots22,stage21,stage20,stage19,stage18,stage17,stage16,stage15,stage14,stage13,stage12,stage11,stage10,stage9,stage8,stage7,stage6,stage5,stage4,stage3,stage2,stage1,stage0,put,bankSlot,sourceSlots,sourceTapes] using (ha.source 1)
      · simpa [slots22,stage21,stage20,stage19,stage18,stage17,stage16,stage15,stage14,stage13,stage12,stage11,stage10,stage9,stage8,stage7,stage6,stage5,stage4,stage3,stage2,stage1,stage0,put] using (ha.fresh 395 (by decide))
      · simp [slots22,stage21,stage20,stage19,stage18,stage17,stage16,stage15,stage14,stage13,stage12,stage11,stage10,stage9,stage8,stage7,stage6,stage5,stage4,stage3,stage2,stage1,stage0,put]
    )
    (by
      intro k
      fin_cases k
      · exact ha.source_head 1
      · exact ha.fresh_head 395 (by decide)
      · exact ha.reset_head
    )
  simpa [program22,slots22,stage22,put,reset22] using hr

def reset23 (bits word : List Bool) (n m : Nat) := max (reset22 bits word n m) ((width bits)+2)
def stage23 (bits word innerBits outerBits : List Bool) (n m : Nat) (a : Fin 493→List Bool) :=
  put (stage22 bits word innerBits outerBits n m a) 456 (CompareMachine.word (width bits)) (reset23 bits word n m)
def slots23 : Fin 3→Fin 493 := ![2,456,336]
theorem slots23_injective : Function.Injective slots23 := by decide
noncomputable def program23 := RecoveryFocus.machine slots23 unaryMachine
theorem call23 (bits word innerBits outerBits : List Bool) (n m : Nat)
    (h : Fin 493→Nat) (a : Fin 493→List Bool) (ha : Sources bits word innerBits outerBits n m h a) :
    AtRun program23 (2*(width bits)+6) h (stage22 bits word innerBits outerBits n m a) (stage23 bits word innerBits outerBits n m a) := by
  have hr := unary_at slots23 slots23_injective h (stage22 bits word innerBits outerBits n m a)
    (width bits) (reset22 bits word n m)
    (by
      intro k
      fin_cases k
      · simpa [slots23,stage22,stage21,stage20,stage19,stage18,stage17,stage16,stage15,stage14,stage13,stage12,stage11,stage10,stage9,stage8,stage7,stage6,stage5,stage4,stage3,stage2,stage1,stage0,put,bankSlot,sourceSlots,sourceTapes] using (ha.source 1)
      · simpa [slots23,stage22,stage21,stage20,stage19,stage18,stage17,stage16,stage15,stage14,stage13,stage12,stage11,stage10,stage9,stage8,stage7,stage6,stage5,stage4,stage3,stage2,stage1,stage0,put] using (ha.fresh 456 (by decide))
      · simp [slots23,stage22,stage21,stage20,stage19,stage18,stage17,stage16,stage15,stage14,stage13,stage12,stage11,stage10,stage9,stage8,stage7,stage6,stage5,stage4,stage3,stage2,stage1,stage0,put]
    )
    (by
      intro k
      fin_cases k
      · exact ha.source_head 1
      · exact ha.fresh_head 456 (by decide)
      · exact ha.reset_head
    )
  simpa [program23,slots23,stage23,put,reset23] using hr

def reset24 (bits word : List Bool) (n m : Nat) := max (reset23 bits word n m) ((width bits)+2)
def stage24 (bits word innerBits outerBits : List Bool) (n m : Nat) (a : Fin 493→List Bool) :=
  put (stage23 bits word innerBits outerBits n m a) 464 (CompareMachine.word (width bits)) (reset24 bits word n m)
def slots24 : Fin 3→Fin 493 := ![2,464,336]
theorem slots24_injective : Function.Injective slots24 := by decide
noncomputable def program24 := RecoveryFocus.machine slots24 unaryMachine
theorem call24 (bits word innerBits outerBits : List Bool) (n m : Nat)
    (h : Fin 493→Nat) (a : Fin 493→List Bool) (ha : Sources bits word innerBits outerBits n m h a) :
    AtRun program24 (2*(width bits)+6) h (stage23 bits word innerBits outerBits n m a) (stage24 bits word innerBits outerBits n m a) := by
  have hr := unary_at slots24 slots24_injective h (stage23 bits word innerBits outerBits n m a)
    (width bits) (reset23 bits word n m)
    (by
      intro k
      fin_cases k
      · simpa [slots24,stage23,stage22,stage21,stage20,stage19,stage18,stage17,stage16,stage15,stage14,stage13,stage12,stage11,stage10,stage9,stage8,stage7,stage6,stage5,stage4,stage3,stage2,stage1,stage0,put,bankSlot,sourceSlots,sourceTapes] using (ha.source 1)
      · simpa [slots24,stage23,stage22,stage21,stage20,stage19,stage18,stage17,stage16,stage15,stage14,stage13,stage12,stage11,stage10,stage9,stage8,stage7,stage6,stage5,stage4,stage3,stage2,stage1,stage0,put] using (ha.fresh 464 (by decide))
      · simp [slots24,stage23,stage22,stage21,stage20,stage19,stage18,stage17,stage16,stage15,stage14,stage13,stage12,stage11,stage10,stage9,stage8,stage7,stage6,stage5,stage4,stage3,stage2,stage1,stage0,put]
    )
    (by
      intro k
      fin_cases k
      · exact ha.source_head 1
      · exact ha.fresh_head 464 (by decide)
      · exact ha.reset_head
    )
  simpa [program24,slots24,stage24,put,reset24] using hr

def reset25 (bits word : List Bool) (n m : Nat) := max (reset24 bits word n m) ((width bits)+2)
def stage25 (bits word innerBits outerBits : List Bool) (n m : Nat) (a : Fin 493→List Bool) :=
  put (stage24 bits word innerBits outerBits n m a) 480 (CompareMachine.word (width bits)) (reset25 bits word n m)
def slots25 : Fin 3→Fin 493 := ![2,480,336]
theorem slots25_injective : Function.Injective slots25 := by decide
noncomputable def program25 := RecoveryFocus.machine slots25 unaryMachine
theorem call25 (bits word innerBits outerBits : List Bool) (n m : Nat)
    (h : Fin 493→Nat) (a : Fin 493→List Bool) (ha : Sources bits word innerBits outerBits n m h a) :
    AtRun program25 (2*(width bits)+6) h (stage24 bits word innerBits outerBits n m a) (stage25 bits word innerBits outerBits n m a) := by
  have hr := unary_at slots25 slots25_injective h (stage24 bits word innerBits outerBits n m a)
    (width bits) (reset24 bits word n m)
    (by
      intro k
      fin_cases k
      · simpa [slots25,stage24,stage23,stage22,stage21,stage20,stage19,stage18,stage17,stage16,stage15,stage14,stage13,stage12,stage11,stage10,stage9,stage8,stage7,stage6,stage5,stage4,stage3,stage2,stage1,stage0,put,bankSlot,sourceSlots,sourceTapes] using (ha.source 1)
      · simpa [slots25,stage24,stage23,stage22,stage21,stage20,stage19,stage18,stage17,stage16,stage15,stage14,stage13,stage12,stage11,stage10,stage9,stage8,stage7,stage6,stage5,stage4,stage3,stage2,stage1,stage0,put] using (ha.fresh 480 (by decide))
      · simp [slots25,stage24,stage23,stage22,stage21,stage20,stage19,stage18,stage17,stage16,stage15,stage14,stage13,stage12,stage11,stage10,stage9,stage8,stage7,stage6,stage5,stage4,stage3,stage2,stage1,stage0,put]
    )
    (by
      intro k
      fin_cases k
      · exact ha.source_head 1
      · exact ha.fresh_head 480 (by decide)
      · exact ha.reset_head
    )
  simpa [program25,slots25,stage25,put,reset25] using hr

def reset26 (bits word : List Bool) (n m : Nat) := max (reset25 bits word n m) ((width bits+1)+2)
def stage26 (bits word innerBits outerBits : List Bool) (n m : Nat) (a : Fin 493→List Bool) :=
  put (stage25 bits word innerBits outerBits n m a) 368 (CompareMachine.word (width bits+1)) (reset26 bits word n m)
def slots26 : Fin 3→Fin 493 := ![14,368,336]
theorem slots26_injective : Function.Injective slots26 := by decide
noncomputable def program26 := RecoveryFocus.machine slots26 unaryMachine
theorem call26 (bits word innerBits outerBits : List Bool) (n m : Nat)
    (h : Fin 493→Nat) (a : Fin 493→List Bool) (ha : Sources bits word innerBits outerBits n m h a) :
    AtRun program26 (2*(width bits+1)+6) h (stage25 bits word innerBits outerBits n m a) (stage26 bits word innerBits outerBits n m a) := by
  have hr := unary_at slots26 slots26_injective h (stage25 bits word innerBits outerBits n m a)
    (width bits+1) (reset25 bits word n m)
    (by
      intro k
      fin_cases k
      · simpa [slots26,stage25,stage24,stage23,stage22,stage21,stage20,stage19,stage18,stage17,stage16,stage15,stage14,stage13,stage12,stage11,stage10,stage9,stage8,stage7,stage6,stage5,stage4,stage3,stage2,stage1,stage0,put,bankSlot,sourceSlots,sourceTapes] using (ha.source 6)
      · simpa [slots26,stage25,stage24,stage23,stage22,stage21,stage20,stage19,stage18,stage17,stage16,stage15,stage14,stage13,stage12,stage11,stage10,stage9,stage8,stage7,stage6,stage5,stage4,stage3,stage2,stage1,stage0,put] using (ha.fresh 368 (by decide))
      · simp [slots26,stage25,stage24,stage23,stage22,stage21,stage20,stage19,stage18,stage17,stage16,stage15,stage14,stage13,stage12,stage11,stage10,stage9,stage8,stage7,stage6,stage5,stage4,stage3,stage2,stage1,stage0,put]
    )
    (by
      intro k
      fin_cases k
      · exact ha.source_head 6
      · exact ha.fresh_head 368 (by decide)
      · exact ha.reset_head
    )
  simpa [program26,slots26,stage26,put,reset26] using hr

def reset27 (bits word : List Bool) (n m : Nat) := max (reset26 bits word n m) ((width bits+1)+2)
def stage27 (bits word innerBits outerBits : List Bool) (n m : Nat) (a : Fin 493→List Bool) :=
  put (stage26 bits word innerBits outerBits n m a) 437 (CompareMachine.word (width bits+1)) (reset27 bits word n m)
def slots27 : Fin 3→Fin 493 := ![14,437,336]
theorem slots27_injective : Function.Injective slots27 := by decide
noncomputable def program27 := RecoveryFocus.machine slots27 unaryMachine
theorem call27 (bits word innerBits outerBits : List Bool) (n m : Nat)
    (h : Fin 493→Nat) (a : Fin 493→List Bool) (ha : Sources bits word innerBits outerBits n m h a) :
    AtRun program27 (2*(width bits+1)+6) h (stage26 bits word innerBits outerBits n m a) (stage27 bits word innerBits outerBits n m a) := by
  have hr := unary_at slots27 slots27_injective h (stage26 bits word innerBits outerBits n m a)
    (width bits+1) (reset26 bits word n m)
    (by
      intro k
      fin_cases k
      · simpa [slots27,stage26,stage25,stage24,stage23,stage22,stage21,stage20,stage19,stage18,stage17,stage16,stage15,stage14,stage13,stage12,stage11,stage10,stage9,stage8,stage7,stage6,stage5,stage4,stage3,stage2,stage1,stage0,put,bankSlot,sourceSlots,sourceTapes] using (ha.source 6)
      · simpa [slots27,stage26,stage25,stage24,stage23,stage22,stage21,stage20,stage19,stage18,stage17,stage16,stage15,stage14,stage13,stage12,stage11,stage10,stage9,stage8,stage7,stage6,stage5,stage4,stage3,stage2,stage1,stage0,put] using (ha.fresh 437 (by decide))
      · simp [slots27,stage26,stage25,stage24,stage23,stage22,stage21,stage20,stage19,stage18,stage17,stage16,stage15,stage14,stage13,stage12,stage11,stage10,stage9,stage8,stage7,stage6,stage5,stage4,stage3,stage2,stage1,stage0,put]
    )
    (by
      intro k
      fin_cases k
      · exact ha.source_head 6
      · exact ha.fresh_head 437 (by decide)
      · exact ha.reset_head
    )
  simpa [program27,slots27,stage27,put,reset27] using hr

def reset28 (bits word : List Bool) (n m : Nat) := max (reset27 bits word n m) ((limit bits)+2)
def stage28 (bits word innerBits outerBits : List Bool) (n m : Nat) (a : Fin 493→List Bool) :=
  put (stage27 bits word innerBits outerBits n m a) 374 (CompareMachine.word (limit bits)) (reset28 bits word n m)
def slots28 : Fin 3→Fin 493 := ![21,374,336]
theorem slots28_injective : Function.Injective slots28 := by decide
noncomputable def program28 := RecoveryFocus.machine slots28 unaryMachine
theorem call28 (bits word innerBits outerBits : List Bool) (n m : Nat)
    (h : Fin 493→Nat) (a : Fin 493→List Bool) (ha : Sources bits word innerBits outerBits n m h a) :
    AtRun program28 (2*(limit bits)+6) h (stage27 bits word innerBits outerBits n m a) (stage28 bits word innerBits outerBits n m a) := by
  have hr := unary_at slots28 slots28_injective h (stage27 bits word innerBits outerBits n m a)
    (limit bits) (reset27 bits word n m)
    (by
      intro k
      fin_cases k
      · simpa [slots28,stage27,stage26,stage25,stage24,stage23,stage22,stage21,stage20,stage19,stage18,stage17,stage16,stage15,stage14,stage13,stage12,stage11,stage10,stage9,stage8,stage7,stage6,stage5,stage4,stage3,stage2,stage1,stage0,put,bankSlot,sourceSlots,sourceTapes] using (ha.source 7)
      · simpa [slots28,stage27,stage26,stage25,stage24,stage23,stage22,stage21,stage20,stage19,stage18,stage17,stage16,stage15,stage14,stage13,stage12,stage11,stage10,stage9,stage8,stage7,stage6,stage5,stage4,stage3,stage2,stage1,stage0,put] using (ha.fresh 374 (by decide))
      · simp [slots28,stage27,stage26,stage25,stage24,stage23,stage22,stage21,stage20,stage19,stage18,stage17,stage16,stage15,stage14,stage13,stage12,stage11,stage10,stage9,stage8,stage7,stage6,stage5,stage4,stage3,stage2,stage1,stage0,put]
    )
    (by
      intro k
      fin_cases k
      · exact ha.source_head 7
      · exact ha.fresh_head 374 (by decide)
      · exact ha.reset_head
    )
  simpa [program28,slots28,stage28,put,reset28] using hr

def reset29 (bits word : List Bool) (n m : Nat) := max (reset28 bits word n m) ((limit bits)+2)
def stage29 (bits word innerBits outerBits : List Bool) (n m : Nat) (a : Fin 493→List Bool) :=
  put (stage28 bits word innerBits outerBits n m a) 443 (CompareMachine.word (limit bits)) (reset29 bits word n m)
def slots29 : Fin 3→Fin 493 := ![21,443,336]
theorem slots29_injective : Function.Injective slots29 := by decide
noncomputable def program29 := RecoveryFocus.machine slots29 unaryMachine
theorem call29 (bits word innerBits outerBits : List Bool) (n m : Nat)
    (h : Fin 493→Nat) (a : Fin 493→List Bool) (ha : Sources bits word innerBits outerBits n m h a) :
    AtRun program29 (2*(limit bits)+6) h (stage28 bits word innerBits outerBits n m a) (stage29 bits word innerBits outerBits n m a) := by
  have hr := unary_at slots29 slots29_injective h (stage28 bits word innerBits outerBits n m a)
    (limit bits) (reset28 bits word n m)
    (by
      intro k
      fin_cases k
      · simpa [slots29,stage28,stage27,stage26,stage25,stage24,stage23,stage22,stage21,stage20,stage19,stage18,stage17,stage16,stage15,stage14,stage13,stage12,stage11,stage10,stage9,stage8,stage7,stage6,stage5,stage4,stage3,stage2,stage1,stage0,put,bankSlot,sourceSlots,sourceTapes] using (ha.source 7)
      · simpa [slots29,stage28,stage27,stage26,stage25,stage24,stage23,stage22,stage21,stage20,stage19,stage18,stage17,stage16,stage15,stage14,stage13,stage12,stage11,stage10,stage9,stage8,stage7,stage6,stage5,stage4,stage3,stage2,stage1,stage0,put] using (ha.fresh 443 (by decide))
      · simp [slots29,stage28,stage27,stage26,stage25,stage24,stage23,stage22,stage21,stage20,stage19,stage18,stage17,stage16,stage15,stage14,stage13,stage12,stage11,stage10,stage9,stage8,stage7,stage6,stage5,stage4,stage3,stage2,stage1,stage0,put]
    )
    (by
      intro k
      fin_cases k
      · exact ha.source_head 7
      · exact ha.fresh_head 443 (by decide)
      · exact ha.reset_head
    )
  simpa [program29,slots29,stage29,put,reset29] using hr

def reset30 (bits word : List Bool) (n m : Nat) := max (reset29 bits word n m) ((n)+2)
def stage30 (bits word innerBits outerBits : List Bool) (n m : Nat) (a : Fin 493→List Bool) :=
  put (stage29 bits word innerBits outerBits n m a) 406 (CompareMachine.word (n)) (reset30 bits word n m)
def slots30 : Fin 3→Fin 493 := ![270,406,336]
theorem slots30_injective : Function.Injective slots30 := by decide
noncomputable def program30 := RecoveryFocus.machine slots30 unaryMachine
theorem call30 (bits word innerBits outerBits : List Bool) (n m : Nat)
    (h : Fin 493→Nat) (a : Fin 493→List Bool) (ha : Sources bits word innerBits outerBits n m h a) :
    AtRun program30 (2*(n)+6) h (stage29 bits word innerBits outerBits n m a) (stage30 bits word innerBits outerBits n m a) := by
  have hr := unary_at slots30 slots30_injective h (stage29 bits word innerBits outerBits n m a)
    (n) (reset29 bits word n m)
    (by
      intro k
      fin_cases k
      · simpa [slots30,stage29,stage28,stage27,stage26,stage25,stage24,stage23,stage22,stage21,stage20,stage19,stage18,stage17,stage16,stage15,stage14,stage13,stage12,stage11,stage10,stage9,stage8,stage7,stage6,stage5,stage4,stage3,stage2,stage1,stage0,put,bankSlot,sourceSlots,sourceTapes] using (ha.source 8)
      · simpa [slots30,stage29,stage28,stage27,stage26,stage25,stage24,stage23,stage22,stage21,stage20,stage19,stage18,stage17,stage16,stage15,stage14,stage13,stage12,stage11,stage10,stage9,stage8,stage7,stage6,stage5,stage4,stage3,stage2,stage1,stage0,put] using (ha.fresh 406 (by decide))
      · simp [slots30,stage29,stage28,stage27,stage26,stage25,stage24,stage23,stage22,stage21,stage20,stage19,stage18,stage17,stage16,stage15,stage14,stage13,stage12,stage11,stage10,stage9,stage8,stage7,stage6,stage5,stage4,stage3,stage2,stage1,stage0,put]
    )
    (by
      intro k
      fin_cases k
      · exact ha.source_head 8
      · exact ha.fresh_head 406 (by decide)
      · exact ha.reset_head
    )
  simpa [program30,slots30,stage30,put,reset30] using hr

def reset31 (bits word : List Bool) (n m : Nat) := max (reset30 bits word n m) ((n)+2)
def stage31 (bits word innerBits outerBits : List Bool) (n m : Nat) (a : Fin 493→List Bool) :=
  put (stage30 bits word innerBits outerBits n m a) 489 (CompareMachine.word (n)) (reset31 bits word n m)
def slots31 : Fin 3→Fin 493 := ![270,489,336]
theorem slots31_injective : Function.Injective slots31 := by decide
noncomputable def program31 := RecoveryFocus.machine slots31 unaryMachine
theorem call31 (bits word innerBits outerBits : List Bool) (n m : Nat)
    (h : Fin 493→Nat) (a : Fin 493→List Bool) (ha : Sources bits word innerBits outerBits n m h a) :
    AtRun program31 (2*(n)+6) h (stage30 bits word innerBits outerBits n m a) (stage31 bits word innerBits outerBits n m a) := by
  have hr := unary_at slots31 slots31_injective h (stage30 bits word innerBits outerBits n m a)
    (n) (reset30 bits word n m)
    (by
      intro k
      fin_cases k
      · simpa [slots31,stage30,stage29,stage28,stage27,stage26,stage25,stage24,stage23,stage22,stage21,stage20,stage19,stage18,stage17,stage16,stage15,stage14,stage13,stage12,stage11,stage10,stage9,stage8,stage7,stage6,stage5,stage4,stage3,stage2,stage1,stage0,put,bankSlot,sourceSlots,sourceTapes] using (ha.source 8)
      · simpa [slots31,stage30,stage29,stage28,stage27,stage26,stage25,stage24,stage23,stage22,stage21,stage20,stage19,stage18,stage17,stage16,stage15,stage14,stage13,stage12,stage11,stage10,stage9,stage8,stage7,stage6,stage5,stage4,stage3,stage2,stage1,stage0,put] using (ha.fresh 489 (by decide))
      · simp [slots31,stage30,stage29,stage28,stage27,stage26,stage25,stage24,stage23,stage22,stage21,stage20,stage19,stage18,stage17,stage16,stage15,stage14,stage13,stage12,stage11,stage10,stage9,stage8,stage7,stage6,stage5,stage4,stage3,stage2,stage1,stage0,put]
    )
    (by
      intro k
      fin_cases k
      · exact ha.source_head 8
      · exact ha.fresh_head 489 (by decide)
      · exact ha.reset_head
    )
  simpa [program31,slots31,stage31,put,reset31] using hr

def reset32 (bits word : List Bool) (n m : Nat) := max (reset31 bits word n m) ((m)+2)
def stage32 (bits word innerBits outerBits : List Bool) (n m : Nat) (a : Fin 493→List Bool) :=
  put (stage31 bits word innerBits outerBits n m a) 491 (CompareMachine.word (m)) (reset32 bits word n m)
def slots32 : Fin 3→Fin 493 := ![274,491,336]
theorem slots32_injective : Function.Injective slots32 := by decide
noncomputable def program32 := RecoveryFocus.machine slots32 unaryMachine
theorem call32 (bits word innerBits outerBits : List Bool) (n m : Nat)
    (h : Fin 493→Nat) (a : Fin 493→List Bool) (ha : Sources bits word innerBits outerBits n m h a) :
    AtRun program32 (2*(m)+6) h (stage31 bits word innerBits outerBits n m a) (stage32 bits word innerBits outerBits n m a) := by
  have hr := unary_at slots32 slots32_injective h (stage31 bits word innerBits outerBits n m a)
    (m) (reset31 bits word n m)
    (by
      intro k
      fin_cases k
      · simpa [slots32,stage31,stage30,stage29,stage28,stage27,stage26,stage25,stage24,stage23,stage22,stage21,stage20,stage19,stage18,stage17,stage16,stage15,stage14,stage13,stage12,stage11,stage10,stage9,stage8,stage7,stage6,stage5,stage4,stage3,stage2,stage1,stage0,put,bankSlot,sourceSlots,sourceTapes] using (ha.source 9)
      · simpa [slots32,stage31,stage30,stage29,stage28,stage27,stage26,stage25,stage24,stage23,stage22,stage21,stage20,stage19,stage18,stage17,stage16,stage15,stage14,stage13,stage12,stage11,stage10,stage9,stage8,stage7,stage6,stage5,stage4,stage3,stage2,stage1,stage0,put] using (ha.fresh 491 (by decide))
      · simp [slots32,stage31,stage30,stage29,stage28,stage27,stage26,stage25,stage24,stage23,stage22,stage21,stage20,stage19,stage18,stage17,stage16,stage15,stage14,stage13,stage12,stage11,stage10,stage9,stage8,stage7,stage6,stage5,stage4,stage3,stage2,stage1,stage0,put]
    )
    (by
      intro k
      fin_cases k
      · exact ha.source_head 9
      · exact ha.fresh_head 491 (by decide)
      · exact ha.reset_head
    )
  simpa [program32,slots32,stage32,put,reset32] using hr

def reset33 (bits word : List Bool) (n m : Nat) := max (reset32 bits word n m) ((erase bits)+2)
def stage33 (bits word innerBits outerBits : List Bool) (n m : Nat) (a : Fin 493→List Bool) :=
  put (stage32 bits word innerBits outerBits n m a) 359 (List.replicate (erase bits) true) (reset33 bits word n m)
def slots33 : Fin 4→Fin 493 := ![16,337,359,336]
theorem slots33_injective : Function.Injective slots33 := by decide
noncomputable def program33 := RecoveryFocus.machine slots33 ClockUnarySum.machine
theorem call33 (bits word innerBits outerBits : List Bool) (n m : Nat)
    (h : Fin 493→Nat) (a : Fin 493→List Bool) (ha : Sources bits word innerBits outerBits n m h a) :
    AtRun program33 (2*(erase bits)+6) h (stage32 bits word innerBits outerBits n m a) (stage33 bits word innerBits outerBits n m a) := by
  have hr := erase_at slots33 slots33_injective h (stage32 bits word innerBits outerBits n m a)
    (erase bits) (reset32 bits word n m)
    (by
      intro k
      fin_cases k
      · simpa [slots33,stage32,stage31,stage30,stage29,stage28,stage27,stage26,stage25,stage24,stage23,stage22,stage21,stage20,stage19,stage18,stage17,stage16,stage15,stage14,stage13,stage12,stage11,stage10,stage9,stage8,stage7,stage6,stage5,stage4,stage3,stage2,stage1,stage0,put,bankSlot,sourceSlots,sourceTapes] using (ha.source 10)
      · simpa [slots33,stage32,stage31,stage30,stage29,stage28,stage27,stage26,stage25,stage24,stage23,stage22,stage21,stage20,stage19,stage18,stage17,stage16,stage15,stage14,stage13,stage12,stage11,stage10,stage9,stage8,stage7,stage6,stage5,stage4,stage3,stage2,stage1,stage0,put] using (ha.spare)
      · simpa [slots33,stage32,stage31,stage30,stage29,stage28,stage27,stage26,stage25,stage24,stage23,stage22,stage21,stage20,stage19,stage18,stage17,stage16,stage15,stage14,stage13,stage12,stage11,stage10,stage9,stage8,stage7,stage6,stage5,stage4,stage3,stage2,stage1,stage0,put] using (ha.fresh 359 (by decide))
      · simp [slots33,stage32,stage31,stage30,stage29,stage28,stage27,stage26,stage25,stage24,stage23,stage22,stage21,stage20,stage19,stage18,stage17,stage16,stage15,stage14,stage13,stage12,stage11,stage10,stage9,stage8,stage7,stage6,stage5,stage4,stage3,stage2,stage1,stage0,put]
    )
    (by
      intro k
      fin_cases k
      · exact ha.source_head 10
      · exact ha.spare_head
      · exact ha.fresh_head 359 (by decide)
      · exact ha.reset_head
    )
  simpa [program33,slots33,stage33,put,reset33] using hr

def reset34 (bits word : List Bool) (n m : Nat) := max (reset33 bits word n m) ((erase bits)+2)
def stage34 (bits word innerBits outerBits : List Bool) (n m : Nat) (a : Fin 493→List Bool) :=
  put (stage33 bits word innerBits outerBits n m a) 428 (List.replicate (erase bits) true) (reset34 bits word n m)
def slots34 : Fin 4→Fin 493 := ![16,337,428,336]
theorem slots34_injective : Function.Injective slots34 := by decide
noncomputable def program34 := RecoveryFocus.machine slots34 ClockUnarySum.machine
theorem call34 (bits word innerBits outerBits : List Bool) (n m : Nat)
    (h : Fin 493→Nat) (a : Fin 493→List Bool) (ha : Sources bits word innerBits outerBits n m h a) :
    AtRun program34 (2*(erase bits)+6) h (stage33 bits word innerBits outerBits n m a) (stage34 bits word innerBits outerBits n m a) := by
  have hr := erase_at slots34 slots34_injective h (stage33 bits word innerBits outerBits n m a)
    (erase bits) (reset33 bits word n m)
    (by
      intro k
      fin_cases k
      · simpa [slots34,stage33,stage32,stage31,stage30,stage29,stage28,stage27,stage26,stage25,stage24,stage23,stage22,stage21,stage20,stage19,stage18,stage17,stage16,stage15,stage14,stage13,stage12,stage11,stage10,stage9,stage8,stage7,stage6,stage5,stage4,stage3,stage2,stage1,stage0,put,bankSlot,sourceSlots,sourceTapes] using (ha.source 10)
      · simpa [slots34,stage33,stage32,stage31,stage30,stage29,stage28,stage27,stage26,stage25,stage24,stage23,stage22,stage21,stage20,stage19,stage18,stage17,stage16,stage15,stage14,stage13,stage12,stage11,stage10,stage9,stage8,stage7,stage6,stage5,stage4,stage3,stage2,stage1,stage0,put] using (ha.spare)
      · simpa [slots34,stage33,stage32,stage31,stage30,stage29,stage28,stage27,stage26,stage25,stage24,stage23,stage22,stage21,stage20,stage19,stage18,stage17,stage16,stage15,stage14,stage13,stage12,stage11,stage10,stage9,stage8,stage7,stage6,stage5,stage4,stage3,stage2,stage1,stage0,put] using (ha.fresh 428 (by decide))
      · simp [slots34,stage33,stage32,stage31,stage30,stage29,stage28,stage27,stage26,stage25,stage24,stage23,stage22,stage21,stage20,stage19,stage18,stage17,stage16,stage15,stage14,stage13,stage12,stage11,stage10,stage9,stage8,stage7,stage6,stage5,stage4,stage3,stage2,stage1,stage0,put]
    )
    (by
      intro k
      fin_cases k
      · exact ha.source_head 10
      · exact ha.spare_head
      · exact ha.fresh_head 428 (by decide)
      · exact ha.reset_head
    )
  simpa [program34,slots34,stage34,put,reset34] using hr

noncomputable def bankProgram := (Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine program1 program2) program3) program4) program5) program6) program7) program8) program9) program10) program11) program12) program13) program14) program15) program16) program17) program18) program19) program20) program21) program22) program23) program24) program25) program26) program27) program28) program29) program30) program31) program32) program33) program34)
def bankBudget (bits word : List Bool) (n m : Nat) :=
  66*width bits+28*word.length+4*limit bits+4*n+2*m+4*erase bits+281
theorem bank_run (bits word innerBits outerBits : List Bool) (n m : Nat)
    (h : Fin 493→Nat) (a : Fin 493→List Bool) (ha : Sources bits word innerBits outerBits n m h a) :
    AtRun bankProgram (bankBudget bits word n m) h a (stage34 bits word innerBits outerBits n m a) := by
  have hr := (((((((((((((((((((((((((((((((((call1 bits word innerBits outerBits n m h a ha).seq (call2 bits word innerBits outerBits n m h a ha)).seq (call3 bits word innerBits outerBits n m h a ha)).seq (call4 bits word innerBits outerBits n m h a ha)).seq (call5 bits word innerBits outerBits n m h a ha)).seq (call6 bits word innerBits outerBits n m h a ha)).seq (call7 bits word innerBits outerBits n m h a ha)).seq (call8 bits word innerBits outerBits n m h a ha)).seq (call9 bits word innerBits outerBits n m h a ha)).seq (call10 bits word innerBits outerBits n m h a ha)).seq (call11 bits word innerBits outerBits n m h a ha)).seq (call12 bits word innerBits outerBits n m h a ha)).seq (call13 bits word innerBits outerBits n m h a ha)).seq (call14 bits word innerBits outerBits n m h a ha)).seq (call15 bits word innerBits outerBits n m h a ha)).seq (call16 bits word innerBits outerBits n m h a ha)).seq (call17 bits word innerBits outerBits n m h a ha)).seq (call18 bits word innerBits outerBits n m h a ha)).seq (call19 bits word innerBits outerBits n m h a ha)).seq (call20 bits word innerBits outerBits n m h a ha)).seq (call21 bits word innerBits outerBits n m h a ha)).seq (call22 bits word innerBits outerBits n m h a ha)).seq (call23 bits word innerBits outerBits n m h a ha)).seq (call24 bits word innerBits outerBits n m h a ha)).seq (call25 bits word innerBits outerBits n m h a ha)).seq (call26 bits word innerBits outerBits n m h a ha)).seq (call27 bits word innerBits outerBits n m h a ha)).seq (call28 bits word innerBits outerBits n m h a ha)).seq (call29 bits word innerBits outerBits n m h a ha)).seq (call30 bits word innerBits outerBits n m h a ha)).seq (call31 bits word innerBits outerBits n m h a ha)).seq (call32 bits word innerBits outerBits n m h a ha)).seq (call33 bits word innerBits outerBits n m h a ha)).seq (call34 bits word innerBits outerBits n m h a ha)
  have he : (((((((((((((((((((((((((((((((((4*(width bits)+8)+1+(4*(width bits)+8))+1+(4*(width bits)+8))+1+(4*(width bits)+8))+1+(4*(width bits)+8))+1+(4*(width bits)+8))+1+(4*(width bits)+8))+1+(4*(width bits)+8))+1+(4*(width bits)+8))+1+(4*(width bits)+8))+1+(4*(width bits)+8))+1+(4*(width bits)+8))+1+(4*(width bits)+8))+1+(4*(word.length)+8))+1+(4*(word.length)+8))+1+(4*(word.length)+8))+1+(4*(word.length)+8))+1+(4*(word.length)+8))+1+(4*(word.length)+8))+1+(4*(word.length)+8))+1+(2*(width bits)+6))+1+(2*(width bits)+6))+1+(2*(width bits)+6))+1+(2*(width bits)+6))+1+(2*(width bits)+6))+1+(2*(width bits+1)+6))+1+(2*(width bits+1)+6))+1+(2*(limit bits)+6))+1+(2*(limit bits)+6))+1+(2*(n)+6))+1+(2*(n)+6))+1+(2*(m)+6))+1+(2*(erase bits)+6))+1+(2*(erase bits)+6)=bankBudget bits word n m := by unfold bankBudget; omega
  rw [he] at hr
  exact hr

end NearCubicWires.RepairOrdinary.RecoveryColdCompact

