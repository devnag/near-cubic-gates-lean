import Proof.Supplier.EquationCutRestore

/-! The agreed common twenty-one-tape bank for both passes of one cut. -/
namespace NearCubicWires.RepairOrdinary.EquationCut.Ambient
open LocalBitMultitape RecoveryRootRound MatrixScoreBatch
open RepairSource.VerifierDecoding RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def extraHeads : Fin 4→Nat := ![1,1,0,0]
def extras (C L p : Nat) (odd : Bool) : Fin 4→List Bool :=
  ![CompareMachine.word L,CompareMachine.word (p+2),[odd],List.replicate C false]
def heads (pos : Nat) (out : List Bool) : Fin 21→Nat :=
  Fin.addCases (m:=17) (n:=4) (motive:=fun _=>Nat) (EquationScalarStream.heads pos out.length) extraHeads
def tapes (C : Nat) (source out : List Bool) (L p : Nat) (odd : Bool) : Fin 21→List Bool :=
  Fin.addCases (m:=17) (n:=4) (motive:=fun _=>List Bool) (EquationScalarStream.tapes C source out) (extras C L p odd)
def slots : Fin 5→Fin 21 := ![0,14,17,18,19]
def restoreSlots : Fin 6→Fin 21 := ![0,14,17,18,19,20]
def weightProgram := RecoveryFocus.machine slots weightMachine
def restoreProgram := RecoveryFocus.machine restoreSlots restored
def scalarProgram (negate : Bool) := TapeEmbedding.machine 4 (EquationScalarStream.machine negate)
def secondTail := Composition.machine (scalarProgram false) (scalarProgram true)
def second := Composition.machine weightProgram secondTail
def machine := Composition.machine restoreProgram second
def budget (C : Nat) := 16*C
def entry (C pos : Nat) (source out : List Bool) (L p : Nat) (odd : Bool) :=
  RecoveryCalls.restarted machine (heads pos out) (tapes C source out L p odd)

theorem pick (i : Fin 21) : RecoveryFocus.pick slots i=
    (if i=0 then some 0 else if i=14 then some 1 else if i=17 then some 2 else
      if i=18 then some 3 else if i=19 then some 4 else none) := by
  fin_cases i
  all_goals first
    | exact RecoveryFocus.pick_slot slots (by decide) 0
    | exact RecoveryFocus.pick_slot slots (by decide) 1
    | exact RecoveryFocus.pick_slot slots (by decide) 2
    | exact RecoveryFocus.pick_slot slots (by decide) 3
    | exact RecoveryFocus.pick_slot slots (by decide) 4
    | decide
theorem pick_restore (i : Fin 21) : RecoveryFocus.pick restoreSlots i=
    (if i=0 then some 0 else if i=14 then some 1 else if i=17 then some 2 else
      if i=18 then some 3 else if i=19 then some 4 else if i=20 then some 5 else none) := by
  fin_cases i
  all_goals first
    | exact RecoveryFocus.pick_slot restoreSlots (by decide) 0
    | exact RecoveryFocus.pick_slot restoreSlots (by decide) 1
    | exact RecoveryFocus.pick_slot restoreSlots (by decide) 2
    | exact RecoveryFocus.pick_slot restoreSlots (by decide) 3
    | exact RecoveryFocus.pick_slot restoreSlots (by decide) 4
    | exact RecoveryFocus.pick_slot restoreSlots (by decide) 5
    | decide

end
end NearCubicWires.RepairOrdinary.EquationCut.Ambient
