import Proof.Supplier.EquationScalarStream
import Proof.Supplier.EquationZeroField
import Proof.Amplification.RecoveryCursorCalls
import Proof.PCP.ProjectionNormalizationForwardRules
import Proof.PCP.ProjectionNormalizationSuffixRestore

/-! Small forward source pass: widen all weights and branch on the actual
odd flag to emit the optional ignored coordinate. -/
namespace NearCubicWires.RepairOrdinary.EquationCut
open LocalBitMultitape RecoveryExecution RecoveryRootRound MatrixScoreBatch
open RepairSource.VerifierDecoding RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def heads (pos : Nat) (out : List Bool) : Fin 5→Nat := ![pos,out.length,1,1,0]
def tapes (source out : List Bool) (L p : Nat) (odd : Bool) : Fin 5→List Bool :=
  ![source,out,CompareMachine.word L,CompareMachine.word (p+2),[odd]]
def weightSlots : Fin 3→Fin 5 := ![0,1,2]
def zeroSlots : Fin 2→Fin 5 := ![3,1]
def scalarSlots : Fin 2→Fin 5 := ![0,1]
def weightProgram := RecoveryFocus.machine weightSlots EquationWidenLoop.machine
def zeroProgram := RecoveryFocus.machine zeroSlots EquationZeroField.machine
def scalarProgram := RecoveryFocus.machine scalarSlots EquationWiden.machine
def weightSizes : Fin 2→Nat := ![Fintype.card (RepeatMachine.Control 5),4]
def weightPrograms : (j : Fin 2)→Machine 5 (weightSizes j) :=
  Fin.cases weightProgram (Fin.cases zeroProgram (fun i=>nomatch i))
def weightNext (j : Fin 2) (_ : Fin (weightSizes j)) (bs : Fin 5→Bool) : Option (Fin 2) :=
  if j=0 ∧ bs 4=true then some 1 else none
def weightMachine := RecoveryCalls.machine weightSizes weightPrograms 0 weightNext
def weightEntry (j : Fin 2) (source out : List Bool) (pos L p : Nat) (odd : Bool) :=
  controlConfig (RecoveryCalls.code weightSizes j)
    (RecoveryCalls.restarted (weightPrograms j) (heads pos out) (tapes source out L p odd))
def paddedWeights (p : Nat) (odd : Bool) (values : List Int) :=
  EquationWidenLoop.stream (p+1) values++if odd then frame (signMagnitude (p+1) 0) else []
def weightBudget (L p : Nat) := L*(2*p+8)+3*p+13
def baseTail := Composition.machine scalarProgram scalarProgram
def base := Composition.machine weightMachine baseTail
def restored := CursorRestore.machine base 0

theorem pick_weight (i : Fin 5) : RecoveryFocus.pick weightSlots i=
    (if i=0 then some 0 else if i=1 then some 1 else if i=2 then some 2 else none) := by
  fin_cases i
  all_goals first
    | exact RecoveryFocus.pick_slot weightSlots (by decide) 0
    | exact RecoveryFocus.pick_slot weightSlots (by decide) 1
    | exact RecoveryFocus.pick_slot weightSlots (by decide) 2
    | decide
theorem pick_zero (i : Fin 5) : RecoveryFocus.pick zeroSlots i=
    (if i=3 then some 0 else if i=1 then some 1 else none) := by
  fin_cases i
  all_goals first
    | exact RecoveryFocus.pick_slot zeroSlots (by decide) 0
    | exact RecoveryFocus.pick_slot zeroSlots (by decide) 1
    | decide
theorem pick_scalar (i : Fin 5) : RecoveryFocus.pick scalarSlots i=
    (if i=0 then some 0 else if i=1 then some 1 else none) := by
  fin_cases i
  all_goals first
    | exact RecoveryFocus.pick_slot scalarSlots (by decide) 0
    | exact RecoveryFocus.pick_slot scalarSlots (by decide) 1
    | decide

theorem widen_forward : CursorRestore.NoLeft EquationWiden.machine 0 := by
  intro q bs a ha
  fin_cases q <;> simp [EquationWiden.machine] at ha <;> cases ha <;> simp

theorem weight_forward : CursorRestore.NoLeft weightProgram 0 :=
  CursorRestore.focus_forward weightSlots (by decide) EquationWidenLoop.machine 0
    (CursorRestore.repeat_forward EquationWiden.machine (fun _ _=>true) 0 widen_forward)
theorem zero_forward : CursorRestore.NoLeft zeroProgram 0 := by
  intro q bs a ha
  unfold zeroProgram RecoveryFocus.machine at ha
  obtain ⟨b,hb,he⟩ := Option.map_eq_some_iff.mp ha
  subst a
  simp [RecoveryFocus.action,pick_zero]

theorem calls_forward {t k : Nat} (sizes : Fin k→Nat)
    (programs : (j : Fin k)→Machine t (sizes j)) (first : Fin k)
    (next : (j : Fin k)→Fin (sizes j)→(Fin t→Bool)→Option (Fin k)) (i : Fin t)
    (hf : ∀ j,CursorRestore.NoLeft (programs j) i) :
    CursorRestore.NoLeft (RecoveryCalls.machine sizes programs first next) i := by
  intro q bs a ha
  cases hc : (RecoveryCalls.controlCode sizes).symm q with
  | none => simp [RecoveryCalls.machine,hc] at ha
  | some j =>
    simp only [RecoveryCalls.machine,hc] at ha
    split at ha
    · cases ha; simp
    · obtain ⟨b,hb,he⟩ := Option.map_eq_some_iff.mp ha
      subst a
      exact hf j.1 j.2 bs b hb

theorem base_forward : CursorRestore.NoLeft base 0 := by
  apply CursorRestore.composition_forward
  · apply calls_forward
    intro j
    fin_cases j
    · exact weight_forward
    · exact zero_forward
  · apply CursorRestore.composition_forward
    all_goals exact CursorRestore.focus_forward scalarSlots (by decide) EquationWiden.machine 0 widen_forward

end
end NearCubicWires.RepairOrdinary.EquationCut
