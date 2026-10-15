import Proof.Amplification.RecoveryMarkerFlags

/-! A marker atom is an actual decoded literal and saved natural field.
Mode0 retains the payload polarity and requires a singleton clause;
mode1 requires the false committed tag; mode2 requires the true count tag
and tests the clause tail. -/
namespace NearCubicWires.RepairOrdinary.RecoveryMarkerAtom
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryMarkerClause
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

private abbrev stateCount {t s : Nat} (_ : Machine t s) := s
noncomputable abbrev literalStates := stateCount literalMachine
noncomputable abbrev saveStates (which : Fin 3) := stateCount (RecoveryMarkerSave.machine which)
noncomputable abbrev emptyStates := stateCount emptyMachine
noncomputable def sizes (which : Fin 3) : Fin 6→Nat := ![literalStates,2,saveStates which,emptyStates,2,2]
noncomputable def programs (which : Fin 3) : (j : Fin 6)→Machine 57 (sizes which j)
  | ⟨0,_⟩=>literalMachine
  | ⟨1,_⟩=>RecoveryMarkerFlags.flatMachine
  | ⟨2,_⟩=>RecoveryMarkerSave.machine which
  | ⟨3,_⟩=>emptyMachine
  | ⟨4,_⟩=>RecoveryMarkerFlags.answerMachine true
  | ⟨5,_⟩=>RecoveryMarkerFlags.answerMachine false
  | ⟨n+6,h⟩=>False.elim (by omega)
def tagOK (which : Fin 3) (sign : Bool) :=
  if which.val=0 then true else if which.val=1 then !sign else sign
def gate (which : Fin 3) (bits : Fin 57→Bool) := bits 28 && bits 27 && tagOK which (bits 23)
noncomputable def next (which : Fin 3) (j : Fin 6) (_ : Fin (sizes which j))
    (bits : Fin 57→Bool) : Option (Fin 6) :=
  ![some (if gate which bits then if which.val=0 then 1 else 2 else 5),some 2,
    some (if which.val=1 then 4 else 3),some (if bits 23 then 5 else 4),none,none] j
noncomputable def machine (which : Fin 3) := RecoveryCalls.machine (sizes which) (programs which) 0 (next which)

def good (which : Fin 3) (x : State) :=
  x.inner.present && x.inner.data.result && tagOK which x.inner.data.flag
def withSign (which : Fin 3) (x : State) := if which.val=0 then RecoveryMarkerFlags.flat x else x
def saved (which : Fin 3) (x : State) := RecoveryMarkerSave.saved x which
def tested (which : Fin 3) (x : State) := if which.val=1 then saved which x else emptyStep (saved which x)
def tailAnswer (which : Fin 3) (x : State) := if which.val=1 then true else !(tested which x).inner.data.flag
def final (which : Fin 3) (x : State) := RecoveryMarkerFlags.answered (tested which x) (tailAnswer which x)
def output (which : Fin 3) (x : State) :=
  let y := literalStep x
  if good which y then final which (withSign which y) else RecoveryMarkerFlags.answered y false
def answer (which : Fin 3) (x : State) :=
  good which (literalStep x) && tailAnswer which (withSign which (literalStep x))
def saveBudget (width : Nat) := 262144*(width+1)^2+8*width+12
def budget (width : Nat) := 1048576*(width+1)^2

theorem gate_tapes (which : Fin 3) (x : State) :
    gate which (fun i=>readTapeBit (x.tapes i) 0)=good which x := rfl

theorem tested_valid (which : Fin 3) (x : State) (hx : x.Valid) : (tested which x).Valid := by
  have hs := RecoveryMarkerSave.saved_valid x which hx
  unfold tested
  split
  · exact hs
  · exact empty_valid _ hs

theorem tested_width (which : Fin 3) (x : State) : (tested which x).width=x.width := by
  unfold tested
  split
  · exact RecoveryMarkerSave.saved_width x which
  · exact (RecoveryClauseState.after_length (saved which x).inner.data 0).trans (RecoveryMarkerSave.saved_width x which)

theorem good_present (which : Fin 3) (x : State) (hg : good which (literalStep x)=true) :
    RadixSemantics.value x.inner.data.bits≠0 := by
  have hp : (literalStep x).inner.present=true := by
    simp only [good,Bool.and_eq_true] at hg
    exact hg.1.1
  rw [show (literalStep x).inner.present=decide (RadixSemantics.value x.inner.data.bits≠0)
    from RecoveryRawLiteral.output_present x.inner,decide_eq_true_eq] at hp
  exact hp

def variableWord (x : State) := RecoveryChildSelection.word false (RecoveryRawLiteral.literal x.inner)
theorem variable_length (x : State) : (variableWord x).length=(literalStep x).width := by
  rw [show (literalStep x).width=x.width from RecoveryRawLiteral.output_width x.inner]
  exact (RecoveryChildSelection.word_length false (RecoveryRawLiteral.literal x.inner)).trans
    (RecoveryCellStore.headWord_length x.inner.data.bits)
theorem variable_field (which : Fin 3) (x : State) (hg : good which (literalStep x)=true) :
    (literalStep x).inner.data.fields 0=frame (variableWord x) :=
  (RecoveryRawLiteral.output_variable x.inner (good_present which x hg)).1

end NearCubicWires.RepairOrdinary.RecoveryMarkerAtom
