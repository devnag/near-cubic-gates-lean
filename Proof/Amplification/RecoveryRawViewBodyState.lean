import Proof.Amplification.RecoveryRawViewFlag

/-! One fixed raw-view clause controller. Missing outer cells and rejected
counts stop with the physically cleared flag; successful counts drive the
existing exact clause checker on the actual extracted natural code. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRawViewBody
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryRawView
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

private abbrev stateCount {t s : Nat} (_ : Machine t s) := s
noncomputable abbrev outerStates := stateCount outerMachine
noncomputable abbrev clearStates := stateCount RecoveryRawView.clearMachine
noncomputable abbrev copyStates := stateCount RecoveryRawView.copyMachine
noncomputable abbrev clauseStates := stateCount clauseMachine
noncomputable def sizes : Fin 6→Nat := ![2,outerStates,clearStates,5,copyStates,clauseStates]
noncomputable def programs : (j : Fin 6)→Machine 65 (sizes j)
  | ⟨0,_⟩=>flagMachine false
  | ⟨1,_⟩=>outerMachine
  | ⟨2,_⟩=>RecoveryRawView.clearMachine
  | ⟨3,_⟩=>countMachine
  | ⟨4,_⟩=>RecoveryRawView.copyMachine
  | ⟨5,_⟩=>clauseMachine
  | ⟨n+6,h⟩=>False.elim (by omega)
noncomputable def next : (j : Fin 6)→Fin (sizes j)→(Fin 65→Bool)→Option (Fin 6)
  | ⟨0,_⟩,_,_=>some 1
  | ⟨1,_⟩,_,bits=>if bits 59 then some 2 else none
  | ⟨2,_⟩,_,_=>some 3
  | ⟨3,_⟩,q,_=>if q.val=3 then some 4 else none
  | ⟨4,_⟩,_,_=>some 5
  | ⟨5,_⟩,_,_=>none
  | ⟨n+6,h⟩,_,_=>False.elim (by omega)
noncomputable def machine := RecoveryCalls.machine sizes programs 0 next

def clauseBudget (width limit : Nat) := RecoveryRawClause.budget width limit
def copyBudget (width limit : Nat) := 8*width+8+clauseBudget width limit+2
def countBudget (width limit : Nat) := 3*limit+3+copyBudget width limit+1
def clearBudget (x : State) := clearCost x+countBudget x.width x.limit+1
def outerBudget (x : State) := RecoveryStoredListCell.time x.outer.bits+clearBudget x+1
def budget (x : State) := outerBudget x+2

def headWord (x : State) := RecoveryCellStore.headWord x.outer.bits
def staged (x : State) := cleared (outerStep (flagged x false))
def prepared (x : State) (n : Nat) := copied (counted (staged x) n) (headWord x)
def output (x : State) (n : Nat) := finished (prepared x n)
def answer (x : State) (word : List Bool) (k : Nat) : Bool :=
  if RadixSemantics.value x.outer.bits=0 then false else
    match readCount x.limit (word.drop k) with
    | none=>false
    | some (n,_)=>clauseAnswer (prepared x n)

theorem clause_budget_mono (width n limit : Nat) (hn : n ≤ limit) :
    RecoveryRawClause.budget width n ≤ clauseBudget width limit := by
  unfold clauseBudget RecoveryRawClause.budget RecoveryRawLiteralLoop.budget
  have h := Nat.mul_le_mul_right (RecoveryRawLiteralLoop.bodyBudget width+3) hn
  omega

theorem head_width (x : State) (hx : x.Valid) : (headWord x).length=x.width :=
  (RecoveryCellStore.headWord_length x.outer.bits).trans hx.2.2.1

theorem staged_valid (x : State) (hx : x.Valid) : (staged x).Valid :=
  cleared_valid _ (outer_step_valid _ (flagged_valid x false hx))

theorem staged_field (x : State) (hn : RadixSemantics.value x.outer.bits≠0) :
    (staged x).outer.fields 0=frame (headWord x) := by
  change (x.outer.after 0).fields 0=_
  simp only [RecoveryClauseState.State.after,hn,ite_false,Function.update_self]
  rfl

theorem prepared_valid (x : State) (hx : x.Valid) (n : Nat) (hn : n ≤ x.limit) :
    (prepared x n).Valid :=
  copied_valid _ _ (counted_valid _ n (staged_valid x hx) hn) (head_width x hx)

theorem prepared_width (x : State) (hx : x.Valid) (n : Nat) : (prepared x n).width=x.width :=
  copied_width _ _ (head_width x hx)

theorem prepared_count (x : State) (n : Nat) : (prepared x n).count=n := rfl
theorem prepared_limit (x : State) (n : Nat) : (prepared x n).limit=x.limit := rfl

end NearCubicWires.RepairOrdinary.RecoveryRawViewBody
