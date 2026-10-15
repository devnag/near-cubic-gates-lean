import Proof.Amplification.RecoveryRawSATEnd

/-! The raw-SAT table controller runs its physical count driver, tests the
remaining code on success, and executes a false write on rejection. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRawSATTable
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryRawSAT
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def rejectMachine : Machine 71 2 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val==1
  rule := fun q _=>if q.val=0 then
    some ⟨1,fun i=>if i=27 then some false else none,fun _=>.stay⟩ else none
def rejected (c : Configuration 71 2) : Configuration 71 2 :=
  ⟨1,c.heads,Function.update c.tapes 27 [false]⟩

theorem reject_run (c : Configuration 71 2) (hc : c.control=0) (hh : c.heads 27=0)
    (bit : Bool) (ht : c.tapes 27=[bit]) :
    ∃ r,runFrom rejectMachine 1 c=some r ∧ r.final=rejected c ∧ r.steps=1 := by
  have h : step rejectMachine c=some (rejected c) := by
    simp only [step,rejectMachine,hc,Fin.val_zero,if_true]
    apply congrArg some
    apply configuration_ext
    · rfl
    · rfl
    · funext i
      by_cases hi : i=27
      · subst i
        change writeTapeBit (c.tapes 27) (c.heads 27) false=[false]
        rw [hh,ht]
        rfl
      · simp only [applyAction,if_neg hi,rejected,Function.update_of_ne hi]
  exact (Timed.single (by simp [rejectMachine,hc]) h).run (by rfl)

private abbrev stateCount {t s : Nat} (_ : Machine t s) := s
noncomputable abbrev bodyStates := stateCount RecoveryRawSAT.machine
noncomputable abbrev loopStates := stateCount RecoveryRawSATLoop.machine
noncomputable abbrev endStates := stateCount RecoveryRawSATEnd.machine
noncomputable def sizes : Fin 3→Nat := ![loopStates,endStates,2]
noncomputable def programs : (j : Fin 3)→Machine 71 (sizes j)
  | ⟨0,_⟩=>RecoveryRawSATLoop.machine
  | ⟨1,_⟩=>RecoveryRawSATEnd.machine
  | ⟨2,_⟩=>rejectMachine
  | ⟨n+3,h⟩=>False.elim (by omega)
noncomputable def next : (j : Fin 3)→Fin (sizes j)→(Fin 71→Bool)→Option (Fin 3)
  | ⟨0,_⟩,q,_=>some (if q=RepeatMachine.phaseCode bodyStates 3 then 1 else 2)
  | ⟨1,_⟩,_,_=>none
  | ⟨2,_⟩,_,_=>none
  | ⟨n+3,h⟩,_,_=>False.elim (by omega)
noncomputable def machine := RecoveryCalls.machine sizes programs 0 next
def budget (width total : Nat) := RecoveryRawSATLoop.budget width total+262144*(width+1)^2+5
def answer (width cap committed count total : Nat) (word : List Bool) (code : Nat) :=
  prefixCheck (clauseCheck width cap committed count word) total code && decide (tailCode total code=0)

theorem phases_ne : RepeatMachine.phaseCode bodyStates 4≠RepeatMachine.phaseCode bodyStates 3 := by
  intro h
  have he : (4 : Fin 5)=3 := Sum.inr.inj ((RepeatMachine.code bodyStates).injective h)
  exact (by decide : (4 : Fin 5)≠3) he

theorem end_budget (width cap committed count : Nat) (word : List Bool) (x : State)
    (hx : Inv width cap committed count word x) :
    RecoveryRawSATEnd.budget x ≤ 262144*(width+1)^2+2 := by
  have h := RecoveryRawSAT.cell_cost x word hx.valid
  rw [hx.width_eq] at h
  exact Nat.add_le_add_right h 2

theorem end_restart (x : State) (total : Nat) :
    RecoveryCalls.restarted (programs 1)
      (RepeatMachine.cfg 3 (RecoveryRawSATLoop.source x) total 1).heads
      (RepeatMachine.cfg 3 (RecoveryRawSATLoop.source x) total 1).tapes=
      RecoveryRawSATEnd.cfg x.tapes total RecoveryRawSATEnd.machine.start := by
  simp only [RecoveryCalls.restarted,RepeatMachine.cfg,controlConfig,RecoveryRawSATLoop.source,
    RecoveryRawSATEnd.cfg,TapeEmbedding.config,State.cfg]
  rfl

end NearCubicWires.RepairOrdinary.RecoveryRawSATTable
