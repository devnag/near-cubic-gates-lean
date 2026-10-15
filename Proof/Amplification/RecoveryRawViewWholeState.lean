import Proof.Amplification.RecoveryRawViewLoopInvariant

/-! One outer raw-view controller runs the actual clause count and then
tests that the remaining input code is empty. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRawViewWhole
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryRawView
open RepairSource.VerifierDecoding
open RecoveryRawViewLoop
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

private abbrev stateCount {t s : Nat} (_ : Machine t s) := s
noncomputable abbrev bodyStates := stateCount RecoveryRawViewBody.machine
noncomputable abbrev loopStates := stateCount RecoveryRawViewLoop.machine
noncomputable abbrev endStates := stateCount RecoveryRawViewEnd.machine
noncomputable def sizes : Fin 2→Nat := ![loopStates,endStates]
noncomputable def programs : (j : Fin 2)→Machine 66 (sizes j)
  | ⟨0,_⟩=>RecoveryRawViewLoop.machine
  | ⟨1,_⟩=>RecoveryRawViewEnd.machine
  | ⟨n+2,h⟩=>False.elim (by omega)
noncomputable def next : (j : Fin 2)→Fin (sizes j)→(Fin 66→Bool)→Option (Fin 2)
  | ⟨0,_⟩,q,_=>if q=RepeatMachine.phaseCode bodyStates 3 then some 1 else none
  | ⟨1,_⟩,_,_=>none
  | ⟨n+2,h⟩,_,_=>False.elim (by omega)
noncomputable def machine := RecoveryCalls.machine sizes programs 0 next
def budget (width total : Nat) := RecoveryRawViewLoop.budget width total+262144*(width+1)^2+4
def answer (word : List Bool) (total : Nat) (x : Cursor) :=
  (out word total x).1 && decide (RecoveryRawViewBody.code (out word total x).2.data=0)

theorem phases_ne : RepeatMachine.phaseCode bodyStates 4≠RepeatMachine.phaseCode bodyStates 3 := by
  intro h
  have he : (4 : Fin 5)=3 := Sum.inr.inj ((RepeatMachine.code bodyStates).injective h)
  exact (by decide : (4 : Fin 5)≠3) he

theorem end_budget (width : Nat) (word : List Bool) (x : Cursor) (hx : Inv width word x) :
    RecoveryRawViewEnd.budget x.data ≤ 262144*(width+1)^2+2 := by
  have h := RecoveryStoredListCell.time_bound x.data.outer.bits
  unfold RecoveryStoredListCell.budget at h
  rw [hx.1.2.2.1,hx.2.1] at h
  exact Nat.add_le_add_right h 2

end NearCubicWires.RepairOrdinary.RecoveryRawViewWhole
