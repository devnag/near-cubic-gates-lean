import Proof.CaseAnalysis.ScheduleCompare
import Proof.Amplification.RecoveryEraseConstant
import Proof.PCP.PCPPairReusable

/-! The common recovery program tests its fixed source onset against the
actual selected length. The onset is printed by fixed finite control; the
selected length and any backing cells are retained. No initialized constant
or scratch is an input premise. -/
namespace NearCubicWires.RepairSource.CloseoutSchedule.OnsetGuard
open LocalBitMultitape RepairOrdinary RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def constantSlots : Fin 2→Fin 7:=![1,2]
def compareSlots : Fin 6→Fin 7:=![1,0,3,4,5,6]
def input (C N : Nat) : Fin 7→List Bool:=
  ![ZeroPadding.pad C (List.replicate N true),[],[],[],[],[],[]]
def caps (C : Nat) : Fin 6→Nat:=![0,C,0,0,0,0]
def middle (onset C N : Nat) := install constantSlots (input C N)
  (![List.replicate onset true,List.replicate onset false] : Fin 2→List Bool)
def output (onset C N : Nat) := install compareSlots (middle onset C N)
  (fun i=>ZeroPadding.pad (caps C i) (RawCompare.output onset N i))
def first (onset : Nat):=RecoveryFocus.machine constantSlots (RecoveryEraseConstant.resetMachine onset)
def second:=RecoveryFocus.machine compareSlots RawCompare.machine
def machine (onset : Nat):=Composition.machine (first onset) second

theorem compare_input (onset C N : Nat) (i : Fin 6) :
    middle onset C N (compareSlots i)=
      ZeroPadding.pad (caps C i) (RawCompare.input onset N i):=by
  fin_cases i
  · change install constantSlots _ _ (constantSlots 0)=_
    rw [install_slot _ (by decide)]
    exact (ZeroPadding.pad_zero _).symm
  · change install constantSlots _ _ 0=_
    rw [install_other _ _ _ _ (by decide)]
    rfl
  · change install constantSlots _ _ 3=_
    rw [install_other _ _ _ _ (by decide)]
    rfl
  · change install constantSlots _ _ 4=_
    rw [install_other _ _ _ _ (by decide)]
    rfl
  · change install constantSlots _ _ 5=_
    rw [install_other _ _ _ _ (by decide)]
    rfl
  · change install constantSlots _ _ 6=_
    rw [install_other _ _ _ _ (by decide)]
    rfl

theorem guard_run (onset C N : Nat) :
    ClockJoin.ReadyRun (machine onset) (6*onset+18) (input C N) (output onset C N):=by
  obtain ⟨r,hr,ht,hh,hs⟩:=RecoveryEraseConstant.constant_ready onset
  have hc:ClockJoin.ReadyRun (RecoveryEraseConstant.resetMachine onset) (2*onset+2)
      (fun _=>[]) ![List.replicate onset true,List.replicate onset false]:=
    ⟨r,hr,ht,hh,hs.le⟩
  have ha:=hc.focus constantSlots
    (by decide) (input C N) (by intro i;fin_cases i <;> rfl)
  have hr:=PCPPairReusable.padded_ready _ _ _ (RawCompare.compare_run onset N) (caps C)
  have hb:=hr.focus compareSlots (by decide) (middle onset C N) (compare_input onset C N)
  have h:=ClockJoin.join _ _ _ _ _ _ _ ha hb
  apply ClockJoin.enlarge _ _ _ _ _ h
  unfold RawCompare.budget
  have hm:=Nat.min_le_left onset N
  omega

theorem output_flag (onset C N : Nat) :
    output onset C N 5=[decide (onset≤N)]:=by
  change install compareSlots _ _ (compareSlots 4)=_
  rw [install_slot _ (by decide)]
  exact ZeroPadding.pad_zero _

theorem output_length (onset C N : Nat) :
    output onset C N 0=ZeroPadding.pad C (List.replicate N true):=by
  change install compareSlots _ _ (compareSlots 1)=_
  rw [install_slot _ (by decide)]
  rfl

end
end NearCubicWires.RepairSource.CloseoutSchedule.OnsetGuard
