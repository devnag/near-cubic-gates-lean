import Proof.CaseAnalysis.ScheduleOnsetGuard
import Proof.CaseAnalysis.ScheduleFramed

/-! The common program's cold schedule, fixed onset test and ordinary refuter
request share the actual selected-length tape and retain the original address.
Only nine initially blank tapes are added to the accepted schedule. -/
namespace NearCubicWires.RepairSource.CloseoutSchedule.Guarded
open LocalBitMultitape RepairOrdinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def tapes (w : Nat):=Cold.tapes w+9
def old (w : Nat) (i : Fin (Cold.tapes w)) : Fin (tapes w):=i.castAdd 9
def fresh (w : Nat) (i : Fin 9) : Fin (tapes w):=i.natAdd (Cold.tapes w)
def guardSlots (w : Nat) : Fin 7→Fin (tapes w):=
  ![old w (Cold.port w 2),fresh w 0,fresh w 1,fresh w 2,fresh w 3,fresh w 4,fresh w 5]
def frameSlots (w : Nat) : Fin 4→Fin (tapes w):=
  ![old w (Cold.port w 2),fresh w 6,fresh w 7,fresh w 8]
def input (w : Nat) (bits : List Bool) : Fin (tapes w)→List Bool:=
  Fin.addCases (Cold.input w bits) (fun _ : Fin 9=>[])

theorem old_injective (w : Nat) : Function.Injective (old w):=by
  intro a b h
  exact Fin.ext (congrArg (fun i : Fin (tapes w)=>i.val) h)
theorem old_fresh (w : Nat) (i : Fin (Cold.tapes w)) (j : Fin 9) : old w i≠fresh w j:=by
  intro h
  have hv:=congrArg Fin.val h
  have hi:=i.isLt
  change i.val=Cold.tapes w+j.val at hv
  omega
theorem guard_injective (w : Nat) : Function.Injective (guardSlots w):=by
  intro a b h
  have hv:=congrArg Fin.val h
  fin_cases a <;> fin_cases b <;>
    simp [guardSlots,old,fresh,Cold.port,Cold.core,Cold.tapes] at hv ⊢
  omega
theorem frame_injective (w : Nat) : Function.Injective (frameSlots w):=by
  intro a b h
  have hv:=congrArg Fin.val h
  fin_cases a <;> fin_cases b <;>
    simp [frameSlots,old,fresh,Cold.port,Cold.core,Cold.tapes] at hv ⊢
theorem guard_source (w : Nat) (i : Fin 7) : guardSlots w i≠old w (Cold.extra w 0):=by
  intro h
  have hv:=congrArg Fin.val h
  fin_cases i <;> simp [guardSlots,old,fresh,Cold.port,Cold.core,Cold.extra,Cold.tapes] at hv
theorem frame_source (w : Nat) (i : Fin 4) : frameSlots w i≠old w (Cold.extra w 0):=by
  intro h
  have hv:=congrArg Fin.val h
  fin_cases i <;> simp [frameSlots,old,fresh,Cold.port,Cold.core,Cold.extra,Cold.tapes] at hv
  omega
theorem frame_flag (w : Nat) (i : Fin 4) : frameSlots w i≠fresh w 4:=by
  intro h
  have hv:=congrArg Fin.val h
  fin_cases i <;> simp [frameSlots,old,fresh,Cold.port,Cold.core,Cold.tapes] at hv
theorem guard_unused (w : Nat) (i : Fin 7) (j : Fin 9) (hj : 6≤j.val) :
    guardSlots w i≠fresh w j:=by
  intro h
  have hv:=congrArg Fin.val h
  fin_cases i <;> simp [guardSlots,old,fresh,Cold.port,Cold.core,Cold.tapes] at hv <;> omega

def first {w states : Nat} (p : Machine (Cold.tapes w) states):=RecoveryFocus.machine (old w) p
def guard (w onset : Nat):=RecoveryFocus.machine (guardSlots w) (OnsetGuard.machine onset)
def framePhase (w : Nat):=RecoveryFocus.machine (frameSlots w) Output.machine
def guardedPrefix {w states : Nat} (p : Machine (Cold.tapes w) states) (onset : Nat):=
  Composition.machine (first p) (guard w onset)
def machine {w states : Nat} (p : Machine (Cold.tapes w) states) (onset : Nat):=
  Composition.machine (guardedPrefix p onset) (framePhase w)

end
end NearCubicWires.RepairSource.CloseoutSchedule.Guarded
