import Proof.Gates.GateRecovery.Proof.CaseAnalysis.ScheduleDock

namespace GR

/-! Shared cold schedule wiring: the actual C producer feeds the sweep
driver directly; metadata shares only the retained framed language input. -/
namespace NearCubicWires.RepairSource.CloseoutSchedule.Cold
open LocalBitMultitape RepairOrdinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def tapes (w : Nat) := w+6+30
def core (w : Nat) (i : Fin (w+6)) : Fin (tapes w) := i.castAdd 30
def port (w : Nat) (i : Fin 6) : Fin (tapes w) := core w (i.natAdd w)
def extra (w : Nat) (i : Fin 30) : Fin (tapes w) := i.natAdd (w+6)
def capacitySlots (w : Nat) (i : Fin 26) : Fin (tapes w) :=
  if i.val=24 then port w 3 else extra w (i.castAdd 4)
def metadataSlots (w : Nat) : Fin 8 → Fin (tapes w) :=
  ![extra w 0,port w 5,extra w 26,extra w 27,port w 1,extra w 28,port w 0,extra w 29]
def clearSlots (w : Nat) (i : Fin (w+3)) : Fin (tapes w) :=
  ⟨if i.val < w then i.val else i.val+2,by have := i.isLt; dsimp [tapes]; split_ifs <;> omega⟩

theorem core_injective (w : Nat) : Function.Injective (core w) := by
  intro a b h
  exact Fin.ext (congrArg (fun i : Fin (tapes w) => i.val) h)
theorem capacity_injective (w : Nat) : Function.Injective (capacitySlots w) := by
  intro a b h
  have hv := congrArg Fin.val h
  apply Fin.ext
  by_cases ha : a.val=24 <;> by_cases hb : b.val=24 <;>
    simp [capacitySlots,ha,hb,port,core,extra] at hv <;> omega
theorem metadata_injective (w : Nat) : Function.Injective (metadataSlots w) := by
  intro a b h
  have hv := congrArg Fin.val h
  fin_cases a <;> fin_cases b <;> simp [metadataSlots,port,core,extra] at hv ⊢ <;> omega
theorem clear_injective (w : Nat) : Function.Injective (clearSlots w) := by
  intro a b h
  have hv := congrArg Fin.val h
  apply Fin.ext
  dsimp only [clearSlots] at hv
  split_ifs at hv <;> omega

theorem clear_work (w : Nat) (i : Fin w) : clearSlots w (i.castAdd 3) = core w (i.castAdd 6) := by
  apply Fin.ext
  simp [clearSlots,core,i.isLt]
theorem clear_port (w : Nat) (i : Fin 3) : clearSlots w (i.natAdd w) =
    port w ⟨i.val+2,by have := i.isLt; omega⟩ := by
  apply Fin.ext
  simp [clearSlots,port,core]
  omega
theorem core_extra (w : Nat) (i : Fin (w+6)) (j : Fin 30) : core w i ≠ extra w j := by
  intro h
  have hv := congrArg Fin.val h
  have := i.isLt
  change i.val = w+6+j.val at hv
  omega
theorem work_capacity (w : Nat) (i : Fin w) (j : Fin 26) :
    capacitySlots w j ≠ core w (i.castAdd 6) := by
  intro h
  have hv := congrArg Fin.val h
  have := i.isLt
  by_cases hj : j.val=24 <;> simp [capacitySlots,hj,port,core,extra] at hv <;> omega
theorem work_metadata (w : Nat) (i : Fin w) (j : Fin 8) :
    metadataSlots w j ≠ core w (i.castAdd 6) := by
  intro h
  have hv := congrArg Fin.val h
  have := i.isLt
  fin_cases j <;> simp [metadataSlots,port,core,extra] at hv <;> omega

end
end NearCubicWires.RepairSource.CloseoutSchedule.Cold

end GR
