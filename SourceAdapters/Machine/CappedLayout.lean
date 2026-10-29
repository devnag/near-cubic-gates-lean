import SourceAdapters.Machine.CappedPreparedClock
import Proof.Amplification.RecoveryFocusDock

/-! `app:sources`, "Uniform three-query PCPP and code interfaces", and the proof of `lem:multitape-refuter`: fixed finite tape wiring for the exact capped word algorithm. -/
namespace NearCubicGates.Adapters.Machine.Capped.Layout
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
set_option autoImplicit false

def tapes (p : Program) : ℕ := 8+(p.tapeCount+6)

def preparedSlot (p : Program) (i : Fin (p.tapeCount+1+1+1+1)) : Fin (tapes p) :=
  ⟨if i.val=0 then 1 else if i.val=p.tapeCount then 2 else if i.val=p.tapeCount+2 then 3 else 8+i.val,
    by have := i.isLt; unfold tapes; split_ifs <;> omega⟩

def outputSlot (p : Program) : Fin (tapes p) := ⟨8+(p.tapeCount+4),by unfold tapes; omega⟩
def originSlot (p : Program) : Fin (tapes p) := ⟨8+(p.tapeCount+5),by unfold tapes; omega⟩

theorem preparedSlot_injective (p : Program) : Function.Injective (preparedSlot p) := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  simp only [preparedSlot] at hv
  split_ifs at hv <;> omega

theorem outputSlot_fresh (p : Program) (i : Fin (p.tapeCount+1+1+1+1)) :
    preparedSlot p i ≠ outputSlot p := by
  intro h
  have hv := congrArg Fin.val h
  have hi := i.isLt
  simp only [preparedSlot,outputSlot] at hv
  split_ifs at hv <;> omega

theorem originSlot_fresh (p : Program) (i : Fin (p.tapeCount+1+1+1+1)) :
    preparedSlot p i ≠ originSlot p := by
  intro h
  have hv := congrArg Fin.val h
  have hi := i.isLt
  simp only [preparedSlot,originSlot] at hv
  split_ifs at hv <;> omega

theorem request_slots : RequestLoader.requestSlot 1=1 ∧
    RequestLoader.requestSlot 2=2 ∧ RequestLoader.requestSlot 3=3 := by decide

noncomputable def prepared (p : Program) := RecoveryFocus.machine (preparedSlot p) (preparedMachine p)
def loader (p : Program) := TapeEmbedding.machine (p.tapeCount+6) RequestLoader.requestMachine

def resultSlot (p : Program) (i : Fin 6) : Fin (tapes p) :=
  ![preparedSlot p (preparedOutputSlot p),outputSlot p,originSlot p,
    preparedSlot p (preparedMarkerSlot p),preparedSlot p (preparedClockSlot p),
    preparedSlot p (preparedStatusSlot p)] i

end NearCubicGates.Adapters.Machine.Capped.Layout
