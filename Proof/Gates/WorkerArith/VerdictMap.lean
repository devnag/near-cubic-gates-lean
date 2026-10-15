import Proof.Gates.WorkerArith.WeakWorkerDefs
import Proof.Gates.WorkerArith.VerdictMain

set_option autoImplicit false

namespace NearCubicGates.Close.WorkerArith.WorkerBounds

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.SourceInterfaces NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutLanguage
open NearCubicGates.PublishedSources.PCPP NearCubicGates.Close.Gadget NearCubicGates.Close.Transfer
open NearCubicGates.Close NearCubicGates.Close.WordPrograms NearCubicGates.Close.CheckedPCPP NearCubicGates.Close.Interfaces
open NearCubicGates.Close.Setup NearCubicGates.Close.WorkerArith.WeakWorker

noncomputable section

variable {s : GateSources} {P : ThreeQueryPCPP} {g : GateParams} (D : SetupData s P g)

/-- The first stream past the composite's block (the counter block starts here). -/
def tailBase : ℕ := 16 + D.tA + D.cf.t

theorem nsW_eq : nsW D + 1 = tailBase D + D.tc + 46 := by unfold nsW tailBase; omega

theorem fifteen_le : 15 ≤ nsW D := by unfold nsW; omega

/-- The spare streams `5, 6, 7, 8, 10, …, 15` (index `k < 10`). -/
def spareIdx (k : ℕ) : ℕ := if k < 4 then 5 + k else 6 + k

/-- The stream of tape `j`. -/
def vmapIdx (j : ℕ) : ℕ := if j = 0 then 4 else if j ≤ 10 then spareIdx (j - 1) else tailBase D + (j - 11)

theorem vmapIdx_lt (t : ℕ) (hroom : tailBase D + t ≤ nsW D + 12) (j : ℕ) (hj : j < t) :
    vmapIdx D j < nsW D + 1 := by
  have := fifteen_le D
  unfold vmapIdx spareIdx
  split_ifs <;> omega

/-- **The map of a `t`-tape machine's tapes onto the worker's streams.** -/
def vmapOf (t : ℕ) (hroom : tailBase D + t ≤ nsW D + 12) : Fin t → Fin (nsW D + 1) :=
  fun j => ⟨vmapIdx D j.val, vmapIdx_lt D t hroom j.val j.isLt⟩

theorem tailBase_ge : 16 ≤ tailBase D := by unfold tailBase; omega

theorem vmapIdx_inj {a b : ℕ} (h : vmapIdx D a = vmapIdx D b) : a = b := by
  have := tailBase_ge D
  unfold vmapIdx spareIdx at h
  split_ifs at h <;> omega

variable (t : ℕ) (hroom : tailBase D + t ≤ nsW D + 12)

theorem vmapOf_val (j : Fin t) : (vmapOf D t hroom j).val = vmapIdx D j.val := rfl

theorem vmapOf_inj : Function.Injective (vmapOf D t hroom) := by
  intro a b h
  exact Fin.ext (vmapIdx_inj D (congrArg Fin.val h))

theorem vmapOf_zero (j : Fin t) (hj : j.val = 0) : vmapOf D t hroom j = sVI D := by
  apply Fin.ext
  rw [vmapOf_val, hj]
  rfl

theorem vmapOf_ne_L (j : Fin t) : vmapOf D t hroom j ≠ sL D := by
  intro h
  have h1 := congrArg Fin.val h
  rw [vmapOf_val] at h1
  have h2 : (sL D).val = 9 := rfl
  have := tailBase_ge D
  rw [h2] at h1
  unfold vmapIdx spareIdx at h1
  split_ifs at h1 <;> omega

theorem vmapOf_blank (j : Fin t) (hj : j.val ≠ 0) : BlankAtExit D (vmapOf D t hroom j) := by
  unfold BlankAtExit
  have hv := vmapOf_val D t hroom j
  have hL := vmapOf_ne_L D t hroom j
  by_cases h10 : j.val ≤ 10
  · left
    have e : vmapIdx D j.val = spareIdx (j.val - 1) := by unfold vmapIdx; rw [if_neg hj, if_pos h10]
    rw [hv, e]
    unfold spareIdx
    refine ⟨?_, ?_, hL⟩ <;> split_ifs <;> omega
  · right
    have e : vmapIdx D j.val = tailBase D + (j.val - 11) := by unfold vmapIdx; rw [if_neg hj, if_neg h10]
    rw [hv, e]
    unfold tailBase
    omega

/-- **The facts `WeakWorker.WeakWorkerOf` asks of `vmap`**, for any verdict machine with room. -/
theorem vmap_ok {γ εT : ℚ} (vm : Worker.VerdictMachine γ εT)
    (h : tailBase D + vm.wf.program.tapeCount ≤ nsW D + 12) :
    Function.Injective (vmapOf D _ h) ∧ vmapOf D _ h (inTape vm.wf.program) = sVI D ∧
      (∀ j, vmapOf D _ h j ≠ sL D) ∧
      (∀ j, j ≠ inTape vm.wf.program → BlankAtExit D (vmapOf D _ h j)) := by
  refine ⟨vmapOf_inj D _ h, vmapOf_zero D _ h _ rfl, vmapOf_ne_L D _ h, fun j hj => vmapOf_blank D _ h j ?_⟩
  intro h0
  exact hj (Fin.ext h0)

theorem verdictMachine_tapes (γ εT : ℚ) : (verdictMachine γ εT).wf.program.tapeCount = 47 := rfl

theorem room_iff (t : ℕ) : tailBase D + t ≤ nsW D + 12 ↔ t ≤ D.tc + 57 := by
  have := nsW_eq D
  omega

theorem verdict_room (γ εT : ℚ) :
    tailBase D + (verdictMachine γ εT).wf.program.tapeCount ≤ nsW D + 12 := by
  rw [verdictMachine_tapes, room_iff]
  omega

end

end NearCubicGates.Close.WorkerArith.WorkerBounds
