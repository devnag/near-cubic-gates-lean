import Proof.MachineModel.OrdinaryMatrixBatchRankReverseBounds

/-! The actual cold key-scanner bank is allocated by the retained paid D
counter. Native H/B/M fields and the Buckets sentinel remain untouched. -/
namespace NearCubicWires.RepairOrdinary.MatrixBucketWorkspace
open LocalBitMultitape RecoveryRootRound SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def clearSlots : Fin 30 → Fin 34 := ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,28,29,30,31,32,23,33]
theorem clear_injective : Function.Injective clearSlots := by decide
def clearPick : Fin 34 → Option (Fin 30) := ![some 0,some 1,some 2,some 3,some 4,some 5,some 6,some 7,some 8,some 9,some 10,some 11,some 12,some 13,some 14,some 15,some 16,some 17,some 18,some 19,some 20,some 21,some 22,some 28,none,none,none,none,some 23,some 24,some 25,some 26,some 27,some 29]
theorem pick_clear (i : Fin 34) : RecoveryFocus.pick clearSlots i=clearPick i := by
  fin_cases i
  all_goals first
    | decide
    | exact RecoveryFocus.pick_slot clearSlots clear_injective 0
    | exact RecoveryFocus.pick_slot clearSlots clear_injective 1
    | exact RecoveryFocus.pick_slot clearSlots clear_injective 2
    | exact RecoveryFocus.pick_slot clearSlots clear_injective 3
    | exact RecoveryFocus.pick_slot clearSlots clear_injective 4
    | exact RecoveryFocus.pick_slot clearSlots clear_injective 5
    | exact RecoveryFocus.pick_slot clearSlots clear_injective 6
    | exact RecoveryFocus.pick_slot clearSlots clear_injective 7
    | exact RecoveryFocus.pick_slot clearSlots clear_injective 8
    | exact RecoveryFocus.pick_slot clearSlots clear_injective 9
    | exact RecoveryFocus.pick_slot clearSlots clear_injective 10
    | exact RecoveryFocus.pick_slot clearSlots clear_injective 11
    | exact RecoveryFocus.pick_slot clearSlots clear_injective 12
    | exact RecoveryFocus.pick_slot clearSlots clear_injective 13
    | exact RecoveryFocus.pick_slot clearSlots clear_injective 14
    | exact RecoveryFocus.pick_slot clearSlots clear_injective 15
    | exact RecoveryFocus.pick_slot clearSlots clear_injective 16
    | exact RecoveryFocus.pick_slot clearSlots clear_injective 17
    | exact RecoveryFocus.pick_slot clearSlots clear_injective 18
    | exact RecoveryFocus.pick_slot clearSlots clear_injective 19
    | exact RecoveryFocus.pick_slot clearSlots clear_injective 20
    | exact RecoveryFocus.pick_slot clearSlots clear_injective 21
    | exact RecoveryFocus.pick_slot clearSlots clear_injective 22
    | exact RecoveryFocus.pick_slot clearSlots clear_injective 23
    | exact RecoveryFocus.pick_slot clearSlots clear_injective 24
    | exact RecoveryFocus.pick_slot clearSlots clear_injective 25
    | exact RecoveryFocus.pick_slot clearSlots clear_injective 26
    | exact RecoveryFocus.pick_slot clearSlots clear_injective 27
    | exact RecoveryFocus.pick_slot clearSlots clear_injective 28
    | exact RecoveryFocus.pick_slot clearSlots clear_injective 29
noncomputable def machine := RecoveryFocus.machine clearSlots (RecoveryScratchErase.resetMachine 28)
def input (D H M B count : ℕ) : Fin 34 → List Bool := fun i =>
  if i=23 then List.replicate D true else if i=24 then frame (binary H 0)
  else if i=25 then frame (binary H B) else if i=26 then frame (binary M 0)
  else if i=27 then UnaryTemplate.tape count else []
def output (D H M B count : ℕ) : Fin 34 → List Bool := fun i =>
  if i=23 then List.replicate D true else if i=24 then frame (binary H 0)
  else if i=25 then frame (binary H B) else if i=26 then frame (binary M 0)
  else if i=27 then UnaryTemplate.tape count else List.replicate (if i=33 then D+1 else D) false

theorem workspace_ready (D H M B count : ℕ) :
    ReadyRun machine (2*D+4) (input D H M B count) (output D H M B count) := by
  have base := RecoveryScratchErase.erase_ready D 0 (fun _ : Fin 28 => []) (by intro i; simp)
  have focused := base.focus clearSlots clear_injective (input D H M B count) (by
    intro i; fin_cases i <;> rfl)
  have he : install clearSlots (input D H M B count)
      (Fin.addCases (m := 29) (n := 1) (motive := fun _ => List Bool)
        (Fin.addCases (m := 28) (n := 1) (motive := fun _ => List Bool)
          (fun _ => List.replicate D false) (fun _ => List.replicate D true))
        (fun _ => List.replicate (max 0 (D+1)) false))=output D H M B count := by
    funext i
    fin_cases i <;> simp [install,pick_clear,clearPick,input,output,Fin.addCases]
  rw [he] at focused
  exact focused

end NearCubicWires.RepairOrdinary.MatrixBucketWorkspace
