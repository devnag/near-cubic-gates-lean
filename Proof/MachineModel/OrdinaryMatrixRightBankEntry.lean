import Proof.MachineModel.OrdinaryMatrixRightNativeCall

/-! Allocate the new right output and two reusable right scratch tapes,
clear the old inner coordinate, and physically copy the retained M-zero.
The original rank/key bank is otherwise retained by the enclosing focus. -/
namespace NearCubicWires.RepairOrdinary.MatrixRightBankEntry
open LocalBitMultitape RecoveryRootRound MatrixScoreBatch MatrixScoreWeight
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def clearSlots : Fin 6 → Fin 9 := ![0,1,2,3,4,5]
def copySlots : Fin 4 → Fin 9 := ![6,3,7,8]
theorem clear_injective : Function.Injective clearSlots := by decide
theorem copy_injective : Function.Injective copySlots := by decide
def clearPick : Fin 9 → Option (Fin 6) := ![some 0,some 1,some 2,some 3,some 4,some 5,none,none,none]
def copyPick : Fin 9 → Option (Fin 4) := ![none,none,none,some 1,none,none,some 0,some 2,some 3]
theorem pick_clear (i : Fin 9) : RecoveryFocus.pick clearSlots i=clearPick i := by
  fin_cases i
  all_goals first
    | decide
    | exact RecoveryFocus.pick_slot clearSlots clear_injective 0
    | exact RecoveryFocus.pick_slot clearSlots clear_injective 1
    | exact RecoveryFocus.pick_slot clearSlots clear_injective 2
    | exact RecoveryFocus.pick_slot clearSlots clear_injective 3
    | exact RecoveryFocus.pick_slot clearSlots clear_injective 4
    | exact RecoveryFocus.pick_slot clearSlots clear_injective 5
theorem pick_copy (i : Fin 9) : RecoveryFocus.pick copySlots i=copyPick i := by
  fin_cases i
  all_goals first
    | decide
    | exact RecoveryFocus.pick_slot copySlots copy_injective 0
    | exact RecoveryFocus.pick_slot copySlots copy_injective 1
    | exact RecoveryFocus.pick_slot copySlots copy_injective 2
    | exact RecoveryFocus.pick_slot copySlots copy_injective 3
noncomputable def first := RecoveryFocus.machine clearSlots (RecoveryScratchErase.resetMachine 4)
noncomputable def last := RecoveryFocus.machine copySlots copyMachine
noncomputable def machine := Composition.machine first last
def input (r : Request) (inner : ℕ) : Fin 9 → List Bool :=
  ![[],[],[],scalar (MatrixScoreReusableRanks.D r) r.M inner,List.replicate (MatrixScoreReusableRanks.D r) true,
    zeros (MatrixScoreReusableRanks.D r+1),frame (SignedSortKey.binary r.M 0),
    zeros (MatrixScoreReusableRanks.D r),zeros (MatrixScoreReusableRanks.D r)]
def cleared (r : Request) : Fin 9 → List Bool :=
  ![zeros (MatrixScoreReusableRanks.D r),zeros (MatrixScoreReusableRanks.D r),zeros (MatrixScoreReusableRanks.D r),
    zeros (MatrixScoreReusableRanks.D r),List.replicate (MatrixScoreReusableRanks.D r) true,
    zeros (MatrixScoreReusableRanks.D r+1),frame (SignedSortKey.binary r.M 0),
    zeros (MatrixScoreReusableRanks.D r),zeros (MatrixScoreReusableRanks.D r)]
def output (r : Request) : Fin 9 → List Bool :=
  Function.update (cleared r) 3 (scalar (MatrixScoreReusableRanks.D r) r.M 0)
def budget (r : Request) := 2*MatrixScoreReusableRanks.D r+8*r.M+13

theorem entry_ready (r : Request) (inner : ℕ) : ClockJoin.ReadyRun machine (budget r) (input r inner) (output r) := by
  let D := MatrixScoreReusableRanks.D r
  have hM : 4*r.M+3≤D := (MatrixBatchBucketBankFields.capacity_fit r).2
  let backing : Fin 4 → List Bool := ![[],[],[],scalar D r.M inner]
  have hb : ∀ i,(backing i).length≤D := by
    intro i
    fin_cases i <;> simp [backing,scalar,ZeroPadding.pad_length]
    omega
  have erase := RecoveryScratchErase.erase_ready D (D+1) backing hb
  have erased := erase.focus clearSlots clear_injective (input r inner) (by
    intro i; fin_cases i <;> rfl)
  have he : install clearSlots (input r inner)
      (Fin.addCases (m := 5) (n := 1) (motive := fun _ => List Bool)
        (Fin.addCases (m := 4) (n := 1) (motive := fun _ => List Bool)
          (fun _ => zeros D) (fun _ => List.replicate D true))
        (fun _ => zeros (max (D+1) (D+1))))=cleared r := by
    funext i
    fin_cases i <;> simp [install,pick_clear,clearPick,input,cleared,Fin.addCases]
    all_goals rfl
  have erasedLe : ClockJoin.ReadyRun first (2*D+4) (input r inner) (cleared r) := by
    obtain ⟨actual,ha,atapes,ah,as⟩ := erased
    exact ⟨actual,ha,atapes.trans he,ah,as.le⟩
  have copy := MatrixScoreInitialize.native_copy D r.M 0 hM
  have copied := copy.focus copySlots copy_injective (cleared r) (by
    intro i; fin_cases i <;> rfl)
  have hc : install copySlots (cleared r)
      (![frame (SignedSortKey.binary r.M 0),scalar D r.M 0,zeros D,zeros D] : Fin 4 → List Bool)=output r := by
    funext i
    fin_cases i <;> simp [install,pick_copy,copyPick,cleared,output]
    all_goals rfl
  have copiedLe : ClockJoin.ReadyRun last (8*r.M+8) (cleared r) (output r) := by
    obtain ⟨actual,ha,atapes,ah,as⟩ := copied
    exact ⟨actual,ha,atapes.trans hc,ah,as.le⟩
  have joined := ClockJoin.join first last (2*D+4) (8*r.M+8) _ _ _ erasedLe copiedLe
  have ht : (2*D+4)+1+(8*r.M+8)=budget r := by unfold budget; dsimp [D]; omega
  rw [ht] at joined
  exact joined

end NearCubicWires.RepairOrdinary.MatrixRightBankEntry
