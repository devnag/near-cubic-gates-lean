import Proof.Hierarchy.HierarchyReductionRetained
import Proof.PCP.ProjectionRawFrame

/-! Actual ordinary framing of the constructed hierarchy reduction word.
The length driver is produced by the same hierarchy execution. -/
namespace NearCubicWires.RepairSource.ProjectionNormalization.HierarchyFramedInput
open LocalBitMultitape RepairOrdinary RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def tapes (k : ℕ) := HierarchyReduction.tapes k+2
def old (k : ℕ) (i : Fin (HierarchyReduction.tapes k)) : Fin (tapes k) := i.castAdd 2
def fresh (k : ℕ) (i : Fin 2) : Fin (tapes k) := i.natAdd (HierarchyReduction.tapes k)
def frameSlots (k : ℕ) : Fin 4 → Fin (tapes k) :=
  ![old k (HierarchyReduction.extra k 13),old k (HierarchyReduction.extra k 9),fresh k 0,fresh k 1]
theorem old_injective (k : ℕ) : Function.Injective (old k) := by
  intro a b h; exact Fin.ext (congrArg (fun i : Fin (tapes k) => i.val) h)
theorem frame_injective (k : ℕ) : Function.Injective (frameSlots k) := by
  intro a b h; apply Fin.ext
  have hv := congrArg Fin.val h
  fin_cases a <;> fin_cases b <;>
    simp [frameSlots,old,fresh,HierarchyReduction.extra,HierarchyReduction.tapes] at hv ⊢

def input (k : ℕ) (x : List Bool) : Fin (tapes k) → List Bool := fun i => if i.val=2 then frame x else []
noncomputable def reductionProgram (k C Cpad : ℕ) (code : List Bool) :=
  RecoveryFocus.machine (old k) (HierarchyReduction.machine k C Cpad code)
noncomputable def frameProgram (k : ℕ) := RecoveryFocus.machine (frameSlots k) RawFrame.machine
noncomputable def machine (k C Cpad : ℕ) (code : List Bool) :=
  Composition.machine (reductionProgram k C Cpad code) (frameProgram k)
def budget (k C Cpad : ℕ) (code x : List Bool) := HierarchyReduction.ordinaryBudget k C Cpad code x+1+
  (4*(HierarchyPadding.rawInput k C Cpad code x).length+4)

theorem framed_run (k C Cpad : ℕ) (code x : List Bool) (hpad : k+3 ≤ Cpad) : ∃ out,
    ClockJoin.ReadyRun (machine k C Cpad code) (budget k C Cpad code x) (input k x) out ∧
      out (fresh k 0)=frame (HierarchyPadding.rawInput k C Cpad code x) ∧
      out (old k (HierarchyReduction.xTape k))=frame x := by
  obtain ⟨redOut,hr,hword,hfields,hlen⟩ := HierarchyReduction.retained_run k C Cpad code x hpad
  have hred := hr.focus (old k) (old_injective k) (input k x) (by intro i; rfl)
  let middle := install (old k) (input k x) redOut
  have hmword : middle (frameSlots k 0)=HierarchyPadding.rawInput k C Cpad code x := by
    change install (old k) (input k x) redOut (old k (HierarchyReduction.extra k 13))=_
    rw [install_slot _ (old_injective k)]
    exact hword
  have hmlen : middle (frameSlots k 1)=List.replicate (HierarchyPadding.rawInput k C Cpad code x).length true := by
    change install (old k) (input k x) redOut (old k (HierarchyReduction.extra k 9))=_
    rw [install_slot _ (old_injective k),hlen,HierarchyPadding.raw_length k C Cpad code x hpad]
    rfl
  have hmblank (i : Fin 2) : middle (fresh k i)=[] := by
    dsimp only [middle]
    rw [install_other _ _ _ _ (by
      intro j hj; have hv := congrArg Fin.val hj
      dsimp [old,fresh] at hv; omega)]
    have ht : 3 ≤ HierarchyReduction.tapes k := by
      have h := HierarchyReduction.base_lower k
      dsimp [HierarchyReduction.tapes]; omega
    simp [input,fresh,show HierarchyReduction.tapes k+i.val≠2 by omega]
  have hframe := (RawFrame.ready (HierarchyPadding.rawInput k C Cpad code x)).focus
    (frameSlots k) (frame_injective k) middle (by
      intro i; fin_cases i
      · exact hmword
      · exact hmlen
      · exact hmblank 0
      · exact hmblank 1)
  refine ⟨_,ClockJoin.join _ _ _ _ _ _ _ hred hframe,?_,?_⟩
  · change install (frameSlots k) middle _ (frameSlots k 2)=_
    rw [install_slot _ (frame_injective k)]
    rfl
  · rw [install_other _ _ _ _ (by
      intro i hi; have hv := congrArg Fin.val hi
      have hbase := HierarchyReduction.base_lower k
      fin_cases i <;> simp [frameSlots,old,fresh,HierarchyReduction.xTape,HierarchyReduction.low,
        HierarchyFromInput.field,HierarchyReduction.extra,HierarchyReduction.tapes] at hv)]
    change install (old k) (input k x) redOut (old k (HierarchyReduction.xTape k))=_
    rw [install_slot _ (old_injective k)]
    exact hfields.1

end NearCubicWires.RepairSource.ProjectionNormalization.HierarchyFramedInput
