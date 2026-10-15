import Proof.CaseAnalysis.RecoveryUnaryReuseOriginal

/-! Preserve the second child result, return to the first shared field,
advance the graph count, and physically initialize the constant value to1. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedConstantPrep
open LocalBitMultitape RepairRepresentation RecoveryRootRound RecoveryChildSelection
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 2→Fin 9:=![5,6]
noncomputable def last:=RecoveryFocus.machine slots RepairSource.RecoveryTseitinRawIncrement.machine
noncomputable def machine:=Composition.machine RecoveryBoundedSelectorHandoff.machine last
def output (acc next C : ℕ) : Fin 9→List Bool:=
  ![List.replicate (acc+1) true,ZeroPadding.pad C (List.replicate acc true),List.replicate next true,
    ZeroPadding.pad C (List.replicate next true),ZeroPadding.pad C (List.replicate next true),
    ZeroPadding.pad C [true],List.replicate C false,List.replicate C true,List.replicate (C+1) false]

theorem last_ready (acc index next value C : ℕ) (hC : 1 ≤ C) :
    ReadyRun last 4 (RecoveryBoundedSelectorHandoff.data acc index next value C 5) (output acc next C) := by
  have hp:=RecoveryChildSelection.ReadyRun.pad
    (RepairSource.RecoveryTseitinRawIncrement.increment_ready 0 C hC) (![C,0] : Fin 2→ℕ)
  have h : ReadyRun RepairSource.RecoveryTseitinRawIncrement.machine 4
      ![List.replicate C false,List.replicate C false]
      ![ZeroPadding.pad C [true],List.replicate C false] := by
    convert hp using 1 <;> funext i <;> fin_cases i
    all_goals first | rfl | (exact ZeroPadding.pad_zero _) | (exact (ZeroPadding.pad_zero _).symm)
  have hf:=h.focus slots (by decide) (RecoveryBoundedSelectorHandoff.data acc index next value C 5)
    (by intro j; fin_cases j <;> rfl)
  have he : install slots (RecoveryBoundedSelectorHandoff.data acc index next value C 5)
      ![ZeroPadding.pad C [true],List.replicate C false]=output acc next C := by
    apply HierarchyWidth.install_eq slots (by decide)
    · intro j; fin_cases j <;> rfl
    · intro i hi
      fin_cases i
      all_goals first | exact False.elim (hi 0 rfl) | rfl
  rw [he] at hf
  exact hf

theorem prepare_ready (acc index next value C : ℕ)
    (ha : acc+1 ≤ C) (hi : index ≤ C) (hn : next+1 ≤ C) (hv : value ≤ C) :
    ReadyRun machine (2*C+4*acc+4*next+29)
      (RecoveryBoundedSelectorHandoff.data acc index next value C 0) (output acc next C) := by
  have h:=HierarchyMultiplyEntry.join_exact RecoveryBoundedSelectorHandoff.machine last _ _ _ _ _
    (RecoveryBoundedSelectorHandoff.handoff_ready acc index next value C ha hi hn hv)
    (last_ready acc index next value C (by omega))
  have he : (2*C+4*acc+4*next+24)+1+4=2*C+4*acc+4*next+29 := by omega
  simpa only [machine,he] using h

end NearCubicWires.RepairOrdinary.RecoveryBoundedConstantPrep
