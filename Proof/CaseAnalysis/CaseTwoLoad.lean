import Proof.CaseAnalysis.RowsMetadataCopy
import Proof.Hierarchy.HierarchyAllocation

/-! A paid bounded copy changes exactly its destination in an initialized
bank. The source, actual unary driver and reset log are retained. -/
namespace NearCubicWires.RepairOrdinary.CloseoutCaseTwo.Cold
open LocalBitMultitape RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem load_ready {t : ℕ} (slots : Fin 4→Fin t) (hinj : Function.Injective slots)
    (C : ℕ) (word : List Bool) (A : Fin t→List Bool) (hc : word.length≤C)
    (hi : ∀ j,A (slots j)=CloseoutRowsMetadataCopy.input word C j) :
    ClockJoin.ReadyRun (RecoveryFocus.machine slots RecoveryBoundedTapeCopy.machine) (2*C+4) A
      (Function.update A (slots 1) (ZeroPadding.pad C word)):=by
  obtain ⟨r,hr,ht,hh,hs⟩:=CloseoutRowsMetadataCopy.copy_ready word C hc
  have ready : ClockJoin.ReadyRun RecoveryBoundedTapeCopy.machine (2*C+4)
      (CloseoutRowsMetadataCopy.input word C) (CloseoutRowsMetadataCopy.output word C):=⟨r,hr,ht,hh,hs.le⟩
  have h:=ready.focus slots hinj A hi
  have he : install slots A (CloseoutRowsMetadataCopy.output word C)=Function.update A (slots 1) (ZeroPadding.pad C word):=by
    apply HierarchyAllocation.install_eq slots hinj
    · intro j
      by_cases hj : j=1
      · subst j;rw [Function.update_self];rfl
      · rw [Function.update_of_ne (fun he=>hj (hinj he)),hi]
        fin_cases j <;> first | contradiction | rfl
    · intro i hout
      exact Function.update_of_ne (fun he=>hout 1 he.symm) _ _
  rw [he] at h
  exact h

end NearCubicWires.RepairOrdinary.CloseoutCaseTwo.Cold
