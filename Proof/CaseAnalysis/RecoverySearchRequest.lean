import Proof.CaseAnalysis.RecoverySearchArityFrame
import Proof.Amplification.RecoveryPCPFormulaResumeSearchPairFrame

/-! The actual serialized payload and retained unary description arity
produce the exact external request of the unchanged canonical prefix search. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedSearchRequest
open LocalBitMultitape RecoveryRootRound
open RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def aritySlots : Fin 4→Fin 12:=![1,2,3,4]
def pairSlots : Fin 9→Fin 12:=![0,4,5,6,7,8,9,10,11]
noncomputable def first:=RecoveryFocus.machine aritySlots RecoveryBoundedSearchArityFrame.machine
noncomputable def last:=RecoveryFocus.machine pairSlots RepairSource.RecoveryPCPFormulaResumeSearchPair.framedMachine
noncomputable def machine:=Composition.machine first last
def input (payload total B : ℕ) (i : Fin 12) : List Bool:=
  if i=0 then frame payload.bits else if i=1 then ZeroPadding.pad B (List.replicate total true) else []
noncomputable def middle (payload total B : ℕ):=
  install aritySlots (input payload total B) (RecoveryBoundedSearchArityFrame.output total B)
def budget (payload total : ℕ):=6*total+15+1+
  RepairSource.RecoveryPCPFormulaResumeSearchPair.framedBudget payload.bits (List.replicate total true)

theorem pair_input (payload total B : ℕ) (i : Fin 9) :
    middle payload total B (pairSlots i)=
      RepairSource.RecoveryPCPFormulaResumeSearchPair.fields payload.bits (List.replicate total true) i := by
  fin_cases i
  all_goals first
    | exact install_slot aritySlots (by decide) _ _ 3
    | (rw [middle,install_other _ _ _ _ (by decide)];rfl)

theorem ready (payload total B : ℕ) : ∃ out,
    ClockJoin.ReadyRun machine (budget payload total) (input payload total B) out ∧
      out 10=frame (RepairSource.RecoveryPrefixMeasure.request payload total) ∧
      out 1=ZeroPadding.pad B (List.replicate total true) := by
  have a:=(RecoveryBoundedSearchArityFrame.ready total B).focus aritySlots (by decide)
    (input payload total B) (by intro i;fin_cases i <;> rfl)
  obtain ⟨localOut,hb,hout⟩:=RepairSource.RecoveryPCPFormulaResumeSearchPair.framed_ready
    payload.bits (List.replicate total true)
  have b:=hb.focus pairSlots (by decide) (middle payload total B) (pair_input payload total B)
  have h:=ClockJoin.join first last _ _ _ _ _ a b
  refine ⟨_,h,?_,?_⟩
  · exact (install_slot pairSlots (by decide) _ _ 7).trans hout
  · rw [install_other _ _ _ _ (by decide)]
    exact install_slot aritySlots (by decide) _ _ 0

end NearCubicWires.RepairOrdinary.RecoveryBoundedSearchRequest
