import Proof.CaseAnalysis.CaseTwoConverter
import Proof.CaseAnalysis.CaseTwoHierarchyFrame

/-! Pay canonical conversion and hierarchy framing once. These two retained
frames are the fixed-copy worker's real inputs; each block pays its own
compound copy, source/cache, honest evaluation and clearing. -/
namespace NearCubicWires.RepairOrdinary.CloseoutCaseTwo.PreparedFrames
open LocalBitMultitape RepairRepresentation OuterPCPRecovery RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def oldSlots (i : Fin 135) : Fin 140:=i.castAdd 5
def frameSlots (i : Fin 6) : Fin 140:=if i=0 then 0 else ⟨i.val+134,by omega⟩
theorem old_injective : Function.Injective oldSlots:=by decide
theorem frame_injective : Function.Injective frameSlots:=by decide
def input (hierarchy description address : List Bool) (R B : ℕ) : Fin 140→List Bool:=
  Fin.addCases (m:=135) (n:=5) (Cold.input hierarchy description address R B) (fun _=>[])
noncomputable def first:=RecoveryFocus.machine oldSlots Cold.machine
noncomputable def last:=RecoveryFocus.machine frameSlots HierarchyFrame.machine
noncomputable def machine:=Composition.machine first last
def budget {R : ℕ} (B : ℕ) (c : BooleanCircuit R) (left right : List Bool):=
  Cold.budget B c+1+HierarchyFrame.budget left right

theorem frames_run {R B : ℕ} (c : BooleanCircuit R) (hc : c.size≤B) (left right address : List Bool) : ∃ out,
    ClockJoin.ReadyRun machine (budget B c left right)
      (input (frame left++frame right) (frame (canonicalBoundedCircuitDescription B c)) address R B) out ∧
      out 138=frame (frame left++frame right) ∧ out 132=frame (PCPPNative.descriptor c) ∧
      out 0=frame left++frame right ∧ out 1=frame (canonicalBoundedCircuitDescription B c) ∧ out 2=address:=by
  obtain ⟨native,hr,hn,hH,hD,hA⟩:=Cold.converter_run c hc (frame left++frame right) address
  let initial:=input (frame left++frame right) (frame (canonicalBoundedCircuitDescription B c)) address R B
  have hfirst:=hr.focus oldSlots old_injective initial (by intro i;simp only [initial,input,oldSlots,Fin.addCases_left])
  let middle:=install oldSlots initial native
  obtain ⟨framed,hf,hframe,hkeep⟩:=HierarchyFrame.frame_run left right
  have hin (j : Fin 6) : middle (frameSlots j)=HierarchyFrame.input (frame left++frame right) j:=by
    fin_cases j
    · exact (install_slot oldSlots old_injective initial native 0).trans hH
    all_goals
      rw [show middle _=initial _ from install_other oldSlots initial native _ (by decide)]
      rfl
  have hlast:=hf.focus frameSlots frame_injective middle hin
  refine ⟨_,ClockJoin.join _ _ _ _ _ _ _ hfirst hlast,?_,?_,?_,?_,?_⟩
  · exact (install_slot frameSlots frame_injective _ _ 4).trans hframe
  · rw [install_other frameSlots _ _ 132 (by decide)]
    exact (install_slot oldSlots old_injective _ _ 132).trans hn
  · exact (install_slot frameSlots frame_injective _ _ 0).trans hkeep
  · rw [install_other frameSlots _ _ 1 (by decide)]
    exact (install_slot oldSlots old_injective _ _ 1).trans hD
  · rw [install_other frameSlots _ _ 2 (by decide)]
    exact (install_slot oldSlots old_injective _ _ 2).trans hA

end NearCubicWires.RepairOrdinary.CloseoutCaseTwo.PreparedFrames
