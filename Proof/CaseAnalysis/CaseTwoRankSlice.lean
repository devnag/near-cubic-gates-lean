import Proof.CaseAnalysis.CaseTwoRankField
import Proof.PCP.PCPSerializerCapacityFocus
import Proof.MachineModel.OrdinaryRewindWorkspace

/-! One paid fixed-width field lookup in the original canonical description,
followed by its existing unary-to-binary converter.  The actual source word,
offset and width are retained; all heads return to zero. -/
namespace NearCubicWires.RepairOrdinary.CloseoutCaseTwo.RankSlice
open LocalBitMultitape RepairSource.VerifierDecoding OuterPCPRecovery
open RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slice := Rewind.machine SliceMachine.machine
def sliceInput (pre field tail : List Bool) : Fin 5→List Bool :=
  ![frame (pre++field++tail),[],List.replicate pre.length true,
    List.replicate field.length true,[]]
def sliceOutput (pre field tail : List Bool) : Fin 5→List Bool :=
  ![frame (pre++field++tail),field,List.replicate pre.length true,
    List.replicate field.length true,List.replicate (2*pre.length+2*field.length+2) false]
def sliceBudget (offset width : Nat) := 4*offset+4*width+6

theorem slice_ready (pre field tail : List Bool) :
    ClockJoin.ReadyRun slice (sliceBudget pre.length field.length)
      (sliceInput pre field tail) (sliceOutput pre field tail) := by
  obtain ⟨base,hr,hf,hs,_⟩ := SliceMachine.field_run pre field tail
  obtain ⟨r,rr,rt,rl,rh,rs,_⟩ := Rewind.Workspace.reset_workspace SliceMachine.machine _ _ base hr 0
  have hb : 2*base.steps+2=sliceBudget pre.length field.length := by rw [hs];unfold sliceBudget;omega
  have hin : Fin.addCases (motive:=fun _ : Fin 5=>List Bool) (SliceMachine.input pre field tail)
      (fun _ : Fin 1=>List.replicate 0 false)=sliceInput pre field tail := by
    funext i;fin_cases i <;> rfl
  rw [hb,hin] at rr
  refine ⟨r,rr,?_,rh,rs.le.trans_eq hb⟩
  funext i
  fin_cases i
  · exact (rt 0).trans (by rw [hf];rfl)
  · exact (rt 1).trans (by rw [hf];rfl)
  · exact (rt 2).trans (by rw [hf];rfl)
  · exact (rt 3).trans (by rw [hf];rfl)
  · change r.final.tapes 4=List.replicate (2*pre.length+2*field.length+2) false
    have hj : (0 : Fin 1).natAdd 4=(4 : Fin 5) := by decide
    rw [hj,Nat.zero_max,hs] at rl
    exact rl

def sliceSlots : Fin 5→Fin 14 := fun i=>i.castAdd 9
def countSlots : Fin 10→Fin 14 := ![1,5,6,7,8,9,10,11,12,13]
noncomputable def first := RecoveryFocus.machine sliceSlots slice
noncomputable def last := RecoveryFocus.machine countSlots CloseoutRowsCountBinary.machine
noncomputable def machine := Composition.machine first last
def input (source : List Bool) (offset width : Nat) : Fin 14→List Bool := fun i=>
  if i=0 then frame source else if i=2 then List.replicate offset true
  else if i=3 then List.replicate width true else []
def budget (offset width value : Nat) := sliceBudget offset width+1+CloseoutRowsCountBinary.budget value

theorem field_ready (pre tail : List Bool) (limit value : Nat) (hv : value≤limit) : ∃ out,
    ClockJoin.ReadyRun machine (budget pre.length limit value)
      (input (pre++orderedNatBits limit value++tail) pre.length limit) out ∧
      out 0=frame (pre++orderedNatBits limit value++tail) ∧
      out 2=List.replicate pre.length true ∧ out 3=List.replicate limit true ∧
      out 5=List.replicate value true ∧ out 7=UnaryTemplate.tape value ∧
      out 9=frame (CloseoutRowsCountBinary.bits value) := by
  let field:=orderedNatBits limit value
  let source:=pre++field++tail
  have fl : field.length=limit := orderedNatBits_length limit value
  let before:=input source pre.length limit
  let middle:=install sliceSlots before (sliceOutput pre field tail)
  have hs : ClockJoin.ReadyRun slice (sliceBudget pre.length limit)
      (sliceInput pre field tail) (sliceOutput pre field tail) := by
    simpa only [fl] using slice_ready pre field tail
  obtain ⟨a,ar,ah,atp,ast⟩ := hs.focus_at sliceSlots (by decide) (fun _=>0) before
    (by intro i;fin_cases i <;> simp [before,input,sliceSlots,sliceInput,fl,source,List.append_assoc]) (by intro i;rfl)
  have hfirst : ClockJoin.ReadyRun first (sliceBudget pre.length limit) before middle :=
    ⟨a,ar,atp,by intro i;rw [ah],ast⟩
  obtain ⟨binary,hbinary,b1,b3,b5⟩ := RankField.binary_run limit value hv
  have hc (i : Fin 10) : middle (countSlots i)=RankField.input limit value i := by
    fin_cases i
    · exact install_slot sliceSlots (by decide) before (sliceOutput pre field tail) 1
    all_goals
      rw [show middle _=before _ from install_other sliceSlots before (sliceOutput pre field tail) _ (by decide)]
      rfl
  obtain ⟨b,br,bh,bt,bst⟩ := hbinary.focus_at countSlots (by decide) (fun _=>0) middle hc (by intro i;rfl)
  let final:=install countSlots middle binary
  have hlast : ClockJoin.ReadyRun last (CloseoutRowsCountBinary.budget value) middle final :=
    ⟨b,br,bt,by intro i;rw [bh],bst⟩
  refine ⟨final,ClockJoin.join first last _ _ before middle final hfirst hlast,?_,?_,?_,?_,?_,?_⟩
  · rw [show final 0=middle 0 from install_other countSlots middle binary 0 (by decide)]
    exact install_slot sliceSlots (by decide) before (sliceOutput pre field tail) 0
  · rw [show final 2=middle 2 from install_other countSlots middle binary 2 (by decide)]
    exact install_slot sliceSlots (by decide) before (sliceOutput pre field tail) 2
  · rw [show final 3=middle 3 from install_other countSlots middle binary 3 (by decide)]
    exact (install_slot sliceSlots (by decide) before (sliceOutput pre field tail) 3).trans (by simp [sliceOutput,fl])
  · exact (install_slot countSlots (by decide) middle binary 1).trans b1
  · exact (install_slot countSlots (by decide) middle binary 3).trans b3
  · exact (install_slot countSlots (by decide) middle binary 5).trans b5

end NearCubicWires.RepairOrdinary.CloseoutCaseTwo.RankSlice
