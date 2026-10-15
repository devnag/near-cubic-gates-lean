import Proof.CaseAnalysis.CaseTwoRankAppend

/-! One original fixed-width field is physically sliced and appended as an
exact native natural. The description, paid offset/width, and old native
prefix are retained. The existing appender supplies the zero case as well. -/
namespace NearCubicWires.RepairOrdinary.CloseoutCaseTwo.FieldNative
open LocalBitMultitape RepairRepresentation OuterPCPRecovery RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def sliceSlots : Fin 5→Fin 22 := ![0,1,2,3,4]
def nativeSlots : Fin 18→Fin 22 := ![1,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21]
noncomputable def first:=RecoveryFocus.machine sliceSlots RankSlice.slice
noncomputable def last:=RecoveryFocus.machine nativeSlots PCPPNativeNaturalAppend.machine
noncomputable def machine:=Composition.machine first last
def data (source : List Bool) (offset width : ℕ) (out : List Bool) (i : Fin 22) :=
  if i=0 then frame source else if i=2 then List.replicate offset true
  else if i=3 then List.replicate width true else if i=21 then out else []
def heads (out : List Bool) (i : Fin 22) := if i=21 then out.length else 0
def budget (offset width value : ℕ) :=
  RankSlice.sliceBudget offset width+1+PCPPNativeNaturalAppend.budget value

theorem field_run (pre tail : List Bool) (limit value : ℕ) (out : List Bool)
    (hv : value ≤ limit) :
    let source:=pre++orderedNatBits limit value++tail
    ∃ r,runFrom machine (budget pre.length limit value)
      ⟨machine.start,heads out,data source pre.length limit out⟩=some r ∧
      r.steps ≤ budget pre.length limit value ∧
      r.final.tapes 0=frame source ∧ r.final.heads 0=0 ∧
      r.final.tapes 2=List.replicate pre.length true ∧ r.final.heads 2=0 ∧
      r.final.tapes 3=List.replicate limit true ∧ r.final.heads 3=0 ∧
      r.final.tapes 5=List.replicate value true ∧ r.final.heads 5=0 ∧
      r.final.tapes 21=out++natWord value ∧ r.final.heads 21=(out++natWord value).length := by
  let field:=orderedNatBits limit value
  let source:=pre++field++tail
  let before:=data source pre.length limit out
  let middle:=install sliceSlots before (RankSlice.sliceOutput pre field tail)
  have fl : field.length=limit := orderedNatBits_length limit value
  have hs : ClockJoin.ReadyRun RankSlice.slice (RankSlice.sliceBudget pre.length limit)
      (RankSlice.sliceInput pre field tail) (RankSlice.sliceOutput pre field tail) := by
    simpa only [fl] using RankSlice.slice_ready pre field tail
  obtain ⟨a,ar,ah,atp,ast⟩:=hs.focus_at sliceSlots (by decide) (heads out) before
    (by intro i;fin_cases i <;> simp [before,data,sliceSlots,RankSlice.sliceInput,fl,source,List.append_assoc])
    (by intro i;fin_cases i <;> rfl)
  obtain ⟨base,br,bs,bout,bhead,bvalue,bvhead⟩:=RankAppend.append_run limit value out hv
  have hmiddle (i : Fin 18) : middle (nativeSlots i)=RankAppend.data limit value out i := by
    fin_cases i
    · exact install_slot sliceSlots (by decide) before (RankSlice.sliceOutput pre field tail) 1
    all_goals
      rw [show middle _=before _ from install_other sliceSlots before (RankSlice.sliceOutput pre field tail) _ (by decide)]
      rfl
  obtain ⟨b,hr,_bc,bst,bh,bt,bkeep⟩:=RecoveryFocus.dock nativeSlots (by decide)
    PCPPNativeNaturalAppend.machine _ a.final.heads a.final.tapes
    (RankAppend.entry limit value out)
    (by intro i;rw [ah];fin_cases i <;> rfl)
    (by intro i;rw [atp];exact hmiddle i) base br
  have whole:=Composition.run_join first last _ _ _ a b ar hr
  refine ⟨Composition.joinedReceipt a b,whole,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · change a.steps+1+b.steps ≤ budget pre.length limit value
    rw [bst]
    unfold budget
    omega
  · change b.final.tapes 0=frame source
    rw [(bkeep 0 (by decide)).2,atp]
    exact install_slot sliceSlots (by decide) before (RankSlice.sliceOutput pre field tail) 0
  · change b.final.heads 0=0
    rw [(bkeep 0 (by decide)).1,ah]
    rfl
  · change b.final.tapes 2=List.replicate pre.length true
    rw [(bkeep 2 (by decide)).2,atp]
    exact install_slot sliceSlots (by decide) before (RankSlice.sliceOutput pre field tail) 2
  · change b.final.heads 2=0
    rw [(bkeep 2 (by decide)).1,ah]
    rfl
  · change b.final.tapes 3=List.replicate limit true
    rw [(bkeep 3 (by decide)).2,atp]
    exact (install_slot sliceSlots (by decide) before (RankSlice.sliceOutput pre field tail) 3).trans
      (by simp only [RankSlice.sliceOutput,fl];rfl)
  · change b.final.heads 3=0
    rw [(bkeep 3 (by decide)).1,ah]
    rfl
  · exact (bt 1).trans bvalue
  · exact (bh 1).trans bvhead
  · exact (bt 17).trans bout
  · exact (bh 17).trans bhead

end NearCubicWires.RepairOrdinary.CloseoutCaseTwo.FieldNative
