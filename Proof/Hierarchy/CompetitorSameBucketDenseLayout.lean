import Proof.Hierarchy.CompetitorSameBucketEntryFits
import Proof.Hierarchy.CompetitorSameBucketSortedBounds

/-! Approved whole-source routing: sorted keys go directly to outer tape3,
the dense P/N bank to tape2. Internal sorter tape3 is moved to fresh tape462;
no full-table copy is introduced. All grouping work tapes start blank. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSameBucketColdDense
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open MatrixScoreBatch (Request)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def width (r : Request) := CompetitorPlaneWidth.width (natBitLength r.U) r.p
def publicInput {t : ℕ} (r : Request) (w : ℕ) (i : Fin t) : List Bool :=
  if i.val=0 then MatrixScoreBatch.physicalInput r else if i.val=1 then List.replicate w true else []
def input (r : Request) : Fin 511 → List Bool := publicInput r (width r)
def sourceSlots (i : Fin 462) : Fin 511 :=
  if i.val=2 then 3 else if i.val=3 then 462 else ⟨i.val,by omega⟩
def groupSlots (i : Fin 53) : Fin 511 :=
  if i.val=0 then 3 else if i.val=1 then 1 else if i.val=2 then 42 else if i.val=3 then 227 else
  if i.val=4 then 2 else ⟨i.val+458,by omega⟩

theorem source_value (i : Fin 462) : (sourceSlots i).val=
    if i.val=2 then 3 else if i.val=3 then 462 else i.val := by
  unfold sourceSlots
  split_ifs <;> rfl
theorem group_value (i : Fin 53) : (groupSlots i).val=
    if i.val=0 then 3 else if i.val=1 then 1 else if i.val=2 then 42 else
    if i.val=3 then 227 else if i.val=4 then 2 else i.val+458 := by
  unfold groupSlots
  split_ifs <;> rfl

theorem source_injective : Function.Injective sourceSlots := by
  intro i j h
  have hv:=congrArg (fun a : Fin 511=>a.val) h
  have hi:=i.isLt
  have hj:=j.isLt
  simp only [source_value] at hv
  split_ifs at hv
  all_goals apply Fin.ext;omega

theorem group_injective : Function.Injective groupSlots := by
  intro i j h
  have hv:=congrArg (fun a : Fin 511=>a.val) h
  have hi:=i.isLt
  have hj:=j.isLt
  simp only [group_value] at hv
  split_ifs at hv
  all_goals apply Fin.ext;omega

theorem source_range (i : Fin 462) : (sourceSlots i).val ≤ 462 ∧ (sourceSlots i).val≠2 := by
  have hi:=i.isLt
  simp only [source_value]
  split_ifs <;> omega

theorem group_avoids_zero (i : Fin 53) : groupSlots i≠0 := by
  intro h
  have hv:=congrArg (fun a : Fin 511=>a.val) h
  change (groupSlots i).val=0 at hv
  rw [group_value] at hv
  split_ifs at hv

theorem extend_public {t e : ℕ} (ht : 2 ≤ t) (r : Request) (w : ℕ) :
    Fin.addCases (m := t) (n := e) (motive := fun _=>List Bool) (publicInput r w) (fun _=>[])=
      publicInput r w := by
  funext i
  refine Fin.addCases (fun j=>?_) (fun j=>?_) i
  · rw [Fin.addCases_left]
    rfl
  · rw [Fin.addCases_right]
    have hz : t+j.val≠0 := by omega
    have ho : t+j.val≠1 := by omega
    simp only [publicInput,Fin.val_natAdd,if_neg hz,if_neg ho]

theorem source_input (r : Request) (w : ℕ) : CompetitorSameBucketColdSorted.input r w=publicInput r w := by
  have base : CompetitorSameBucketCold.input r w=publicInput r w := by
    funext i
    simp only [CompetitorSameBucketCold.input,publicInput,Fin.ext_iff]
    rfl
  simp only [CompetitorSameBucketColdSorted.input,CompetitorSameBucketColdKeyStream.input,
    CompetitorSameBucketColdZeroGrid.input,CompetitorSameBucketColdGate.input,
    CompetitorSameBucketColdInitialized.input,CompetitorSameBucketColdWorkspace.input,
    CompetitorSameBucketColdAllocate.oldTapes,CompetitorSameBucketColdCoefficient.input,
    CompetitorSameBucketColdBlocks.input,CompetitorSameBucketColdCapacity.input,base]
  rw [extend_public (by decide : 2 ≤ 342),extend_public (by decide : 2 ≤ 360),
    extend_public (by decide : 2 ≤ 382),extend_public (by decide : 2 ≤ 398),
    extend_public (by decide : 2 ≤ 442),extend_public (by decide : 2 ≤ 455),
    extend_public (by decide : 2 ≤ 456)]

theorem source_selected (r : Request) (i : Fin 462) :
    input r (sourceSlots i)=CompetitorSameBucketColdSorted.input r (width r) i := by
  rw [source_input]
  by_cases hi2 : i.val=2
  · have he : i=2 := Fin.ext hi2
    subst i;rfl
  by_cases hi3 : i.val=3
  · have he : i=3 := Fin.ext hi3
    subst i;rfl
  simp only [input,sourceSlots,hi2,hi3,↓reduceIte,publicInput]

theorem group_input (w p m : ℕ) (source : List Bool) (i : Fin 53) :
    CompetitorSameBucketGroupCold.input w p m source i=
      if i=0 then source else if i=1 then List.replicate w true else
      if i=2 then List.replicate p true else if i=3 then List.replicate m true else [] := by
  fin_cases i <;> rfl

noncomputable def first := RecoveryFocus.machine sourceSlots CompetitorSameBucketColdSorted.machine
noncomputable def last := RecoveryFocus.machine groupSlots CompetitorSameBucketGroupCold.machine
noncomputable def machine := Composition.machine first last

end NearCubicWires.RepairOrdinary.CompetitorSameBucketColdDense
