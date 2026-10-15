import Proof.MachineModel.NativeWidth
import Proof.Supplier.RowCommonAllocation

/-! The same measured native cache supplies p and the exact coefficient
allocation F. No width or capacity word is an input to this whole run. -/
namespace NearCubicWires.ExtIncidence.NativeAllocation
open LocalBitMultitape RepairOrdinary ExtDecompositionBatch RepairRepresentation
open RepairOrdinary.RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def old (i : Fin 66) : Fin 88:=i.castAdd 22
def slots : Fin 25→Fin 88:=![39,53,31,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87]
theorem slots_injective : Function.Injective slots:=by decide
noncomputable def first:=TapeEmbedding.machine 22 NativeWidth.machine
noncomputable def last:=RecoveryFocus.machine slots RowCommonAllocation.machine
noncomputable def machine:=Composition.machine first last
def capacity {n : ℕ} (gs : List (ExactThresholdGate n)) (Q : ℕ):=
  RowCommonBounds.capacity gs (gs.length*Q) (NativeWidth.width gs Q)
noncomputable def heads {n : ℕ} (gs : List (ExactThresholdGate n)) : Fin 88→ℕ:=
  Fin.addCases (m:=66) (n:=22) (motive:=fun _=>ℕ) (NativeWidth.heads gs) (fun _=>0)
noncomputable def input {n : ℕ} (gs : List (ExactThresholdGate n)) (Q : ℕ) : Fin 88→List Bool:=
  Fin.addCases (m:=66) (n:=22) (motive:=fun _=>List Bool) (NativeWidth.input gs Q) (fun _=>[])
def budget {n : ℕ} (gs : List (ExactThresholdGate n)) (Q : ℕ):=
  NativeWidth.budget gs Q+1+RowCommonAllocation.budget (gs.length*Q) (NativeWidth.width gs Q)
    (RowCachedCoordinateBounds.outer gs (RowCachedCoordinateBounds.width gs))

theorem allocation_run {n : ℕ} (gs : List (ExactThresholdGate n)) (Q : ℕ) : ∃ H O,
    Step machine (budget gs Q) (heads gs) (input gs Q) H O ∧
      O 0=exactListWord gs ∧ H 0=0 ∧ O 3=UnaryTemplate.tape n ∧ H 3=0 ∧
      O 27=List.replicate (RowCachedCoordinateBounds.inner (RowCachedCoordinateBounds.width gs)) true ∧ H 27=0 ∧
      O 31=List.replicate (RowCachedCoordinateBounds.outer gs (RowCachedCoordinateBounds.width gs)) true ∧ H 31=0 ∧
      (∀ j,H (old (NativeWidth.old (NativeDimensions.slots j)))=0) ∧
      (∀ j,O (old (NativeWidth.old (NativeDimensions.slots j)))=RowCommonTupleDimensions.output (RowCachedCoordinateBounds.width gs) gs.length Q j) ∧
      (∀ j,H (old (NativeWidth.slots j))=0) ∧
      (∀ j,O (old (NativeWidth.slots j))=NativeFieldWidth.output (RowTupleFixedCapacity.width gs Q) Q j) ∧
      O 86=List.replicate (capacity gs Q) true ∧ H 86=0:=by
  obtain ⟨H,A,run,cache,ch,arity,ah,inner,ih,outer,oh,dh,dt,wh,wt⟩:=NativeWidth.width_run gs Q
  have start:=run.embed (fun _ : Fin 22=>0) (fun _=>[])
  let H' : Fin 88→ℕ:=Fin.addCases (m:=66) (n:=22) (motive:=fun _=>ℕ) H (fun _=>0)
  let A' : Fin 88→List Bool:=Fin.addCases (m:=66) (n:=22) (motive:=fun _=>List Bool) A (fun _=>[])
  let D:=RowCachedCoordinateBounds.outer gs (RowCachedCoordinateBounds.width gs)
  have hh : ∀ j,H' (slots j)=0:=by
    intro j;fin_cases j
    · exact dh 5
    · exact wh 4
    · exact oh
    all_goals rfl
  have ha : ∀ j,A' (slots j)=RowCommonAllocation.input (gs.length*Q) (NativeWidth.width gs Q) D j:=by
    intro j;fin_cases j
    · exact dt 5
    · exact wt 4
    · exact outer
    all_goals rfl
  obtain ⟨r,hr,rh,rt,_rs⟩:=(RowCommonAllocation.allocation_ready (gs.length*Q) (NativeWidth.width gs Q) D).focus_at
    slots slots_injective H' A' ha hh
  have whole:=start.seq (Step.of_run hr rh rt)
  let O:=install slots A' (RowCommonAllocation.output (gs.length*Q) (NativeWidth.width gs Q) D)
  have field (j : Fin 25) : O (slots j)=RowCommonAllocation.output (gs.length*Q) (NativeWidth.width gs Q) D j:=
    install_slot slots slots_injective A' _ j
  have retained (i : Fin 66) : O (old i)=A i:=by
    by_cases h39 : i=39
    · subst i;exact (field 0).trans (dt 5).symm
    by_cases h53 : i=53
    · subst i;exact (field 1).trans (wt 4).symm
    by_cases h31 : i=31
    · subst i;exact (field 2).trans outer.symm
    rw [←show A' (old i)=A i by simp only [A',old,Fin.addCases_left]]
    apply install_other slots A' _ (old i)
    intro j he
    have hv:=congrArg (fun x : Fin 88=>x.val) he
    have hi:=i.isLt
    have n39 : i.val≠39:=fun h=>h39 (Fin.ext h)
    have n53 : i.val≠53:=fun h=>h53 (Fin.ext h)
    have n31 : i.val≠31:=fun h=>h31 (Fin.ext h)
    fin_cases j <;> simp [slots,old] at hv <;> omega
  refine ⟨H',O,whole,(retained 0).trans cache,ch,(retained 3).trans arity,ah,
    (retained 27).trans inner,ih,(retained 31).trans outer,oh,?_,?_,?_,?_,?_,hh 23⟩
  · intro j;simpa only [H',old,Fin.addCases_left] using dh j
  · intro j;exact (retained (NativeWidth.old (NativeDimensions.slots j))).trans (dt j)
  · intro j;simpa only [H',old,Fin.addCases_left] using wh j
  · intro j;exact (retained (NativeWidth.slots j)).trans (wt j)
  · change O (slots 23)=_
    rw [field]
    change List.replicate (RowCommonAllocation.value (gs.length*Q) (NativeWidth.width gs Q) D) true=_
    rw [show D=RowCachedCoordinateBounds.outer gs (RowCachedCoordinateBounds.width gs) from rfl,
      RowCommonAllocation.capacity_eq]
    rfl

end NearCubicWires.ExtIncidence.NativeAllocation
