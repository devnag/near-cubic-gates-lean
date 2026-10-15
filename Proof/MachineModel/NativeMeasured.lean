import Proof.MachineModel.NativeCapacity

/-! One measured cache supplies the actual p, F, and full preparation C.
Only the mode's short w and Q are additional inputs to this whole run. -/
namespace NearCubicWires.ExtIncidence.NativeMeasured
open LocalBitMultitape RepairOrdinary ExtDecompositionBatch RepairRepresentation
open RepairOrdinary.RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def old (i : Fin 88) : Fin 135:=i.castAdd 47
def slots : Fin 52→Fin 135:=![3,53,86,88,4,36,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,128,129,130,131,132,133,134]
theorem slots_injective : Function.Injective slots:=by decide
noncomputable def first:=TapeEmbedding.machine 47 NativeAllocation.machine
noncomputable def last:=RecoveryFocus.machine slots NativeCapacity.machine
noncomputable def machine:=Composition.machine first last
def extra (w : ℕ) (i : Fin 47) : List Bool:=if i=0 then List.replicate w true else []
noncomputable def heads {n : ℕ} (gs : List (ExactThresholdGate n)) : Fin 135→ℕ:=
  Fin.addCases (m:=88) (n:=47) (motive:=fun _=>ℕ) (NativeAllocation.heads gs) (fun _=>0)
noncomputable def input {n : ℕ} (gs : List (ExactThresholdGate n)) (Q w : ℕ) : Fin 135→List Bool:=
  Fin.addCases (m:=88) (n:=47) (motive:=fun _=>List Bool) (NativeAllocation.input gs Q) (extra w)
def capacity {n : ℕ} (gs : List (ExactThresholdGate n)) (Q w : ℕ):=
  CloseoutRowsPreparationBounds.capacity n (NativeWidth.width gs Q) (NativeAllocation.capacity gs Q) w gs.length Q
def budget {n : ℕ} (gs : List (ExactThresholdGate n)) (Q w : ℕ):=NativeAllocation.budget gs Q+1+
  NativeCapacity.budget n (NativeWidth.width gs Q) (NativeAllocation.capacity gs Q) w gs.length Q

theorem measured_run {n : ℕ} (gs : List (ExactThresholdGate n)) (Q w : ℕ) : ∃ H O,
    Step machine (budget gs Q w) (heads gs) (input gs Q w) H O ∧
      O 0=exactListWord gs ∧ H 0=0 ∧ O 3=UnaryTemplate.tape n ∧ H 3=0 ∧
      O 27=List.replicate (RowCachedCoordinateBounds.inner (RowCachedCoordinateBounds.width gs)) true ∧ H 27=0 ∧
      O 31=List.replicate (RowCachedCoordinateBounds.outer gs (RowCachedCoordinateBounds.width gs)) true ∧ H 31=0 ∧
      (∀ j,H (old (NativeAllocation.old (NativeWidth.old (NativeDimensions.slots j))))=0) ∧
      (∀ j,O (old (NativeAllocation.old (NativeWidth.old (NativeDimensions.slots j))))=
        RowCommonTupleDimensions.output (RowCachedCoordinateBounds.width gs) gs.length Q j) ∧
      (∀ j,H (old (NativeAllocation.old (NativeWidth.slots j)))=0) ∧
      (∀ j,O (old (NativeAllocation.old (NativeWidth.slots j)))=
        NativeFieldWidth.output (RowTupleFixedCapacity.width gs Q) Q j) ∧
      O 86=List.replicate (NativeAllocation.capacity gs Q) true ∧ H 86=0 ∧
      (∀ j,H (slots (NativeCapacity.old j))=0) ∧
      (∀ j,O (slots (NativeCapacity.old j))=
        NativeCapacityParameters.output n (NativeWidth.width gs Q) (NativeAllocation.capacity gs Q) w gs.length Q j) ∧
      O 133=List.replicate (capacity gs Q w) true ∧ H 133=0:=by
  obtain ⟨H,A,run,cache,ch,arity,ah,inner,ih,outer,oh,dh,dt,wh,wt,allocated,fh⟩:=
    NativeAllocation.allocation_run gs Q
  have start:=run.embed (fun _ : Fin 47=>0) (extra w)
  let H' : Fin 135→ℕ:=Fin.addCases (m:=88) (n:=47) (motive:=fun _=>ℕ) H (fun _=>0)
  let A' : Fin 135→List Bool:=Fin.addCases (m:=88) (n:=47) (motive:=fun _=>List Bool) A (extra w)
  have hh : ∀ j,H' (slots j)=0:=by
    intro j;fin_cases j
    · exact ah
    · exact wh 4
    · exact fh
    · rfl
    · exact dh 1
    · exact dh 2
    all_goals rfl
  have ha : ∀ j,A' (slots j)=NativeCapacity.input n (NativeWidth.width gs Q) (NativeAllocation.capacity gs Q) w gs.length Q j:=by
    intro j;fin_cases j
    · exact arity
    · exact wt 4
    · exact allocated
    · rfl
    · exact dt 1
    · exact dt 2
    all_goals rfl
  obtain ⟨result,ready,keep,value⟩:=NativeCapacity.capacity_run n (NativeWidth.width gs Q) (NativeAllocation.capacity gs Q) w gs.length Q
  obtain ⟨r,hr,rh,rt,_rs⟩:=ready.focus_at slots slots_injective H' A' ha hh
  have whole:=start.seq (Step.of_run hr rh rt)
  let O:=install slots A' result
  have field (j : Fin 52) : O (slots j)=result j:=install_slot slots slots_injective A' result j
  have six (j : Fin 6) : O (slots (j.castAdd 46))=A' (slots (j.castAdd 46)):=by
    have kept:=(field (NativeCapacity.old (j.castAdd 26))).trans (keep (j.castAdd 26))
    rw [NativeCapacityParameters.input_retained] at kept
    have source:=ha (NativeCapacity.old (j.castAdd 26))
    simp only [NativeCapacity.input,NativeCapacity.old,Fin.addCases_left] at source
    have restored:=kept.trans source.symm
    fin_cases j <;> exact restored
  have retained (i : Fin 88) : O (old i)=A i:=by
    by_cases h3 : i=3
    · subst i;exact six 0
    by_cases h53 : i=53
    · subst i;exact six 1
    by_cases h86 : i=86
    · subst i;exact six 2
    by_cases h4 : i=4
    · subst i;exact six 4
    by_cases h36 : i=36
    · subst i;exact six 5
    rw [←show A' (old i)=A i by simp only [A',old,Fin.addCases_left]]
    apply install_other slots A' result (old i)
    intro j he
    have hv:=congrArg (fun x : Fin 135=>x.val) he
    have hi:=i.isLt
    have n3 : i.val≠3:=fun h=>h3 (Fin.ext h)
    have n53 : i.val≠53:=fun h=>h53 (Fin.ext h)
    have n86 : i.val≠86:=fun h=>h86 (Fin.ext h)
    have n4 : i.val≠4:=fun h=>h4 (Fin.ext h)
    have n36 : i.val≠36:=fun h=>h36 (Fin.ext h)
    fin_cases j <;> simp [slots,old] at hv <;> omega
  refine ⟨H',O,whole,(retained 0).trans cache,ch,(retained 3).trans arity,ah,
    (retained 27).trans inner,ih,(retained 31).trans outer,oh,?_,?_,?_,?_,
    (retained 86).trans allocated,fh,?_,?_,(field 50).trans value,hh 50⟩
  · intro j;simpa only [H',old,Fin.addCases_left] using dh j
  · intro j;exact (retained _).trans (dt j)
  · intro j;simpa only [H',old,Fin.addCases_left] using wh j
  · intro j;exact (retained _).trans (wt j)
  · intro j;exact hh _
  · intro j;exact (field _).trans (keep j)

end NearCubicWires.ExtIncidence.NativeMeasured
