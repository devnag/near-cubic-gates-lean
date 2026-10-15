import Proof.MachineModel.NativeDimensions
import Proof.MachineModel.NativeFieldWidth

/-! The complete measured-cache run produces the final p=base+Q word and
signed-field driver, retaining every shared cache/dimension field. -/
namespace NearCubicWires.ExtIncidence.NativeWidth
open LocalBitMultitape RepairOrdinary ExtDecompositionBatch RepairRepresentation
open RepairOrdinary.RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def old (i : Fin 51) : Fin 66:=i.castAdd 15
def slots : Fin 17→Fin 66:=![43,36,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65]
theorem slots_injective : Function.Injective slots:=by decide
noncomputable def first:=TapeEmbedding.machine 15 NativeDimensions.machine
noncomputable def last:=RecoveryFocus.machine slots NativeFieldWidth.machine
noncomputable def machine:=Composition.machine first last
def width {n : ℕ} (gs : List (ExactThresholdGate n)) (Q : ℕ):=RowTupleFixedCapacity.width gs Q+Q
noncomputable def heads {n : ℕ} (gs : List (ExactThresholdGate n)) : Fin 66→ℕ:=
  Fin.addCases (m:=51) (n:=15) (motive:=fun _=>ℕ) (NativeDimensions.heads gs) (fun _=>0)
noncomputable def input {n : ℕ} (gs : List (ExactThresholdGate n)) (Q : ℕ) : Fin 66→List Bool:=
  Fin.addCases (m:=51) (n:=15) (motive:=fun _=>List Bool) (NativeDimensions.input gs Q) (fun _=>[])
def budget {n : ℕ} (gs : List (ExactThresholdGate n)) (Q : ℕ):=
  NativeDimensions.budget gs Q+1+NativeFieldWidth.budget (RowTupleFixedCapacity.width gs Q) Q

theorem width_run {n : ℕ} (gs : List (ExactThresholdGate n)) (Q : ℕ) : ∃ H O,
    Step machine (budget gs Q) (heads gs) (input gs Q) H O ∧
      O 0=exactListWord gs ∧ H 0=0 ∧ O 3=UnaryTemplate.tape n ∧ H 3=0 ∧
      O 27=List.replicate (RowCachedCoordinateBounds.inner (RowCachedCoordinateBounds.width gs)) true ∧ H 27=0 ∧
      O 31=List.replicate (RowCachedCoordinateBounds.outer gs (RowCachedCoordinateBounds.width gs)) true ∧ H 31=0 ∧
      (∀ j,H (old (NativeDimensions.slots j))=0) ∧
      (∀ j,O (old (NativeDimensions.slots j))=RowCommonTupleDimensions.output (RowCachedCoordinateBounds.width gs) gs.length Q j) ∧
      (∀ j,H (slots j)=0) ∧ (∀ j,O (slots j)=NativeFieldWidth.output (RowTupleFixedCapacity.width gs Q) Q j):=by
  obtain ⟨H,A,run,cache,ch,arity,ah,inner,ih,outer,oh,dh,dt⟩:=NativeDimensions.dimensions_run gs Q
  have start:=run.embed (fun _ : Fin 15=>0) (fun _=>[])
  let H' : Fin 66→ℕ:=Fin.addCases (m:=51) (n:=15) (motive:=fun _=>ℕ) H (fun _=>0)
  let A' : Fin 66→List Bool:=Fin.addCases (m:=51) (n:=15) (motive:=fun _=>List Bool) A (fun _=>[])
  have hh : ∀ j,H' (slots j)=0:=by
    intro j;fin_cases j
    · exact dh 9
    · exact dh 2
    all_goals rfl
  have ha : ∀ j,A' (slots j)=NativeFieldWidth.input (RowTupleFixedCapacity.width gs Q) Q j:=by
    intro j;fin_cases j
    · exact dt 9
    · exact dt 2
    all_goals rfl
  obtain ⟨r,hr,rh,rt,_rs⟩:=(NativeFieldWidth.ready (RowTupleFixedCapacity.width gs Q) Q).focus_at
    slots slots_injective H' A' ha hh
  have whole:=start.seq (Step.of_run hr rh rt)
  let O:=install slots A' (NativeFieldWidth.output (RowTupleFixedCapacity.width gs Q) Q)
  have field (j : Fin 17) : O (slots j)=NativeFieldWidth.output (RowTupleFixedCapacity.width gs Q) Q j:=
    install_slot slots slots_injective A' _ j
  have retained (i : Fin 51) : O (old i)=A i:=by
    by_cases h43 : i=43
    · subst i;exact (field 0).trans (dt 9).symm
    by_cases h36 : i=36
    · subst i;exact (field 1).trans (dt 2).symm
    rw [←show A' (old i)=A i by simp only [A',old,Fin.addCases_left]]
    apply install_other slots A' _ (old i)
    intro j he
    have hv:=congrArg (fun x : Fin 66=>x.val) he
    have hi:=i.isLt
    have n43 : i.val≠43:=fun h=>h43 (Fin.ext h)
    have n36 : i.val≠36:=fun h=>h36 (Fin.ext h)
    fin_cases j <;> simp [slots,old] at hv <;> omega
  refine ⟨H',O,whole,(retained 0).trans cache,ch,(retained 3).trans arity,ah,
    (retained 27).trans inner,ih,(retained 31).trans outer,oh,?_,?_,hh,field⟩
  · intro j;simpa only [H',old,Fin.addCases_left] using dh j
  · intro j;exact (retained (NativeDimensions.slots j)).trans (dt j)

theorem width_guards {n : ℕ} (gs : List (ExactThresholdGate n)) (Q : ℕ) :
    Q ≤ width gs Q ∧ RowTupleFixedCapacity.width gs Q ≤ width gs Q:=by
  unfold width;omega

end NearCubicWires.ExtIncidence.NativeWidth
