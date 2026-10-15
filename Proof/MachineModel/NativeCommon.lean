import Proof.MachineModel.NativeMeasure
import Proof.Supplier.RowCommonResources

/-! The measured original cache supplies both actual common capacity words.
These are produced once for the fixed shared native cache. -/
namespace NearCubicWires.ExtIncidence.NativeCommon
open LocalBitMultitape RepairOrdinary ExtDecompositionBatch RepairRepresentation
open RepairOrdinary.RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def old (i : Fin 21) : Fin 36:=i.castAdd 15
def slots : Fin 17→Fin 36:=![15,19,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35]
theorem slots_injective : Function.Injective slots:=by decide
noncomputable def first:=TapeEmbedding.machine 15 NativeMeasure.machine
noncomputable def last:=RecoveryFocus.machine slots RowCommonResources.machine
noncomputable def machine:=Composition.machine first last
noncomputable def heads {n : ℕ} (gs : List (ExactThresholdGate n)) : Fin 36→ℕ:=
  Fin.addCases (m:=21) (n:=15) (motive:=fun _=>ℕ) (NativeMeasure.heads gs) (fun _=>0)
noncomputable def input {n : ℕ} (gs : List (ExactThresholdGate n)) : Fin 36→List Bool:=
  Fin.addCases (m:=21) (n:=15) (motive:=fun _=>List Bool) (NativeMeasure.input gs) (fun _=>[])
def scale {n : ℕ} (gs : List (ExactThresholdGate n)):=RowCommonSize.scale (exactListWord gs).length n gs.length
def budget {n : ℕ} (gs : List (ExactThresholdGate n)):=
  NativeMeasure.budget gs+1+RowCommonResources.budget (RowCachedCoordinateBounds.width gs) (scale gs)

theorem common_run {n : ℕ} (gs : List (ExactThresholdGate n)) : ∃ H O,
    Step machine (budget gs) (heads gs) (input gs) H O ∧
      O 0=exactListWord gs ∧ H 0=0 ∧
      O 3=UnaryTemplate.tape n ∧ H 3=0 ∧
      O 4=UnaryTemplate.tape gs.length ∧ H 4=0 ∧
      O 5=List.replicate (exactListWord gs).length true ∧ H 5=0 ∧
      O 15=List.replicate (RowCachedCoordinateBounds.width gs) true ∧ H 15=0 ∧
      O 27=List.replicate (RowCachedCoordinateBounds.inner (RowCachedCoordinateBounds.width gs)) true ∧ H 27=0 ∧
      O 31=List.replicate (RowCachedCoordinateBounds.outer gs (RowCachedCoordinateBounds.width gs)) true ∧ H 31=0:=by
  obtain ⟨H,A,measured,cache,ch,hh,ha⟩:=NativeMeasure.measured_run gs
  have start:=measured.embed (fun _ : Fin 15=>0) (fun _=>[])
  let H' : Fin 36→ℕ:=Fin.addCases (m:=21) (n:=15) (motive:=fun _=>ℕ) H (fun _=>0)
  let A' : Fin 36→List Bool:=Fin.addCases (m:=21) (n:=15) (motive:=fun _=>List Bool) A (fun _=>[])
  have ah : ∀ j,H' (slots j)=0:=by
    intro j;fin_cases j
    · exact hh 11
    · exact hh 15
    all_goals rfl
  have atape : ∀ j,A' (slots j)=RowCommonResources.input (RowCachedCoordinateBounds.width gs) (scale gs) j:=by
    intro j;fin_cases j
    · exact ha 11
    · exact ha 15
    all_goals rfl
  obtain ⟨r,hr,rh,rt,_rs⟩:=(RowCommonResources.resources_ready (RowCachedCoordinateBounds.width gs) (scale gs)).focus_at
    slots slots_injective H' A' atape ah
  have whole:=start.seq (Step.of_run hr rh rt)
  let O:=install slots A' (RowCommonResources.output (RowCachedCoordinateBounds.width gs) (scale gs))
  have keep (i : Fin 36) (hi : ∀ j,slots j≠i) : O i=A' i:=install_other slots A' _ i hi
  have fields (j : Fin 17) : O (slots j)=RowCommonResources.output (RowCachedCoordinateBounds.width gs) (scale gs) j:=
    install_slot slots slots_injective A' _ j
  refine ⟨H',O,whole,(keep 0 (by decide)).trans cache,ch,
    (keep 3 (by decide)).trans (ha 1),hh 1,
    (keep 4 (by decide)).trans (ha 2),hh 2,
    (keep 5 (by decide)).trans (ha 0),hh 0,?_,ah 0,?_,ah 8,?_,ah 12⟩
  · exact fields 0
  · change O (slots 8)=_
    rw [fields]
    change List.replicate ((RowCachedCoordinateBounds.width gs+1)*32) true=
      List.replicate (32*(RowCachedCoordinateBounds.width gs+1)) true
    rw [Nat.mul_comm]
  · change O (slots 12)=_
    rw [fields]
    change List.replicate (scale gs*256) true=List.replicate (RowCachedCoordinateBounds.outer gs (RowCachedCoordinateBounds.width gs)) true
    rw [scale,RowCommonResources.scale_eq]
    simp only [RowCachedCoordinateBounds.outer,Nat.mul_comm]

end NearCubicWires.ExtIncidence.NativeCommon
