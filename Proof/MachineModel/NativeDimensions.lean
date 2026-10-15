import Proof.MachineModel.NativeCommon
import Proof.Supplier.RowCommonTupleDimensions
import Proof.Supplier.RowTupleFixedCapacity

/-! The actual shared cache and degree driver produce the native occurrence
bound and base coefficient width. The final width still adds Q for constants. -/
namespace NearCubicWires.ExtIncidence.NativeDimensions
open LocalBitMultitape RepairOrdinary ExtDecompositionBatch RepairRepresentation
open RepairOrdinary.RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 17→Fin 51:=![15,4,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50]
theorem slots_injective : Function.Injective slots:=by decide
noncomputable def first:=TapeEmbedding.machine 15 NativeCommon.machine
noncomputable def last:=RecoveryFocus.machine slots RowCommonTupleDimensions.machine
noncomputable def machine:=Composition.machine first last
def extra (Q : ℕ) : Fin 15→List Bool:=fun i=>if i=0 then UnaryTemplate.tape Q else []
noncomputable def heads {n : ℕ} (gs : List (ExactThresholdGate n)) : Fin 51→ℕ:=
  Fin.addCases (m:=36) (n:=15) (motive:=fun _=>ℕ) (NativeCommon.heads gs) (fun _=>0)
noncomputable def input {n : ℕ} (gs : List (ExactThresholdGate n)) (Q : ℕ) : Fin 51→List Bool:=
  Fin.addCases (m:=36) (n:=15) (motive:=fun _=>List Bool) (NativeCommon.input gs) (extra Q)
def budget {n : ℕ} (gs : List (ExactThresholdGate n)) (Q : ℕ):=
  NativeCommon.budget gs+1+RowCommonTupleDimensions.budget (RowCachedCoordinateBounds.width gs) gs.length Q

theorem dimensions_run {n : ℕ} (gs : List (ExactThresholdGate n)) (Q : ℕ) : ∃ H O,
    Step machine (budget gs Q) (heads gs) (input gs Q) H O ∧
      O 0=exactListWord gs ∧ H 0=0 ∧ O 3=UnaryTemplate.tape n ∧ H 3=0 ∧
      O 27=List.replicate (RowCachedCoordinateBounds.inner (RowCachedCoordinateBounds.width gs)) true ∧ H 27=0 ∧
      O 31=List.replicate (RowCachedCoordinateBounds.outer gs (RowCachedCoordinateBounds.width gs)) true ∧ H 31=0 ∧
      (∀ j,H (slots j)=0) ∧
      (∀ j,O (slots j)=RowCommonTupleDimensions.output (RowCachedCoordinateBounds.width gs) gs.length Q j):=by
  obtain ⟨H,A,common,cache,ch,arity,ah,N,Nh,_bytes,_byteh,w,wh,inner,ih,outer,oh⟩:=NativeCommon.common_run gs
  have start:=common.embed (fun _ : Fin 15=>0) (extra Q)
  let H' : Fin 51→ℕ:=Fin.addCases (m:=36) (n:=15) (motive:=fun _=>ℕ) H (fun _=>0)
  let A' : Fin 51→List Bool:=Fin.addCases (m:=36) (n:=15) (motive:=fun _=>List Bool) A (extra Q)
  have hh : ∀ j,H' (slots j)=0:=by
    intro j;fin_cases j
    · exact wh
    · exact Nh
    all_goals rfl
  have ha : ∀ j,A' (slots j)=RowCommonTupleDimensions.input (RowCachedCoordinateBounds.width gs) gs.length Q j:=by
    intro j;fin_cases j
    · exact w
    · exact N
    all_goals rfl
  obtain ⟨r,hr,rh,rt,_rs⟩:=(RowCommonTupleDimensions.dimensions_ready (RowCachedCoordinateBounds.width gs) gs.length Q).focus_at
    slots slots_injective H' A' ha hh
  have whole:=start.seq (Step.of_run hr rh rt)
  refine ⟨H',_,whole,?_,ch,?_,ah,?_,ih,?_,oh,hh,?_⟩
  · exact (install_other slots A' _ 0 (by decide)).trans cache
  · exact (install_other slots A' _ 3 (by decide)).trans arity
  · exact (install_other slots A' _ 27 (by decide)).trans inner
  · exact (install_other slots A' _ 31 (by decide)).trans outer
  · intro j;exact install_slot slots slots_injective A' _ j

end NearCubicWires.ExtIncidence.NativeDimensions
