import Proof.MachineModel.Layout
import Proof.Supplier.RowCacheMass
import Proof.Supplier.RowCommonSize
import Proof.Circuits.DecompositionCountPosition
import Proof.PCP.PCPSerializerCapacityFocus

/-! Measure the SAME native child cache and compute its common width and
scale. No decomposition source is called and no byte count is supplied. -/
namespace NearCubicWires.ExtIncidence.NativeMeasure
open LocalBitMultitape RepairOrdinary ExtDecompositionBatch RepairRepresentation
open RepairOrdinary.RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 17→Fin 21:=![5,3,4,7,8,9,10,11,12,13,14,15,16,17,18,19,20]
theorem slots_injective : Function.Injective slots:=by decide
def directions (i : Fin 21) : HeadMove:=if i=3 ∨ i=4 then .left else .stay
noncomputable def measure:=TapeEmbedding.machine 14 RowCacheMass.machine
def position:=DecompositionCountPosition.move directions
noncomputable def first:=Composition.machine measure position
noncomputable def size:=RecoveryFocus.machine slots RowCommonSize.machine
noncomputable def machine:=Composition.machine first size
noncomputable def heads {n : ℕ} (gs : List (ExactThresholdGate n)) : Fin 21→ℕ:=
  Fin.addCases (m:=7) (n:=14) (motive:=fun _=>ℕ) (RowCacheMass.input gs).heads (fun _=>0)
noncomputable def input {n : ℕ} (gs : List (ExactThresholdGate n)) : Fin 21→List Bool:=
  Fin.addCases (m:=7) (n:=14) (motive:=fun _=>List Bool) (RowCacheMass.input gs).tapes (fun _=>[])
def budget {n : ℕ} (gs : List (ExactThresholdGate n)):=
  RowCacheMass.budget gs+3+RowCommonSize.budget (exactListWord gs).length n gs.length

theorem measured_run {n : ℕ} (gs : List (ExactThresholdGate n)) : ∃ H O,
    Step machine (budget gs) (heads gs) (input gs) H O ∧
      O 0=exactListWord gs ∧ H 0=0 ∧ (∀ j,H (slots j)=0) ∧
      (∀ j,O (slots j)=RowCommonSize.output (exactListWord gs).length n gs.length j):=by
  obtain ⟨base,hb,bt,bh,bB,bBh,bn,bnh,bN,bNh,bs⟩:=RowCacheMass.mass_run gs
  have measured : Step RowCacheMass.machine (RowCacheMass.budget gs)
      (RowCacheMass.input gs).heads (RowCacheMass.input gs).tapes base.final.heads base.final.tapes:=
    ⟨base,hb,rfl,rfl,bs.le⟩
  have firstRun:=measured.embed (fun _ : Fin 14=>0) (fun _=>[])
  let H : Fin 21→ℕ:=Fin.addCases (m:=7) (n:=14) (motive:=fun _=>ℕ) base.final.heads (fun _=>0)
  let A : Fin 21→List Bool:=Fin.addCases (m:=7) (n:=14) (motive:=fun _=>List Bool) base.final.tapes (fun _=>[])
  obtain ⟨m,hm,mf,_ms⟩:=DecompositionCountPosition.move_run directions H A
  have moving:=Step.of_run hm (congrArg Configuration.heads mf) (congrArg Configuration.tapes mf)
  let H' : Fin 21→ℕ:=fun i=>(directions i).apply (H i)
  have oldRun : Step first (RowCacheMass.budget gs+2) (heads gs) (input gs) H' A:=firstRun.seq moving
  have hh : ∀ j,H' (slots j)=0:=by
    intro j;fin_cases j
    · exact bBh
    · change base.final.heads 3-1=0;rw [bnh]
    · change base.final.heads 4-1=0;rw [bNh]
    all_goals rfl
  have ha : ∀ j,A (slots j)=RowCommonSize.input (exactListWord gs).length n gs.length j:=by
    intro j;fin_cases j
    · exact bB
    · exact bn
    · exact bN
    all_goals rfl
  obtain ⟨last,hr,lh,lt,_ls⟩:=(RowCommonSize.size_ready (exactListWord gs).length n gs.length).focus_at
    slots slots_injective H' A ha hh
  have finalRun:=oldRun.seq (Step.of_run hr lh lt)
  have time : RowCacheMass.budget gs+2+1+RowCommonSize.budget (exactListWord gs).length n gs.length=
      budget gs:=by unfold budget;omega
  rw [time] at finalRun
  refine ⟨_,_,finalRun,?_,?_,hh,?_⟩
  · exact (install_other slots A _ 0 (by decide)).trans bt
  · exact bh
  · intro j;exact install_slot slots slots_injective A _ j

end NearCubicWires.ExtIncidence.NativeMeasure
