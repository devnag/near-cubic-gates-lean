import Proof.MachineModel.OrdinaryMatrixScoreAccumulate
import Proof.CaseAnalysis.WitnessHeaderSwitch
import Proof.MachineModel.Layout

/-! The two actual support flags select the existing binary accumulator.
Excluded scores skip old hits; withCandidated scores also skip the candidate.
Both control paths retain the flags, scalar source, and all tape heads. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsTouching.ScoreAdd
open LocalBitMultitape ExtDecompositionBatch RecoveryRootRound RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def probe : Machine 7 1 where
  descriptionBits:=0
  start:=0
  halted:=fun _=>true
  rule:=fun _ _=>none
noncomputable def add:=TapeEmbedding.machine 2 MatrixScoreAccumulate.machine
def skip (withCandidate hit cur : Bool):=hit || (withCandidate && cur)
def good (withCandidate : Bool) (bits : Fin 7→Bool):= !(skip withCandidate (bits 5) (bits 6))
noncomputable def machine (withCandidate : Bool):=
  CloseoutWitness.HeaderSwitch.machine probe add probe (good withCandidate) (fun _=>true)
def input (w x a P : ℕ) (backing : List Bool) (hit cur : Bool) (i : Fin 7):List Bool:=
  Fin.addCases (m:=5) (n:=2) (motive:=fun _=>List Bool)
    (MatrixScoreAccumulate.input w x a backing) ![ZeroPadding.pad P [hit],ZeroPadding.pad P [cur]] i
def added (w x a P : ℕ) (hit cur : Bool) (i : Fin 7):List Bool:=
  Fin.addCases (m:=5) (n:=2) (motive:=fun _=>List Bool)
    (MatrixScoreAccumulate.output w x a) ![ZeroPadding.pad P [hit],ZeroPadding.pad P [cur]] i

theorem probe_run (A : Fin 7→List Bool):Step probe 0 (fun _=>0) A (fun _=>0) A:=by
  obtain ⟨r,hr,hf,_⟩:=(Timed.refl probe (⟨0,fun _=>0,A⟩ : Configuration 7 1)).run (by rfl)
  exact Step.of_run hr (congrArg Configuration.heads hf) (congrArg Configuration.tapes hf)

theorem flag_read (withCandidate hit cur : Bool) (w x a P : ℕ) (backing : List Bool):
    good withCandidate (fun i=>readTapeBit (input w x a P backing hit cur i) 0)= !(skip withCandidate hit cur):=by
  unfold good skip
  have h1:readTapeBit (input w x a P backing hit cur 5) 0=hit:=by
    change readTapeBit (ZeroPadding.pad P [hit]) 0=hit
    rw [ZeroPadding.read_pad];rfl
  have h2:readTapeBit (input w x a P backing hit cur 6) 0=cur:=by
    change readTapeBit (ZeroPadding.pad P [cur]) 0=cur
    rw [ZeroPadding.read_pad];rfl
  change (!(readTapeBit (input w x a P backing hit cur 5) 0 || withCandidate && readTapeBit (input w x a P backing hit cur 6) 0))=_
  rw [h1,h2]

theorem add_run (withCandidate hit cur : Bool) (w x a P : ℕ) (backing : List Bool)
    (hb:backing.length≤2*w+1) (hfit:skip withCandidate hit cur=false→x+a<2^w):
    Step (machine withCandidate) (12*w+15) (fun _=>0) (input w x a P backing hit cur)
      (fun _=>0) (if skip withCandidate hit cur then input w x a P backing hit cur else added w x a P hit cur):=by
  obtain ⟨first,hr,hh,ht,_⟩:=probe_run (input w x a P backing hit cur)
  have read:good withCandidate first.final.scanned= !(skip withCandidate hit cur):=by
    change good withCandidate (fun i=>readTapeBit (first.final.tapes i) (first.final.heads i))=_
    rw [hh,ht]
    exact flag_read withCandidate hit cur w x a P backing
  cases hs:skip withCandidate hit cur with
  | true=>
    obtain ⟨r,rr,rs,rh,rt⟩:=CloseoutWitness.HeaderSwitch.rejected probe add probe (good withCandidate)
      (fun _=>true) 0 (fun _=>0) (input w x a P backing hit cur) first hr (by rw [read,hs];rfl)
    have result:Step (machine withCandidate) 1 (fun _=>0) (input w x a P backing hit cur)
        (fun _=>0) (input w x a P backing hit cur):=⟨r,rr,rh.trans hh,rt.trans ht,rs⟩
    simpa [hs] using result.enlarge (m:=12*w+15) (by omega)
  | false=>
    have worker:=(Step.of_ready (MatrixScoreAccumulate.accumulate_ready w x a backing (hfit hs) hb)).embed
      (fun _ : Fin 2=>0) (![ZeroPadding.pad P [hit],ZeroPadding.pad P [cur]] : Fin 2→List Bool)
    have worked:Step add (12*w+13) (fun _=>0) (input w x a P backing hit cur)
        (fun _=>0) (added w x a P hit cur):=by
      refine worker.congr_in ?_ rfl |>.congr ?_ rfl
      all_goals funext i;fin_cases i <;> rfl
    obtain ⟨last,lr,lh,lt,_⟩:=worked
    obtain ⟨r,rr,rs,rh,rt⟩:=CloseoutWitness.HeaderSwitch.accepted probe add probe (good withCandidate)
      (fun _=>true) 1 (Or.inl rfl) 0 (12*w+13) (fun _=>0) (input w x a P backing hit cur) first last hr
      (by rw [hh,ht];exact lr) (by rw [read,hs];rfl) rfl
    have result:Step (machine withCandidate) (0+1+(12*w+13)+1) (fun _=>0) (input w x a P backing hit cur)
        (fun _=>0) (added w x a P hit cur):=by
      refine ⟨r,rr,?_,rt.trans lt,rs⟩
      exact rh.trans lh
    simpa [hs] using result.enlarge (m:=12*w+15) (by omega)

end NearCubicWires.RepairOrdinary.CloseoutRowsTouching.ScoreAdd
