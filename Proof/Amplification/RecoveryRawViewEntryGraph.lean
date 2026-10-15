import Proof.Amplification.RecoveryRawViewEntryCount

/-! Fixed raw-view entry controller: clear the result, physically produce
the outer count, and run the same whole view checker on that produced tape. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRawViewEntry
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryRawView
open RepairSource.VerifierDecoding
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

private abbrev stateCount {t s : Nat} (_ : Machine t s) := s
noncomputable abbrev viewStates := stateCount RecoveryRawViewWhole.machine
noncomputable def flagMachine := TapeEmbedding.machine 1 (RecoveryRawView.flagMachine false)
noncomputable def sizes : Fin 3→Nat := ![2,5,viewStates]
noncomputable def programs : (j : Fin 3)→Machine 66 (sizes j)
  | ⟨0,_⟩=>flagMachine
  | ⟨1,_⟩=>countMachine
  | ⟨2,_⟩=>RecoveryRawViewWhole.machine
  | ⟨n+3,h⟩=>False.elim (by omega)
noncomputable def next : (j : Fin 3)→Fin (sizes j)→(Fin 66→Bool)→Option (Fin 3)
  | ⟨0,_⟩,_,_=>some 1
  | ⟨1,_⟩,q,_=>if q.val=3 then some 2 else none
  | ⟨2,_⟩,_,_=>none
  | ⟨n+3,h⟩,_,_=>False.elim (by omega)
noncomputable def machine := RecoveryCalls.machine sizes programs 0 next

def cursor (x : State) (k n : Nat) : RecoveryRawViewLoop.Cursor := ⟨advanced x n,k+n+1⟩
def viewBudget (width : Nat) := 268435456*(width+1)^4
def countBudget (x : State) := 3*x.limit+3+viewBudget x.width+2
def budget (x : State) := countBudget x+2
def countAnswer (x : State) (word : List Bool) (k : Nat) :=
  (readCount x.limit (word.drop k)).any (fun pair=>RecoveryRawViewWhole.answer word pair.1 (cursor x k pair.1))
def countOutput (x : State) (word : List Bool) (k : Nat) : State×Nat :=
  match readCount x.limit (word.drop k) with
  | none=>(x,0)
  | some (n,_)=>
    (RecoveryRawViewEnd.tested (RecoveryRawViewLoop.out word n (cursor x k n)).2.data,n)
def answer (x : State) (word : List Bool) (k : Nat) := countAnswer (flagged x false) word k
def output (x : State) (word : List Bool) (k : Nat) := countOutput (flagged x false) word k

theorem cursor_valid (x : State) (word : List Bool) (k n : Nat) (hx : x.Valid)
    (hs : x.inner.stream.source=frame word) (hp : x.inner.stream.pos=2*k) :
    RecoveryRawViewLoop.Inv x.width word (cursor x k n) := by
  refine ⟨advanced_valid x n hx,rfl,hs,?_⟩
  change x.inner.stream.pos+2*n+2=2*(k+n+1)
  omega

theorem flag_run (x : State) :
    ∃ r,runFrom flagMachine 1 (RecoveryRawViewEnd.cfg x 0 flagMachine.start)=some r ∧
      r.final=RecoveryRawViewEnd.cfg (flagged x false) 0 1 ∧ r.steps=1 := by
  obtain ⟨base,hr,hf,hs⟩ := RecoveryRawView.flag_run x false
  have h := TapeEmbedding.run_embed (RecoveryRawView.flagMachine false) (fun _ : Fin 1=>1)
    (fun _=>CompareMachine.word 0) 1 _ base hr
  refine ⟨TapeEmbedding.receipt (fun _ : Fin 1=>1) (fun _=>CompareMachine.word 0) base,h,?_,hs⟩
  change TapeEmbedding.config _ _ base.final=_
  rw [hf]
  rfl

end NearCubicWires.RepairOrdinary.RecoveryRawViewEntry
