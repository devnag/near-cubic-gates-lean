import Proof.SourceAssembly.SourceParityQuery
import Proof.SourceAssembly.SourceParitySymmetricBody

/- One bitmap scan writes the exact identity bottoms and declared supports,
and simultaneously produces their actual count. The finite program is fixed. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace SourceAssemblySymmetricScan
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open CloseoutRowsEstimatorParity RecoveryRootRound RepairSource.VerifierDecoding
open CloseoutRowsEstimator
noncomputable section

def H (pos : Nat) (out : Fin 2→List Bool) : Fin 8→Nat:=
  Fin.addCases (motive:=fun _=>Nat) (SymmetricBody.H pos out) (fun _ : Fin 1=>1)
def A (q j n C : Nat) (tail bits : List Bool) (out : Fin 2→List Bool) : Fin 8→List Bool:=
  Fin.addCases (motive:=fun _=>List Bool) (SymmetricBody.A q j C tail bits out) (fun _ : Fin 1=>CompareMachine.word n)
def countSlots : Fin 1→Fin 8:=![7]
def count:=RecoveryFocus.machine countSlots Counter.machine
def idle:=SubstitutionRepeat.idle 8
def test (bs : Fin 8→Bool):=bs 6
def guard:=CloseoutRowsGateColdPair.machine idle count test
def writer:=TapeEmbedding.machine 1 SymmetricBody.machine
def body:=Composition.machine guard writer
def cost (q : Nat):=2*q+5+SymmetricBody.cost q

theorem increment (q j n C pos : Nat) (tail bits : List Bool) (out : Fin 2→List Bool) :
    Step count (2*n+2) (H pos out) (A q j n C tail bits out)
      (H pos out) (A q j (n+1) C tail bits out) := by
  refine SubstitutionDock.run _ _ (by decide) _ _ _ _ _ _ _ _ (Counter.increment_run n)
    ?_ ?_ ?_ ?_ ?_ ?_
  all_goals first
  | (intro i;fin_cases i <;>rfl)
  | (intro i hi;fin_cases i <;>first | rfl | exact False.elim (hi 0 rfl))

theorem idle_run (q j n C pos : Nat) (tail bits : List Bool) (out : Fin 2→List Bool) :
    Step idle 0 (H pos out) (A q j n C tail bits out) (H pos out) (A q j n C tail bits out) := by
  exact Step.of_run (rfl : runFrom idle 0 ⟨0,H pos out,A q j n C tail bits out⟩=
    some ⟨⟨0,H pos out,A q j n C tail bits out⟩,0,(⟨0,H pos out,A q j n C tail bits out⟩ : Configuration 8 1).tapeCells⟩) rfl rfl

theorem guard_run (b : Bool) (q j n C pos : Nat) (tail bits : List Bool) (out : Fin 2→List Bool)
    (hb : readTapeBit bits pos=b) :
    Step guard (2*n+4) (H pos out) (A q j n C tail bits out)
      (H pos out) (A q j (n+b.toNat) C tail bits out) := by
  cases b with
  | false=>
    exact (CloseoutRowsSupportStream.rejected_step count (idle_run q j n C pos tail bits out) test hb).enlarge (by omega)
  | true=>
    exact (CloseoutRowsSupportStream.guarded_step (idle_run q j n C pos tail bits out)
      (increment q j n C pos tail bits out) test hb).enlarge (by omega)

theorem body_run (b : Bool) (q j n C pos : Nat) (tail bits : List Bool) (out : Fin 2→List Bool)
    (hj : j<q) (hn : n ≤ q) (hC : 2*(natWord q).length+1 ≤ C) (hb : readTapeBit bits pos=b) :
    Step body (cost q) (H pos out) (A q j n C tail bits out)
      (H (pos+1) (SymmetricBody.append b q j out))
      (A q (j+1) (n+b.toNat) C tail bits (SymmetricBody.append b q j out)) := by
  exact ((guard_run b q j n C pos tail bits out hb).seq
    ((SymmetricBody.body_run b q j C pos tail bits out hj hC hb).embed
      (fun _ : Fin 1=>1) (fun _ : Fin 1=>CompareMachine.word (n+b.toNat)))).enlarge (by unfold cost;omega)

def selected (bits : List Bool) (j : Nat):=(List.range j).filter (fun k=>readTapeBit bits k)
def outputs (q : Nat) (bits : List Bool) (j : Nat) : Fin 2→List Bool:=
  fun i=>(selected bits j).flatMap (fun k=>SymmetricBody.emitted q k i)
theorem selected_succ (bits : List Bool) (j : Nat) :
    selected bits (j+1)=selected bits j++if readTapeBit bits j then [j] else [] := by
  simp only [selected,List.range_succ,List.filter_append]
  cases h:readTapeBit bits j <;>simp [h]
theorem count_succ (bits : List Bool) (j : Nat) :
    (selected bits (j+1)).length=(selected bits j).length+(readTapeBit bits j).toNat := by
  rw [selected_succ,List.length_append]
  cases readTapeBit bits j <;>rfl
theorem outputs_succ (q : Nat) (bits : List Bool) (j : Nat) :
    outputs q bits (j+1)=SymmetricBody.append (readTapeBit bits j) q j (outputs q bits j) := by
  funext i
  simp only [outputs,selected_succ,List.flatMap_append,SymmetricBody.append]
  cases readTapeBit bits j <;>simp

def machine:=CloseoutRowsDegreeLoop.machine body
def source {s : Nat} (p : Machine 8 s) (q C : Nat) (tail bits : List Bool) (j : Nat) : Configuration 8 s:=
  ⟨p.start,H j (outputs q bits j),A q j (selected bits j).length C tail bits (outputs q bits j)⟩
def budget (q : Nat):=q*(cost q+3)+3

theorem run (q C : Nat) (tail bits : List Bool) (hC : 2*(natWord q).length+1 ≤ C) :
    ∃ r,runFrom machine (budget q) (RepeatMachine.cfg 0 (source body q C tail bits 0) q 1)=some r ∧
      r.final=RepeatMachine.cfg 3 (source body q C tail bits q) q 1 ∧r.steps ≤ budget q := by
  apply CloseoutRowsDegreeLoop.loop_run body (fun j _=>source body q C tail bits j) (fun _=>[]) (cost q) q
    (by intro j hj out;rfl) _ []
  intro j hj out
  have hn : (selected bits j).length ≤ q:=
    (List.length_filter_le _ _).trans (by simp;omega)
  have actual:=body_run (readTapeBit bits j) q j (selected bits j).length C j tail bits (outputs q bits j)
    hj hn hC rfl
  rw [←count_succ,←outputs_succ] at actual
  exact actual

end
end SourceAssemblySymmetricScan
