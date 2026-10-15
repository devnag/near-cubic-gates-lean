import Proof.MachineModel.ClosureRawRelabelMachine
import Proof.MachineModel.Runs

/-! Physically form the runtime offset N*yi+1 from retained unary N and yi.
The offset tape starts empty; the leading sentinel and one are constant bytes.
All four heads return to zero, with the full reset log preserved. -/
namespace NearCubicWires.P1Closure.RawRelabelOffset
open LocalBitMultitape RepairOrdinary RecoveryExecution ExtDecompositionBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def seed : Machine 3 3 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>decide (q=2)
  rule:=fun q _=>if q=0 then some ⟨1,![none,none,some false],![.stay,.stay,.right]⟩
    else if q=1 then some ⟨2,![none,none,some true],![.stay,.stay,.right]⟩ else none

def raw:=Composition.machine seed ClockUnaryProduct.raw
def machine:=MaskedReset.machine raw (fun _=>true)
def rawBudget (N yi : ℕ):=N*(2*yi+3)+5
def budget (N yi : ℕ):=2*rawBudget N yi+2
def input (N yi L : ℕ) : Fin 4→List Bool:=
  ![List.replicate N true,false::List.replicate yi true,[],List.replicate L false]
def output (N yi L : ℕ) : Fin 4→List Bool:=
  ![List.replicate N true,false::List.replicate yi true,false::List.replicate (N*yi+1) true,
    List.replicate L false]

theorem seed_run (A B : List Bool) :
    Step seed 2 (fun _=>0) ![A,B,[]] ![0,0,2] ![A,B,[false,true]] := by
  let cfg (s : Fin 3) (out : List Bool) : Configuration 3 3:=⟨s,![0,0,out.length],![A,B,out]⟩
  have first:step seed (cfg 0 [])=some (cfg 1 [false]):=by
    apply congrArg some
    apply configuration_ext
    · rfl
    · funext i;fin_cases i <;> rfl
    · funext i;fin_cases i <;> rfl
  have last:step seed (cfg 1 [false])=some (cfg 2 [false,true]):=by
    apply congrArg some
    apply configuration_ext
    · rfl
    · funext i;fin_cases i <;> rfl
    · funext i;fin_cases i <;> rfl
  obtain ⟨r,hr,hf,_⟩:=((Timed.single (by rfl) first).trans (Timed.single (by rfl) last)).run (by rfl)
  have h:=Step.of_run hr (congrArg Configuration.heads hf) (congrArg Configuration.tapes hf)
  exact h.congr_in (by funext i;fin_cases i <;> rfl) rfl

theorem product_run (N yi : ℕ) :
    Step ClockUnaryProduct.raw (N*(2*yi+3)+2) ![0,0,2]
      ![List.replicate N true,false::List.replicate yi true,[false,true]]
      ![N,1,N*yi+2]
      ![List.replicate N true,false::List.replicate yi true,false::List.replicate (N*yi+1) true] := by
  have hp:=ClockUnaryProduct.loop_prefix N yi 0 N [false,true] (by simp)
  have boot:step ClockUnaryProduct.raw (ClockUnaryProduct.config 0 N yi 0 0 [false,true])=
      some (ClockUnaryProduct.config 1 N yi 0 1 [false,true]):=by
    simp [step,ClockUnaryProduct.raw,ClockUnaryProduct.config]
    apply configuration_ext
    · rfl
    · funext i;fin_cases i <;> simp [applyAction,ClockUnaryProduct.action,HeadMove.apply]
    · funext i;fin_cases i <;> simp [applyAction,ClockUnaryProduct.action]
  have h:=Prefix.step (by simp) (by rfl) boot hp
  obtain ⟨r,hr,hf,_,_⟩:=h.run (by rfl) (by simp;omega)
  have word:[false,true]++List.replicate (N*yi) true=false::List.replicate (N*yi+1) true:=by
    rw [List.replicate_succ];rfl
  have hstep:=Step.of_run hr (congrArg Configuration.heads hf) (congrArg Configuration.tapes hf)
  have cost:N*(2*yi+3)+1+1=N*(2*yi+3)+2:=by omega
  rw [cost] at hstep
  refine hstep.congr ?_ ?_
  · funext i;fin_cases i <;> simp [ClockUnaryProduct.config,Nat.add_comm]
    omega
  · simp only [ClockUnaryProduct.config,word]

theorem run (N yi L : ℕ) (hL : rawBudget N yi≤L) :
    Step machine (budget N yi) (fun _=>0) (input N yi L) (fun _=>0) (output N yi L) := by
  have first:=seed_run (List.replicate N true) (false::List.replicate yi true)
  have second:=product_run N yi
  have combined:=first.seq second
  have cost:2+1+(N*(2*yi+3)+2)=rawBudget N yi:=by unfold rawBudget;omega
  rw [cost] at combined
  have reset:=combined.mask (fun _=>true) (by intros;rfl) hL
  refine (reset.congr_in ?_ ?_).congr ?_ ?_
  all_goals funext i;fin_cases i <;> rfl

end NearCubicWires.P1Closure.RawRelabelOffset
