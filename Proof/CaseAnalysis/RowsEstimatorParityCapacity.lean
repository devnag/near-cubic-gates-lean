import Proof.CaseAnalysis.RowsEstimatorParityBitmap
import Proof.CaseAnalysis.RowsEstimatorDriverPorts

/-! The local parity work driver is physically derived from the retained arity, independently of source capacity. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorParity.Capacity
open LocalBitMultitape RecoveryRootRound ExtDecompositionBatch CloseoutRowsEstimator
open RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def value (q : ℕ):=256*(q+1)^2
def copySlots : Fin 3→Fin 22:=![0,1,2]
def sources : Fin 1→Fin 22:=![1]
def powerSlots : Fin (DimensionPolynomial.tapes 2)→Fin 22:=DriverPorts.slots 4 sources (by decide)
noncomputable def copy:=RecoveryFocus.machine copySlots (UWalkUnary.machine false false)
noncomputable def power:=RecoveryFocus.machine powerSlots (DriverPower.machine 2 256)
noncomputable def core:=Composition.machine copy power
def input (P q : ℕ) : Fin 22→List Bool:=fun i=>if i=0 then UWalkUnary.source P q else []
def direction (left : Bool) : Fin 22→HeadMove:=fun i=>if i=0 then if left then .left else .right else .stay
noncomputable def machine:=Composition.machine
  (Composition.machine (DecompositionCountPosition.move (direction true)) core)
  (DecompositionCountPosition.move (direction false))
def heads (i : Fin 22):=if i=0 then 1 else 0
def budget (q : ℕ):=2*q+11+DriverPower.budget 2 256 q

theorem core_run (P q : ℕ) : ∃ out,
    ClockJoin.ReadyRun core (2*q+6+1+DriverPower.budget 2 256 q) (input P q) out ∧
      out 0=UWalkUnary.source P q ∧out 1=List.replicate q true ∧out 11=List.replicate (value q) true := by
  let firstOut:=install copySlots (input P q) (UWalkUnary.result false false P q)
  have first:ClockJoin.ReadyRun copy (2*q+6) (input P q) firstOut:=
    (UWalkUnary.ready false false P q).focus copySlots (by decide) (input P q) (by intro i;fin_cases i <;>rfl)
  have p0:firstOut 0=UWalkUnary.source P q:=install_slot copySlots (by decide) _ _ 0
  have p1:firstOut 1=List.replicate q true:=by
    change install copySlots _ _ (copySlots 1)=_
    rw [install_slot copySlots (by decide)]
    simp [UWalkUnary.result,UWalkUnary.output,UWalkUnary.lead]
  obtain ⟨made,actual,original,result⟩:=DriverPower.ready 2 256 q
  obtain ⟨out,last,old,_fresh,fields⟩:=DriverPorts.run 4 sources (by decide)
    (by intro i j _;exact Subsingleton.elim i j) (by intro i;fin_cases i;decide)
    (DriverPower.machine 2 256) (DriverPower.budget 2 256 q) firstOut
    (DimensionPolynomial.input 2 q) made actual
    (by intro i;by_cases hi:i.val<1
        · have hz:i=⟨0,by decide⟩:=Fin.ext (by dsimp;omega)
          subst i
          exact p1
        · simp [hi,DimensionPolynomial.input,show i.val≠0 by omega])
    (by intro i hi;have hz:i=⟨0,by decide⟩:=Fin.ext (by dsimp;omega);subst i;exact original)
    (by intro i hi
        rw [show firstOut i=input P q i from install_other copySlots _ _ i (by
          intro j he;fin_cases j <;> have hv:=congrArg Fin.val he <;> simp [copySlots] at hv <;> omega)]
        simp [input,show i≠0 by intro h;subst i;contradiction])
  refine ⟨out,ClockJoin.join copy power _ _ _ _ _ first last,(old 0 (by decide)).trans p0,
    (old 1 (by decide)).trans p1,?_⟩
  exact (fields (DriverPower.valueSlot 2)).trans result

theorem capacity_run (P q : ℕ) : ∃ out,
    Step machine (budget q) heads (input P q) heads out ∧
      out 0=UWalkUnary.source P q ∧out 1=List.replicate q true ∧out 11=List.replicate (value q) true := by
  obtain ⟨out,ready,h0,h1,h11⟩:=core_run P q
  obtain ⟨r0,hr0,rf0,_⟩:=DecompositionCountPosition.move_run (direction true) heads (input P q)
  have first:Step (DecompositionCountPosition.move (direction true)) 1 heads (input P q)
      (fun _=>0) (input P q):=by
    apply Step.of_run hr0 ?_ (by rw [rf0])
    rw [rf0]
    funext i
    by_cases h:i=0 <;> simp [direction,heads,HeadMove.apply,h]
  obtain ⟨r1,hr1,rf1,_⟩:=DecompositionCountPosition.move_run (direction false) (fun _=>0) out
  have last:Step (DecompositionCountPosition.move (direction false)) 1 (fun _=>0) out heads out:=by
    apply Step.of_run hr1 ?_ (by rw [rf1])
    rw [rf1]
    funext i
    by_cases h:i=0 <;> simp [direction,heads,HeadMove.apply,h]
  obtain ⟨r,hr,rt,rh,rs⟩:=ready
  have middle:Step core (2*q+6+1+DriverPower.budget 2 256 q) (fun _=>0) (input P q) (fun _=>0) out:=
    ⟨r,hr,funext rh,rt,rs⟩
  have full:=(first.seq middle).seq last
  have ht:1+1+(2*q+6+1+DriverPower.budget 2 256 q)+1+1=budget q:=by unfold budget;omega
  rw [ht] at full
  exact ⟨out,full,h0,h1,h11⟩

theorem budget_bound (q : ℕ) : budget q≤42*(value q+1) := by
  have h:=DriverPower.budget_linear 2 256 q (by decide) (by decide)
  simp only [budget,value] at *
  nlinarith

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorParity.Capacity
