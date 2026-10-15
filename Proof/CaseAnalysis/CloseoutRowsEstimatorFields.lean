import Proof.CaseAnalysis.RowsEstimatorScanRun
import Proof.PCP.ProjectionDimensionTemplate
import Proof.Supplier.EquationCountTools

/-! Produce the scanner's field-count template from the actual retained
raw d and parity bit using the existing paid dimension/count workers. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Fields
open LocalBitMultitape RecoveryRootRound RepairSource.ProjectionNormalization
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def ds : Fin 3→Fin 10:=![0,2,3]
def ws : Fin 4→Fin 10:=![2,1,4,5]
def us : Fin 3→Fin 10:=![4,6,7]
def ns : Fin 3→Fin 10:=![6,8,9]
def w (d : ℕ) (odd : Bool):=2*d-odd.toNat

def input (d : ℕ) (odd : Bool) : Fin 10→List Bool:=
  ![List.replicate d true,[odd],[],[],[],[],[],[],[],[]]
def a1 (d : ℕ) (odd : Bool) (i : Fin 10) : List Bool:=
  if i=2 then UnaryTemplate.tape d else if i=3 then List.replicate (d+3) false else input d odd i
def a2 (d : ℕ) (odd : Bool) (i : Fin 10) : List Bool:=
  if i=4 then CompareMachine.word (w d odd)
  else if i=5 then List.replicate (EquationWeightCount.ticks d odd) false else a1 d odd i
def a3 (d : ℕ) (odd : Bool) (i : Fin 10) : List Bool:=
  if i=6 then List.replicate (w d odd+1) true
  else if i=7 then List.replicate (w d odd+2) false else a2 d odd i
def output (d : ℕ) (odd : Bool) (i : Fin 10) : List Bool:=
  if i=8 then UnaryTemplate.tape (w d odd+2)
  else if i=9 then List.replicate (w d odd+4) false else a3 d odd i

noncomputable def first:=RecoveryFocus.machine ds (DimensionTemplate.machine false)
noncomputable def second:=RecoveryFocus.machine ws EquationWeightCount.machine
noncomputable def third:=RecoveryFocus.machine us (UWalkUnary.machine false true)
noncomputable def fourth:=RecoveryFocus.machine ns (DimensionTemplate.machine true)
noncomputable def machine:=Composition.machine (Composition.machine (Composition.machine first second) third) fourth
def budget (d : ℕ) (odd : Bool):=6*d+4*w d odd+33

theorem first_ready (d : ℕ) (odd : Bool) :
    ClockJoin.ReadyRun first (2*d+8) (input d odd) (a1 d odd):=by
  have h:=(DimensionTemplate.ready false d).focus ds (by decide) (input d odd)
    (by intro j;fin_cases j <;> rfl)
  have he:=HierarchyWidth.install_eq ds (by decide) (input d odd) (a1 d odd)
    (DimensionTemplate.output false d)
    (by intro j;fin_cases j <;> rfl)
    (by
      intro i hi
      have h2:i≠2:=fun h=>hi 1 h.symm
      have h3:i≠3:=fun h=>hi 2 h.symm
      simp only [a1,h2,h3,ite_false])
  rw [he] at h
  exact h

theorem second_ready (d : ℕ) (odd : Bool) :
    ClockJoin.ReadyRun second (4*d+6) (a1 d odd) (a2 d odd):=by
  have h:=(EquationWeightCount.ready d odd).focus ws (by decide) (a1 d odd)
    (by intro j;fin_cases j <;> rfl)
  have he:=HierarchyWidth.install_eq ws (by decide) (a1 d odd) (a2 d odd)
    (EquationWeightCount.result d odd)
    (by intro j;fin_cases j <;> rfl)
    (by
      intro i hi
      have h4:i≠4:=fun h=>hi 2 h.symm
      have h5:i≠5:=fun h=>hi 3 h.symm
      simp only [a2,h4,h5,ite_false])
  rw [he] at h
  exact h

theorem third_input (d : ℕ) (odd : Bool) (j : Fin 3) :
    a2 d odd (us j)=(![CompareMachine.word (w d odd),[],[]] : Fin 3→List Bool) j:=by
  fin_cases j <;> rfl

theorem third_output (d : ℕ) (odd : Bool) :
    install us (a2 d odd)
      ![CompareMachine.word (w d odd),UWalkUnary.output false true (w d odd),List.replicate (w d odd+2) false]
      =a3 d odd:=by
  apply HierarchyWidth.install_eq us (by decide)
  · intro j;fin_cases j <;> rfl
  · intro i hi
    have h6:i≠6:=fun h=>hi 1 h.symm
    have h7:i≠7:=fun h=>hi 2 h.symm
    simp only [a3,h6,h7,ite_false]

theorem third_ready (d : ℕ) (odd : Bool) :
    ClockJoin.ReadyRun third (2*w d odd+6) (a2 d odd) (a3 d odd):=by
  obtain ⟨r,hr,rt,rh,rs⟩:=(EquationCountTools.word_ready false true (w d odd)).focus us
    (by decide) (a2 d odd) (third_input d odd)
  exact ⟨r,hr,rt.trans (third_output d odd),rh,rs⟩

theorem fourth_input (d : ℕ) (odd : Bool) (j : Fin 3) :
    a3 d odd (ns j)=DimensionTemplate.input (w d odd+1) j:=by
  fin_cases j <;> rfl

theorem fourth_output (d : ℕ) (odd : Bool) :
    install ns (a3 d odd) (DimensionTemplate.output true (w d odd+1))=output d odd:=by
  apply HierarchyWidth.install_eq ns (by decide)
  · intro j;fin_cases j <;> rfl
  · intro i hi
    have h8:i≠8:=fun h=>hi 1 h.symm
    have h9:i≠9:=fun h=>hi 2 h.symm
    simp only [output,h8,h9,ite_false]

theorem fourth_ready (d : ℕ) (odd : Bool) :
    ClockJoin.ReadyRun fourth (2*(w d odd+1)+8) (a3 d odd) (output d odd):=by
  obtain ⟨r,hr,rt,rh,rs⟩:=(DimensionTemplate.ready true (w d odd+1)).focus ns
    (by decide) (a3 d odd) (fourth_input d odd)
  exact ⟨r,hr,rt.trans (fourth_output d odd),rh,rs⟩

theorem ready (d : ℕ) (odd : Bool) :
    ClockJoin.ReadyRun machine (budget d odd) (input d odd) (output d odd):=by
  have h:=ClockJoin.join _ _ _ _ _ _ _
    (ClockJoin.join _ _ _ _ _ _ _
      (ClockJoin.join _ _ _ _ _ _ _ (first_ready d odd) (second_ready d odd))
      (third_ready d odd)) (fourth_ready d odd)
  have ht:(((2*d+8)+1+(4*d+6))+1+(2*w d odd+6))+1+(2*(w d odd+1)+8)=budget d odd:=by
    unfold budget;omega
  rw [ht] at h
  exact h

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Fields
