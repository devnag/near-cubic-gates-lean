import Proof.Supplier.RowCommonTupleDimensions

/-! Add the actual degree Q to the native base width, including an empty
cache, and print the exact signed-field driver. All four calls are paid. -/
namespace NearCubicWires.ExtIncidence.NativeFieldWidth
open LocalBitMultitape RepairOrdinary
open RepairOrdinary.RecoveryRootRound
open RepairOrdinary.RowCommonSize (put focus_put)
open RepairSource.ProjectionNormalization RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def input (u Q : ℕ) : RowCommonSize.Store:=fun i=>
  if i=0 then List.replicate u true else if i=1 then UnaryTemplate.tape Q else []
def data1 (u Q : ℕ):=put (input u Q) 2 3 (List.replicate Q true) (List.replicate (Q+2) false)
def data2 (u Q : ℕ):=put (data1 u Q) 4 5 (List.replicate (u+Q) true) (List.replicate (u+Q+2) false)
def data3 (u Q : ℕ):=put (data2 u Q) 6 7 (UnaryTemplate.tape (u+Q)) (List.replicate (u+Q+3) false)
def output (u Q : ℕ):=put (data3 u Q) 8 9 (CompareMachine.word (u+Q+1)) (List.replicate (u+Q+2) false)
def s1 : Fin 3→Fin 17:=![1,2,3]
def s2 : Fin 4→Fin 17:=![0,2,4,5]
def s3 : Fin 3→Fin 17:=![4,6,7]
def s4 : Fin 3→Fin 17:=![6,8,9]
noncomputable def phase1:=RecoveryFocus.machine s1 (UWalkUnary.machine false false)
noncomputable def phase2:=RecoveryFocus.machine s2 ClockUnarySum.machine
noncomputable def phase3:=RecoveryFocus.machine s3 (DimensionTemplate.machine false)
noncomputable def phase4:=RecoveryFocus.machine s4 (UWalkUnary.machine true true)
noncomputable def machine:=Composition.machine (Composition.machine (Composition.machine phase1 phase2) phase3) phase4
def budget (u Q : ℕ):=2*Q+6*(u+Q)+29

theorem ready1 (u Q : ℕ) : ClockJoin.ReadyRun phase1 (2*Q+6) (input u Q) (data1 u Q):=by
  apply focus_put _ _ _ _ (DecompositionCountDrivers.template_ready false false Q) s1 (by decide) _ 1 2
  · intro i;fin_cases i <;> simp [input,s1]
  · intro i;fin_cases i <;> simp [put,input,s1,UWalkUnary.output,UWalkUnary.lead]
theorem ready2 (u Q : ℕ) : ClockJoin.ReadyRun phase2 (2*(u+Q)+6) (data1 u Q) (data2 u Q):=by
  apply focus_put _ _ _ _ (ClockUnarySum.sum_ready u Q) s2 (by decide) _ 2 3
  · intro i;fin_cases i <;> simp [data1,put,input,s2]
  · intro i;fin_cases i <;> simp [data1,put,input,s2]
theorem ready3 (u Q : ℕ) : ClockJoin.ReadyRun phase3 (2*(u+Q)+8) (data2 u Q) (data3 u Q):=by
  apply focus_put _ _ _ _ (DimensionTemplate.ready false (u+Q)) s3 (by decide) _ 1 2
  · intro i;fin_cases i <;> simp [data2,data1,put,input,s3,DimensionTemplate.input]
  · intro i;fin_cases i <;> simp [data2,put,s3,DimensionTemplate.output]
theorem ready4 (u Q : ℕ) : ClockJoin.ReadyRun phase4 (2*(u+Q)+6) (data3 u Q) (output u Q):=by
  apply focus_put _ _ _ _ (DecompositionCountDrivers.template_ready true true (u+Q)) s4 (by decide) _ 1 2
  · intro i;fin_cases i <;> simp [data3,data2,data1,put,input,s4]
  · intro i;fin_cases i <;> simp [data3,put,s4,UWalkUnary.output,UWalkUnary.lead,CompareMachine.word]
theorem ready (u Q : ℕ) : ClockJoin.ReadyRun machine (budget u Q) (input u Q) (output u Q):=by
  have h:=ClockJoin.join _ _ _ _ _ _ _
    (ClockJoin.join _ _ _ _ _ _ _ (ClockJoin.join _ _ _ _ _ _ _ (ready1 u Q) (ready2 u Q))
      (ready3 u Q)) (ready4 u Q)
  have time : (2*Q+6)+1+(2*(u+Q)+6)+1+(2*(u+Q)+8)+1+(2*(u+Q)+6)=budget u Q:=by
    unfold budget;omega
  rw [time] at h
  exact h

end NearCubicWires.ExtIncidence.NativeFieldWidth
