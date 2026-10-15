import Proof.Supplier.RowCommonResources
import Proof.PCP.ProjectionDimensionTemplate

/-! The common occurrence bound N*Q and output width w*N*Q are computed
from their actual retained unary drivers. The signed-field driver p+1 is
printed in precisely the CompareMachine representation of the row bank. -/
namespace NearCubicWires.RepairOrdinary.RowCommonTupleDimensions
open LocalBitMultitape RecoveryRootRound
open RepairSource.ProjectionNormalization RepairSource.VerifierDecoding
open RowCommonSize (put focus_put)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def input (w N Q : ℕ) : RowCommonSize.Store := fun i=>
  if i=0 then List.replicate w true else if i=1 then UnaryTemplate.tape N
  else if i=2 then UnaryTemplate.tape Q else []
def data1 (w N Q : ℕ) := put (input w N Q) 3 4
  (List.replicate N true) (List.replicate (N+2) false)
def data2 (w N Q : ℕ) := put (data1 w N Q) 5 6
  (List.replicate (N*Q) true) (List.replicate (WilliamsUnaryProduct.scratch N Q) false)
def data3 (w N Q : ℕ) := put (data2 w N Q) 7 8
  (UnaryTemplate.tape (N*Q)) (List.replicate (N*Q+3) false)
def data4 (w N Q : ℕ) := put (data3 w N Q) 9 10
  (List.replicate (w*(N*Q)) true) (List.replicate (WilliamsUnaryProduct.scratch w (N*Q)) false)
def data5 (w N Q : ℕ) := put (data4 w N Q) 11 12
  (UnaryTemplate.tape (w*(N*Q))) (List.replicate (w*(N*Q)+3) false)
def output (w N Q : ℕ) := put (data5 w N Q) 13 14
  (CompareMachine.word (w*(N*Q)+1)) (List.replicate (w*(N*Q)+2) false)
def slots1 : Fin 3→Fin 17 := ![1,3,4]
def slots2 : Fin 4→Fin 17 := ![3,2,5,6]
def slots3 : Fin 3→Fin 17 := ![5,7,8]
def slots4 : Fin 4→Fin 17 := ![0,7,9,10]
def slots5 : Fin 3→Fin 17 := ![9,11,12]
def slots6 : Fin 3→Fin 17 := ![11,13,14]
noncomputable def phase1 := RecoveryFocus.machine slots1 (UWalkUnary.machine false false)
noncomputable def phase2 := RecoveryFocus.machine slots2 ClockUnaryProduct.machine
noncomputable def phase3 := RecoveryFocus.machine slots3 (DimensionTemplate.machine false)
noncomputable def phase4 := RecoveryFocus.machine slots4 ClockUnaryProduct.machine
noncomputable def phase5 := RecoveryFocus.machine slots5 (DimensionTemplate.machine false)
noncomputable def phase6 := RecoveryFocus.machine slots6 (UWalkUnary.machine true true)
noncomputable def first := Composition.machine phase1 phase2
noncomputable def second := Composition.machine first phase3
noncomputable def third := Composition.machine second phase4
noncomputable def fourth := Composition.machine third phase5
noncomputable def machine := Composition.machine fourth phase6
def budget (w N Q : ℕ) := (2*N+6)+WilliamsUnaryProduct.budget N Q+(2*(N*Q)+8)+
  WilliamsUnaryProduct.budget w (N*Q)+(2*(w*(N*Q))+8)+(2*(w*(N*Q))+6)+5

theorem ready1 (w N Q : ℕ) : ClockJoin.ReadyRun phase1 (2*N+6) (input w N Q) (data1 w N Q) := by
  apply focus_put _ _ _ _ (DecompositionCountDrivers.template_ready false false N) slots1 (by decide) _ 1 2
  · intro i; fin_cases i <;> simp [input,slots1]
  · intro i; fin_cases i <;> simp [put,input,slots1,UWalkUnary.output,UWalkUnary.lead]
theorem ready2 (w N Q : ℕ) : ClockJoin.ReadyRun phase2 (WilliamsUnaryProduct.budget N Q)
    (data1 w N Q) (data2 w N Q) := by
  apply focus_put _ _ _ _ (RowCommonResources.product_ready N Q) slots2 (by decide) _ 2 3
  · intro i; fin_cases i <;> simp [data1,put,input,slots2,WilliamsUnaryProduct.input]
  · intro i; fin_cases i <;> simp [data1,put,input,slots2,WilliamsUnaryProduct.output]
theorem ready3 (w N Q : ℕ) : ClockJoin.ReadyRun phase3 (2*(N*Q)+8) (data2 w N Q) (data3 w N Q) := by
  apply focus_put _ _ _ _ (DimensionTemplate.ready false (N*Q)) slots3 (by decide) _ 1 2
  · intro i; fin_cases i <;> simp [data2,data1,put,input,slots3,DimensionTemplate.input]
  · intro i; fin_cases i <;> simp [data2,put,slots3,DimensionTemplate.output]
theorem ready4 (w N Q : ℕ) : ClockJoin.ReadyRun phase4 (WilliamsUnaryProduct.budget w (N*Q))
    (data3 w N Q) (data4 w N Q) := by
  apply focus_put _ _ _ _ (RowCommonResources.product_ready w (N*Q)) slots4 (by decide) _ 2 3
  · intro i; fin_cases i <;> simp [data3,data2,data1,put,input,slots4,WilliamsUnaryProduct.input]
  · intro i; fin_cases i <;> simp [data3,data2,data1,put,input,slots4,WilliamsUnaryProduct.output]
theorem ready5 (w N Q : ℕ) : ClockJoin.ReadyRun phase5 (2*(w*(N*Q))+8) (data4 w N Q) (data5 w N Q) := by
  apply focus_put _ _ _ _ (DimensionTemplate.ready false (w*(N*Q))) slots5 (by decide) _ 1 2
  · intro i; fin_cases i <;> simp [data4,data3,data2,data1,put,input,slots5,DimensionTemplate.input]
  · intro i; fin_cases i <;> simp [data4,put,slots5,DimensionTemplate.output]
theorem ready6 (w N Q : ℕ) : ClockJoin.ReadyRun phase6 (2*(w*(N*Q))+6) (data5 w N Q) (output w N Q) := by
  apply focus_put _ _ _ _ (DecompositionCountDrivers.template_ready true true (w*(N*Q))) slots6 (by decide) _ 1 2
  · intro i; fin_cases i <;> simp [data5,data4,data3,data2,data1,put,input,slots6]
  · intro i; fin_cases i <;> simp [data5,put,slots6,UWalkUnary.output,UWalkUnary.lead,CompareMachine.word]

private theorem first_ready (w N Q : ℕ) : ClockJoin.ReadyRun first
    ((2*N+6)+1+WilliamsUnaryProduct.budget N Q) (input w N Q) (data2 w N Q) :=
  ClockJoin.join phase1 phase2 _ _ _ _ _ (ready1 w N Q) (ready2 w N Q)
private theorem second_ready (w N Q : ℕ) : ClockJoin.ReadyRun second
    (((2*N+6)+1+WilliamsUnaryProduct.budget N Q)+1+(2*(N*Q)+8)) (input w N Q) (data3 w N Q) :=
  ClockJoin.join first phase3 _ _ _ _ _ (first_ready w N Q) (ready3 w N Q)
private theorem third_ready (w N Q : ℕ) : ClockJoin.ReadyRun third
    ((((2*N+6)+1+WilliamsUnaryProduct.budget N Q)+1+(2*(N*Q)+8))+1+WilliamsUnaryProduct.budget w (N*Q))
    (input w N Q) (data4 w N Q) :=
  ClockJoin.join second phase4 _ _ _ _ _ (second_ready w N Q) (ready4 w N Q)
private theorem fourth_ready (w N Q : ℕ) : ClockJoin.ReadyRun fourth
    (((((2*N+6)+1+WilliamsUnaryProduct.budget N Q)+1+(2*(N*Q)+8))+1+WilliamsUnaryProduct.budget w (N*Q))+1+(2*(w*(N*Q))+8))
    (input w N Q) (data5 w N Q) :=
  ClockJoin.join third phase5 _ _ _ _ _ (third_ready w N Q) (ready5 w N Q)
theorem dimensions_ready (w N Q : ℕ) : ClockJoin.ReadyRun machine (budget w N Q) (input w N Q) (output w N Q) := by
  have ht : budget w N Q=(2*N+6)+1+WilliamsUnaryProduct.budget N Q+1+(2*(N*Q)+8)+1+
      WilliamsUnaryProduct.budget w (N*Q)+1+(2*(w*(N*Q))+8)+1+(2*(w*(N*Q))+6) := by unfold budget; omega
  rw [ht]
  exact ClockJoin.join fourth phase6 _ _ _ _ _ (fourth_ready w N Q) (ready6 w N Q)

end NearCubicWires.RepairOrdinary.RowCommonTupleDimensions
