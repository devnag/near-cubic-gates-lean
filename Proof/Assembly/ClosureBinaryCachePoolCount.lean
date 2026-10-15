import Proof.Supplier.RowCommonResources
import Proof.Assembly.ClosureBinaryInitialize

/-! Compute the actual native pool cardinality from the exponential driver
already produced by BinaryInitialize and the decoded ORIGINAL child count.
No replicated-count word is an input. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1Closure.BinaryCacheColdPoolCount
open LocalBitMultitape RepairOrdinary RecoveryRootRound ExtDecompositionBatch
open RepairSource.VerifierDecoding
open RowCommonSize (put focus_put)

def input (n N : Nat) : RowCommonSize.Store := fun i=>
  if i=0 then CompareMachine.word n else if i=1 then UnaryTemplate.tape N else []
def data1 (n N : Nat) := put (input n N) 2 3
  (List.replicate (n+1) true) (List.replicate (n+2) false)
def data2 (n N : Nat) := put (data1 n N) 4 5
  (List.replicate ((n+1)*N) true) (List.replicate (WilliamsUnaryProduct.scratch (n+1) N) false)
def data3 (n N : Nat) := put (data2 n N) 6 7 [true] [false]
def output (n N : Nat) := put (data3 n N) 8 9
  (List.replicate ((n+1)*N+1) true) (List.replicate ((n+1)*N+3) false)
def slots1 : Fin 3→Fin 17 := ![0,2,3]
def slots2 : Fin 4→Fin 17 := ![2,1,4,5]
def slots3 : Fin 2→Fin 17 := ![6,7]
def slots4 : Fin 4→Fin 17 := ![4,6,8,9]
noncomputable def phase1 := RecoveryFocus.machine slots1 (UWalkUnary.machine false true)
noncomputable def phase2 := RecoveryFocus.machine slots2 ClockUnaryProduct.machine
noncomputable def phase3 := RecoveryFocus.machine slots3 (HierarchyFixedWord.machine [true])
noncomputable def phase4 := RecoveryFocus.machine slots4 ClockUnarySum.machine
noncomputable def machine := Composition.machine (Composition.machine (Composition.machine phase1 phase2) phase3) phase4
def budget (n N : Nat) := (2*n+6)+WilliamsUnaryProduct.budget (n+1) N+4+(2*((n+1)*N+1)+6)+3

theorem count_ready (n : Nat) :
    ClockJoin.ReadyRun (UWalkUnary.machine false true) (2*n+6)
      ![CompareMachine.word n,[],[]]
      ![CompareMachine.word n,List.replicate (n+1) true,List.replicate (n+2) false] := by
  have source : UWalkUnary.source (n+1) n=CompareMachine.word n := by
    simp [UWalkUnary.source,ZeroPadding.pad,CompareMachine.word]
  simpa only [UWalkUnary.input,UWalkUnary.result,source,UWalkUnary.output,UWalkUnary.lead,
    Bool.false_eq_true,↓reduceIte,Bool.toNat_true,List.nil_append] using UWalkUnary.ready false true (n+1) n

theorem ready1 (n N : Nat) : ClockJoin.ReadyRun phase1 (2*n+6) (input n N) (data1 n N) := by
  apply focus_put _ _ _ _ (count_ready n) slots1 (by decide) _ 1 2
  · intro i;fin_cases i <;>simp [input,slots1]
  · intro i;fin_cases i <;>simp [put,input,slots1]
theorem ready2 (n N : Nat) : ClockJoin.ReadyRun phase2 (WilliamsUnaryProduct.budget (n+1) N)
    (data1 n N) (data2 n N) := by
  apply focus_put _ _ _ _ (RowCommonResources.product_ready (n+1) N) slots2 (by decide) _ 2 3
  · intro i;fin_cases i <;>simp [data1,put,input,slots2,WilliamsUnaryProduct.input]
  · intro i;fin_cases i <;>simp [data1,put,input,slots2,WilliamsUnaryProduct.output]
theorem ready3 (n N : Nat) : ClockJoin.ReadyRun phase3 4 (data2 n N) (data3 n N) := by
  apply focus_put _ _ _ _ (RowCommonResources.literal_ready [true]) slots3 (by decide) _ 0 1
  · intro i;fin_cases i <;>simp [data2,data1,put,input,slots3]
  · intro i;fin_cases i <;>simp [put,slots3]
theorem ready4 (n N : Nat) : ClockJoin.ReadyRun phase4 (2*((n+1)*N+1)+6) (data3 n N) (output n N) := by
  apply focus_put _ _ _ _ (ClockUnarySum.sum_ready ((n+1)*N) 1) slots4 (by decide) _ 2 3
  · intro i;fin_cases i <;>simp [data3,data2,data1,put,input,slots4]
  · intro i;fin_cases i <;>simp [data3,data2,put,slots4,Nat.add_assoc]

theorem run (n N : Nat) : ClockJoin.ReadyRun machine (budget n N) (input n N) (output n N) := by
  have all := ClockJoin.join _ _ _ _ _ _ _
    (ClockJoin.join _ _ _ _ _ _ _ (ClockJoin.join _ _ _ _ _ _ _ (ready1 n N) (ready2 n N)) (ready3 n N))
    (ready4 n N)
  have hb : (2*n+6+1+WilliamsUnaryProduct.budget (n+1) N)+1+4+1+(2*((n+1)*N+1)+6)=budget n N := by
    unfold budget;omega
  rw [hb] at all
  exact all

theorem binary_output (K N : Nat) : output (2^K-1) N 8=List.replicate (2^K*N+1) true := by
  have h : 2^K-1+1=2^K := by have := Nat.two_pow_pos K;omega
  change List.replicate ((2^K-1+1)*N+1) true=_
  rw [h]

end NearCubicWires.P1Closure.BinaryCacheColdPoolCount
