import Proof.Supplier.RowCommonSize
import Proof.Supplier.RowCachedCoordinateBounds

/-! Produce the exact two native-cache capacities from the measured radix
width and common source scale. Only fixed constants index these machines. -/
namespace NearCubicWires.RepairOrdinary.RowCommonResources
open LocalBitMultitape RecoveryRootRound
open RowCommonSize (put focus_put)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def input (w S : ℕ) : RowCommonSize.Store := fun i=>
  if i=0 then List.replicate w true else if i=1 then List.replicate S true else []
def data1 (w S : ℕ) := put (input w S) 2 3 [true] [false]
def data2 (w S : ℕ) := put (data1 w S) 4 5
  (List.replicate (w+1) true) (List.replicate (w+1+2) false)
def data3 (w S : ℕ) := put (data2 w S) 6 7 (UnaryTemplate.tape 32) (List.replicate 34 false)
def data4 (w S : ℕ) := put (data3 w S) 8 9
  (List.replicate ((w+1)*32) true) (List.replicate (WilliamsUnaryProduct.scratch (w+1) 32) false)
def data5 (w S : ℕ) := put (data4 w S) 10 11 (UnaryTemplate.tape 256) (List.replicate 258 false)
def output (w S : ℕ) := put (data5 w S) 12 13
  (List.replicate (S*256) true) (List.replicate (WilliamsUnaryProduct.scratch S 256) false)
def slots1 : Fin 2→Fin 17 := ![2,3]
def slots2 : Fin 4→Fin 17 := ![0,2,4,5]
def slots3 : Fin 2→Fin 17 := ![6,7]
def slots4 : Fin 4→Fin 17 := ![4,6,8,9]
def slots5 : Fin 2→Fin 17 := ![10,11]
def slots6 : Fin 4→Fin 17 := ![1,10,12,13]
noncomputable def phase1 := RecoveryFocus.machine slots1 (HierarchyFixedWord.machine [true])
noncomputable def phase2 := RecoveryFocus.machine slots2 ClockUnarySum.machine
noncomputable def phase3 := RecoveryFocus.machine slots3 (HierarchyFixedWord.machine (UnaryTemplate.tape 32))
noncomputable def phase4 := RecoveryFocus.machine slots4 ClockUnaryProduct.machine
noncomputable def phase5 := RecoveryFocus.machine slots5 (HierarchyFixedWord.machine (UnaryTemplate.tape 256))
noncomputable def phase6 := RecoveryFocus.machine slots6 ClockUnaryProduct.machine
noncomputable def first := Composition.machine phase1 phase2
noncomputable def second := Composition.machine first phase3
noncomputable def third := Composition.machine second phase4
noncomputable def fourth := Composition.machine third phase5
noncomputable def machine := Composition.machine fourth phase6
def budget (w S : ℕ) := 4+(2*(w+1)+6)+70+WilliamsUnaryProduct.budget (w+1) 32+
  518+WilliamsUnaryProduct.budget S 256+5

theorem literal_ready (bits : List Bool) : ClockJoin.ReadyRun (HierarchyFixedWord.machine bits)
    (2*bits.length+2) (fun _=>[]) ![bits,List.replicate bits.length false] := by
  obtain ⟨r,hr,rt,rh,rs⟩:=HierarchyFixedWord.word_ready bits
  exact ⟨r,hr,rt,rh,rs.le⟩
theorem product_ready (d e : ℕ) : ClockJoin.ReadyRun ClockUnaryProduct.machine
    (WilliamsUnaryProduct.budget d e) (WilliamsUnaryProduct.input d e) (WilliamsUnaryProduct.output d e) := by
  obtain ⟨r,hr,rt,rh,rs⟩:=WilliamsUnaryProduct.product_ready d e
  exact ⟨r,hr,rt,rh,rs.le⟩
theorem ready1 (w S : ℕ) : ClockJoin.ReadyRun phase1 4 (input w S) (data1 w S) := by
  apply focus_put _ _ _ _ (literal_ready [true]) slots1 (by decide) _ 0 1
  · intro i; fin_cases i <;> simp [input,slots1]
  · intro i; fin_cases i <;> simp [put,slots1]
theorem ready2 (w S : ℕ) : ClockJoin.ReadyRun phase2 (2*(w+1)+6) (data1 w S) (data2 w S) := by
  apply focus_put _ _ _ _ (ClockUnarySum.sum_ready w 1) slots2 (by decide) _ 2 3
  · intro i; fin_cases i <;> simp [data1,put,input,slots2]
  · intro i; fin_cases i <;> simp [data1,put,input,slots2]
theorem ready3 (w S : ℕ) : ClockJoin.ReadyRun phase3 70 (data2 w S) (data3 w S) := by
  apply focus_put _ _ _ _ (literal_ready (UnaryTemplate.tape 32)) slots3 (by decide) _ 0 1
  · intro i; fin_cases i <;> simp [data2,data1,put,input,slots3]
  · intro i; fin_cases i <;> simp [put,slots3,UnaryTemplate.tape]
theorem ready4 (w S : ℕ) : ClockJoin.ReadyRun phase4 (WilliamsUnaryProduct.budget (w+1) 32)
    (data3 w S) (data4 w S) := by
  apply focus_put _ _ _ _ (product_ready (w+1) 32) slots4 (by decide) _ 2 3
  · intro i; fin_cases i <;> simp [data3,data2,data1,put,input,slots4,WilliamsUnaryProduct.input]
  · intro i; fin_cases i <;> simp [data3,data2,put,slots4,WilliamsUnaryProduct.output]
theorem ready5 (w S : ℕ) : ClockJoin.ReadyRun phase5 518 (data4 w S) (data5 w S) := by
  apply focus_put _ _ _ _ (literal_ready (UnaryTemplate.tape 256)) slots5 (by decide) _ 0 1
  · intro i; fin_cases i <;> simp [data4,data3,data2,data1,put,input,slots5]
  · intro i; fin_cases i <;> simp [put,slots5,UnaryTemplate.tape]
theorem ready6 (w S : ℕ) : ClockJoin.ReadyRun phase6 (WilliamsUnaryProduct.budget S 256)
    (data5 w S) (output w S) := by
  apply focus_put _ _ _ _ (product_ready S 256) slots6 (by decide) _ 2 3
  · intro i; fin_cases i <;> simp [data5,data4,data3,data2,data1,put,input,slots6,WilliamsUnaryProduct.input]
  · intro i; fin_cases i <;> simp [data5,data4,data3,data2,data1,put,input,slots6,WilliamsUnaryProduct.output]

private theorem first_ready (w S : ℕ) : ClockJoin.ReadyRun first (4+1+(2*(w+1)+6))
    (input w S) (data2 w S) :=
  ClockJoin.join phase1 phase2 _ _ _ _ _ (ready1 w S) (ready2 w S)
private theorem second_ready (w S : ℕ) : ClockJoin.ReadyRun second ((4+1+(2*(w+1)+6))+1+70)
    (input w S) (data3 w S) :=
  ClockJoin.join first phase3 _ _ _ _ _ (first_ready w S) (ready3 w S)
private theorem third_ready (w S : ℕ) : ClockJoin.ReadyRun third
    (((4+1+(2*(w+1)+6))+1+70)+1+WilliamsUnaryProduct.budget (w+1) 32)
    (input w S) (data4 w S) :=
  ClockJoin.join second phase4 _ _ _ _ _ (second_ready w S) (ready4 w S)
private theorem fourth_ready (w S : ℕ) : ClockJoin.ReadyRun fourth
    ((((4+1+(2*(w+1)+6))+1+70)+1+WilliamsUnaryProduct.budget (w+1) 32)+1+518)
    (input w S) (data5 w S) :=
  ClockJoin.join third phase5 _ _ _ _ _ (third_ready w S) (ready5 w S)
theorem resources_ready (w S : ℕ) : ClockJoin.ReadyRun machine (budget w S) (input w S) (output w S) := by
  have ht : budget w S=
      4+1+(2*(w+1)+6)+1+70+1+WilliamsUnaryProduct.budget (w+1) 32+1+518+1+
        WilliamsUnaryProduct.budget S 256 := by unfold budget; omega
  rw [ht]
  exact ClockJoin.join fourth phase6 _ _ _ _ _ (fourth_ready w S) (ready6 w S)

theorem scale_eq {n : ℕ} (gs : List (ExactThresholdGate n)) :
    RowCommonSize.scale (RepairRepresentation.exactListWord gs).length n gs.length=
      RowCachedCoordinateBounds.size gs (RowCachedCoordinateBounds.width gs) := by
  unfold RowCommonSize.scale RowCachedCoordinateBounds.size RowCachedCoordinateBounds.width
  ring
theorem size_budget_bound (B n N : ℕ) : RowCommonSize.budget B n N≤32*RowCommonSize.scale B n N+64 := by
  unfold RowCommonSize.budget RowCommonSize.scale WilliamsUnaryProduct.budget
  nlinarith

end NearCubicWires.RepairOrdinary.RowCommonResources
