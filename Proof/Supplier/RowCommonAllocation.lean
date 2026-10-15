import Proof.Supplier.RowCommonResources
import Proof.PCP.ProjectionDimensionTemplate
import Proof.Supplier.RowCommonBounds

/-! Construct exactly the existing outer row capacity from its paid raw
maximum occurrence count, common output width and native cache capacity.
The source D=256*S makes the multiplier64 reproduce the original16384. -/
namespace NearCubicWires.RepairOrdinary.RowCommonAllocation
open LocalBitMultitape RecoveryRootRound
open RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

abbrev Store := Fin 25→List Bool
def put (a : Store) (i j : Fin 25) (x y : List Bool) : Store :=
  fun k=>if k=i then x else if k=j then y else a k
def input (m p D : ℕ) : Store := fun i=>
  if i=0 then List.replicate m true else if i=1 then List.replicate p true
  else if i=2 then List.replicate D true else []
def value (m p D : ℕ) := ((m+1)*D)*64+p*16+64
def data1 (m p D : ℕ) := put (input m p D) 3 4
  (UnaryTemplate.tape D) (List.replicate (D+3) false)
def data2 (m p D : ℕ) := put (data1 m p D) 5 6
  ([true]) ([false])
def data3 (m p D : ℕ) := put (data2 m p D) 7 8
  (List.replicate (m+1) true) (List.replicate (m+1+2) false)
def data4 (m p D : ℕ) := put (data3 m p D) 9 10
  (List.replicate ((m+1)*D) true) (List.replicate (WilliamsUnaryProduct.scratch (m+1) D) false)
def data5 (m p D : ℕ) := put (data4 m p D) 11 12
  (UnaryTemplate.tape 64) (List.replicate 66 false)
def data6 (m p D : ℕ) := put (data5 m p D) 13 14
  (List.replicate (((m+1)*D)*64) true) (List.replicate (WilliamsUnaryProduct.scratch ((m+1)*D) 64) false)
def data7 (m p D : ℕ) := put (data6 m p D) 15 16
  (UnaryTemplate.tape 16) (List.replicate 18 false)
def data8 (m p D : ℕ) := put (data7 m p D) 17 18
  (List.replicate (p*16) true) (List.replicate (WilliamsUnaryProduct.scratch p 16) false)
def data9 (m p D : ℕ) := put (data8 m p D) 19 20
  (List.replicate (((m+1)*D)*64+p*16) true) (List.replicate (((m+1)*D)*64+p*16+2) false)
def data10 (m p D : ℕ) := put (data9 m p D) 21 22
  (List.replicate 64 true) (List.replicate 64 false)
def output (m p D : ℕ) := put (data10 m p D) 23 24
  (List.replicate (value m p D) true) (List.replicate (value m p D+2) false)
def slots1 : Fin 3→Fin 25 := ![2,3,4]
noncomputable def phase1 := RecoveryFocus.machine slots1 (DimensionTemplate.machine false)
def slots2 : Fin 2→Fin 25 := ![5,6]
noncomputable def phase2 := RecoveryFocus.machine slots2 (HierarchyFixedWord.machine [true])
def slots3 : Fin 4→Fin 25 := ![0,5,7,8]
noncomputable def phase3 := RecoveryFocus.machine slots3 (ClockUnarySum.machine)
def slots4 : Fin 4→Fin 25 := ![7,3,9,10]
noncomputable def phase4 := RecoveryFocus.machine slots4 (ClockUnaryProduct.machine)
def slots5 : Fin 2→Fin 25 := ![11,12]
noncomputable def phase5 := RecoveryFocus.machine slots5 (HierarchyFixedWord.machine (UnaryTemplate.tape 64))
def slots6 : Fin 4→Fin 25 := ![9,11,13,14]
noncomputable def phase6 := RecoveryFocus.machine slots6 (ClockUnaryProduct.machine)
def slots7 : Fin 2→Fin 25 := ![15,16]
noncomputable def phase7 := RecoveryFocus.machine slots7 (HierarchyFixedWord.machine (UnaryTemplate.tape 16))
def slots8 : Fin 4→Fin 25 := ![1,15,17,18]
noncomputable def phase8 := RecoveryFocus.machine slots8 (ClockUnaryProduct.machine)
def slots9 : Fin 4→Fin 25 := ![13,17,19,20]
noncomputable def phase9 := RecoveryFocus.machine slots9 (ClockUnarySum.machine)
def slots10 : Fin 2→Fin 25 := ![21,22]
noncomputable def phase10 := RecoveryFocus.machine slots10 (HierarchyFixedWord.machine (List.replicate 64 true))
def slots11 : Fin 4→Fin 25 := ![19,21,23,24]
noncomputable def phase11 := RecoveryFocus.machine slots11 (ClockUnarySum.machine)
noncomputable def joined1 := phase1
noncomputable def joined2 := Composition.machine joined1 phase2
noncomputable def joined3 := Composition.machine joined2 phase3
noncomputable def joined4 := Composition.machine joined3 phase4
noncomputable def joined5 := Composition.machine joined4 phase5
noncomputable def joined6 := Composition.machine joined5 phase6
noncomputable def joined7 := Composition.machine joined6 phase7
noncomputable def joined8 := Composition.machine joined7 phase8
noncomputable def joined9 := Composition.machine joined8 phase9
noncomputable def joined10 := Composition.machine joined9 phase10
noncomputable def machine := Composition.machine joined10 phase11
def budget (m p D : ℕ) := (2*D+8)+(4)+(2*(m+1)+6)+(WilliamsUnaryProduct.budget (m+1) D)+(134)+(WilliamsUnaryProduct.budget ((m+1)*D) 64)+(38)+(WilliamsUnaryProduct.budget p 16)+(2*(((m+1)*D)*64+p*16)+6)+(130)+(2*value m p D+6)+10

theorem focus_put {t s : ℕ} (p : Machine t s) (fuel : ℕ) (src dst : Fin t→List Bool)
    (h : ClockJoin.ReadyRun p fuel src dst) (slots : Fin t→Fin 25)
    (hs : Function.Injective slots) (a : Store) (i j : Fin t) (x y : List Bool)
    (hin : ∀ k,a (slots k)=src k)
    (hout : ∀ k,put a (slots i) (slots j) x y (slots k)=dst k) :
    ClockJoin.ReadyRun (RecoveryFocus.machine slots p) fuel a (put a (slots i) (slots j) x y) := by
  have hf:=h.focus slots hs a hin
  have he:=HierarchyWidth.install_eq slots hs a (put a (slots i) (slots j) x y) dst hout (by
    intro k hk
    simp [put,Ne.symm (hk i),Ne.symm (hk j)])
  rw [he] at hf
  exact hf

theorem ready1 (m p D : ℕ) : ClockJoin.ReadyRun phase1 (2*D+8) (input m p D) (data1 m p D) := by
  apply focus_put _ _ _ _ (DimensionTemplate.ready false D) slots1 (by decide) _ 1 2
  · intro i; fin_cases i <;> simp [input,slots1,DimensionTemplate.input]
  · intro i; fin_cases i <;> simp [input,put,slots1,DimensionTemplate.output]
theorem ready2 (m p D : ℕ) : ClockJoin.ReadyRun phase2 (4) (data1 m p D) (data2 m p D) := by
  apply focus_put _ _ _ _ (RowCommonResources.literal_ready [true]) slots2 (by decide) _ 0 1
  · intro i; fin_cases i <;> simp [data1,input,put,slots2]
  · intro i; fin_cases i <;> simp [put,slots2]
theorem ready3 (m p D : ℕ) : ClockJoin.ReadyRun phase3 (2*(m+1)+6) (data2 m p D) (data3 m p D) := by
  apply focus_put _ _ _ _ (ClockUnarySum.sum_ready m 1) slots3 (by decide) _ 2 3
  · intro i; fin_cases i <;> simp [data2,data1,input,put,slots3]
  · intro i; fin_cases i <;> simp [data2,data1,input,put,slots3]
theorem ready4 (m p D : ℕ) : ClockJoin.ReadyRun phase4 (WilliamsUnaryProduct.budget (m+1) D) (data3 m p D) (data4 m p D) := by
  apply focus_put _ _ _ _ (RowCommonResources.product_ready (m+1) D) slots4 (by decide) _ 2 3
  · intro i; fin_cases i <;> simp [data3,data2,data1,input,put,slots4,WilliamsUnaryProduct.input]
  · intro i; fin_cases i <;> simp [data3,data2,data1,put,slots4,WilliamsUnaryProduct.output]
theorem ready5 (m p D : ℕ) : ClockJoin.ReadyRun phase5 (134) (data4 m p D) (data5 m p D) := by
  apply focus_put _ _ _ _ (RowCommonResources.literal_ready (UnaryTemplate.tape 64)) slots5 (by decide) _ 0 1
  · intro i; fin_cases i <;> simp [data4,data3,data2,data1,input,put,slots5]
  · intro i; fin_cases i <;> simp [put,slots5,UnaryTemplate.tape]
theorem ready6 (m p D : ℕ) : ClockJoin.ReadyRun phase6 (WilliamsUnaryProduct.budget ((m+1)*D) 64) (data5 m p D) (data6 m p D) := by
  apply focus_put _ _ _ _ (RowCommonResources.product_ready ((m+1)*D) 64) slots6 (by decide) _ 2 3
  · intro i; fin_cases i <;> simp [data5,data4,data3,data2,data1,input,put,slots6,WilliamsUnaryProduct.input]
  · intro i; fin_cases i <;> simp [data5,data4,put,slots6,WilliamsUnaryProduct.output]
theorem ready7 (m p D : ℕ) : ClockJoin.ReadyRun phase7 (38) (data6 m p D) (data7 m p D) := by
  apply focus_put _ _ _ _ (RowCommonResources.literal_ready (UnaryTemplate.tape 16)) slots7 (by decide) _ 0 1
  · intro i; fin_cases i <;> simp [data6,data5,data4,data3,data2,data1,input,put,slots7]
  · intro i; fin_cases i <;> simp [put,slots7,UnaryTemplate.tape]
theorem ready8 (m p D : ℕ) : ClockJoin.ReadyRun phase8 (WilliamsUnaryProduct.budget p 16) (data7 m p D) (data8 m p D) := by
  apply focus_put _ _ _ _ (RowCommonResources.product_ready p 16) slots8 (by decide) _ 2 3
  · intro i; fin_cases i <;> simp [data7,data6,data5,data4,data3,data2,data1,input,put,slots8,WilliamsUnaryProduct.input]
  · intro i; fin_cases i <;> simp [data7,data6,data5,data4,data3,data2,data1,input,put,slots8,WilliamsUnaryProduct.output]
theorem ready9 (m p D : ℕ) : ClockJoin.ReadyRun phase9 (2*(((m+1)*D)*64+p*16)+6) (data8 m p D) (data9 m p D) := by
  apply focus_put _ _ _ _ (ClockUnarySum.sum_ready (((m+1)*D)*64) (p*16)) slots9 (by decide) _ 2 3
  · intro i; fin_cases i <;> simp [data8,data7,data6,data5,data4,data3,data2,data1,input,put,slots9]
  · intro i; fin_cases i <;> simp [data8,data7,data6,put,slots9]
theorem ready10 (m p D : ℕ) : ClockJoin.ReadyRun phase10 (130) (data9 m p D) (data10 m p D) := by
  apply focus_put _ _ _ _ (RowCommonResources.literal_ready (List.replicate 64 true)) slots10 (by decide) _ 0 1
  · intro i; fin_cases i <;> simp [data9,data8,data7,data6,data5,data4,data3,data2,data1,input,put,slots10]
  · intro i; fin_cases i <;> simp [put,slots10]
theorem ready11 (m p D : ℕ) : ClockJoin.ReadyRun phase11 (2*value m p D+6) (data10 m p D) (output m p D) := by
  apply focus_put _ _ _ _ (ClockUnarySum.sum_ready (((m+1)*D)*64+p*16) 64) slots11 (by decide) _ 2 3
  · intro i; fin_cases i <;> simp [data10,data9,data8,data7,data6,data5,data4,data3,data2,data1,input,put,slots11]
  · intro i; fin_cases i <;> simp [data10,data9,put,slots11,value]

private theorem joined2_ready (m p D : ℕ) : ClockJoin.ReadyRun joined2
    ((2*D+8)+1+(4)) (input m p D) (data2 m p D) :=
  ClockJoin.join joined1 phase2 _ _ _ _ _ (ready1 m p D) (ready2 m p D)
private theorem joined3_ready (m p D : ℕ) : ClockJoin.ReadyRun joined3
    ((2*D+8)+1+(4)+1+(2*(m+1)+6)) (input m p D) (data3 m p D) :=
  ClockJoin.join joined2 phase3 _ _ _ _ _ (joined2_ready m p D) (ready3 m p D)
private theorem joined4_ready (m p D : ℕ) : ClockJoin.ReadyRun joined4
    ((2*D+8)+1+(4)+1+(2*(m+1)+6)+1+(WilliamsUnaryProduct.budget (m+1) D)) (input m p D) (data4 m p D) :=
  ClockJoin.join joined3 phase4 _ _ _ _ _ (joined3_ready m p D) (ready4 m p D)
private theorem joined5_ready (m p D : ℕ) : ClockJoin.ReadyRun joined5
    ((2*D+8)+1+(4)+1+(2*(m+1)+6)+1+(WilliamsUnaryProduct.budget (m+1) D)+1+(134)) (input m p D) (data5 m p D) :=
  ClockJoin.join joined4 phase5 _ _ _ _ _ (joined4_ready m p D) (ready5 m p D)
private theorem joined6_ready (m p D : ℕ) : ClockJoin.ReadyRun joined6
    ((2*D+8)+1+(4)+1+(2*(m+1)+6)+1+(WilliamsUnaryProduct.budget (m+1) D)+1+(134)+1+(WilliamsUnaryProduct.budget ((m+1)*D) 64)) (input m p D) (data6 m p D) :=
  ClockJoin.join joined5 phase6 _ _ _ _ _ (joined5_ready m p D) (ready6 m p D)
private theorem joined7_ready (m p D : ℕ) : ClockJoin.ReadyRun joined7
    ((2*D+8)+1+(4)+1+(2*(m+1)+6)+1+(WilliamsUnaryProduct.budget (m+1) D)+1+(134)+1+(WilliamsUnaryProduct.budget ((m+1)*D) 64)+1+(38)) (input m p D) (data7 m p D) :=
  ClockJoin.join joined6 phase7 _ _ _ _ _ (joined6_ready m p D) (ready7 m p D)
private theorem joined8_ready (m p D : ℕ) : ClockJoin.ReadyRun joined8
    ((2*D+8)+1+(4)+1+(2*(m+1)+6)+1+(WilliamsUnaryProduct.budget (m+1) D)+1+(134)+1+(WilliamsUnaryProduct.budget ((m+1)*D) 64)+1+(38)+1+(WilliamsUnaryProduct.budget p 16)) (input m p D) (data8 m p D) :=
  ClockJoin.join joined7 phase8 _ _ _ _ _ (joined7_ready m p D) (ready8 m p D)
private theorem joined9_ready (m p D : ℕ) : ClockJoin.ReadyRun joined9
    ((2*D+8)+1+(4)+1+(2*(m+1)+6)+1+(WilliamsUnaryProduct.budget (m+1) D)+1+(134)+1+(WilliamsUnaryProduct.budget ((m+1)*D) 64)+1+(38)+1+(WilliamsUnaryProduct.budget p 16)+1+(2*(((m+1)*D)*64+p*16)+6)) (input m p D) (data9 m p D) :=
  ClockJoin.join joined8 phase9 _ _ _ _ _ (joined8_ready m p D) (ready9 m p D)
private theorem joined10_ready (m p D : ℕ) : ClockJoin.ReadyRun joined10
    ((2*D+8)+1+(4)+1+(2*(m+1)+6)+1+(WilliamsUnaryProduct.budget (m+1) D)+1+(134)+1+(WilliamsUnaryProduct.budget ((m+1)*D) 64)+1+(38)+1+(WilliamsUnaryProduct.budget p 16)+1+(2*(((m+1)*D)*64+p*16)+6)+1+(130)) (input m p D) (data10 m p D) :=
  ClockJoin.join joined9 phase10 _ _ _ _ _ (joined9_ready m p D) (ready10 m p D)
theorem allocation_ready (m p D : ℕ) : ClockJoin.ReadyRun machine (budget m p D) (input m p D) (output m p D) := by
  have ht : budget m p D=(2*D+8)+1+(4)+1+(2*(m+1)+6)+1+(WilliamsUnaryProduct.budget (m+1) D)+1+(134)+1+(WilliamsUnaryProduct.budget ((m+1)*D) 64)+1+(38)+1+(WilliamsUnaryProduct.budget p 16)+1+(2*(((m+1)*D)*64+p*16)+6)+1+(130)+1+(2*value m p D+6) := by unfold budget; omega
  rw [ht]
  exact ClockJoin.join joined10 phase11 _ _ _ _ _ (joined10_ready m p D) (ready11 m p D)

theorem capacity_eq {n : ℕ} (gs : List (ExactThresholdGate n)) (m p : ℕ) :
    value m p (RowCachedCoordinateBounds.outer gs (RowCachedCoordinateBounds.width gs))=
      RowCommonBounds.capacity gs m p := by
  unfold value RowCachedCoordinateBounds.outer RowCommonBounds.capacity
  ring
theorem budget_bound (m p D : ℕ) (hD : 1≤D) : budget m p D≤16*value m p D := by
  have hm : m+1≤(m+1)*D := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left (m+1) hD
  unfold budget WilliamsUnaryProduct.budget value
  nlinarith

end NearCubicWires.RepairOrdinary.RowCommonAllocation
