import Proof.Supplier.RowCommonSize
import Proof.MachineModel.ClosureRadix

/-! Produce the compact metadata scale from independently measured cache
bytes and radix. Reuses the first six existing arithmetic phases verbatim;
the final addition reads the separate radix word instead of the cache mass.
All parameters are runtime tape data; the machine is fixed. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1Closure.CompactSize
open LocalBitMultitape RepairOrdinary RecoveryRootRound ExtDecompositionBatch

def value (B n N b : Nat) := B+(n+1)*(N+1)+b+1
def input (B n N b : Nat) : Fin 18 → List Bool :=
  Fin.addCases (m:=17) (n:=1) (motive:=fun _ => List Bool)
    (RowCommonSize.input B n N) (fun _ => List.replicate b true)
def middle (B n N b : Nat) : Fin 18 → List Bool :=
  Fin.addCases (m:=17) (n:=1) (motive:=fun _ => List Bool)
    (RowCommonSize.data6 B n N) (fun _ => List.replicate b true)
def slots : Fin 4 → Fin 18 := ![13,17,15,16]
def sumInput (a b : Nat) : Fin 4 → List Bool := ![List.replicate a true,List.replicate b true,[],[]]
def sumOutput (a b : Nat) : Fin 4 → List Bool :=
  ![List.replicate a true,List.replicate b true,List.replicate (a+b) true,List.replicate (a+b+2) false]
noncomputable def output (B n N b : Nat) : Fin 18 → List Bool :=
  install slots (middle B n N b)
    (sumOutput ((B+1)+((n+1)*N+(n+1))) b)
noncomputable def first := TapeEmbedding.machine 1 RowCommonSize.fifth
noncomputable def last := RecoveryFocus.machine slots ClockUnarySum.machine
noncomputable def machine := Composition.machine first last
def firstCost (B n N : Nat) :=
  (2*n+6)+1+WilliamsUnaryProduct.budget (n+1) N+
  1+(2*((n+1)*N+(n+1))+6)+1+4+1+(2*(B+1)+6)+
  1+(2*((B+1)+((n+1)*N+(n+1)))+6)
def budget (B n N b : Nat) := firstCost B n N+1+(2*value B n N b+6)

theorem ready (B n N b : Nat) :
    ClockJoin.ReadyRun machine (budget B n N b) (input B n N b) (output B n N b) := by
  have h2 := ClockJoin.join _ _ _ _ _ _ _ (RowCommonSize.ready1 B n N) (RowCommonSize.ready2 B n N)
  have h3 := ClockJoin.join _ _ _ _ _ _ _ h2 (RowCommonSize.ready3 B n N)
  have h4 := ClockJoin.join _ _ _ _ _ _ _ h3 (RowCommonSize.ready4 B n N)
  have h5 := ClockJoin.join _ _ _ _ _ _ _ h4 (RowCommonSize.ready5 B n N)
  have h6 : ClockJoin.ReadyRun RowCommonSize.fifth (firstCost B n N)
      (RowCommonSize.input B n N) (RowCommonSize.data6 B n N) :=
    ClockJoin.join _ _ _ _ _ _ _ h5 (RowCommonSize.ready6 B n N)
  obtain ⟨r,hr,rt,rh,_rs⟩ := h6
  have start := (Step.of_run hr (funext rh) rt).embed (fun _ : Fin 1 => 0)
    (fun _ => List.replicate b true)
  have zero : (Fin.addCases (m:=17) (n:=1) (motive:=fun _ => Nat)
      (fun _ => 0) (fun _ => 0)) = (fun _ => 0) := by
    funext i
    exact Fin.addCases (by intro i; simp) (by intro i; simp) i
  have start := start.congr_in zero rfl |>.congr zero rfl
  have hin : ∀ i,middle B n N b (slots i)=
      sumInput ((B+1)+((n+1)*N+(n+1))) b i := by
    intro i
    fin_cases i <;> simp [middle,slots,RowCommonSize.data6,RowCommonSize.data5,
      RowCommonSize.data4,RowCommonSize.data3,RowCommonSize.data2,RowCommonSize.data1,
      RowCommonSize.input,RowCommonSize.put,sumInput,Fin.addCases]
  obtain ⟨s,hs,st,sh,_ss⟩ := (ClockUnarySum.sum_ready
    ((B+1)+((n+1)*N+(n+1))) b).focus slots (by decide) (middle B n N b) hin
  have whole := start.seq (Step.of_run hs (funext sh) st)
  have hv : ((B+1)+((n+1)*N+(n+1)))+b = value B n N b := by
    unfold value
    ring
  obtain ⟨z,hz,zh,zt,zs⟩ := whole
  refine ⟨z,?_,zt,fun i => congrFun zh i,?_⟩
  · simpa only [budget, hv, run, initialConfiguration, machine, first, last, input] using hz
  · simpa only [budget, hv] using zs

theorem scale_word (B n N b : Nat) :
    output B n N b 15 = List.replicate (value B n N b) true := by
  have h := install_slot slots (by decide) (middle B n N b)
    (sumOutput ((B+1)+((n+1)*N+(n+1))) b) 2
  change output B n N b 15 = List.replicate _ true at h
  convert h using 2
  unfold value
  ring

theorem retained (B n N b : Nat) (i : Fin 3) :
    output B n N b (i.castAdd 15) = input B n N b (i.castAdd 15) := by
  rw [output, install_other slots (middle B n N b) _ _ (by
    intro j h
    have hv := congrArg Fin.val h
    have hi := i.isLt
    fin_cases j <;> simp [slots] at hv <;> omega)]
  fin_cases i <;> rfl

theorem radix_word (B n N b : Nat) :
    output B n N b 17 = List.replicate b true :=
  install_slot slots (by decide) (middle B n N b) _ 1

theorem value_eq {n : Nat} (gs : List (ExactThresholdGate n)) [P1Radix gs] :
    value (RepairRepresentation.exactListWord gs).length n gs.length (P1Radix.bits gs) =
      RowCachedCoordinateBounds.size gs (P1Radix.bits gs) := by
  unfold value RowCachedCoordinateBounds.size
  ring

theorem budget_bound (B n N b : Nat) : budget B n N b ≤ 32*(value B n N b+1) := by
  unfold budget firstCost value WilliamsUnaryProduct.budget
  nlinarith

end NearCubicWires.P1Closure.CompactSize
