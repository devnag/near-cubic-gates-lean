import Proof.Hierarchy.CompetitorSameBucketPairEmit

/-! Physically derive the raw fixed record length L=4H+1 and its sentinel
from the actual raw H field. All auxiliary fields begin blank. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSameBucketRecordDriver
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open CompetitorRationalProducts
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def fourSlots : Fin 2 → Fin 13 := ![1,2]
def oneSlots : Fin 2 → Fin 13 := ![3,4]
def productSlots : Fin 4 → Fin 13 := ![0,1,5,6]
def sumSlots : Fin 4 → Fin 13 := ![5,3,7,8]
def templateSlots : Fin 5 → Fin 13 := ![7,9,10,11,12]
noncomputable def four := RecoveryFocus.machine fourSlots (HierarchyFixedWord.machine (UnaryTemplate.tape 4))
noncomputable def one := RecoveryFocus.machine oneSlots (HierarchyFixedWord.machine [true])
noncomputable def product := RecoveryFocus.machine productSlots ClockUnaryProduct.machine
noncomputable def sum := RecoveryFocus.machine sumSlots ClockUnarySum.machine
noncomputable def template := RecoveryFocus.machine templateSlots MatrixRawDimension.resetMachine
noncomputable def constants := Composition.machine four one
noncomputable def arithmetic := Composition.machine product (Composition.machine sum template)
noncomputable def machine := Composition.machine constants arithmetic

def input (h : ℕ) : Fin 13 → List Bool := fun i => if i=0 then List.replicate h true else []
def constantOutput (h : ℕ) : Fin 13 → List Bool :=
  ![List.replicate h true,UnaryTemplate.tape 4,List.replicate 6 false,[true],[false],[],[],[],[],[],[],[],[]]
def productOutput (h : ℕ) : Fin 13 → List Bool :=
  ![List.replicate h true,UnaryTemplate.tape 4,List.replicate 6 false,[true],[false],
    List.replicate (4*h) true,List.replicate (WilliamsUnaryProduct.scratch h 4) false,[],[],[],[],[],[]]
def sumOutput (h : ℕ) : Fin 13 → List Bool :=
  ![List.replicate h true,UnaryTemplate.tape 4,List.replicate 6 false,[true],[false],
    List.replicate (4*h) true,List.replicate (WilliamsUnaryProduct.scratch h 4) false,
    List.replicate (4*h+1) true,List.replicate (4*h+3) false,[],[],[],[]]
def budget (h : ℕ) := 46*h+48

theorem four_injective : Function.Injective fourSlots := by decide
def fourPick : Fin 13 → Option (Fin 2) := ![none,some 0,some 1,none,none,none,none,none,none,none,none,none,none]
theorem four_pick (i : Fin 13) : RecoveryFocus.pick fourSlots i=fourPick i := by
  classical
  fin_cases i
  · unfold RecoveryFocus.pick; apply dif_neg; decide
  · exact RecoveryFocus.pick_slot fourSlots four_injective 0
  · exact RecoveryFocus.pick_slot fourSlots four_injective 1
  · unfold RecoveryFocus.pick; apply dif_neg; decide
  · unfold RecoveryFocus.pick; apply dif_neg; decide
  · unfold RecoveryFocus.pick; apply dif_neg; decide
  · unfold RecoveryFocus.pick; apply dif_neg; decide
  · unfold RecoveryFocus.pick; apply dif_neg; decide
  · unfold RecoveryFocus.pick; apply dif_neg; decide
  · unfold RecoveryFocus.pick; apply dif_neg; decide
  · unfold RecoveryFocus.pick; apply dif_neg; decide
  · unfold RecoveryFocus.pick; apply dif_neg; decide
  · unfold RecoveryFocus.pick; apply dif_neg; decide

theorem one_injective : Function.Injective oneSlots := by decide
def onePick : Fin 13 → Option (Fin 2) := ![none,none,none,some 0,some 1,none,none,none,none,none,none,none,none]
theorem one_pick (i : Fin 13) : RecoveryFocus.pick oneSlots i=onePick i := by
  classical
  fin_cases i
  · unfold RecoveryFocus.pick; apply dif_neg; decide
  · unfold RecoveryFocus.pick; apply dif_neg; decide
  · unfold RecoveryFocus.pick; apply dif_neg; decide
  · exact RecoveryFocus.pick_slot oneSlots one_injective 0
  · exact RecoveryFocus.pick_slot oneSlots one_injective 1
  · unfold RecoveryFocus.pick; apply dif_neg; decide
  · unfold RecoveryFocus.pick; apply dif_neg; decide
  · unfold RecoveryFocus.pick; apply dif_neg; decide
  · unfold RecoveryFocus.pick; apply dif_neg; decide
  · unfold RecoveryFocus.pick; apply dif_neg; decide
  · unfold RecoveryFocus.pick; apply dif_neg; decide
  · unfold RecoveryFocus.pick; apply dif_neg; decide
  · unfold RecoveryFocus.pick; apply dif_neg; decide

theorem product_injective : Function.Injective productSlots := by decide
def productPick : Fin 13 → Option (Fin 4) := ![some 0,some 1,none,none,none,some 2,some 3,none,none,none,none,none,none]
theorem product_pick (i : Fin 13) : RecoveryFocus.pick productSlots i=productPick i := by
  classical
  fin_cases i
  · exact RecoveryFocus.pick_slot productSlots product_injective 0
  · exact RecoveryFocus.pick_slot productSlots product_injective 1
  · unfold RecoveryFocus.pick; apply dif_neg; decide
  · unfold RecoveryFocus.pick; apply dif_neg; decide
  · unfold RecoveryFocus.pick; apply dif_neg; decide
  · exact RecoveryFocus.pick_slot productSlots product_injective 2
  · exact RecoveryFocus.pick_slot productSlots product_injective 3
  · unfold RecoveryFocus.pick; apply dif_neg; decide
  · unfold RecoveryFocus.pick; apply dif_neg; decide
  · unfold RecoveryFocus.pick; apply dif_neg; decide
  · unfold RecoveryFocus.pick; apply dif_neg; decide
  · unfold RecoveryFocus.pick; apply dif_neg; decide
  · unfold RecoveryFocus.pick; apply dif_neg; decide

theorem sum_injective : Function.Injective sumSlots := by decide
def sumPick : Fin 13 → Option (Fin 4) := ![none,none,none,some 1,none,some 0,none,some 2,some 3,none,none,none,none]
theorem sum_pick (i : Fin 13) : RecoveryFocus.pick sumSlots i=sumPick i := by
  classical
  fin_cases i
  · unfold RecoveryFocus.pick; apply dif_neg; decide
  · unfold RecoveryFocus.pick; apply dif_neg; decide
  · unfold RecoveryFocus.pick; apply dif_neg; decide
  · exact RecoveryFocus.pick_slot sumSlots sum_injective 1
  · unfold RecoveryFocus.pick; apply dif_neg; decide
  · exact RecoveryFocus.pick_slot sumSlots sum_injective 0
  · unfold RecoveryFocus.pick; apply dif_neg; decide
  · exact RecoveryFocus.pick_slot sumSlots sum_injective 2
  · exact RecoveryFocus.pick_slot sumSlots sum_injective 3
  · unfold RecoveryFocus.pick; apply dif_neg; decide
  · unfold RecoveryFocus.pick; apply dif_neg; decide
  · unfold RecoveryFocus.pick; apply dif_neg; decide
  · unfold RecoveryFocus.pick; apply dif_neg; decide

theorem constants_ready (h : ℕ) : ClockJoin.ReadyRun constants 19 (input h) (constantOutput h) := by
  have firstReady : ClockJoin.ReadyRun (HierarchyFixedWord.machine (UnaryTemplate.tape 4)) 14 (fun _ => [])
      ![UnaryTemplate.tape 4,List.replicate 6 false] := by
    obtain ⟨r,hr,ht,hh,hs⟩ := HierarchyFixedWord.word_ready (UnaryTemplate.tape 4)
    exact ⟨r,hr,ht,hh,hs.le⟩
  have hfirst := bounded_focus fourSlots four_injective _ _ _ firstReady (input h)
    (by intro i; fin_cases i <;> rfl)
  let mid := install fourSlots (input h) ![UnaryTemplate.tape 4,List.replicate 6 false]
  have secondReady : ClockJoin.ReadyRun (HierarchyFixedWord.machine [true]) 4 (fun _ => []) ![[true],[false]] := by
    obtain ⟨r,hr,ht,hh,hs⟩ := HierarchyFixedWord.word_ready [true]
    exact ⟨r,hr,ht,hh,hs.le⟩
  have hlast := bounded_focus oneSlots one_injective _ _ _ secondReady mid
    (by
      intro i
      fin_cases i
      · exact install_other fourSlots _ _ 3 (by decide)
      · exact install_other fourSlots _ _ 4 (by decide))
  have hall := ClockJoin.join four one _ _ _ _ _ hfirst hlast
  have he : install oneSlots mid ![[true],[false]]=constantOutput h := by
    funext i
    simp only [install,one_pick,mid,four_pick]
    fin_cases i <;> simp [onePick,fourPick,input,constantOutput]
  rw [he] at hall
  exact hall

theorem product_ready (h : ℕ) : ClockJoin.ReadyRun product (WilliamsUnaryProduct.budget h 4)
    (constantOutput h) (productOutput h) := by
  have hrun := bounded_focus productSlots product_injective _ _ _ (CompetitorDimensions.unary_ready h 4)
    (constantOutput h) (by intro i; fin_cases i <;> rfl)
  have he : install productSlots (constantOutput h) (WilliamsUnaryProduct.output h 4)=productOutput h := by
    funext i
    simp only [install,product_pick]
    fin_cases i <;> simp [productPick,constantOutput,productOutput,WilliamsUnaryProduct.output,Nat.mul_comm]
  rw [he] at hrun
  exact hrun

theorem sum_ready (h : ℕ) : ClockJoin.ReadyRun sum (2*(4*h+1)+6) (productOutput h) (sumOutput h) := by
  have hrun := bounded_focus sumSlots sum_injective _ _ _ (ClockUnarySum.sum_ready (4*h) 1)
    (productOutput h) (by intro i; fin_cases i <;> rfl)
  have he : install sumSlots (productOutput h)
      ![List.replicate (4*h) true,List.replicate 1 true,List.replicate (4*h+1) true,List.replicate (4*h+1+2) false]=sumOutput h := by
    funext i
    simp only [install,sum_pick]
    fin_cases i <;> simp [sumPick,productOutput,sumOutput,Nat.add_assoc]
  rw [he] at hrun
  exact hrun

theorem driver_ready (h : ℕ) : ∃ out,ClockJoin.ReadyRun machine (budget h) (input h) out ∧
    out 0=List.replicate h true ∧ out 9=List.replicate (4*h+1) true ∧ out 10=List.replicate (4*h+1) true ∧
    out 11=UnaryTemplate.tape (4*h+1) := by
  obtain ⟨base,hb,b9,b10,b11,bh,bs⟩ := MatrixRawDimension.reset_run (4*h+1)
  have hready : ClockJoin.ReadyRun MatrixRawDimension.resetMachine (4*(4*h+1)+8)
      (MatrixRawDimension.resetInput (4*h+1)) base.final.tapes := ⟨base,hb,rfl,bh,bs.le⟩
  have hlast := bounded_focus templateSlots (by decide) _ _ _ hready (sumOutput h)
    (by intro i; fin_cases i <;> rfl)
  have htail := ClockJoin.join sum template _ _ _ _ _ (sum_ready h) hlast
  have harith := ClockJoin.join product (Composition.machine sum template) _ _ _ _ _ (product_ready h) htail
  have hall := ClockJoin.join constants arithmetic _ _ _ _ _ (constants_ready h) harith
  have he : 19+1+(WilliamsUnaryProduct.budget h 4+1+((2*(4*h+1)+6)+1+(4*(4*h+1)+8)))=budget h := by
    unfold budget WilliamsUnaryProduct.budget
    omega
  rw [he] at hall
  refine ⟨_,hall,?_,?_,?_,?_⟩
  · exact install_other templateSlots _ _ 0 (by decide)
  · exact (install_slot templateSlots (by decide) _ _ 1).trans b9
  · exact (install_slot templateSlots (by decide) _ _ 2).trans b10
  · exact (install_slot templateSlots (by decide) _ _ 3).trans b11

end NearCubicWires.RepairOrdinary.CompetitorSameBucketRecordDriver
