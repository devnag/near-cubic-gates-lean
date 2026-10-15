import Proof.MachineModel.OrdinaryMatrixPacketAppend
import Proof.PCP.ProjectionDimensionTemplate

/-! Produce the native count-bit sentinel from retained U and d templates.
All copies, successor construction, both products and final sentinels are
executed; the caller supplies no U² or native-width driver. -/
namespace NearCubicWires.RepairOrdinary.MatrixPacketDimensions
open LocalBitMultitape RecoveryRootRound
open RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def copied (n : ℕ) : Fin 5 → List Bool :=
  ![UnaryTemplate.tape n,List.replicate n true,List.replicate n true,UnaryTemplate.tape n,List.replicate (2*n+5) false]

theorem copy_ready (n : ℕ) : ClockJoin.ReadyRun MatrixTemplateCopy.resetMachine (4*n+12)
    (MatrixTemplateCopy.resetInput n) (copied n) := by
  obtain ⟨base,hb,h0,h1,h2,h3,bs⟩ := MatrixTemplateCopy.copy_run n
  obtain ⟨actual,ha,ht,log,hh,hs,_⟩ := Rewind.Workspace.reset_workspace MatrixTemplateCopy.machine _ _ base hb 0
  have htime : 2*base.steps+2=4*n+12 := by omega
  rw [htime] at ha hs
  refine ⟨actual,ha,?_,hh,hs.le⟩
  funext i; fin_cases i
  · exact (ht 0).trans h0
  · exact (ht 1).trans h1
  · exact (ht 2).trans h2
  · exact (ht 3).trans h3
  · change actual.final.tapes 4=List.replicate (2*n+5) false
    simpa [Fin.natAdd,bs] using log

def slots0 : Fin 5 → Fin 18 := ![0,2,3,4,5]
theorem inj0 : Function.Injective slots0 := by decide
theorem pick0 (i : Fin 18) : RecoveryFocus.pick slots0 i=(![some 0,none,some 1,some 2,some 3,some 4,none,none,none,none,none,none,none,none,none,none,none,none] : Fin 18 → Option (Fin 5)) i := by
  fin_cases i
  · exact RecoveryFocus.pick_slot slots0 inj0 0
  · decide
  · exact RecoveryFocus.pick_slot slots0 inj0 1
  · exact RecoveryFocus.pick_slot slots0 inj0 2
  · exact RecoveryFocus.pick_slot slots0 inj0 3
  · exact RecoveryFocus.pick_slot slots0 inj0 4
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
def slots1 : Fin 5 → Fin 18 := ![1,6,7,8,9]
theorem inj1 : Function.Injective slots1 := by decide
theorem pick1 (i : Fin 18) : RecoveryFocus.pick slots1 i=(![none,some 0,none,none,none,none,some 1,some 2,some 3,some 4,none,none,none,none,none,none,none,none] : Fin 18 → Option (Fin 5)) i := by
  fin_cases i
  · decide
  · exact RecoveryFocus.pick_slot slots1 inj1 0
  · decide
  · decide
  · decide
  · decide
  · exact RecoveryFocus.pick_slot slots1 inj1 1
  · exact RecoveryFocus.pick_slot slots1 inj1 2
  · exact RecoveryFocus.pick_slot slots1 inj1 3
  · exact RecoveryFocus.pick_slot slots1 inj1 4
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
def slots2 : Fin 3 → Fin 18 := ![6,10,11]
theorem inj2 : Function.Injective slots2 := by decide
theorem pick2 (i : Fin 18) : RecoveryFocus.pick slots2 i=(![none,none,none,none,none,none,some 0,none,none,none,some 1,some 2,none,none,none,none,none,none] : Fin 18 → Option (Fin 3)) i := by
  fin_cases i
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · exact RecoveryFocus.pick_slot slots2 inj2 0
  · decide
  · decide
  · decide
  · exact RecoveryFocus.pick_slot slots2 inj2 1
  · exact RecoveryFocus.pick_slot slots2 inj2 2
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
def slots3 : Fin 4 → Fin 18 := ![2,0,12,13]
theorem inj3 : Function.Injective slots3 := by decide
theorem pick3 (i : Fin 18) : RecoveryFocus.pick slots3 i=(![some 1,none,some 0,none,none,none,none,none,none,none,none,none,some 2,some 3,none,none,none,none] : Fin 18 → Option (Fin 4)) i := by
  fin_cases i
  · exact RecoveryFocus.pick_slot slots3 inj3 1
  · decide
  · exact RecoveryFocus.pick_slot slots3 inj3 0
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · exact RecoveryFocus.pick_slot slots3 inj3 2
  · exact RecoveryFocus.pick_slot slots3 inj3 3
  · decide
  · decide
  · decide
  · decide
def slots4 : Fin 4 → Fin 18 := ![12,10,14,15]
theorem inj4 : Function.Injective slots4 := by decide
theorem pick4 (i : Fin 18) : RecoveryFocus.pick slots4 i=(![none,none,none,none,none,none,none,none,none,none,some 1,none,some 0,none,some 2,some 3,none,none] : Fin 18 → Option (Fin 4)) i := by
  fin_cases i
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · exact RecoveryFocus.pick_slot slots4 inj4 1
  · decide
  · exact RecoveryFocus.pick_slot slots4 inj4 0
  · decide
  · exact RecoveryFocus.pick_slot slots4 inj4 2
  · exact RecoveryFocus.pick_slot slots4 inj4 3
  · decide
  · decide
def slots5 : Fin 3 → Fin 18 := ![14,16,17]
theorem inj5 : Function.Injective slots5 := by decide
theorem pick5 (i : Fin 18) : RecoveryFocus.pick slots5 i=(![none,none,none,none,none,none,none,none,none,none,none,none,none,none,some 0,none,some 1,some 2] : Fin 18 → Option (Fin 3)) i := by
  fin_cases i
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · exact RecoveryFocus.pick_slot slots5 inj5 0
  · decide
  · exact RecoveryFocus.pick_slot slots5 inj5 1
  · exact RecoveryFocus.pick_slot slots5 inj5 2
noncomputable def program0 := RecoveryFocus.machine slots0 (MatrixTemplateCopy.resetMachine)
noncomputable def program1 := RecoveryFocus.machine slots1 (MatrixTemplateCopy.resetMachine)
noncomputable def program2 := RecoveryFocus.machine slots2 (DimensionTemplate.machine true)
noncomputable def program3 := RecoveryFocus.machine slots3 (ClockUnaryProduct.machine)
noncomputable def program4 := RecoveryFocus.machine slots4 (ClockUnaryProduct.machine)
noncomputable def program5 := RecoveryFocus.machine slots5 (DimensionTemplate.machine false)
noncomputable def machine := Composition.machine
  (Composition.machine (Composition.machine (Composition.machine (Composition.machine program0 program1) program2) program3) program4) program5

def input (U d : ℕ) : Fin 18 → List Bool := fun i => if i=0 then UnaryTemplate.tape U else if i=1 then UnaryTemplate.tape d else []
noncomputable def data1 (U d : ℕ) := install slots0 (input U d) (copied U)
noncomputable def data2 (U d : ℕ) := install slots1 (data1 U d) (copied d)
noncomputable def data3 (U d : ℕ) := install slots2 (data2 U d) (DimensionTemplate.output true d)
noncomputable def data4 (U d : ℕ) := install slots3 (data3 U d) (WilliamsUnaryProduct.output U U)
noncomputable def data5 (U d : ℕ) := install slots4 (data4 U d) (WilliamsUnaryProduct.output (U*U) (d+1))
noncomputable def output (U d : ℕ) := install slots5 (data5 U d) (DimensionTemplate.output false (U*U*(d+1)))
def budget (U d : ℕ) := 6*U^2*(d+1)+10*U^2+10*U+6*d+57

theorem dimensions_ready (U d : ℕ) : ClockJoin.ReadyRun machine (budget U d) (input U d) (output U d) := by
  have h0 := (copy_ready U).focus slots0 inj0 (input U d) (by
    intro i; fin_cases i
    all_goals simp only [input,slots0,MatrixTemplateCopy.resetInput,MatrixTemplateCopy.input,Fin.addCases]; rfl)
  have h1 := (copy_ready d).focus slots1 inj1 (data1 U d) (by
    intro i; fin_cases i
    all_goals simp only [data1,install,pick0,input,copied,slots1,MatrixTemplateCopy.resetInput,MatrixTemplateCopy.input,Fin.addCases]; rfl)
  have h2 := (DimensionTemplate.ready true d).focus slots2 inj2 (data2 U d) (by
    intro i; fin_cases i
    all_goals simp only [data2,data1,install,pick0,pick1,input,copied,slots2,DimensionTemplate.input]; rfl)
  have h3 := ((show ClockJoin.ReadyRun _ _ _ _ from let ⟨r,hr,ht,hh,hs⟩ := WilliamsUnaryProduct.product_ready U U; ⟨r,hr,ht,hh,hs.le⟩)).focus slots3 inj3 (data3 U d) (by
    intro i; fin_cases i
    all_goals simp only [data3,data2,data1,install,pick0,pick1,pick2,input,copied,slots3,DimensionTemplate.output,WilliamsUnaryProduct.input]; rfl)
  have h4 := ((show ClockJoin.ReadyRun _ _ _ _ from let ⟨r,hr,ht,hh,hs⟩ := WilliamsUnaryProduct.product_ready (U*U) (d+1); ⟨r,hr,ht,hh,hs.le⟩)).focus slots4 inj4 (data4 U d) (by
    intro i; fin_cases i
    all_goals simp only [data4,data3,data2,data1,install,pick0,pick1,pick2,pick3,input,copied,slots4,DimensionTemplate.output,WilliamsUnaryProduct.input,WilliamsUnaryProduct.output]; rfl)
  have h5 := (DimensionTemplate.ready false (U*U*(d+1))).focus slots5 inj5 (data5 U d) (by
    intro i; fin_cases i
    all_goals simp only [data5,data4,data3,data2,data1,install,pick0,pick1,pick2,pick3,pick4,input,copied,slots5,DimensionTemplate.input,DimensionTemplate.output,WilliamsUnaryProduct.output]; rfl)
  have joined := ClockJoin.join _ _ _ _ _ _ _
    (ClockJoin.join _ _ _ _ _ _ _
      (ClockJoin.join _ _ _ _ _ _ _
        (ClockJoin.join _ _ _ _ _ _ _
          (ClockJoin.join _ _ _ _ _ _ _ h0 h1) h2) h3) h4) h5
  have hb : ((((4*U+12)+1+(4*d+12))+1+(2*d+8))+1+WilliamsUnaryProduct.budget U U)+1+
      WilliamsUnaryProduct.budget (U*U) (d+1)+1+(2*(U*U*(d+1))+8)=budget U d := by
    unfold budget WilliamsUnaryProduct.budget
    ring
  rw [hb] at joined
  exact joined

theorem output_fields (U d : ℕ) : output U d 0=UnaryTemplate.tape U ∧ output U d 1=UnaryTemplate.tape d ∧
    output U d 16=UnaryTemplate.tape (U^2*(d+1)) := by
  simp only [output,data5,data4,data3,data2,data1,install,pick0,pick1,pick2,pick3,pick4,pick5,
    input,copied,DimensionTemplate.output,WilliamsUnaryProduct.output]
  simp [pow_two]

end NearCubicWires.RepairOrdinary.MatrixPacketDimensions
