import Proof.MachineModel.OrdinaryMatrixVariablePacketCapacity
import Proof.MachineModel.ClockUnarySum

/-! Physical U+1 and d+p+1 sentinels from the actual retained U/d/p.
These feed the packet workspace capacity polynomial; no derived dimension
is installed by the caller. -/
namespace NearCubicWires.RepairOrdinary.MatrixPacketCapacityDimensions
open LocalBitMultitape RecoveryRootRound
open RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots0 : Fin 5 → Fin 21 := ![0,3,4,5,6]
theorem inj0 : Function.Injective slots0 := by decide
theorem pick0 (i : Fin 21) : RecoveryFocus.pick slots0 i=(![some 0,none,none,some 1,some 2,some 3,some 4,none,none,none,none,none,none,none,none,none,none,none,none,none,none] : Fin 21 → Option (Fin 5)) i := by
  fin_cases i
  · exact RecoveryFocus.pick_slot slots0 inj0 0
  · decide
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
  · decide
  · decide
noncomputable def program0 := RecoveryFocus.machine slots0 (MatrixTemplateCopy.resetMachine)
def slots1 : Fin 5 → Fin 21 := ![1,7,8,9,10]
theorem inj1 : Function.Injective slots1 := by decide
theorem pick1 (i : Fin 21) : RecoveryFocus.pick slots1 i=(![none,some 0,none,none,none,none,none,some 1,some 2,some 3,some 4,none,none,none,none,none,none,none,none,none,none] : Fin 21 → Option (Fin 5)) i := by
  fin_cases i
  · decide
  · exact RecoveryFocus.pick_slot slots1 inj1 0
  · decide
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
  · decide
  · decide
noncomputable def program1 := RecoveryFocus.machine slots1 (MatrixTemplateCopy.resetMachine)
def slots2 : Fin 5 → Fin 21 := ![2,11,12,13,14]
theorem inj2 : Function.Injective slots2 := by decide
theorem pick2 (i : Fin 21) : RecoveryFocus.pick slots2 i=(![none,none,some 0,none,none,none,none,none,none,none,none,some 1,some 2,some 3,some 4,none,none,none,none,none,none] : Fin 21 → Option (Fin 5)) i := by
  fin_cases i
  · decide
  · decide
  · exact RecoveryFocus.pick_slot slots2 inj2 0
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · exact RecoveryFocus.pick_slot slots2 inj2 1
  · exact RecoveryFocus.pick_slot slots2 inj2 2
  · exact RecoveryFocus.pick_slot slots2 inj2 3
  · exact RecoveryFocus.pick_slot slots2 inj2 4
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
noncomputable def program2 := RecoveryFocus.machine slots2 (MatrixTemplateCopy.resetMachine)
def slots3 : Fin 4 → Fin 21 := ![7,11,15,16]
theorem inj3 : Function.Injective slots3 := by decide
theorem pick3 (i : Fin 21) : RecoveryFocus.pick slots3 i=(![none,none,none,none,none,none,none,some 0,none,none,none,some 1,none,none,none,some 2,some 3,none,none,none,none] : Fin 21 → Option (Fin 4)) i := by
  fin_cases i
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · exact RecoveryFocus.pick_slot slots3 inj3 0
  · decide
  · decide
  · decide
  · exact RecoveryFocus.pick_slot slots3 inj3 1
  · decide
  · decide
  · decide
  · exact RecoveryFocus.pick_slot slots3 inj3 2
  · exact RecoveryFocus.pick_slot slots3 inj3 3
  · decide
  · decide
  · decide
  · decide
noncomputable def program3 := RecoveryFocus.machine slots3 (ClockUnarySum.machine)
def slots4 : Fin 3 → Fin 21 := ![15,17,18]
theorem inj4 : Function.Injective slots4 := by decide
theorem pick4 (i : Fin 21) : RecoveryFocus.pick slots4 i=(![none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,some 0,none,some 1,some 2,none,none] : Fin 21 → Option (Fin 3)) i := by
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
  · decide
  · exact RecoveryFocus.pick_slot slots4 inj4 0
  · decide
  · exact RecoveryFocus.pick_slot slots4 inj4 1
  · exact RecoveryFocus.pick_slot slots4 inj4 2
  · decide
  · decide
noncomputable def program4 := RecoveryFocus.machine slots4 (DimensionTemplate.machine true)
def slots5 : Fin 3 → Fin 21 := ![3,19,20]
theorem inj5 : Function.Injective slots5 := by decide
theorem pick5 (i : Fin 21) : RecoveryFocus.pick slots5 i=(![none,none,none,some 0,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,some 1,some 2] : Fin 21 → Option (Fin 3)) i := by
  fin_cases i
  · decide
  · decide
  · decide
  · exact RecoveryFocus.pick_slot slots5 inj5 0
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
  · decide
  · exact RecoveryFocus.pick_slot slots5 inj5 1
  · exact RecoveryFocus.pick_slot slots5 inj5 2
noncomputable def program5 := RecoveryFocus.machine slots5 (DimensionTemplate.machine true)
noncomputable def machine := Composition.machine
  (Composition.machine (Composition.machine (Composition.machine (Composition.machine program0 program1) program2) program3) program4) program5
def input (U d p : ℕ) : Fin 21 → List Bool := fun i => if i=0 then UnaryTemplate.tape U else if i=1 then UnaryTemplate.tape d else if i=2 then UnaryTemplate.tape p else []
noncomputable def data1 (U d p : ℕ) := install slots0 (input U d p) (MatrixPacketDimensions.copied U)
noncomputable def data2 (U d p : ℕ) := install slots1 (data1 U d p) (MatrixPacketDimensions.copied d)
noncomputable def data3 (U d p : ℕ) := install slots2 (data2 U d p) (MatrixPacketDimensions.copied p)
noncomputable def data4 (U d p : ℕ) := install slots3 (data3 U d p) (![List.replicate d true,List.replicate p true,List.replicate (d+p) true,List.replicate (d+p+2) false])
noncomputable def data5 (U d p : ℕ) := install slots4 (data4 U d p) (DimensionTemplate.output true (d+p))
noncomputable def data6 (U d p : ℕ) := install slots5 (data5 U d p) (DimensionTemplate.output true U)
def budget (U d p : ℕ) := 6*U+8*d+8*p+63

theorem dimensions_ready (U d p : ℕ) : ClockJoin.ReadyRun machine (budget U d p) (input U d p) (data6 U d p) := by
  have h0 := (MatrixPacketDimensions.copy_ready U).focus slots0 inj0 (input U d p) (by
    intro i; fin_cases i
    all_goals simp only [input,slots0,MatrixTemplateCopy.resetInput,MatrixTemplateCopy.input,Fin.addCases]; rfl)
  have h1 := (MatrixPacketDimensions.copy_ready d).focus slots1 inj1 (data1 U d p) (by
    intro i; fin_cases i
    all_goals simp only [data1,install,pick0,input,MatrixPacketDimensions.copied,slots1,MatrixTemplateCopy.resetInput,MatrixTemplateCopy.input,Fin.addCases]; rfl)
  have h2 := (MatrixPacketDimensions.copy_ready p).focus slots2 inj2 (data2 U d p) (by
    intro i; fin_cases i
    all_goals simp only [data2,data1,install,pick0,pick1,input,MatrixPacketDimensions.copied,slots2,MatrixTemplateCopy.resetInput,MatrixTemplateCopy.input,Fin.addCases]; rfl)
  have h3 := (ClockUnarySum.sum_ready d p).focus slots3 inj3 (data3 U d p) (by
    intro i; fin_cases i
    all_goals simp only [data3,data2,data1,install,pick0,pick1,pick2,input,MatrixPacketDimensions.copied,slots3]; rfl)
  have h4 := (DimensionTemplate.ready true (d+p)).focus slots4 inj4 (data4 U d p) (by
    intro i; fin_cases i
    all_goals simp only [data4,data3,data2,data1,install,pick0,pick1,pick2,pick3,input,MatrixPacketDimensions.copied,slots4,DimensionTemplate.input]; rfl)
  have h5 := (DimensionTemplate.ready true U).focus slots5 inj5 (data5 U d p) (by
    intro i; fin_cases i
    all_goals simp only [data5,data4,data3,data2,data1,install,pick0,pick1,pick2,pick3,pick4,input,MatrixPacketDimensions.copied,slots5,DimensionTemplate.input,DimensionTemplate.output]; rfl)
  have joined := ClockJoin.join _ _ _ _ _ _ _ (ClockJoin.join _ _ _ _ _ _ _ (ClockJoin.join _ _ _ _ _ _ _ (ClockJoin.join _ _ _ _ _ _ _ (ClockJoin.join _ _ _ _ _ _ _ h0 h1) h2) h3) h4) h5
  have hb : (((((4*U+12)+1+(4*d+12))+1+(4*p+12))+1+(2*(d+p)+6))+1+(2*(d+p)+8))+1+(2*U+8)=budget U d p := by
    unfold budget
    ring
  rw [hb] at joined
  exact joined

theorem output_fields (U d p : ℕ) : (data6 U d p) 0=UnaryTemplate.tape U ∧ (data6 U d p) 1=UnaryTemplate.tape d ∧ (data6 U d p) 2=UnaryTemplate.tape p ∧ (data6 U d p) 17=UnaryTemplate.tape (d+p+1) ∧ (data6 U d p) 19=UnaryTemplate.tape (U+1) := by
  simp only [data6,data5,data4,data3,data2,data1,install,pick0,pick1,pick2,pick3,pick4,pick5,input,MatrixPacketDimensions.copied,DimensionTemplate.output]
  simp

end NearCubicWires.RepairOrdinary.MatrixPacketCapacityDimensions
