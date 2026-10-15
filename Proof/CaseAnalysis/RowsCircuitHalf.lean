import Proof.CaseAnalysis.RowsCircuitNativePrefix
import Proof.MachineModel.OrdinaryMatrixBucketDivide
import Proof.MachineModel.UWalkArithmetic

/-! Divide an actually produced small description counter by two. The
fixed divisor is printed and the existing native quotient restores every
head. The possibly larger policy cap is not copied into scratch. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsCircuitHalf
open LocalBitMultitape RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def literalSlots : Fin 2 → Fin 5 := ![1,2]
def divideSlots : Fin 4 → Fin 5 := ![0,1,3,4]
noncomputable def literal:=RecoveryFocus.machine literalSlots (HierarchyFixedWord.machine (UnaryTemplate.tape 2))
noncomputable def divide:=RecoveryFocus.machine divideSlots MatrixBucketDivide.machine
noncomputable def machine:=Composition.machine literal divide
def input (n : ℕ) : Fin 5 → List Bool := ![List.replicate n true,[],[],[],[]]
def middle (n : ℕ) : Fin 5 → List Bool :=
  ![List.replicate n true,UnaryTemplate.tape 2,List.replicate 4 false,[],[]]
def budget (n : ℕ):=8*n+17

theorem half_run (n : ℕ) : ∃ out,
    ClockJoin.ReadyRun machine (budget n) (input n) out ∧
      out 0=List.replicate n true ∧ out 3=List.replicate (n/2) true:=by
  have lit:=(UWalkNumbers.fixed_ready (UnaryTemplate.tape 2)).focus literalSlots (by decide) (input n)
    (by intro i;fin_cases i <;> rfl)
  have lm:install literalSlots (input n)
      ![UnaryTemplate.tape 2,List.replicate (UnaryTemplate.tape 2).length false]=middle n:=by
    funext i;fin_cases i
    · exact install_other _ _ _ _ (by decide)
    · exact install_slot _ (by decide : Function.Injective literalSlots) _ _ 0
    · exact install_slot _ (by decide : Function.Injective literalSlots) _ _ 1
    · exact install_other _ _ _ _ (by decide)
    · exact install_other _ _ _ _ (by decide)
  rw [lm] at lit
  obtain ⟨r,hr,r0,_r1,r2,rh,rs⟩:=MatrixBucketDivide.divide_run n 2 (by decide)
  have quotient:ClockJoin.ReadyRun MatrixBucketDivide.machine (8*n+6)
      (MatrixBucketDivide.resetInput n 2) r.final.tapes:=⟨r,hr,rfl,rh,rs⟩
  have q:=quotient.focus divideSlots (by decide) (middle n) (by intro i;fin_cases i <;> rfl)
  have all:=ClockJoin.join literal divide _ _ _ _ _ lit q
  have ht:(2*(UnaryTemplate.tape 2).length+2)+1+(8*n+6)=budget n:=by
    change (2*4+2)+1+(8*n+6)=8*n+17
    omega
  rw [ht] at all
  refine ⟨_,all,?_,?_⟩
  · exact (install_slot divideSlots (by decide) _ _ 0).trans r0
  · exact (install_slot divideSlots (by decide) _ _ 2).trans r2

end NearCubicWires.RepairOrdinary.CloseoutRowsCircuitHalf
