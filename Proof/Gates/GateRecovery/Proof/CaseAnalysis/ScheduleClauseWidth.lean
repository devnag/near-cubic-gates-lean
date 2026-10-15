import Proof.CaseAnalysis.ScheduleClog
import Proof.PCP.ProjectionDimensionPolynomialBounds
import Proof.Amplification.RecoveryTseitinRawIncrement
import Proof.Gates.GateRecovery.Proof.CaseAnalysis.Language

namespace GR

/-! One cold ordinary program computes the literal selected clause width
clog(2,(q+2)^D). The degree is fixed before the hierarchy clock; no ceiling
logarithm or exponentiation is treated as a machine instruction. -/
namespace NearCubicWires.RepairSource.CloseoutSchedule.Clause
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound VerifierDecoding
open ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem increment_cold (q : Nat) : ClockJoin.ReadyRun RecoveryTseitinRawIncrement.machine
    (2*q+4) ![List.replicate q true,[]]
    ![List.replicate (q+1) true,List.replicate (q+1) false] := by
  obtain ⟨a,ha,hf,hs⟩:=RecoveryTseitinRawIncrement.raw_run q
  obtain ⟨r,hr,rt,rl,rh,rs,_⟩:=Rewind.Workspace.reset_workspace
    RecoveryTseitinRawIncrement.raw _ _ a ha 0
  have he : 2*a.steps+2=2*q+4 := by omega
  rw [he] at hr
  have hi : (Fin.addCases (motive:=fun _ : Fin 2=>List Bool)
      (fun _ : Fin 1=>List.replicate q true) (fun _ : Fin 1=>List.replicate 0 false))=
      ![List.replicate q true,[]] := by funext i;fin_cases i <;> rfl
  rw [hi] at hr
  refine ⟨r,hr,?_,rh,by omega⟩
  funext i;fin_cases i
  · simpa [hf,RecoveryTseitinRawIncrement.cfg] using rt 0
  · simpa [hs] using rl

def tapes (D : Nat) := 26+2*D
def incrementSlots (D : Nat) : Fin 2→Fin (tapes D) := fun i=>⟨i.val,by have:=i.isLt;dsimp [tapes];omega⟩
def polynomialSlots (D : Nat) : Fin (DimensionPolynomial.tapes D)→Fin (tapes D) :=
  fun i=>⟨if i.val=0 then 0 else i.val+1,by have:=i.isLt;dsimp [tapes,DimensionPolynomial.tapes] at *;split_ifs <;> omega⟩
def clogSlots (D : Nat) : Fin 12→Fin (tapes D) :=
  fun i=>⟨if i.val=0 then 6+2*D else 14+2*D+i.val,by have:=i.isLt;dsimp [tapes];split_ifs <;> omega⟩
theorem increment_injective (D : Nat) : Function.Injective (incrementSlots D) := by
  intro a b h
  have hv:=congrArg (fun i : Fin (tapes D)=>i.val) h
  exact Fin.ext hv
theorem polynomial_injective (D : Nat) : Function.Injective (polynomialSlots D) := by
  intro a b h
  have hv:=congrArg Fin.val h
  apply Fin.ext
  dsimp only [polynomialSlots] at hv
  split_ifs at hv <;> omega
theorem clog_injective (D : Nat) : Function.Injective (clogSlots D) := by
  intro a b h
  have hv:=congrArg Fin.val h
  apply Fin.ext
  dsimp only [clogSlots] at hv
  split_ifs at hv <;> omega

def input (D q : Nat) : Fin (tapes D)→List Bool := fun i=>if i.val=0 then List.replicate q true else []
def incremented (D q : Nat) := install (incrementSlots D) (input D q)
  ![List.replicate (q+1) true,List.replicate (q+1) false]
def increment (D : Nat) := RecoveryFocus.machine (incrementSlots D) RecoveryTseitinRawIncrement.machine
def polynomial (D : Nat) := RecoveryFocus.machine (polynomialSlots D) (DimensionPolynomial.machine D 1)
def clog (D : Nat) := RecoveryFocus.machine (clogSlots D) Clog.machine
def machine (D : Nat) := Composition.machine (Composition.machine (increment D) (polynomial D)) (clog D)
def widthSlot (D : Nat) := clogSlots D 10
def qSlot (D : Nat) : Fin (tapes D) := ⟨0,by simp [tapes]⟩
def budget (D q : Nat) := (2*q+4)+1+DimensionPolynomial.budget D 1 (q+1)+1+Clog.budget ((q+2)^D)

theorem clause_run (D q : Nat) (hD : 1 ≤ D) : ∃ out,
    ClockJoin.ReadyRun (machine D) (budget D q) (input D q) out ∧
      out (qSlot D)=List.replicate (q+1) true ∧
      out (widthSlot D)=CompareMachine.word (CloseoutLanguage.clauseWidth D q) := by
  have hi:=(increment_cold q).focus (incrementSlots D) (increment_injective D) (input D q)
    (by intro i;fin_cases i <;> rfl)
  change ClockJoin.ReadyRun (increment D) (2*q+4) (input D q) (incremented D q) at hi
  have inc_zero : incremented D q (qSlot D)=List.replicate (q+1) true := by
    change install (incrementSlots D) _ _ (incrementSlots D 0)=_
    rw [install_slot _ (increment_injective D)]
    rfl
  have inc_blank (i : Fin (tapes D)) (h : 2 ≤ i.val) : incremented D q i=[] := by
    rw [incremented,install_other _ _ _ _ (by
      intro j hj;have hv:=congrArg Fin.val hj;have:=j.isLt;dsimp [incrementSlots] at hv;omega)]
    simp [input,show i.val≠0 by omega]
  obtain ⟨powerOut,hp,hq,hv,_,_⟩:=DimensionPolynomial.polynomial_run D 1 (q+1) (by decide)
  have hpf:=hp.focus (polynomialSlots D) (polynomial_injective D) (incremented D q) (by
    intro i
    by_cases he : i.val=0
    · have hz : i=⟨0,by simp [DimensionPolynomial.tapes]⟩:=Fin.ext he
      subst i
      exact inc_zero
    · rw [DimensionPolynomial.input,if_neg he]
      exact inc_blank _ (by simp [polynomialSlots,he];omega))
  let afterPower:=install (polynomialSlots D) (incremented D q) powerOut
  change ClockJoin.ReadyRun (polynomial D) (DimensionPolynomial.budget D 1 (q+1))
    (incremented D q) afterPower at hpf
  have power_zero : afterPower (qSlot D)=List.replicate (q+1) true := by
    change install (polynomialSlots D) _ _ (polynomialSlots D ⟨0,by simp [DimensionPolynomial.tapes]⟩)=_
    rw [install_slot _ (polynomial_injective D)]
    exact hq
  have power_value : afterPower (clogSlots D 0)=List.replicate ((q+2)^D) true := by
    have he : clogSlots D 0=polynomialSlots D (DimensionPolynomial.rawSlot D) := by
      apply Fin.ext
      simp [clogSlots,polynomialSlots,DimensionPolynomial.rawSlot,DimensionPolynomial.binarySlots]
      omega
    rw [he]
    change install (polynomialSlots D) _ _ _=_
    rw [install_slot _ (polynomial_injective D)]
    simpa [DimensionPolynomial.value,Nat.add_assoc] using hv
  have power_blank (i : Fin (tapes D)) (h : 15+2*D ≤ i.val) : afterPower i=[] := by
    dsimp only [afterPower]
    rw [install_other _ _ _ _ (by
      intro j hj;have hv:=congrArg Fin.val hj;have:=j.isLt
      dsimp [polynomialSlots,DimensionPolynomial.tapes] at hv this
      split_ifs at hv <;> omega)]
    exact inc_blank i (by omega)
  have hval : 2 ≤ (q+2)^D := by
    exact (show 2 ≤ q+2 by omega).trans (Nat.le_self_pow (by omega) _)
  obtain ⟨clogOut,hc,hw⟩:=Clog.clog_run ((q+2)^D) hval
  have hcf:=hc.focus (clogSlots D) (clog_injective D) afterPower (by
    intro i
    by_cases he : i=0
    · subst i;exact power_value
    · rw [Clog.input,if_neg he]
      have hv : i.val≠0 := by intro h;exact he (Fin.ext h)
      exact power_blank _ (by simp [clogSlots,hv];omega))
  refine ⟨_,ClockJoin.join _ _ _ _ _ _ _ (ClockJoin.join _ _ _ _ _ _ _ hi hpf) hcf,?_,?_⟩
  · rw [install_other _ _ _ _ (by
      intro j hj;have hv:=congrArg Fin.val hj
      dsimp [clogSlots,qSlot] at hv;split_ifs at hv <;> omega)]
    exact power_zero
  · rw [widthSlot,install_slot _ (clog_injective D)]
    exact hw

end
end NearCubicWires.RepairSource.CloseoutSchedule.Clause

end GR
