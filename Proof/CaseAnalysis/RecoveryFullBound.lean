import Proof.CaseAnalysis.PairClockExact
import Proof.CaseAnalysis.ScheduleClog
import Proof.MachineModel.UWalkUnary
import Proof.PCP.ProjectionDimensionPolynomialBounds

/-! The exact full canonical-search cap from its actual raw width. The
existing power producer writes FULLB+1; one paid first-cell rewrite gives
Compare(FULLB), and the existing sentinel copier writes raw FULLB. -/
namespace NearCubicWires.RepairOrdinary.RecoveryFullBound
open LocalBitMultitape RepairSource RecoveryScheduleEnvelope RecoveryRootRound
open RepairSource.ProjectionNormalization RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def exponent (d : ℕ) := 2^oracleDepth d
def base (d : ℕ) := DimensionPolynomial.tapes (exponent d)
def tapes (d : ℕ) := base d+2
def old (d : ℕ) (i : Fin (base d)) : Fin (tapes d) := i.castAdd 2
def extra (d : ℕ) (i : Fin 2) : Fin (tapes d) := i.natAdd (base d)
def sourceSlot (d : ℕ) : Fin (tapes d) := old d ⟨0,by simp [base,DimensionPolynomial.tapes]⟩
def compareSlot (d : ℕ) := old d (DimensionPolynomial.rawSlot (exponent d))
def rawSlot (d : ℕ) := extra d 0
def logSlot (d : ℕ) := extra d 1
def clearSlots (d : ℕ) : Fin 1→Fin (tapes d) := fun _=>compareSlot d
def copySlots (d : ℕ) : Fin 3→Fin (tapes d) := ![compareSlot d,rawSlot d,logSlot d]
def power (d : ℕ) := RecoveryFocus.machine (old d) (DimensionPolynomial.machine (exponent d) 1)
def clear (d : ℕ) := RecoveryFocus.machine (clearSlots d) LookupReadBit.clear
def copy (d : ℕ) := RecoveryFocus.machine (copySlots d) (UWalkUnary.machine false false)
def machine (d : ℕ) := Composition.machine (Composition.machine (power d) (clear d)) (copy d)
def input (d R : ℕ) (i : Fin (tapes d)) := if i.val=0 then List.replicate R true else []
def budget (d R : ℕ) := DimensionPolynomial.budget (exponent d) 1 R+2*oracleSizeBound d R+9

theorem old_injective (d : ℕ) : Function.Injective (old d) := by
  intro i j h
  exact Fin.ext (congrArg (fun x : Fin (tapes d)=>x.val) h)
theorem old_away (d : ℕ) (i : Fin 2) : ∀ j,old d j≠extra d i := by
  intro j h
  have hv:=congrArg Fin.val h
  have hj:=j.isLt
  simp only [old,extra,Fin.val_castAdd,Fin.val_natAdd] at hv
  omega
theorem clear_injective (d : ℕ) : Function.Injective (clearSlots d) :=
  fun i j _=>Subsingleton.elim i j
theorem compare_value (d : ℕ) : (compareSlot d).val=5+2*exponent d := by
  simp [compareSlot,old,DimensionPolynomial.rawSlot,DimensionPolynomial.binarySlots]
  omega
theorem copy_injective (d : ℕ) : Function.Injective (copySlots d) := by
  intro i j h
  have hv:=congrArg Fin.val h
  fin_cases i <;>fin_cases j <;>simp [copySlots,compareSlot,rawSlot,logSlot,old,extra,
    base,DimensionPolynomial.tapes,DimensionPolynomial.rawSlot,DimensionPolynomial.binarySlots] at hv ⊢ <;>omega
theorem copy_away_source (d : ℕ) : ∀ i,copySlots d i≠sourceSlot d := by
  intro i h
  have hv:=congrArg Fin.val h
  fin_cases i <;>simp [copySlots,compareSlot,rawSlot,logSlot,sourceSlot,old,extra,
    base,DimensionPolynomial.tapes,DimensionPolynomial.rawSlot,DimensionPolynomial.binarySlots] at hv

theorem power_value (d R : ℕ) : DimensionPolynomial.value (exponent d) 1 R=oracleSizeBound d R+1 := by
  simpa only [DimensionPolynomial.value,exponent,Nat.one_mul,oracleSizeBound] using
    (CloseoutPairClock.pairClock_succ_exact (oracleDepth d) R).symm

theorem cold_run (d R : ℕ) : ∃ out,
    ClockJoin.ReadyRun (machine d) (budget d R) (input d R) out ∧
      out (sourceSlot d)=List.replicate R true ∧
      out (rawSlot d)=List.replicate (oracleSizeBound d R) true ∧
      out (compareSlot d)=CompareMachine.word (oracleSizeBound d R) := by
  let B:=oracleSizeBound d R
  obtain ⟨A,ha,hR,hvalue,_,_⟩:=DimensionPolynomial.polynomial_run (exponent d) 1 R (by decide)
  rw [power_value] at hvalue
  have hp:=ha.focus (old d) (old_injective d) (input d R) (by intro i;rfl)
  let mid:=install (old d) (input d R) A
  have mid_extra (i : Fin 2) : mid (extra d i)=[] := by
    rw [show mid (extra d i)=input d R (extra d i) from install_other _ _ _ _ (old_away d i)]
    simp only [input,extra,Fin.val_natAdd]
    rw [if_neg (by unfold base DimensionPolynomial.tapes;omega)]
  have hc : ClockJoin.ReadyRun LookupReadBit.clear 1
      (fun _=>List.replicate (B+1) true) (fun _=>CompareMachine.word B) := by
    simpa only [Nat.add_sub_cancel] using CloseoutSchedule.Clog.clear_raw (B+1) (by omega)
  have hcf:=hc.focus (clearSlots d) (clear_injective d) mid (by
    intro i
    exact (install_slot (old d) (old_injective d) _ _ (DimensionPolynomial.rawSlot (exponent d))).trans hvalue)
  let marked:=install (clearSlots d) mid (fun _=>CompareMachine.word B)
  have marked_extra (i : Fin 2) : marked (extra d i)=[] := by
    rw [show marked (extra d i)=mid (extra d i) from install_other _ _ _ _ (by
      intro j h
      exact old_away d i (DimensionPolynomial.rawSlot (exponent d)) h)]
    exact mid_extra i
  have hb : ClockJoin.ReadyRun (UWalkUnary.machine false false) (2*B+6)
      ![CompareMachine.word B,[],[]]
      ![CompareMachine.word B,List.replicate B true,List.replicate (B+2) false] := by
    simpa [UWalkUnary.input,UWalkUnary.result,UWalkUnary.source,ZeroPadding.pad_zero,
      UWalkUnary.output,UWalkUnary.lead] using
        UWalkUnary.ready false false 0 B
  have hbf:=hb.focus (copySlots d) (copy_injective d) marked (by
    intro i
    fin_cases i
    · exact install_slot (clearSlots d) (clear_injective d) _ _ 0
    · exact marked_extra 0
    · exact marked_extra 1)
  have whole:=ClockJoin.join _ _ _ _ _ _ _ (ClockJoin.join _ _ _ _ _ _ _ hp hcf) hbf
  have he : (DimensionPolynomial.budget (exponent d) 1 R+1+1)+1+(2*B+6)=budget d R := by
    unfold budget
    dsimp only [B]
    omega
  rw [he] at whole
  refine ⟨_,whole,?_,?_,?_⟩
  · rw [install_other _ _ _ _ (copy_away_source d)]
    dsimp only [marked]
    rw [install_other _ _ _ _ (by
      intro i h
      exact copy_away_source d 0 h)]
    exact (install_slot (old d) (old_injective d) _ _ ⟨0,by simp [base,DimensionPolynomial.tapes]⟩).trans hR
  · exact install_slot (copySlots d) (copy_injective d) _ _ 1
  · exact install_slot (copySlots d) (copy_injective d) _ _ 0

end
end NearCubicWires.RepairOrdinary.RecoveryFullBound
