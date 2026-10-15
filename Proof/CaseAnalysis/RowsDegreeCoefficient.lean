import Proof.CaseAnalysis.RowsDegreeSign
import Proof.Hierarchy.CompetitorDenominator

/-! The actual binLift coefficient is computed once from unary j and the
common unary width p. Existing power, normalization and signed-field writers
produce its complete cached frame in linear short-width time. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsDegreeCoefficient
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open CloseoutRowsDegreeSign (positive)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def signSlots : Fin 3 → Fin 14 := ![0,2,3]
def powerSlots : Fin 6 → Fin 14 := ![0,4,5,6,7,8]
def normalizeSlots : Fin 5 → Fin 14 := ![1,4,9,10,11]
def emitSlots : Fin 4 → Fin 14 := ![2,9,12,13]
noncomputable def sign := RecoveryFocus.machine signSlots CloseoutRowsDegreeSign.machine
noncomputable def power := RecoveryFocus.machine powerSlots ClockFields.machine
noncomputable def normalize := RecoveryFocus.machine normalizeSlots ClockNormalize.machine
noncomputable def emit := RecoveryFocus.machine emitSlots RowCoefficientEmit.machine
noncomputable def machine := Composition.machine sign
  (Composition.machine power (Composition.machine normalize emit))
def budget (j p : ℕ) := 6*j+8*p+43

def powerValues (j : ℕ) : Fin 6 → List Bool :=
  ![List.replicate j true,frame (CompetitorDenominator.powerBits j),List.replicate (j+3) true,
    List.replicate (2*(j+3)) true,List.replicate (2*(j+3)+2) true,List.replicate (2*j+10) false]
def normalizeValues (j p : ℕ) : Fin 5 → List Bool :=
  ![List.replicate p true,frame (CompetitorDenominator.powerBits j),frame (binary p (2^j)),
    [true],List.replicate (2*p+1) false]
def input (j p : ℕ) : Fin 14 → List Bool :=
  ![List.replicate j true,List.replicate p true,[],[],[],[],[],[],[],[],[],[],[],[]]
noncomputable def signed (j p : ℕ) : Fin 14 → List Bool :=
  install signSlots (input j p) (CloseoutRowsDegreeSign.output j)
noncomputable def powered (j p : ℕ) : Fin 14 → List Bool :=
  install powerSlots (signed j p) (powerValues j)
noncomputable def normalized (j p : ℕ) : Fin 14 → List Bool :=
  install normalizeSlots (powered j p) (normalizeValues j p)
noncomputable def output (j p : ℕ) :=
  install emitSlots (normalized j p) (RowCoefficientEmit.output (positive j) (binary p (2^j)) 0)

theorem sign_ready (j p : ℕ) : ClockJoin.ReadyRun sign (2*j+4) (input j p) (signed j p) := by
  obtain ⟨r,hr,ht,hh,hs⟩ := CloseoutRowsDegreeSign.sign_ready j
  have h : ClockJoin.ReadyRun CloseoutRowsDegreeSign.machine (2*j+4)
      (CloseoutRowsDegreeSign.input j) (CloseoutRowsDegreeSign.output j) := ⟨r,hr,ht,hh,hs.le⟩
  exact h.focus signSlots (by decide) (input j p) (by intro i; fin_cases i <;> rfl)

theorem power_ready (j p : ℕ) : ClockJoin.ReadyRun power (4*j+22) (signed j p) (powered j p) := by
  obtain ⟨r,hr,h0,h1,h2,h3,h4,h5,hh,hs⟩ := ClockFields.fields_run j
  have h : ClockJoin.ReadyRun ClockFields.machine (4*j+22)
      (Fin.addCases (m := 5) (n := 1) (motive := fun _ => List Bool)
        ![List.replicate j true,[],[],[],[]] (fun _ => [])) (powerValues j) := by
    refine ⟨r,hr,?_,hh,hs.le⟩
    funext i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
    · exact h3
    · exact h4
    · exact h5
  apply h.focus powerSlots (by decide) (signed j p)
  intro i
  fin_cases i
  · exact install_slot signSlots (by decide) _ _ 0
  all_goals
    change install signSlots (input j p) _ _=_
    rw [install_other _ _ _ _ (by decide)]
    rfl

theorem normalize_ready (j p : ℕ) (hj : j<p) :
    ClockJoin.ReadyRun normalize (4*p+4) (powered j p) (normalized j p) := by
  obtain ⟨r,hr,h0,h1,h2,h3,h4,hh,hs⟩ := ClockScalarFields.scalar_run p
    (CompetitorDenominator.powerBits j) (by simp [CompetitorDenominator.powerBits]; omega)
  rw [CompetitorDenominator.power_value] at h2
  have h : ClockJoin.ReadyRun ClockNormalize.machine (4*p+4)
      (ClockNormalize.input p (CompetitorDenominator.powerBits j)) (normalizeValues j p) := by
    refine ⟨r,hr,?_,hh,hs.le⟩
    funext i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
    · exact h3
    · exact h4
  apply h.focus normalizeSlots (by decide) (powered j p)
  intro i
  fin_cases i
  case «1» => exact install_slot powerSlots (by decide) _ _ 1
  all_goals
    change install powerSlots (signed j p) _ _=_
    rw [install_other _ _ _ _ (by decide),signed,install_other _ _ _ _ (by decide)]
    rfl

theorem emit_ready (j p : ℕ) : ClockJoin.ReadyRun emit (4*p+10) (normalized j p) (output j p) := by
  obtain ⟨r,hr,ht,hh,hs⟩ := RowCoefficientEmit.emit_ready (positive j) (binary p (2^j)) 0
  simp only [binary_length] at hr hs
  have h : ClockJoin.ReadyRun RowCoefficientEmit.machine (4*p+10)
      (RowCoefficientEmit.input (positive j) (binary p (2^j)) 0)
      (RowCoefficientEmit.output (positive j) (binary p (2^j)) 0) := ⟨r,hr,ht,hh,hs.le⟩
  apply h.focus emitSlots (by decide) (normalized j p)
  intro i
  fin_cases i
  · change install normalizeSlots (powered j p) _ 2=_
    rw [install_other _ _ _ _ (by decide),powered,install_other _ _ _ _ (by decide)]
    exact install_slot signSlots (by decide) _ _ 1
  · exact install_slot normalizeSlots (by decide) _ _ 2
  all_goals
    change install normalizeSlots (powered j p) _ _=_
    rw [install_other _ _ _ _ (by decide),powered,install_other _ _ _ _ (by decide),
      signed,install_other _ _ _ _ (by decide)]
    rfl

theorem coefficient_ready (j p : ℕ) (hj : j<p) :
    ClockJoin.ReadyRun machine (budget j p) (input j p) (output j p) ∧
    output j p 12=frame (MatrixScoreBatch.signMagnitude p ((-2 : ℤ)^j)) := by
  have tail := ClockJoin.join normalize emit _ _ _ _ _ (normalize_ready j p hj) (emit_ready j p)
  have middle := ClockJoin.join power (Composition.machine normalize emit) _ _ _ _ _ (power_ready j p) tail
  have whole := ClockJoin.join sign (Composition.machine power (Composition.machine normalize emit))
    _ _ _ _ _ (sign_ready j p) middle
  have htime : (2*j+4)+1+((4*j+22)+1+((4*p+4)+1+(4*p+10)))=budget j p := by unfold budget; omega
  rw [htime] at whole
  refine ⟨whole,?_⟩
  change install emitSlots (normalized j p) (RowCoefficientEmit.output (positive j) (binary p (2^j)) 0)
    (emitSlots 2)=_
  rw [install_slot _ (by decide)]
  simp only [RowCoefficientEmit.output,MatrixScoreBatch.signMagnitude,CloseoutRowsDegreeSign.power_sign,
    Int.natAbs_pow]
  rfl

end NearCubicWires.RepairOrdinary.CloseoutRowsDegreeCoefficient
