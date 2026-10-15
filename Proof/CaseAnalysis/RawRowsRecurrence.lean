import Proof.CaseAnalysis.RawRowsLeaf

/-! The paper's existing raw list recurrence, applied to the current GF2
constructors. Reuses the mathematical recurrence from ParityCapFirstProofs
without its obsolete executor imports or mode-specific wrappers. -/
namespace NearCubicWires.RepairSource.CloseoutRawRows
open CanonicalFourfoldRowProgram SupplierListPolynomial SupplierListSchedule
open SupplierToeplitz SupplierToeplitzCore
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def terminalCoordinateRawLedger (population terminalWindow : ℕ) : ℕ :=
  (terminalWindow + 1) ^ 2 * (population + 1) ^ terminalWindow

def deltaCoordinateRawLedger (population windowWidth : ℕ) : ℕ :=
  (2 * windowWidth + 1) ^ 2 *
    (2 * population + 1) ^ (2 * windowWidth)

theorem structuralTerminalPolynomialVector_length_le
    (depth population terminalWindow : Nat) (candidate : Fin (population+1)) :
    (structuralTerminalPolynomialVector depth population terminalWindow candidate).length ≤
      terminalCoordinateRawLedger population terminalWindow := by
  unfold structuralTerminalPolynomialVector structuralTerminalWindowPolynomial terminalCoordinateRawLedger
  simpa only [terminalLiteralVariableCodes,List.length_ofFn] using
    window_bound (terminalLiteralVariableCodes depth population) 0 terminalWindow candidate.val

theorem structuralDeltaFactor_length_le
    {rank depth population : Nat} (label : Fin population → BinaryVector rank)
    (seed : ToeplitzSeed rank) (window : Fin depth → Nat) (level : Fin depth)
    (parent child : Fin (population+1)) :
    (structuralDeltaFactor label seed window level parent child).length ≤
      deltaCoordinateRawLedger population (window level) := by
  unfold structuralDeltaFactor
  dsimp only
  split
  · exact Nat.zero_le _
  · unfold structuralDeltaWindowPolynomial deltaCoordinateRawLedger
    dsimp only
    simpa only [deltaLiteralVariableCodes,List.length_ofFn] using
      window_bound (deltaLiteralVariableCodes (population := population) level)
        ((hashIndexCell label seed (zeroPrefixCell rank (level.val+1))).card-window level)
        (2*window level) _

theorem structuralCombineListLevel_length_le
    {rank depth population childBound : ℕ}
    (label : Fin population → BinaryVector rank)
    (seed : ToeplitzSeed rank)
    (window : Fin depth → ℕ) (level : Fin depth)
    (childPolynomials : StructuralListPolynomialVector population)
    (hchildren : ∀ child, (childPolynomials child).length ≤ childBound)
    (parent : Fin (population + 1)) :
    (structuralCombineListLevel label seed window level childPolynomials
        parent).length ≤
      (population + 1) *
        (childBound * deltaCoordinateRawLedger population (window level)) := by
  unfold structuralCombineListLevel
  rw [sum_length]
  simp only [List.map_ofFn, Function.comp_def,
    List.sum_ofFn]
  calc
    (∑ child : Fin (population + 1),
      (structuralGF2Mul (childPolynomials child)
        (structuralDeltaFactor label seed window level parent child)).length) ≤
        ∑ _child : Fin (population + 1),
          childBound * deltaCoordinateRawLedger population (window level) := by
      apply Finset.sum_le_sum
      intro child _
      rw [mul_length]
      exact Nat.mul_le_mul (hchildren child)
        (structuralDeltaFactor_length_le label seed window level parent child)
    _ = (population + 1) *
        (childBound * deltaCoordinateRawLedger population (window level)) := by
      simp

/-- Closed recursion budget matching `structuralListPolynomialVectorFrom`
constructor-for-constructor. -/
def structuralListCoordinateRawLedgerFrom
    (depth population : ℕ) (window : Fin depth → ℕ)
    (terminalWindow level : ℕ) : ℕ :=
  if hlevel : level < depth then
    (population + 1) *
      (structuralListCoordinateRawLedgerFrom depth population window
          terminalWindow (level + 1) *
        deltaCoordinateRawLedger population (window ⟨level, hlevel⟩))
  else
    terminalCoordinateRawLedger population terminalWindow
termination_by depth - level
decreasing_by omega

theorem structuralListPolynomialVectorFrom_length_le
    {rank depth population : ℕ}
    (label : Fin population → BinaryVector rank)
    (seed : ToeplitzSeed rank)
    (window : Fin depth → ℕ) (terminalWindow level : ℕ)
    (candidate : Fin (population + 1)) :
    (structuralListPolynomialVectorFrom label seed window terminalWindow level
        candidate).length ≤
      structuralListCoordinateRawLedgerFrom depth population window
        terminalWindow level := by
  rw [structuralListPolynomialVectorFrom,
    structuralListCoordinateRawLedgerFrom]
  by_cases hlevel : level < depth
  · rw [dif_pos hlevel, dif_pos hlevel]
    exact structuralCombineListLevel_length_le label seed window
      ⟨level, hlevel⟩ _
      (fun child => structuralListPolynomialVectorFrom_length_le label seed
        window terminalWindow (level + 1) child) candidate
  · rw [dif_neg hlevel, dif_neg hlevel]
    exact structuralTerminalPolynomialVector_length_le depth population
      terminalWindow candidate
termination_by depth - level
decreasing_by omega

def structuralListCoordinateRawLedger
    (depth population : ℕ) (window : Fin depth → ℕ)
    (terminalWindow : ℕ) : ℕ :=
  structuralListCoordinateRawLedgerFrom depth population window terminalWindow 0

theorem structuralListPolynomialVector_length_le
    {rank depth population : ℕ}
    (label : Fin population → BinaryVector rank)
    (seed : ToeplitzSeed rank)
    (window : Fin depth → ℕ) (terminalWindow : ℕ)
    (candidate : Fin (population + 1)) :
    (structuralListPolynomialVector label seed window terminalWindow
        candidate).length ≤
      structuralListCoordinateRawLedger depth population window
        terminalWindow := by
  unfold structuralListPolynomialVector structuralListCoordinateRawLedger
  exact structuralListPolynomialVectorFrom_length_le label seed window
    terminalWindow 0 candidate

end
end NearCubicWires.RepairSource.CloseoutRawRows
