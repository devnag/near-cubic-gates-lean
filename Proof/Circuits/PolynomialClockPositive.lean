import Proof.Circuits.PolynomialClockPower
import Proof.Circuits.CanonicalBinaryOutput

/-! Actual short binary powering followed by canonical output extraction.
Only positive inputs enter this branch; a literal marker selects it below. -/
namespace NearCubicWires.RepairOrdinary.PolynomialClock
open LocalBitMultitape RecoveryRootRound SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def tapes (k : ℕ) := HierarchyFromInput.tapes (k+2)+3
def old (k : ℕ) (i : Fin (HierarchyFromInput.tapes (k+2))) : Fin (tapes k) := i.castAdd 3
def fresh (k : ℕ) (i : Fin 3) : Fin (tapes k) := i.natAdd (HierarchyFromInput.tapes (k+2))
def outputTape (k : ℕ) := fresh k 1
def slots (k : ℕ) : Fin 4 → Fin (tapes k) :=
  ![old k (PolynomialClockPower.outputTape (k+2) (by omega)),fresh k 0,fresh k 1,fresh k 2]
theorem old_injective (k : ℕ) : Function.Injective (old k) := by
  intro a b h; exact Fin.ext (congrArg (fun i : Fin (tapes k) => i.val) h)
theorem slots_injective (k : ℕ) : Function.Injective (slots k) := by
  intro a b h
  have hv := congrArg Fin.val h
  have hp := (PolynomialClockPower.outputTape (k+2) (by omega)).isLt
  fin_cases a <;> fin_cases b <;> simp [slots,old,fresh] at hv ⊢ <;> omega

def input (k : ℕ) (n : ℕ) : Fin (tapes k) → List Bool :=
  Fin.addCases (HierarchyFromInput.input (k+2) (List.replicate n true)) (fun _ => [])
noncomputable def powerProgram (k : ℕ) := RecoveryFocus.machine (old k)
  (PolynomialClockPower.machine (k+2) (by omega))
noncomputable def outputProgram (k : ℕ) := RecoveryFocus.machine (slots k) CanonicalPositiveOutput.machine
noncomputable def positive (k : ℕ) := Composition.machine (powerProgram k) (outputProgram k)
def positiveBudget (k n : ℕ) := PolynomialClockPower.budget (k+2) (List.replicate n true)+
  1+(8*HierarchyBinary.width 1 (k+2) n+9)

theorem positive_run (k n : ℕ) (hn : 0<n) : ∃ out,
    ClockJoin.ReadyRun (positive k) (positiveBudget k n) (input k n) out ∧
      out (outputTape k)=(n^(k+2)).bits := by
  obtain ⟨a,ha,hao,haw,hax⟩ := PolynomialClockPower.from_input_run (k+2) (by omega) (List.replicate n true)
  simp only [List.length_replicate] at hao
  have hp := ha.focus (old k) (old_injective k) (input k n) (by intro i; simp [input,old])
  let middle := install (old k) (input k n) a
  have hfit : n^(k+2)<2^HierarchyBinary.width 1 (k+2) n :=
    (Nat.lt_succ_self _).trans (HierarchyBinary.successor_fit 1 (k+2) n)
  obtain ⟨b,hb,hbo⟩ := CanonicalPositiveOutput.binary_output_run
    (HierarchyBinary.width 1 (k+2) n) (n^(k+2)) (Nat.pow_pos hn) hfit
  have hi : ∀ i,middle (slots k i)=CanonicalPositiveOutput.input (binary (HierarchyBinary.width 1 (k+2) n) (n^(k+2))) i := by
    intro i; fin_cases i
    · change install (old k) (input k n) a (old k (PolynomialClockPower.outputTape (k+2) (by omega)))=_
      rw [install_slot _ (old_injective k)]
      exact hao
    all_goals
      dsimp only [middle]
      rw [install_other _ _ _ _ (by
        intro j hj; have hv := congrArg Fin.val hj
        simp [slots,old,fresh] at hv
        omega)]
      simp [input,slots,fresh,CanonicalPositiveOutput.input]
  have hc := hb.focus (slots k) (slots_injective k) middle hi
  exact ⟨_,ClockJoin.join _ _ _ _ _ _ _ hp hc,
    (install_slot _ (slots_injective k) _ _ 2).trans hbo⟩

end NearCubicWires.RepairOrdinary.PolynomialClock
