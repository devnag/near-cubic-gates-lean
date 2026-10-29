import SourceAdapters.Proximity.NumericalRows

/-! Q04, `app:sources`, "Uniform three-query PCPP and code interfaces": all initialization, source-call, loop and output
width preconditions follow from one explicit numerical demand. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.SourceCallee

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicGates.Close.Cells
open NearCubicGates.Published.CW19Proximity

variable {q : ℕ} (V : (C : SourceCircuit) → NonadaptiveVerifier C.arity q)
    (proofLength : SourceCircuit → ℕ) (honest : (p : AcceptedSourceInput) → BitInput (proofLength p.1))
    (budget : ProofCall V → ℕ)
    (P : WordFunction (ProofCall V) (proofCallInput V) (normalizedProofOutput V proofLength honest) budget)

include P in
theorem numerical_constructor (S : SourceCircuit) (a B Wd Lk Bk : ℕ)
    (hr : (V S).randomBits ≤ a * ((sourceCircuitWord S).length + 2))
    (hbud : ∀ request, (proofCallInput V request).length ≤ requestCap q a (sourceCircuitWord S).length →
      budget request ≤ B)
    (hroom : requestCap q a (sourceCircuitWord S).length ≤ Lk) (hclock : B ≤ Bk)
    (hwidth : widthDemand q (sourceCircuitWord S).length (V S).randomBits B ≤ Wd) :
    ConstructorBounds V budget S Wd Lk Bk (widthMeasure q (V S).randomBits B) := by
  let L := (sourceCircuitWord S).length
  let Λ := widthMeasure q (V S).randomBits B
  have hparts : B + auxiliaryCap q (V S).randomBits + blockVariableBound q + 2 * q + 2 ^ q +
      (V S).randomBits + 20 = Λ := rfl
  have hpow : 0 ≤ (2 ^ q : ℕ) := Nat.zero_le _
  change Λ + L + predicateBlockBits q + 10 ≤ Wd at hwidth
  have hWlt := Nat.lt_two_pow_self (n := Wd)
  have hbits := arity_bits_source S
  change S.arity.bits.length ≤ L at hbits
  have hlength := (natBitLength_le_bits_succ L).trans (Nat.add_le_add_right (bits_length_le L) 1)
  dsimp only [L] at hlength
  have hn := natBitLength_le_bits_succ S.arity
  have hrbits := bits_length_le (V S).randomBits
  have hcombined := (natBitLength_le_bits_succ ((V S).randomBits + predicateBlockBits q)).trans
    (Nat.add_le_add_right (bits_length_le _) 1)
  have hlen := request_lengths V a S ⟨0, Nat.two_pow_pos _⟩ hr
  refine ⟨fun coins => numerical_rows V proofLength honest budget P S coins
    (requestCap q a L) B Wd Lk Bk (request_lengths V a S coins hr) hbud hroom hclock hwidth,
    by omega, by omega, ?_, hlen.random.trans hroom, (hbud _ hlen.random).trans hclock,
    by omega, by omega, by omega, by omega, by omega⟩
  have hp : 2 ^ (L + 1) ≤ 2 ^ Wd := Nat.pow_le_pow_right (by decide) (by omega)
  have hL := Nat.lt_two_pow_self (n := L)
  rw [pow_succ] at hp
  omega

/-- The fixed polynomial source budget is evaluated on the proved request cap. -/
def callBudgetCap (q a K e L : ℕ) : ℕ := K * (requestCap q a L + 1) ^ e

theorem budget_below_cap {q : ℕ} (V : (C : SourceCircuit) → NonadaptiveVerifier C.arity q)
    (a K e L : ℕ) (request : ProofCall V) (h : (proofCallInput V request).length ≤ requestCap q a L) :
    K * ((proofCallInput V request).length + 1) ^ e ≤ callBudgetCap q a K e L :=
  Nat.mul_le_mul_left K (Nat.pow_le_pow_left (Nat.add_le_add_right h 1) e)

end NearCubicGates.Adapters.Proximity.SourceCallee
