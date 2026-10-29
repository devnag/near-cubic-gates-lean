import SourceAdapters.Proximity.TrimVerifierCompile
import SourceAdapters.Code.Composition

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": polynomial ordinary witness for the exact verifier schedule,
including the paid length prefix and compiled numeric sorting.
-/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.Trim

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Adapters.Joins
open NearCubicGates.Close.CounterMachine.PrefixProg (noCallee)

noncomputable def verifierCoefficient : ℕ := 10 ^ 6 * 4001 * (54 + TSK noCallee) ^ 2

theorem verifier_budget_bound (r : TrimRequest) :
    langBudget noCallee ⟨16, 1, 0, 0, 0, 0⟩ VV MM
      (LengthPrefix.wrapped (trimRequestWord r))
      (4000 * ((trimRequestWord r).length + 1) ^ 2) ≤
    verifierCoefficient * ((trimRequestWord r).length + 1) ^ 4 := by
  let w := trimRequestWord r
  let L := w.length
  have hlang := NearCubicGates.Close.CounterMachine.PrefixProg.lang_le noCallee 16 1
    (LengthPrefix.wrapped w) (4000 * (L + 1) ^ 2)
  rw [LengthPrefix.wrapped_leadOnes, Nat.one_mul] at hlang
  have hw := LengthPrefix.allocation_bound 16 1 w
  rw [LengthPrefix.wrapped_leadOnes] at hw
  simp only [Nat.one_mul, pow_one] at hw
  have hl := NearCubicGates.Close.CheckedPCPP.NodeEmit.natBitLength_le L
  have hi := LengthPrefix.wrapped_length_bound w
  have hH : 2 ^ natBitLength L * 16 + natBitLength L + (LengthPrefix.wrapped w).length +
      16 + 1 + TSK noCallee + 1 ≤ (54 + TSK noCallee) * (L + 1) := by
    change 2 ^ natBitLength L * 16 ≤ 32 * (L + 1) at hw
    change (LengthPrefix.wrapped w).length ≤ 3 * (L + 1) at hi
    nlinarith
  have hN : 4000 * (L + 1) ^ 2 + 1 ≤ 4001 * (L + 1) ^ 2 := by nlinarith
  refine hlang.trans ?_
  calc
    _ ≤ 10 ^ 6 * ((4001 * (L + 1) ^ 2) * ((54 + TSK noCallee) * (L + 1)) ^ 2) := by
      gcongr
    _ = verifierCoefficient * ((trimRequestWord r).length + 1) ^ 4 := by
      dsimp [verifierCoefficient, L, w]
      ring

noncomputable def boundedVerifierCompilerWordFunction : WordFunction TrimRequest
    (fun r => LengthPrefix.wrapped (trimRequestWord r)) verifierWord
    (fun r => verifierCoefficient * ((trimRequestWord r).length + 1) ^ 4) :=
  verifierCompilerWordFunction.enlargeBudget verifier_budget_bound

noncomputable def verifierPrefixWordFunction : WordFunction TrimRequest
    (fun r => trimRequestWord r)
    (fun r => frame (LengthPrefix.wrapped (trimRequestWord r)))
    (fun r => 10000 * ((trimRequestWord r).length + 1) ^ 2) where
  program := LengthPrefix.polynomialWordFunction.program
  realizes r := LengthPrefix.polynomialWordFunction.realizes (trimRequestWord r)

/-- The trimming request itself is the input; its size header is computed by
an actual preliminary machine and every compiled step has a fixed quartic bound. -/
noncomputable def verifierWordFunction : WordFunction TrimRequest
    (fun r => trimRequestWord r) verifierWord
    (fun r => (20005 + 2 * verifierCoefficient) * ((trimRequestWord r).length + 1) ^ 4) :=
  (NearCubicGates.Adapters.Code.composeFramed verifierPrefixWordFunction boundedVerifierCompilerWordFunction).enlargeBudget
    (fun r => by
      have hp : ((trimRequestWord r).length + 1) ^ 2 ≤
          ((trimRequestWord r).length + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by decide)
      have h1 : 1 ≤ ((trimRequestWord r).length + 1) ^ 4 := Nat.one_le_pow _ _ (by omega)
      nlinarith)

end NearCubicGates.Adapters.Proximity.Trim
