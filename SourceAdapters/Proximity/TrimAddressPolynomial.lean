import SourceAdapters.Proximity.TrimAddressCompile
import SourceAdapters.Code.Composition

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": polynomial ordinary witness for the exact address schedule,
including the paid length prefix and compiled numeric sorting.
-/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.Trim

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Adapters.Joins
open NearCubicGates.Close.CounterMachine.PrefixProg (noCallee)

noncomputable def addressCoefficient : ℕ := 10 ^ 6 * 2001 * (54 + TSK noCallee) ^ 2

theorem address_budget_bound (r : TrimRequest) :
    langBudget noCallee ⟨16, 1, 0, 0, 0, 0⟩ VV MM
      (LengthPrefix.wrapped (trimRequestWord r))
      (2000 * ((trimRequestWord r).length + 1) ^ 2) ≤
    addressCoefficient * ((trimRequestWord r).length + 1) ^ 4 := by
  let w := trimRequestWord r
  let L := w.length
  have hlang := NearCubicGates.Close.CounterMachine.PrefixProg.lang_le noCallee 16 1
    (LengthPrefix.wrapped w) (2000 * (L + 1) ^ 2)
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
  have hN : 2000 * (L + 1) ^ 2 + 1 ≤ 2001 * (L + 1) ^ 2 := by nlinarith
  refine hlang.trans ?_
  calc
    _ ≤ 10 ^ 6 * ((2001 * (L + 1) ^ 2) * ((54 + TSK noCallee) * (L + 1)) ^ 2) := by
      gcongr
    _ = addressCoefficient * ((trimRequestWord r).length + 1) ^ 4 := by
      dsimp [addressCoefficient, L, w]
      ring

noncomputable def boundedAddressCompilerWordFunction : WordFunction TrimRequest
    (fun r => LengthPrefix.wrapped (trimRequestWord r)) trimAddressWord
    (fun r => addressCoefficient * ((trimRequestWord r).length + 1) ^ 4) :=
  addressCompilerWordFunction.enlargeBudget address_budget_bound

noncomputable def addressPrefixWordFunction : WordFunction TrimRequest
    (fun r => trimRequestWord r)
    (fun r => frame (LengthPrefix.wrapped (trimRequestWord r)))
    (fun r => 10000 * ((trimRequestWord r).length + 1) ^ 2) where
  program := LengthPrefix.polynomialWordFunction.program
  realizes r := LengthPrefix.polynomialWordFunction.realizes (trimRequestWord r)

/-- The trimming request itself is the input; its size header is computed by
an actual preliminary machine and every compiled step has a fixed quartic bound. -/
noncomputable def addressWordFunction : WordFunction TrimRequest
    (fun r => trimRequestWord r) trimAddressWord
    (fun r => (20005 + 2 * addressCoefficient) * ((trimRequestWord r).length + 1) ^ 4) :=
  (NearCubicGates.Adapters.Code.composeFramed addressPrefixWordFunction boundedAddressCompilerWordFunction).enlargeBudget
    (fun r => by
      have hp : ((trimRequestWord r).length + 1) ^ 2 ≤
          ((trimRequestWord r).length + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by decide)
      have h1 : 1 ≤ ((trimRequestWord r).length + 1) ^ 4 := Nat.one_le_pow _ _ (by omega)
      nlinarith)

end NearCubicGates.Adapters.Proximity.Trim
