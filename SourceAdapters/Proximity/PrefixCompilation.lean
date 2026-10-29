import SourceAdapters.Proximity.NativePolynomial

/-! Q04, `app:sources`, "Uniform three-query PCPP and code interfaces": uniform polynomial packaging for already proved
quadratic Cells runs with the paid logarithmic input prefix. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.PrefixCompilation

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells NearCubicGates.Published.CW19Proximity
open NearCubicGates.Close.CounterMachine.PrefixProg (noCallee)

theorem budget_bound (word : List Bool) :
    langBudget noCallee ⟨16, 1, 0, 0, 0, 0⟩ VV MM
      (LengthPrefix.wrapped word)
      (20000 * (word.length + 1) ^ 2) ≤
    SourcePrinting.nativeCoefficient * (word.length + 1) ^ 4 := by
  let w := word
  let L := w.length
  have hlang := NearCubicGates.Close.CounterMachine.PrefixProg.lang_le noCallee 16 1
    (LengthPrefix.wrapped w) (20000 * (L + 1) ^ 2)
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
  have hN : 20000 * (L + 1) ^ 2 + 1 ≤ 20001 * (L + 1) ^ 2 := by nlinarith
  refine hlang.trans ?_
  calc
    _ ≤ 10 ^ 6 * ((20001 * (L + 1) ^ 2) * ((54 + TSK noCallee) * (L + 1)) ^ 2) := by
      gcongr
    _ = SourcePrinting.nativeCoefficient * (word.length + 1) ^ 4 := by
      dsimp [SourcePrinting.nativeCoefficient, L, w]
      ring


theorem polynomial {Request : Type} (input output : Request → List Bool)
    (P : WordFunction Request (fun r => LengthPrefix.wrapped (input r)) output
      (fun r => langBudget noCallee ⟨16, 1, 0, 0, 0, 0⟩ VV MM
        (LengthPrefix.wrapped (input r)) (20000 * ((input r).length + 1) ^ 2))) :
    SourcePolyTime input output := by
  let F : WordFunction Request input (fun r => frame (LengthPrefix.wrapped (input r)))
      (fun r => 10000 * ((input r).length + 1) ^ 2) := {
    program := LengthPrefix.polynomialWordFunction.program
    realizes := fun r => LengthPrefix.polynomialWordFunction.realizes (input r) }
  let Q := P.enlargeBudget (fun r => budget_bound (input r))
  obtain ⟨K, e, h⟩ := Code.composeFramed_budget_poly input _ _
    ⟨10000, 2, fun _ => le_rfl⟩ ⟨SourcePrinting.nativeCoefficient, 4, fun _ => le_rfl⟩
  exact ⟨K, e, ⟨(Code.composeFramed F Q).enlargeBudget h⟩⟩

end NearCubicGates.Adapters.Proximity.PrefixCompilation
