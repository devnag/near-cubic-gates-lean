import SourceAdapters.Proximity.NativeCompile
import SourceAdapters.Code.Composition

/-! Q04: full polynomial ordinary witness for the native-to-source codec,
including the actual logarithmic header loader and paid ordinary composition. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.SourcePrinting

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Published.CW19Proximity
open NearCubicGates.Close.CounterMachine.PrefixProg (noCallee)

noncomputable def nativeCoefficient : ℕ := 10 ^ 6 * 20001 * (54 + TSK noCallee) ^ 2

theorem native_budget_bound (S : SourceCircuit) :
    langBudget noCallee ⟨16, 1, 0, 0, 0, 0⟩ VV MM
      (LengthPrefix.wrapped (PCPPNative.descriptor S.circuit))
      (20000 * ((PCPPNative.descriptor S.circuit).length + 1) ^ 2) ≤
    nativeCoefficient * ((PCPPNative.descriptor S.circuit).length + 1) ^ 4 := by
  let w := PCPPNative.descriptor S.circuit
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
    _ = nativeCoefficient * ((PCPPNative.descriptor S.circuit).length + 1) ^ 4 := by
      dsimp [nativeCoefficient, L, w]
      ring

noncomputable def boundedNativeCompilerWordFunction : WordFunction SourceCircuit
    (fun S => LengthPrefix.wrapped (PCPPNative.descriptor S.circuit)) sourceCircuitWord
    (fun S => nativeCoefficient * ((PCPPNative.descriptor S.circuit).length + 1) ^ 4) :=
  nativeCompilerWordFunction.enlargeBudget native_budget_bound

noncomputable def nativePrefixWordFunction : WordFunction SourceCircuit
    (fun S => PCPPNative.descriptor S.circuit)
    (fun S => frame (LengthPrefix.wrapped (PCPPNative.descriptor S.circuit)))
    (fun S => 10000 * ((PCPPNative.descriptor S.circuit).length + 1) ^ 2) where
  program := LengthPrefix.polynomialWordFunction.program
  realizes S := LengthPrefix.polynomialWordFunction.realizes (PCPPNative.descriptor S.circuit)

/-- The native descriptor itself is the input; the size header is computed by
an actual preliminary machine and every compiled step has a fixed quartic bound. -/
noncomputable def nativeSourceWordFunction : WordFunction SourceCircuit
    (fun S => PCPPNative.descriptor S.circuit) sourceCircuitWord
    (fun S => (20005 + 2 * nativeCoefficient) * ((PCPPNative.descriptor S.circuit).length + 1) ^ 4) :=
  (NearCubicGates.Adapters.Code.composeFramed nativePrefixWordFunction boundedNativeCompilerWordFunction).enlargeBudget
    (fun S => by
      have hp : ((PCPPNative.descriptor S.circuit).length + 1) ^ 2 ≤
          ((PCPPNative.descriptor S.circuit).length + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by decide)
      have h1 : 1 ≤ ((PCPPNative.descriptor S.circuit).length + 1) ^ 4 := Nat.one_le_pow _ _ (by omega)
      nlinarith)

end NearCubicGates.Adapters.Proximity.SourcePrinting
