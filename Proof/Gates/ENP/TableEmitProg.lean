import Proof.Gates.ENP.TablePrologue

set_option autoImplicit false

namespace NearCubicGates.Close.ENP.TEmit

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.WordPrograms NearCubicWires.Bindings.MW20

def PECostPoly : Prop :=
  ∃ K e : ℕ, ∀ {ℓ : ℕ} (C : OracleCircuit ℓ ℓ) (post : List Bool),
    prologueCost ℓ C.nodes.length + epilogueCost C ≤
      K * (2 ^ ℓ + ((OracleOutput.word ⟨ℓ, C⟩) ++ post).length + 1) ^ e

/-- The emitter program. -/
def tProgram : WMX 3 40 := .seq prologue (.seq (seedsLoop false) epilogue)

theorem tProgOf_of (hS : SeedsRuns) (hB : TBytesSpec) (hPE : PECostPoly) : Nonempty TProg := by
  obtain ⟨K1, e1, h1⟩ := hS
  obtain ⟨K2, e2, h2⟩ := hPE
  refine ⟨{ prog := tProgram, K := K1 + K2 + 2, e := e1 + e2 + 1, run := fun {ℓ} C post => ?_ }⟩
  obtain ⟨c0, n1, hn1, hrun⟩ := h1 C post
  set X := 2 ^ ℓ + ((OracleOutput.word ⟨ℓ, C⟩) ++ post).length + 1 with hX
  have hX1 : 1 ≤ X := by rw [hX]; exact Nat.le_add_left 1 _
  set cap := c0 + prologueCap ℓ C.nodes.length + epilogueCap C with hcap
  obtain ⟨junk, hs⟩ := hrun cap (by omega)
  have hp := prologue_exec C post cap (by omega)
  have he := epilogue_exec hB C post junk cap (by omega)
  refine ⟨cap, prologueCost ℓ C.nodes.length + 1 + (n1 + 1 + epilogueCost C), junk, ?_, WXExec.seq hp (WXExec.seq hs he)⟩
  have hpe : prologueCost ℓ C.nodes.length + epilogueCost C ≤ K2 * X ^ e2 := h2 C post
  have p1 : X ^ e1 ≤ X ^ (e1 + e2 + 1) := Nat.pow_le_pow_right hX1 (by omega)
  have p2 : X ^ e2 ≤ X ^ (e1 + e2 + 1) := Nat.pow_le_pow_right hX1 (by omega)
  have p3 : 1 ≤ X ^ (e1 + e2 + 1) := Nat.one_le_pow _ _ hX1
  have m1 : K1 * X ^ e1 ≤ K1 * X ^ (e1 + e2 + 1) := Nat.mul_le_mul_left _ p1
  have m2 : K2 * X ^ e2 ≤ K2 * X ^ (e1 + e2 + 1) := Nat.mul_le_mul_left _ p2
  have hsum : prologueCost ℓ C.nodes.length + 1 + (n1 + 1 + epilogueCost C) ≤
      K1 * X ^ (e1 + e2 + 1) + K2 * X ^ (e1 + e2 + 1) + 2 * X ^ (e1 + e2 + 1) := by omega
  calc prologueCost ℓ C.nodes.length + 1 + (n1 + 1 + epilogueCost C)
      ≤ K1 * X ^ (e1 + e2 + 1) + K2 * X ^ (e1 + e2 + 1) + 2 * X ^ (e1 + e2 + 1) := hsum
    _ = (K1 + K2 + 2) * X ^ (e1 + e2 + 1) := by ring

end NearCubicGates.Close.ENP.TEmit
