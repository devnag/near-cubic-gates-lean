import Proof.Gates.Succinct.SubstitutionStep
import Proof.Gates.Succinct.SubstitutionLoopSpecs

set_option autoImplicit false

namespace NearCubicGates.Close.Succinct.SubstMachine

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.Bindings.MW20
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.Succinct NearCubicGates.Close.Outer

variable {q : ℕ}

/-- The loop counter fits the register capacity: `n_C ≤ capH`. -/
theorem nC_le_cap (cap : ℕ) (o : OracleOutput) (B : BooleanCircuit q) (hcap : capH o B ≤ cap) :
    o.circuit.nodes.length ≤ cap := by
  have h1 := (sizes_le o B).1
  have h2 := capH_ge o B
  have h3 : sizeS o B + 2 ≤ (sizeS o B + 2) ^ 4 := Nat.le_self_pow (by norm_num) _
  omega

theorem emLoop (cap : ℕ) (o : OracleOutput) (B : BooleanCircuit q) (hK1 : Kind1OK cap o B)
    (hcap : capH o B ≤ cap) (σ : WState 4 nrH) (hI0 : MInv o B 0 σ) :
    ∃ τ, WExec cap (.whr (regH .iC) (.seq (.dec (regH .iC)) nodeBody)) σ τ
        (o.circuit.nodes.length * (readCost 5 + nIter (sizeS o B) + 20 + 4) + 1) ∧
      MInv o B o.circuit.nodes.length τ ∧ τ.val (regH .iC) = 0 := by
  have hv : ∀ u, σ.val (regH u) = VM o B 0 u := hI0.2.2.2.2.2.2.2.2.2.2.1
  have hiC : σ.val (regH .iC) = o.circuit.nodes.length := by rw [hv]; simp [VM]
  exact UnionMachine.Round.wloopE cap (regH .iC) nodeBody (readCost 5 + nIter (sizeS o B) + 20)
    o.circuit.nodes.length (fun k τ => MInv o B k τ) (nC_le_cap cap o B hcap)
    (fun k hk τ hτ _ => nodeStep cap o B hK1 k hk τ hτ hcap) σ hI0 hiC

theorem loopSpec_of (hK1 : ∀ (o : OracleOutput) {q : ℕ} (B : BooleanCircuit q), Kind1OK (capH o B) o B) :
    LoopSpec := by
  intro o q B σ hI0
  obtain ⟨τ, e, hI, -⟩ := emLoop (capH o B) o B (hK1 o B) le_rfl σ hI0
  exact ⟨τ, _, e, le_rfl, hI⟩

end NearCubicGates.Close.Succinct.SubstMachine
