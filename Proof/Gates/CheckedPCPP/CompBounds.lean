import Proof.Gates.CheckedPCPP.CompRunC

set_option autoImplicit false

namespace NearCubicGates.Close.CheckedPCPP.Comp

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation

theorem fields_le_of_wf {n : ℕ} (nd : BooleanNode n) (idx : ℕ) (h : nd.WellFormedAt idx) (j : Fin 3) :
    PCPPRequestNodeSchema.fields nd j ≤ idx + n + 4 := by
  cases nd with
  | const b =>
    have := Bool.toNat_le b
    fin_cases j <;> (simp [PCPPRequestNodeSchema.fields]; try omega)
  | input i => fin_cases j <;> (simp [PCPPRequestNodeSchema.fields]; try omega)
  | not c => simp [BooleanNode.WellFormedAt] at h; fin_cases j <;> (simp [PCPPRequestNodeSchema.fields]; try omega)
  | and l r => simp [BooleanNode.WellFormedAt] at h; fin_cases j <;> (simp [PCPPRequestNodeSchema.fields]; try omega)
  | or l r => simp [BooleanNode.WellFormedAt] at h; fin_cases j <;> (simp [PCPPRequestNodeSchema.fields]; try omega)

/-- The native descriptor of a circuit is at most quadratic in its size and arity. -/
theorem desc_len_le {n : ℕ} (c : BooleanCircuit n) :
    (PCPPNative.descriptor c).length ≤ (c.size + 1) * (6 * (c.size + n + 4) + 9) + 2 * n + 4 * c.size + 9 := by
  rw [PCPPNative.descriptor_eq]
  have hf : ∀ nd ∈ c.nodes, ∀ j, PCPPRequestNodeSchema.fields nd j ≤ c.size + n + 4 := by
    intro nd hnd j
    obtain ⟨idx, hidx⟩ := List.mem_iff_get.1 hnd
    have hw := c.wellFormed idx
    rw [hidx] at hw
    have := fields_le_of_wf nd idx.val hw j
    have : idx.val < c.size := idx.isLt
    omega
  have hb := ChecksW.flatMap_native_le (c.size + n + 4) c.nodes hf
  have h1 := SubstitutedPoly.natWord_len_le n
  have h2 := SubstitutedPoly.natWord_len_le c.nodes.length
  have h3 := SubstitutedPoly.natWord_len_le c.output.val
  have ho := c.output.isLt
  have hs : c.size = c.nodes.length := rfl
  simp only [List.length_append]
  change c.output.val < c.size at ho
  nlinarith

end NearCubicGates.Close.CheckedPCPP.Comp
