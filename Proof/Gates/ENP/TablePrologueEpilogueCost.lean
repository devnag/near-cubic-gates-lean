import Proof.Gates.ENP.TableSeedsCost
import Proof.Gates.ENP.TableEmitProg

set_option autoImplicit false
set_option linter.unusedVariables false

namespace NearCubicGates.Close.ENP.TableSearch

open NearCubicWires NearCubicWires.Bindings.MW20 NearCubicGates.Close.ENP.TEmit
open NearCubicGates.Close.CheckedPCPP.NodeEmit

theorem pb_tNodes : PB tSize (fun a => (TCirc.tCircuit a.2.1).nodes.length) := by
  refine PB.mono (fun a => ?_) pb_W
  have hT : 2 ^ a.1 ≤ tSize a + 1 := by unfold tSize; omega
  have hm : a.2.1.nodes.length ≤ tSize a + 1 := by
    have := nodes_le_word a.2.1
    have h1 : 1 ≤ 2 ^ a.1 := Nat.one_le_two_pow
    have h2 : (OracleOutput.word ⟨a.1, a.2.1⟩).length ≤ ((OracleOutput.word ⟨a.1, a.2.1⟩) ++ a.2.2).length := by simp
    unfold tSize
    omega
  exact tNodes_le a.2.1 (tSize a + 1) hT hm

theorem pECostPoly : TEmit.PECostPoly := by
  have hT := pb_T
  have hl := pb_ell
  have hm := pb_m
  have hr := pb_r7
  have hN := pb_tNodes
  have h : PB tSize (fun a => prologueCost a.1 a.2.1.nodes.length + epilogueCost a.2.1) := by
    simp only [prologueCost, epilogueCost, nodeCost, fieldCost, TCirc.K]
    repeat pb_step
  obtain ⟨K, e, hK⟩ := h
  exact ⟨K, e, fun {ℓ} C post => hK ⟨ℓ, C, post⟩⟩

end NearCubicGates.Close.ENP.TableSearch
