import Proof.CaseAnalysis.RecoveryGraphSerializeRun
import Proof.CaseAnalysis.RecoveryGraphSupport
import Proof.Circuits.DecompositionSourceBounds

/-! Resource applications for the same original graph and cold serializer.
The formula byte bound is a projection of its paid ordinary producer. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedGraphBudget
open LocalBitMultitape RepairSource ProjectionNormalization PaddedRunnerBudgetClosure
open RecoveryTseitinNative
open private stream_length_le from Proof.PCP.PCPPRequestSourceRuntime
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem graph_bound {n : ℕ} (c : BooleanCircuit n) (W : ℕ)
    (hn : n ≤ W) (hc : c.nodes.length ≤ W) :
    (RecoveryBoundedGraphSerialize.graph c).length ≤ W*(6*(W+W+5)+3) := by
  have hs : (c.nodes.flatMap PCPPRequestNodeSchema.native).length ≤
      c.nodes.length*(6*(n+c.nodes.length+5)+3) := by
    apply stream_length_le
    intro node hm
    obtain ⟨i,hi⟩ := List.mem_iff_get.mp hm
    rw [←hi]
    exact PCPPRequestRuntime.native_width c i
  exact hs.trans (Nat.mul_le_mul hc (by omega))

/-- The existing physical B reservation covers graph bytes, the last-node
counter and description arity. W remains the caller's actual paid value. -/
theorem serializer_fits {n : ℕ} (c : BooleanCircuit n) (W S : ℕ)
    (hn : n ≤ W) (hc : c.nodes.length ≤ W) :
    let B := 32*S+10000000000*(W+1)^6+64
    (RecoveryBoundedGraphSerialize.graph c).length ≤ B ∧
      c.output.val+1 ≤ B ∧ n+1 ≤ B := by
  have hg := graph_bound c W hn hc
  have h6 : (W+1)^2 ≤ (W+1)^6 :=
    Nat.pow_le_pow_right (by omega : 0 < W+1) (by decide)
  have hs : W*(6*(W+W+5)+3) ≤ 64*(W+1)^2 := by nlinarith
  have hW : W+1 ≤ (W+1)^2 := by nlinarith
  have ho := c.output.isLt
  dsimp only
  refine ⟨by nlinarith,by nlinarith,by nlinarith⟩

/-- A fresh output tape cannot contain more bytes than the paid run wrote.
This uses the existing cold original formula, without any encoding prepass. -/
theorem formula_bytes {n : ℕ} (c : BooleanCircuit n) :
    (RecoveryFormulaPayload.input (CircuitInputCNF.circuitInputFormula c)).length ≤
      Cold.budget n c.nodes.length := by
  obtain ⟨r,hr,_,ht,hs⟩ := Cold.cold_run c
  have h := DecompositionSource.one_tape_support Cold.machine _ _ r 1333 0 hr
    (by rfl) (by simp [initialConfiguration,Cold.circuitInput,Cold.input])
  rw [ht,Nat.zero_add] at h
  exact h.trans hs

/-- Only the actual producer budget is needed to bound balanced serialization. -/
theorem serialize_budget {n : ℕ} (c : BooleanCircuit n) :
    Serialize.budget c ≤ 6*Cold.budget n c.nodes.length+8+
      1000000000064*(Cold.budget n c.nodes.length+1)^12 := by
  have hf := formula_bytes c
  have hp := Nat.pow_le_pow_left (Nat.add_le_add_right hf 1) 12
  have hs := RecoveryFormulaFrame.budget_bound
    (RecoveryFormulaPayload.fields (CircuitInputCNF.circuitInputFormula c))
  change RecoveryFormulaFrame.rawBudget _ ≤
    1000000000064*((RecoveryFormulaPayload.input (CircuitInputCNF.circuitInputFormula c)).length+1)^12 at hs
  unfold Serialize.budget Cold.framedBudget
  have hm := Nat.mul_le_mul_left 1000000000064 hp
  omega

end NearCubicWires.RepairOrdinary.RecoveryBoundedGraphBudget
