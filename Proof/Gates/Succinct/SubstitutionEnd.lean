import Proof.Gates.Succinct.SubstitutionPhaseSpecs
import Proof.Gates.Succinct.SubstitutionLoopSpecs
import Proof.Gates.Succinct.SubstitutionMain
import Proof.Gates.Succinct.SubstitutionCopyLoop
import Proof.Gates.Succinct.PointLoop

set_option autoImplicit false

namespace NearCubicGates.Close.Succinct.SubstMachine

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.Bindings.MW20
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.Succinct NearCubicGates.Close.Outer
open RepairRepresentation (natWord)

theorem nIter_le (S : ℕ) :
    nIter S ≤ 100000000 * (S + 2) ^ 5 + 100000000 * (S + 2) ^ 4 + 1000000 * (S + 2) ^ 2 + 1000004 * (S + 2) +
      1000000 := by
  unfold nIter oIter cpIter cIter
  have h1 : (S + 1) * (100000000 * (S + 2) ^ 4 + 1000000 + 4) ≤
      (S + 2) * (100000000 * (S + 2) ^ 4 + 1000000 + 4) := Nat.mul_le_mul_right _ (by omega)
  have e : (S + 2) * (100000000 * (S + 2) ^ 4 + 1000000 + 4) = 100000000 * (S + 2) ^ 5 + 1000004 * (S + 2) := by
    ring
  omega

theorem subst_cost_le (S n : ℕ) (hn : n ≤ S) :
    headCost S + cntCost S + sizesCost S + 1000000 * (S + 2) ^ 3 + n * (readCost 5 + nIter S + 20 + 4) +
      2 * cIter S + 100 ≤ substCostClass S := by
  have hR : readCost 5 = 490000 := by unfold readCost; norm_num
  have hI := nIter_le S
  have hN : n * (readCost 5 + nIter S + 20 + 4) ≤ (S + 2) * (100000000 * (S + 2) ^ 5 + 100000000 * (S + 2) ^ 4 +
      1000000 * (S + 2) ^ 2 + 1000004 * (S + 2) + 1490024) := Nat.mul_le_mul (by omega) (by omega)
  have e : (S + 2) * (100000000 * (S + 2) ^ 5 + 100000000 * (S + 2) ^ 4 + 1000000 * (S + 2) ^ 2 +
      1000004 * (S + 2) + 1490024) = 100000000 * (S + 2) ^ 6 + 100000000 * (S + 2) ^ 5 + 1000000 * (S + 2) ^ 3 +
      1000004 * (S + 2) ^ 2 + 1490024 * (S + 2) := by ring
  have hX2 : 2 ≤ S + 2 := by omega
  unfold headCost cntCost sizesCost cIter substCostClass
  generalize S + 2 = X at hN e hX2 ⊢
  have p1 : X ≤ X ^ 7 := Nat.le_self_pow (by norm_num) X
  have p2 : X ^ 2 ≤ X ^ 7 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have p3 : X ^ 3 ≤ X ^ 7 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have p4 : X ^ 4 ≤ X ^ 7 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have p5 : X ^ 5 ≤ X ^ 7 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have p6 : X ^ 6 ≤ X ^ 7 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have p0 : 1 ≤ X ^ 7 := Nat.one_le_pow _ _ (by omega)
  omega

theorem costSpec : CostSpec := subst_cost_le

theorem endOut (o : OracleOutput) {q : ℕ} (B : BooleanCircuit q) :
    marks (hdrD o B ++ (accI B o.circuit o.circuit.nodes.length).1.flatMap PCPPRequestNodeSchema.native ++
        PCPPRequestNodeSchema.native
          (BooleanNode.not (posF (ofl o.circuit) o.circuit.output.val (B.nodes.length - 1) B.output.val) :
            BooleanNode q) ++
        (List.replicate (q - (szv o B + 1)) (BooleanNode.const false : BooleanNode q)).flatMap
          PCPPRequestNodeSchema.native ++
        natWord (szv o B)) ++ [false] =
      RepairOrdinary.frame (PCPPNative.descriptor (Outer.substCircuit o.circuit B).padToArity) := by
  rw [NearCubicGates.Close.Succinct.frame_eq_marks', descriptor_D B o.circuit, szv_eq,
    ← posM_posF B o.circuit o.circuit.output.val o.circuit.output.isLt.le]
  simp only [hdrD, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]

theorem endOutSpec : EndOutSpec := fun o _ B => endOut o B

end NearCubicGates.Close.Succinct.SubstMachine
