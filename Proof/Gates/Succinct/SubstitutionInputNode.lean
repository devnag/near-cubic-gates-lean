import Proof.Gates.Succinct.SubstitutionInputAndEnd
import Proof.Gates.Succinct.SubstitutionMain

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicGates.Close.Succinct.SubstMachine

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.Bindings.MW20
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.Succinct NearCubicGates.Close.Outer
open RepairRepresentation (natWord)

variable {q : ℕ}

theorem inputMapD_native {ℓ : ℕ} (j : Fin ℓ) :
    (if j.val < q then natWord 1 ++ natWord j.val ++ natWord 0 else natWord 0 ++ natWord 0 ++ natWord 0) =
      PCPPRequestNodeSchema.native (inputMapD j : BooleanNode q) := by
  unfold inputMapD
  split_ifs with hj
  · rfl
  · rfl

theorem inputIndex_len {o : OracleOutput} (B : BooleanCircuit q) (i : ℕ) (hi : i < o.circuit.nodes.length)
    (j : Fin o.ell) (hk : o.circuit.nodes[i]'hi = .input j) : natBitLength j.val ≤ sizeS o B := by
  have h1 := lenC_le o (i + 1)
  rw [lenC_succ o i hi, node_word, hk] at h1
  simp only [orest, otag, List.length_append, natWord_length] at h1
  unfold sizeS
  omega

theorem kind1 {cap : ℕ} {o : OracleOutput} {B : BooleanCircuit q} {i : ℕ} {τ σ1 : WState 4 nrH}
    (h : KCtx cap o B i τ σ1) (j : Fin o.ell) (hk : o.circuit.nodes[i]'h.hi = .input j) :
    ∃ τ3, WExec cap nC1 σ1 τ3 (cIter (sizeS o B) + 4) ∧ MInv o B (i + 1) τ3 ∧
      τ3.val (regH .iC) = o.circuit.nodes.length - i - 1 := by
  have F := h.facts
  have hc := h.cap_le
  have V := h.vals
  have hjS := inputIndex_len B i h.hi j hk
  obtain ⟨hzC, hzB, hzq, hwh, hlb, hdl, hnCw⟩ := sizes_le o B
  rw [hk] at F
  obtain ⟨τ2, e2, sh2, cd2, o2, w2, z2, g2, f2, st2⟩ := nC1b_spec cap σ1 F.2.2.2.2.2.2.2.2.2.2.1
    V.2.2.2.2.2.2.2.1
    (natWord o.ell ++ natWord o.circuit.nodes.length ++ (o.circuit.nodes.take i).flatMap oracleNodeWord ++ natWord 1)
    ((o.circuit.nodes.drop (i + 1)).flatMap oracleNodeWord ++ natWord o.circuit.output.val) j.val
    (by rw [F.1]; simp [otag, orest, List.append_assoc]) (by rw [F.2.1]; simp [otag])
    (by rw [V.2.2.2.2.1, V.2.2.2.1]) (sizeS o B) (by rw [V.2.2.2.1]; omega) hjS
    (hdrD o B ++ (accI B o.circuit i).1.flatMap PCPPRequestNodeSchema.native) F.2.2.2.2.2.2.2.2.1
    F.2.2.2.2.2.2.2.2.2.1 (by omega)
  rw [V.2.2.2.1, inputMapD_native j] at o2
  have hE : (accI B o.circuit (i + 1)).1 = (accI B o.circuit i).1 ++ [(inputMapD j : BooleanNode q)] := by
    rw [accI_succ B o.circuit i h.hi]; simp [hk, substStepG]
  exact kindWrap h nC1b τ2 _ e2 [(inputMapD j : BooleanNode q)] rfl hE
    (by rw [sh2, F.2.1]; simp only [hk, orest, otag, List.length_append]; omega)
    (by rw [cd2]; simp only [hk, orest, List.length_append]; omega)
    (by simpa using o2) w2 f2 st2

end NearCubicGates.Close.Succinct.SubstMachine
