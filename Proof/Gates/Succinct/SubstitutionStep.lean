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

theorem otag_le {ℓ : ℕ} (nd : OracleNode ℓ ℓ) : otag nd ≤ 5 := by cases nd <;> simp [otag]

/-- **The tag of node `i`, read**: the context of the kind lemmas. -/
theorem tagRead (cap : ℕ) (o : OracleOutput) (B : BooleanCircuit q) (i : ℕ) (hi : i < o.circuit.nodes.length)
    (τ : WState 4 nrH) (hI : MInv o B i τ) (hcap : capH o B ≤ cap) :
    ∃ τ1, WExec cap (rd sW RW .tag) (τ.setv (regH .iC) (o.circuit.nodes.length - i - 1)) τ1
        (readCost (otag (o.circuit.nodes[i]'hi))) ∧
      τ1.val (regH .tag) = otag (o.circuit.nodes[i]'hi) ∧
      KCtx cap o B i τ (τ1.setv (regH .tag) 0) := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ := hI
  have hv : ∀ u, τ.val (regH u) = VM o B i u := a11
  set τ0 := τ.setv (regH .iC) (o.circuit.nodes.length - i - 1) with hτ0
  have hsplit := word_split o i hi
  rw [node_word] at hsplit
  have hle := lenC_le o (i + 1)
  rw [lenC_succ o i hi, node_word, List.length_append] at hle
  have htag := otag_le (o.circuit.nodes[i]'hi)
  obtain ⟨hzC, hzB, hzq, hwh, hlb, hdl, hnCw⟩ := sizes_le o B
  have h4 := sq4 (sizeS o B)
  have hcp := capH_ge o B
  have h5 : sizeS o B + 2 ≤ (sizeS o B + 2) ^ 4 := Nat.le_self_pow (by norm_num) _
  have hS : sizeS o B = o.word.length + (PCPPNative.descriptor B).length + q + 1 := rfl
  obtain ⟨τ1, e1, s1, c1, v1, f1, t1⟩ := rd_fr cap sW .cdW .tag (by simp) (by simp) (by simp) (by simp) (by simp)
    (by simp) (by simp) τ0
    (natWord o.ell ++ natWord o.circuit.nodes.length ++ (o.circuit.nodes.take i).flatMap oracleNodeWord)
    (orest (o.circuit.nodes[i]'hi) ++ ((o.circuit.nodes.drop (i + 1)).flatMap oracleNodeWord ++
      natWord o.circuit.output.val)) (otag (o.circuit.nodes[i]'hi))
    (by simp only [τ0, WState.setv_st]; rw [a1, hsplit]; simp only [List.append_assoc])
    (by simp only [τ0, WState.setv_sh]; rw [a2]; simp only [pC, lenC, List.length_append])
    (fun r => by simp only [τ0, WState.setv_val, Function.update_apply, regH_eq_iff, reduceCtorEq, if_false]
                 rw [hv]; exact VM_f o B i r)
    (by simp only [τ0, WState.setv_val, Function.update_apply, regH_eq_iff, reduceCtorEq, if_false]; rw [hv]
        simp [VM, V3, V2, V1])
    (by simp only [τ0, WState.setv_val, Function.update_apply, regH_eq_iff, reduceCtorEq, if_false]; rw [hv]
        simp [VM, V3, V2, V1])
    (by simp only [τ0, WState.setv_val, Function.update_apply, regH_eq_iff, reduceCtorEq, if_false]; rw [hv]
        simp [VM, V3, V2, V1])
    (by simp only [τ0, WState.setv_val, Function.update_apply, regH_eq_iff, reduceCtorEq, if_false]; rw [hv]
        simp only [VM, if_true]; unfold capH at hcap; omega)
  have hcd0 : τ0.val (regH .cdW) = τ.val (regH .cdW) := by simp [τ0]
  refine ⟨τ1, e1, v1, ⟨hi, ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hcap⟩⟩
  · intro j hj; simp only [WState.setv_st, WState.setv_sh]
    rw [(f1.s (by simp [hj])).1, (f1.s (by simp [hj])).2]; simp [τ0]
  · simp only [WState.setv_st]; rw [t1]; simp [τ0]
  · simp only [WState.setv_sh]; rw [s1, a2]; simp only [pC, lenC, List.length_append]
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hu
    simp only [WState.setv_val, Function.update_apply, regH_eq_iff]
    split_ifs with ht
    · subst ht; rw [hv]; simp [VM, V3, V2, V1]
    · rw [f1.v (by simp [hu.1, ht])]; simp [τ0, Function.update_apply, hu.2]
  · simp only [WState.setv_val, Function.update_apply, regH_eq_iff, reduceCtorEq, if_false]; rw [c1, hcd0]
  · simp only [WState.setv_val, Function.update_apply, regH_eq_iff, reduceCtorEq, if_false]
    rw [f1.v (by simp)]; simp [τ0]
  · simp only [WState.setv_cell]; rw [f1.2.2]; simp [τ0]

def Kind1OK (cap : ℕ) (o : OracleOutput) (B : BooleanCircuit q) : Prop :=
  ∀ (i : ℕ) (τ σ1 : WState 4 nrH) (h : KCtx cap o B i τ σ1) (j : Fin o.ell),
    o.circuit.nodes[i]'h.hi = .input j →
    ∃ τ3, WExec cap nC1 σ1 τ3 (cIter (sizeS o B) + 4) ∧ MInv o B (i + 1) τ3 ∧
      τ3.val (regH .iC) = o.circuit.nodes.length - i - 1

theorem nIter_ge (S : ℕ) : oIter S ≤ nIter S ∧ cIter S + 4 ≤ nIter S ∧ 200004 ≤ nIter S := by
  have := cIter_sub S
  unfold nIter; omega

set_option maxHeartbeats 1600000 in
/-- **One node of `C`** (paper §11.4; `Outer.substStepG`). -/
theorem nodeStep (cap : ℕ) (o : OracleOutput) (B : BooleanCircuit q) (hK1 : Kind1OK cap o B) (i : ℕ)
    (hi : i < o.circuit.nodes.length) (τ : WState 4 nrH) (hI : MInv o B i τ) (hcap : capH o B ≤ cap) :
    ∃ τ', WExec cap nodeBody (τ.setv (regH .iC) (o.circuit.nodes.length - i - 1)) τ'
        (readCost 5 + nIter (sizeS o B) + 20) ∧
      MInv o B (i + 1) τ' ∧ τ'.val (regH .iC) = o.circuit.nodes.length - i - 1 := by
  obtain ⟨τ1, e1, v1, K⟩ := tagRead cap o B i hi τ hI hcap
  have hge := nIter_ge (sizeS o B)
  have htag := otag_le (o.circuit.nodes[i]'hi)
  have hrc : readCost (otag (o.circuit.nodes[i]'hi)) ≤ readCost 5 := by
    unfold readCost; exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)
  have fin : ∀ (P : WM 4 nrH) (hP : [nC0, nC1, nC2, nC34 3, nC34 4, nC5][otag (o.circuit.nodes[i]'hi)]'(by simp; omega) = P)
      (τ3 : WState 4 nrH) (n : ℕ), WExec cap P (τ1.setv (regH .tag) 0) τ3 n → n ≤ nIter (sizeS o B) →
      MInv o B (i + 1) τ3 → τ3.val (regH .iC) = o.circuit.nodes.length - i - 1 →
      ∃ τ', WExec cap nodeBody (τ.setv (regH .iC) (o.circuit.nodes.length - i - 1)) τ'
          (readCost 5 + nIter (sizeS o B) + 20) ∧
        MInv o B (i + 1) τ' ∧ τ'.val (regH .iC) = o.circuit.nodes.length - i - 1 := by
    intro P hP τ3 n e3 hn hM hiC
    have eC := caseL_spec cap (regH .tag) [nC0, nC1, nC2, nC34 3, nC34 4, nC5] (otag (o.circuit.nodes[i]'hi))
      (by simp; omega) τ1 τ3 n v1
      (by rw [v1]; have := K.cap; have := capH_ge o B; have : 1 ≤ (sizeS o B + 2) ^ 4 := Nat.one_le_pow _ _ (by omega)
          omega)
      (by rw [hP]; exact e3)
    exact ⟨τ3, WExec.mono (WExec.seq e1 eC) (by omega), hM, hiC⟩
  have hw := o.circuit.wellFormed ⟨i, hi⟩
  simp only [List.get_eq_getElem] at hw
  have hst : (accI B o.circuit (i + 1)).1 = (substStepG B inputMapD [] (accI B o.circuit i) (o.circuit.nodes[i]'hi)).1 := by
    rw [accI_succ B o.circuit i hi]
  match hk : o.circuit.nodes[i]'hi with
  | .const b =>
    obtain ⟨τ3, e3, hM, hiC⟩ := kind0 K b hk
    exact fin nC0 (by simp [hk, otag]) τ3 _ e3 (by omega) hM hiC
  | .input j =>
    obtain ⟨τ3, e3, hM, hiC⟩ := hK1 i τ _ K j hk
    exact fin nC1 (by simp [hk, otag]) τ3 _ e3 (by omega) hM hiC
  | .not c =>
    obtain ⟨τ3, e3, hM, hiC⟩ := kind2 K c hk
    exact fin nC2 (by simp [hk, otag]) τ3 _ e3 (by omega) hM hiC
  | .and l r =>
    rw [hk] at hw hst
    simp only [OracleNode.WellFormedAt] at hw
    obtain ⟨τ3, e3, hM, hiC⟩ := kind34 K 3 (fun x y => BooleanNode.and x y)
      (fun x y => by simp [PCPPRequestNodeSchema.fields]) (by omega) l r (by simp [hk, orest]) hw
      (by rw [hst]; simp [substStepG])
    exact fin (nC34 3) (by simp [hk, otag]) τ3 _ e3 (by omega) hM hiC
  | .or l r =>
    rw [hk] at hw hst
    simp only [OracleNode.WellFormedAt] at hw
    obtain ⟨τ3, e3, hM, hiC⟩ := kind34 K 4 (fun x y => BooleanNode.or x y)
      (fun x y => by simp [PCPPRequestNodeSchema.fields]) (by omega) l r (by simp [hk, orest]) hw
      (by rw [hst]; simp [substStepG])
    exact fin (nC34 4) (by simp [hk, otag]) τ3 _ e3 (by omega) hM hiC
  | .oracle args =>
    obtain ⟨τ3, e3, hM, hiC⟩ := kind5 K args hk
    exact fin nC5 (by simp [hk, otag]) τ3 _ e3 (by omega) hM hiC

end NearCubicGates.Close.Succinct.SubstMachine
