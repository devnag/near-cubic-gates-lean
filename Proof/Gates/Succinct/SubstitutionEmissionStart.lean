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

theorem nbl_two_pow (k : ℕ) : natBitLength (2 ^ k) = k + 1 := by
  unfold natBitLength
  rw [Nat.log_pow (by norm_num)]

theorem nbl_mono' {a b : ℕ} (h : a ≤ b) : natBitLength a ≤ natBitLength b := by
  unfold natBitLength
  exact Nat.add_le_add_right (Nat.log_mono_right h) 1

/-- `natBitLength` of a quadratic quantity is linear. -/
theorem nbl_sq (S M : ℕ) (hM : M ≤ 2 * (S + 2) ^ 2) : natBitLength M ≤ 2 * (S + 2) + 2 := by
  have h1 : S + 2 < 2 ^ (S + 2) := Nat.lt_two_pow_self
  have h2 : (S + 2) ^ 2 ≤ (2 ^ (S + 2)) ^ 2 := Nat.pow_le_pow_left h1.le 2
  have e : 2 ^ (2 * (S + 2) + 1) = 2 * ((2 ^ (S + 2)) ^ 2) := by ring
  have h3 : M ≤ 2 ^ (2 * (S + 2) + 1) := by rw [e]; omega
  have := nbl_mono' h3
  rw [nbl_two_pow] at this
  exact this

theorem nodeCost_one : CheckedPCPP.NodeEmit.nodeCost 1 ≤ 10100 := by
  simp [CheckedPCPP.NodeEmit.nodeCost, CheckedPCPP.NodeEmit.fieldCost, natBitLength, Nat.log_one_right]

/-- The cost of `emStart`. -/
theorem emCost_le (S q M nC : ℕ) (hq : q ≤ S) (hM : M ≤ 2 * (S + 2) ^ 2) (hnM : natBitLength M ≤ 2 * (S + 2) + 2)
    (hnC : nC ≤ S) :
    CheckedPCPP.NodeEmit.fieldCost q 1 + 1 + (CheckedPCPP.NodeEmit.fieldCost M 1 + 1 +
      (CheckedPCPP.NodeEmit.nodeCost 1 + 1 + (3 + 1 + (18 * nC + 3)))) ≤ 1000000 * (S + 2) ^ 3 := by
  have hn1 := nodeCost_one
  have hnq : natBitLength q ≤ q + 1 := nbl_le q
  unfold CheckedPCPP.NodeEmit.fieldCost
  generalize hP : S + 2 = P at hM hnM ⊢
  have hP2 : 2 ≤ P := by omega
  have a1 : (natBitLength q + 10) * (100 * q + 200) ≤ (P + 10) * (100 * P + 200) :=
    Nat.mul_le_mul (by omega) (by omega)
  have a2 : (natBitLength M + 10) * (100 * M + 200) ≤ (2 * P + 12) * (200 * P ^ 2 + 200) :=
    Nat.mul_le_mul (by omega) (by omega)
  have b1 : (P + 10) * (100 * P + 200) ≤ 2000 * P ^ 3 := by nlinarith
  have b2 : (2 * P + 12) * (200 * P ^ 2 + 200) ≤ 5000 * P ^ 3 := by nlinarith
  have b3 : P ≤ P ^ 3 := Nat.le_self_pow (by norm_num) P
  have b4 : 2 * P ^ 2 ≤ 2 * P ^ 3 := by have := Nat.pow_le_pow_right (show 1 ≤ P by omega) (show 2 ≤ 3 by omega); omega
  have b5 : 1 ≤ P ^ 3 := Nat.one_le_pow _ _ (by omega)
  omega

set_option maxHeartbeats 2000000 in
/-- **The start of the emission** (`sec:gadget-machine`, `D_B`'s descriptor: header, then the fold's node `0`). -/
theorem emStart_spec (cap : ℕ) (o : OracleOutput) {q : ℕ} (B : BooleanCircuit q) (σ : WState 4 nrH)
    (hs : StrAt σ o.word (PCPPNative.descriptor B) [] (ofl o.circuit) (natWord o.ell) (pC o) (pB B) 0 0 0)
    (hv : RV σ (V3 o B)) (hcell : σ.cell = false) (hcap : capH o B ≤ cap) :
    ∃ τ, WExec cap emStart σ τ (1000000 * (sizeS o B + 2) ^ 3) ∧ MInv o B 0 τ := by
  obtain ⟨sW0, sD0, sO0, sF0, sL0, hW0, hD0, hO0, hF0, hL0⟩ := hs
  have hv' : ∀ u, σ.val (regH u) = V3 o B u := hv
  obtain ⟨hzC, hzB, hzq, -⟩ := sizes_le o B
  have hzv := szv_le o B
  have hcp := capH_ge o B
  have h4 := sq4 (sizeS o B)
  have hS4 : 1 ≤ (sizeS o B + 2) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hSsq : sizeS o B + 2 ≤ (sizeS o B + 2) ^ 2 := Nat.le_self_pow (by norm_num) _
  -- the values
  have vq : σ.val (regH .q) = q := by rw [hv']; simp [V3, V2, V1]
  have vM : σ.val (regH .M) = szv o B + 1 + (q - (szv o B + 1)) := by rw [hv']; simp [V3, V2, V1]
  have vw7 : σ.val (regH (.w 7)) = 0 := by rw [hv']; simp [V3, V2, V1]
  have vcur : σ.val (regH .cur) = 0 := by rw [hv']; simp [V3, V2, V1]
  have viC : σ.val (regH .iC) = 0 := by rw [hv']; simp [V3, V2, V1]
  have vnC : σ.val (regH .nC) = o.circuit.nodes.length := by rw [hv']; simp [V3, V2, V1]
  have vt : σ.val (regH .t) = 0 := by rw [hv']; simp [V3, V2, V1]
  have hout0 : OutOK σ [] := ⟨by rw [sO0]; rfl, by rw [hO0]; rfl, by rw [vw7]; rfl⟩
  have hcl0 : WClean σ := ⟨fun i _ => by rw [hv']; simp [V3, V2, V1], by rw [hv']; simp [V3, V2, V1]⟩
  have hMle : szv o B + 1 + (q - (szv o B + 1)) ≤ 2 * (sizeS o B + 2) ^ 2 := by omega
  have hnM := nbl_sq (sizeS o B) _ hMle
  have hnq : natBitLength q ≤ q + 1 := nbl_le q
  -- 1: the field `q`
  have e1 := fieldN_spec cap σ .q ⟨fun i => by simp, by simp⟩ [] hout0 hcl0 (by rw [vq]; simp; omega)
  set σ1 := appendO σ sO (regH (.w 7)) (marks (natWord (σ.val (regH .q)))) with hσ1
  have hout1 : OutOK σ1 ([] ++ natWord (σ.val (regH .q))) := appendO_outOK σ _ _ hout0
  have hcl1 : WClean σ1 := appendO_wclean σ _ hcl0
  have v1 : ∀ u, u ≠ .w 7 → σ1.val (regH u) = σ.val (regH u) := fun u hu => appendO_val_ne σ _ u hu
  -- 2: the field `M`
  have e2 := fieldN_spec cap σ1 .M ⟨fun i => by simp, by simp⟩ _ hout1 hcl1 (by
    rw [v1 _ (by simp), vM, vq]
    have := natWord_length q
    simp only [List.nil_append, this]
    omega)
  set σ2 := appendO σ1 sO (regH (.w 7)) (marks (natWord (σ1.val (regH .M)))) with hσ2
  have hout2' : OutOK σ2 ([] ++ natWord (σ.val (regH .q)) ++ natWord (σ1.val (regH .M))) :=
    appendO_outOK σ1 _ _ hout1
  have hout2 : OutOK σ2 (hdrD o B) := by
    have e : [] ++ natWord (σ.val (regH .q)) ++ natWord (σ1.val (regH .M)) = hdrD o B := by
      rw [v1 _ (by simp), vM, vq]; simp [hdrD]
    rw [← e]; exact hout2'
  have hcl2 : WClean σ2 := appendO_wclean σ1 _ hcl1
  have v2 : ∀ u, u ≠ .w 7 → σ2.val (regH u) = σ.val (regH u) := fun u hu =>
    (appendO_val_ne σ1 _ u hu).trans (v1 u hu)
  -- 3: node `0` (`const false`)
  have hfull := out_le o B 0 (Nat.zero_le _)
  rw [accI_zero] at hfull
  obtain ⟨τ3, e3, hout3, hcl3, hf3⟩ := emit_fr cap σ2 ([], 0) ([], 0) ([], 0) (BooleanNode.const false : BooleanNode q)
    (hdrD o B) hout2 hcl2 ⟨fun x hx => by simp at hx, fun x hx => by simp at hx, fun x hx => by simp at hx⟩
    ⟨by simp, by simp, by simp⟩
    ⟨by rw [fv_nil]; rfl, by rw [fv_nil]; rfl, by rw [fv_nil]; rfl⟩ 1
    (fun i => by fin_cases i <;> simp [PCPPRequestNodeSchema.fields])
    (by simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.length_append] at hfull
        unfold capH at hcap; omega)
  have v3 : ∀ u, u ≠ .w 7 → τ3.val (regH u) = σ.val (regH u) := fun u hu =>
    (hf3.v (by simp [hu])).trans (v2 u hu)
  -- 4: `cur := 1`
  have e4 := WExec.inc (cap := cap) (regH .cur) τ3 (by rw [v3 _ (by simp), vcur]; omega)
  set τ4 := τ3.setv (regH .cur) (τ3.val (regH .cur) + 1) with hτ4
  -- 5: `iC := n_C`
  obtain ⟨τ5, e5, h5iC, hf5⟩ := add_fr cap .nC .iC (by simp) (by simp) (by simp) τ4
    (by simp [τ4, v3 _ (show HReg.t ≠ .w 7 by simp), vt])
    (by simp [τ4, v3 _ (show HReg.iC ≠ .w 7 by simp), v3 _ (show HReg.nC ≠ .w 7 by simp), viC, vnC]; omega)
  refine ⟨τ5, ?_, ?_⟩
  · refine WExec.mono (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 e5)))) ?_
    rw [v1 _ (by simp), vM, vq]
    simp only [τ4, WState.setv_val]
    rw [Function.update_of_ne (show regH HReg.nC ≠ regH HReg.cur by simp), v3 _ (by simp), vnC]
    exact emCost_le (sizeS o B) q _ o.circuit.nodes.length (by omega) hMle hnM (by omega)
  · have hstr : ∀ i, i ≠ sO → τ5.st i = σ.st i ∧ τ5.sh i = σ.sh i := by
      intro i hi
      have a := hf5.s (i := i) (by simp)
      have b := hf3.s (i := i) (by simpa using hi)
      have c := appendO_st_ne σ1 (regH (.w 7)) (marks (natWord (σ1.val (regH .M)))) i hi
      have d := appendO_st_ne σ (regH (.w 7)) (marks (natWord (σ.val (regH .q)))) i hi
      refine ⟨?_, ?_⟩
      · rw [a.1]; simp only [τ4, WState.setv_st]; rw [b.1, c.1, d.1]
      · rw [a.2]; simp only [τ4, WState.setv_sh]; rw [b.2, c.2, d.2]
    have v5 : ∀ u, u ≠ .iC → u ≠ .cur → u ≠ .w 7 → τ5.val (regH u) = σ.val (regH u) := by
      intro u h1 h2 h3
      rw [hf5.v (by simp [h1])]
      simp only [τ4, WState.setv_val]
      rw [Function.update_of_ne (by simpa using h2), v3 u h3]
    have w5 : τ5.val (regH (.w 7)) = τ3.val (regH (.w 7)) := by
      rw [hf5.v (by simp)]
      simp only [τ4, WState.setv_val]
      rw [Function.update_of_ne (by simp)]
    have cur5 : τ5.val (regH .cur) = 1 := by
      rw [hf5.v (by simp)]
      simp only [τ4, WState.setv_val, Function.update_self]
      rw [v3 _ (by simp), vcur]
    have iC5 : τ5.val (regH .iC) = o.circuit.nodes.length := by
      rw [h5iC]
      simp only [τ4, WState.setv_val]
      rw [Function.update_of_ne (by simp), Function.update_of_ne (by simp), v3 _ (by simp), v3 _ (by simp), viC, vnC]
      omega
    have hacc : (accI B o.circuit 0).1.flatMap PCPPRequestNodeSchema.native =
        PCPPRequestNodeSchema.native (BooleanNode.const false : BooleanNode q) := by
      rw [accI_zero]; simp
    have hout5 : OutOK τ5 (hdrD o B ++ (accI B o.circuit 0).1.flatMap PCPPRequestNodeSchema.native) := by
      rw [hacc]
      refine ⟨?_, ?_, ?_⟩
      · rw [(hf5.s (by simp)).1]; simp only [τ4, WState.setv_st]; exact hout3.1
      · rw [(hf5.s (by simp)).2]; simp only [τ4, WState.setv_sh]; exact hout3.2.1
      · rw [w5]; exact hout3.2.2
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hout5, ?_, ?_, ?_⟩
    · rw [(hstr sW (by decide)).1, sW0]
    · rw [(hstr sW (by decide)).2, hW0]; simp [lenC]
    · rw [(hstr sD (by decide)).1, sD0]
    · rw [(hstr sD (by decide)).2, hD0]
    · rw [(hstr sF (by decide)).1, sF0]
    · rw [(hstr sF (by decide)).2, hF0]
    · rw [(hstr sL (by decide)).1, sL0]
    · rw [(hstr sL (by decide)).2, hL0]
    · refine ⟨fun i hi => ?_, ?_⟩
      · have hne : HReg.w i ≠ .w 7 := by simpa using hi
        rw [hf5.v (by simp), show τ4.val (regH (.w i)) = τ3.val (regH (.w i)) by
          simp only [τ4, WState.setv_val]; rw [Function.update_of_ne (by simp)]]
        exact hcl3.1 i hi
      · rw [hf5.v (by simp), show τ4.val (regH .wt) = τ3.val (regH .wt) by
          simp only [τ4, WState.setv_val]; rw [Function.update_of_ne (by simp)]]
        exact hcl3.2
    · intro u
      unfold VM
      by_cases hc : u = .cdW
      · subst hc
        rw [v5 _ (by simp) (by simp) (by simp), hv']
        simp [V3, V2, V1, lenC]
      by_cases hu : u = .cur
      · subst hu; rw [cur5, accI_zero]; simp
      by_cases hi : u = .iC
      · subst hi; rw [iC5]; simp
      by_cases hw : u = .w 7
      · subst hw; rw [w5, hout3.2.2, hacc]; simp
      rw [v5 u hi hu hw, hv']
      simp [hc, hu, hi, hw]
    · rw [hf5.2.2]
      simp only [τ4, WState.setv_cell]
      rw [hf3.2.2]
      simp [σ2, σ1, appendO, hcell]

end NearCubicGates.Close.Succinct.SubstMachine
