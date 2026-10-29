import Proof.Gates.Succinct.SubstitutionPlainNode

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

/-- An index whose field is longer than the guard `hc q + 1` is at least `q`. -/
theorem index_ge_of_long (q i : ℕ) (h : hc q + 1 < natBitLength i) : q ≤ i := by
  have hq := lt_two_pow_hc q
  unfold natBitLength at h
  have hi : i ≠ 0 := by intro e; subst e; simp at h
  have h1 : 2 ^ (hc q + 1) ≤ 2 ^ Nat.log 2 i := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 : 2 ^ Nat.log 2 i ≤ i := Nat.pow_log_le_self 2 hi
  have h3 : 2 ^ hc q ≤ 2 ^ (hc q + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

/-- **`C`'s input node, steps 1–3**: the guarded index field (`fieldToG`, guard `hc q + 1`), the skipped second
field, the comparison `[index < q]`. -/
theorem inputNode_front (cap : ℕ) (σ : WState 4 nrH) (hz : CBZ σ) (hg : σ.val (regH .g) = 0) (preW restW : List Bool)
    (i : ℕ) (hW : σ.st sW = preW ++ natWord i ++ natWord 0 ++ restW) (hWh : σ.sh sW = preW.length)
    (hbq : σ.val (regH .bq) = hc (σ.val (regH .q)) + 1) (S : ℕ) (hq : σ.val (regH .q) ≤ S) (hiS : natBitLength i ≤ S)
    (hcap : σ.val (regH .cdW) + 2000 * (S + 2) ^ 2 ≤ cap) :
    ∃ τ1 τ2 τ3 n1 n2 n3, WExec cap (fieldToG sW RW (regH .bq) (regH .f1) (regH .g)) σ τ1 n1 ∧
      WExec cap (sk1 sW RW) τ1 τ2 n2 ∧ WExec cap (lessW .f1 .q) τ2 τ3 n3 ∧
      n1 + n2 + n3 ≤ 9000 * (S + 2) ^ 2 + 5000 ∧
      τ3.sh sW = preW.length + (natWord i).length + (natWord 0).length ∧
      τ3.val (regH .cdW) = σ.val (regH .cdW) + (natWord i).length + (natWord 0).length ∧
      τ3.st sW = σ.st sW ∧ Fr σ τ3 [sW] [.cdW, .f1, .g, .lt] ∧
      τ3.val (regH .f1) ≤ 4 * S + 2 ∧ τ3.val (regH .g) ≤ 1 ∧
      (τ3.val (regH .g) ≠ 0 → σ.val (regH .q) ≤ i) ∧ (τ3.val (regH .g) = 0 → τ3.val (regH .f1) = i) ∧
      τ3.val (regH .lt) = (if τ3.val (regH .f1) < σ.val (regH .q) then 1 else 0) := by
  have hnb := natWord_length i
  have hsq : S + 2 ≤ (S + 2) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hpq : 2 ^ σ.val (regH .bq) ≤ 4 * σ.val (regH .q) + 2 := by
    rw [hbq, pow_succ]; have := two_pow_hc_le (σ.val (regH .q)); omega
  have hbq2 : σ.val (regH .bq) < 2 ^ σ.val (regH .bq) := Nat.lt_two_pow_self
  -- 1. the guarded field
  have hW' : σ.st sW = preW ++ natWord i ++ (natWord 0 ++ restW) := by rw [hW]; simp [List.append_assoc]
  have hones : ones (σ.st sW) (σ.sh sW) = natBitLength i := by rw [hW', hWh]; exact ones_natWord _ _ _
  have hend : fieldEnd (σ.st sW) (σ.sh sW) = preW.length + (natWord i).length := by
    rw [hW', hWh]; exact fieldEnd_natWord _ _ _
  have hfvlt : fieldVal (σ.st sW) (σ.sh sW) (σ.val (regH .bq)) < 2 ^ σ.val (regH .bq) := fieldVal_lt _ _ _
  have hfvi : ¬ σ.val (regH .bq) < natBitLength i → fieldVal (σ.st sW) (σ.sh sW) (σ.val (regH .bq)) = i :=
    fun h => by rw [hW', hWh]; exact fieldVal_natWord _ _ _ _ (by omega)
  have hRW : RW .cd = regH .cdW := fam_cd .cdW
  have hcd : σ.val (RW .cd) = σ.val (regH .cdW) := by rw [hRW]
  have e1 := fieldToG_spec cap sW RW (fam_inj .cdW (by simp)) (regH .bq) (regH .f1) (regH .g)
    (famNe .cdW .bq (by simp) (by simp)) (famNe .cdW .f1 (by simp) (by simp)) (famNe .cdW .g (by simp) (by simp))
    (by simp) σ (famZero .cdW σ hz.f) (hz.z _ (by simp [zl])) hg
    (by have h2 : 2 ^ (σ.val (regH .bq) + 1) = 2 * 2 ^ σ.val (regH .bq) := by ring
        rw [hones, hcd, h2]; omega)
  generalize hτ1 : (((σ.seth sW (fieldEnd (σ.st sW) (σ.sh sW))).setv (RW .cd)
    (σ.val (RW .cd) + 2 * ones (σ.st sW) (σ.sh sW) + 1)).setv (regH .f1)
      (fieldVal (σ.st sW) (σ.sh sW) (σ.val (regH .bq)))).setv (regH .g)
      (if σ.val (regH .bq) < ones (σ.st sW) (σ.sh sW) then 1 else 0) = τ1 at e1
  generalize hFV : fieldVal (σ.st sW) (σ.sh sW) (σ.val (regH .bq)) = fv at hτ1 hfvlt hfvi
  have v1 : ∀ u, u ∉ [HReg.cdW, .f1, .g] → τ1.val (regH u) = σ.val (regH u) := by
    intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hu
    rw [← hτ1]
    simp [Function.update_apply, hRW, hu.1, hu.2.1, hu.2.2]
  have f1v : τ1.val (regH .f1) = fv := by rw [← hτ1]; simp [Function.update_apply]
  have g1v : τ1.val (regH .g) = if σ.val (regH .bq) < natBitLength i then 1 else 0 := by
    rw [← hτ1]; simp [Function.update_apply, hones]
  have c1v : τ1.val (regH .cdW) = σ.val (regH .cdW) + (natWord i).length := by
    rw [← hτ1]; simp [Function.update_apply, hRW, hones, hnb]; ring
  have st1 : τ1.st = σ.st := by rw [← hτ1]; simp
  have sh1 : ∀ y, y ≠ sW → τ1.sh y = σ.sh y := fun y hy => by rw [← hτ1]; simp [Function.update_apply, hy]
  have shW1 : τ1.sh sW = preW.length + (natWord i).length := by rw [← hτ1]; simp [hend]
  have fr1 : Fr σ τ1 [sW] [.cdW, .f1, .g] := by
    refine ⟨fun y hy => ?_, fun r hr => ?_, by rw [← hτ1]; simp⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      exact ⟨by rw [st1], sh1 y hy⟩
    · obtain ⟨u, rfl⟩ := regH_surj r
      apply v1 u
      intro hu
      apply hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl | rfl <;> simp
  -- 2. skip the second field
  obtain ⟨τ2, e2, s2, c2, f2, t2⟩ := sk1_fr cap sW .cdW (by simp) (by simp) (by simp) τ1 (preW ++ natWord i)
    restW 0 (by rw [st1, hW]) (by rw [shW1]; simp) (fun r => by rw [v1 _ (by simp)]; exact hz.f r)
    (by rw [v1 _ (by simp)]; exact hz.z _ (by simp [zl])) (by rw [v1 _ (by simp)]; exact hz.z _ (by simp [zl]))
    (by rw [c1v]; have : natBitLength 0 = 1 := by simp [natBitLength]
        omega)
  have g2 : ∀ u, u ∉ [HReg.cdW, .f1, .g] → τ2.val (regH u) = σ.val (regH u) := fun u hu => by
    rw [f2.v (by simp at hu ⊢; exact hu.1), v1 u hu]
  have f2v : τ2.val (regH .f1) = fv := by rw [f2.v (by simp), f1v]
  have g2v : τ2.val (regH .g) = if σ.val (regH .bq) < natBitLength i then 1 else 0 := by rw [f2.v (by simp), g1v]
  have q2 : τ2.val (regH .q) = σ.val (regH .q) := g2 _ (by simp)
  -- 3. compare the index with `q`
  obtain ⟨τ3, e3, l3, f3⟩ := less_fr cap .f1 .q (by decide) τ2
    (fun u hu => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rw [g2 u (by rcases hu with rfl | rfl | rfl | rfl | rfl <;> simp)]
      exact hz.z u (by rcases hu with rfl | rfl | rfl | rfl | rfl <;> simp [zl]))
    (by rw [f2v, q2]; omega)
  have f3v : τ3.val (regH .f1) = fv := by rw [f3.v (by simp), f2v]
  have g3v : τ3.val (regH .g) = if σ.val (regH .bq) < natBitLength i then 1 else 0 := by rw [f3.v (by simp), g2v]
  rw [f2v, q2] at l3
  have hfc : fieldCost (natBitLength i) (σ.val (regH .bq)) ≤ 8000 * (S + 2) ^ 2 := by
    unfold fieldCost
    have h1 : natBitLength i + σ.val (regH .bq) + 2 ≤ 5 * (S + 2) := by omega
    have h2 : 2 ^ σ.val (regH .bq) + 1 ≤ 4 * (S + 2) := by omega
    have h3 : (natBitLength i + σ.val (regH .bq) + 2) * (2 ^ σ.val (regH .bq) + 1) ≤ (5 * (S + 2)) * (4 * (S + 2)) :=
      Nat.mul_le_mul h1 h2
    have h4 : (5 * (S + 2)) * (4 * (S + 2)) = 20 * (S + 2) ^ 2 := by ring
    rw [Nat.mul_assoc]; omega
  have hsk : skipCost 0 = 4000 := by simp [skipCost, natBitLength]
  refine ⟨τ1, τ2, τ3, _, _, _, e1, e2, e3, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hones, hsk]; omega
  · rw [(f3.s (by simp)).2, s2]; simp only [List.length_append]
  · rw [f3.v (by simp), c2, c1v]
  · rw [(f3.s (by simp)).1, t2, st1]
  · refine ((fr1.trans' f2).trans' f3).mono (by intro x hx; simp at hx ⊢; omega) (fun u hu => ?_)
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl <;> simp
  · rw [f3v]; omega
  · rw [g3v]; split_ifs <;> omega
  · intro h; rw [g3v] at h; split_ifs at h with hl
    · exact index_ge_of_long _ i (by rw [← hbq]; exact hl)
    · exact absurd rfl h
  · intro h; rw [g3v] at h; split_ifs at h with hl
    rw [f3v]; exact hfvi hl
  · rw [l3, f3v]

/-- The node of an input of `C` (`const false` = three `natWord 0` fields). -/
theorem inputNode_constFalse (cap : ℕ) (τ' : WState 4 nrH) (out : List Bool) (ho : OutOK τ' out) (hw : WClean τ')
    (hcap : 2 * out.length + 100 ≤ cap) :
    ∃ τ4, WExec cap emit0 τ' τ4 (CheckedPCPP.NodeEmit.nodeCost 1) ∧
      OutOK τ4 (out ++ (natWord 0 ++ natWord 0 ++ natWord 0)) ∧ WClean τ4 ∧ Fr τ' τ4 [sO] [.w 7] := by
  have hl : (PCPPRequestNodeSchema.native (BooleanNode.const false : BooleanNode 1)).length ≤ 9 := by
    simp [PCPPRequestNodeSchema.native, PCPPRequestNodeSchema.fields, natBitLength]
  obtain ⟨τ4, e4, o4, w4, f4⟩ := emit_fr cap τ' ([], 0) ([], 0) ([], 0) (BooleanNode.const false : BooleanNode 1)
    out ho hw ⟨tok_nil, tok_nil, tok_nil⟩ (by simp) ⟨by rw [fv_nil]; rfl, by rw [fv_nil]; rfl, by rw [fv_nil]; rfl⟩
    1 (fun j => by fin_cases j <;> simp [PCPPRequestNodeSchema.fields]) (by omega)
  exact ⟨τ4, e4, o4, w4, f4⟩

/-- The node of an input `i < q` of `C` (`input i`). -/
theorem inputNode_input (cap : ℕ) (τ' : WState 4 nrH) (out : List Bool) (ho : OutOK τ' out) (hw : WClean τ') (i V : ℕ)
    (hi : τ'.val (regH .f1) = i) (hiV : i ≤ V) (hcap : 2 * out.length + 19 * V + 50 ≤ cap) :
    ∃ τ4, WExec cap (emit ([], 1) ([regH .f1], 0) ([], 0)) τ' τ4 (CheckedPCPP.NodeEmit.nodeCost (V + 1)) ∧
      OutOK τ4 (out ++ (natWord 1 ++ natWord i ++ natWord 0)) ∧ WClean τ4 ∧ Fr τ' τ4 [sO] [.w 7] := by
  have hV : ∀ j, PCPPRequestNodeSchema.fields (BooleanNode.input (⟨i, Nat.lt_succ_self i⟩ : Fin (i + 1))) j ≤ V + 1 :=
    fun j => by fin_cases j <;> simp [PCPPRequestNodeSchema.fields] <;> omega
  have hl := native_len_le (BooleanNode.input (⟨i, Nat.lt_succ_self i⟩ : Fin (i + 1))) (V + 1) hV
  obtain ⟨τ4, e4, o4, w4, f4⟩ := emit_fr cap τ' ([], 1) ([regH .f1], 0) ([], 0)
    (BooleanNode.input (⟨i, Nat.lt_succ_self i⟩ : Fin (i + 1))) out ho hw
    ⟨tok_nil, tok_list [.f1] 0 (by simp), tok_nil⟩ (by simp)
    ⟨by rw [fv_nil]; rfl, by rw [fv_one, hi]; rfl, by rw [fv_nil]; rfl⟩ (V + 1) hV (by omega)
  exact ⟨τ4, e4, o4, w4, f4⟩

/-- **`C`'s input node, step 4**: `const false` if the index was too long for the guard (then it is `≥ q`) or is
`≥ q`, else `input i`. -/
theorem inputNode_emit (cap : ℕ) (τ3 : WState 4 nrH) (i S : ℕ) (out : List Bool) (hout : OutOK τ3 out) (hcl : WClean τ3)
    (q : ℕ) (hf1 : τ3.val (regH .f1) ≤ 4 * S + 2)
    (hlong : τ3.val (regH .g) ≠ 0 → q ≤ i) (hshort : τ3.val (regH .g) = 0 → τ3.val (regH .f1) = i)
    (hlt : τ3.val (regH .lt) = if τ3.val (regH .f1) < q then 1 else 0)
    (hcap : 2 * out.length + 100 * (S + 2) ^ 2 ≤ cap) :
    ∃ τ4 n4, WExec cap (.ifr (regH .g) emit0 (.ifr (regH .lt) (emit ([], 1) ([regH .f1], 0) ([], 0)) emit0))
      τ3 τ4 n4 ∧ n4 ≤ 64000 * (S + 2) ^ 2 + 2 ∧
      OutOK τ4 (out ++ (if i < q then natWord 1 ++ natWord i ++ natWord 0
        else natWord 0 ++ natWord 0 ++ natWord 0)) ∧ WClean τ4 ∧ Fr τ3 τ4 [sO] [.w 7] := by
  have hsq : S + 2 ≤ (S + 2) ^ 2 := Nat.le_self_pow (by norm_num) _
  have n0 := nodeCost_le 1 (4 * S + 3) (by omega)
  have n1 := nodeCost_le (4 * S + 2 + 1) (4 * S + 3) (by omega)
  have hsq' : (4 * S + 3 + 12) ^ 2 ≤ 64 * (S + 2) ^ 2 := by
    have : 4 * S + 3 + 12 ≤ 8 * (S + 2) := by omega
    have h := Nat.pow_le_pow_left this 2
    have e : (8 * (S + 2)) ^ 2 = 64 * (S + 2) ^ 2 := by ring
    omega
  by_cases hg : τ3.val (regH .g) = 0
  · have hfi := hshort hg
    by_cases hiq : i < q
    · have hl1 : τ3.val (regH .lt) = 1 := by rw [hlt, hfi, if_pos hiq]
      obtain ⟨τ4, e4, o4, w4, f4⟩ := inputNode_input cap τ3 out hout hcl i (4 * S + 2) hfi (by omega) (by omega)
      refine ⟨τ4, _, WExec.ifrF hg (WExec.ifrT (by rw [hl1]; omega) e4), by omega, ?_, w4, f4⟩
      rw [if_pos hiq]; exact o4
    · have hl0 : τ3.val (regH .lt) = 0 := by rw [hlt, hfi, if_neg hiq]
      obtain ⟨τ4, e4, o4, w4, f4⟩ := inputNode_constFalse cap τ3 out hout hcl (by omega)
      refine ⟨τ4, _, WExec.ifrF hg (WExec.ifrF hl0 e4), by omega, ?_, w4, f4⟩
      rw [if_neg hiq]; exact o4
  · have hge := hlong hg
    obtain ⟨τ4, e4, o4, w4, f4⟩ := inputNode_constFalse cap τ3 out hout hcl (by omega)
    refine ⟨τ4, _, WExec.ifrT hg e4, by omega, ?_, w4, f4⟩
    rw [if_neg (by omega)]; exact o4

/-- **`C`'s `input i`** (`sec:gadget-machine`; `Outer.substStepG` / `inputMapD`): `input i` if `i < q`, else `const false`;
the index is read with the guard `hc q + 1` (`fieldToG`), and an index longer than the guard is `≥ q`. -/
theorem nC1b_spec (cap : ℕ) (σ : WState 4 nrH) (hz : CBZ σ) (hg : σ.val (regH .g) = 0) (preW restW : List Bool)
    (i : ℕ) (hW : σ.st sW = preW ++ natWord i ++ natWord 0 ++ restW) (hWh : σ.sh sW = preW.length)
    (hbq : σ.val (regH .bq) = hc (σ.val (regH .q)) + 1) (S : ℕ) (hq : σ.val (regH .q) ≤ S) (hiS : natBitLength i ≤ S)
    (out : List Bool) (hout : OutOK σ out) (hcl : WClean σ)
    (hcap : σ.val (regH .cdW) + 2 * out.length + 2000 * (S + 2) ^ 2 ≤ cap) :
    ∃ τ, WExec cap nC1b σ τ (cIter S) ∧
      τ.sh sW = preW.length + (natWord i).length + (natWord 0).length ∧
      τ.val (regH .cdW) = σ.val (regH .cdW) + (natWord i).length + (natWord 0).length ∧
      OutOK τ (out ++ (if i < σ.val (regH .q) then natWord 1 ++ natWord i ++ natWord 0
        else natWord 0 ++ natWord 0 ++ natWord 0)) ∧
      WClean τ ∧ CBZ τ ∧ τ.val (regH .g) = 0 ∧ Fr σ τ [sW, sO] [.cdW, .w 7] ∧ τ.st sW = σ.st sW := by
  have hsq : S + 2 ≤ (S + 2) ^ 2 := Nat.le_self_pow (by norm_num) _
  obtain ⟨τ1, τ2, τ3, n1, n2, n3, e1, e2, e3, hn, s3, c3, t3, fr3, hf1, hg1, hlong, hshort, hlt⟩ :=
    inputNode_front cap σ hz hg preW restW i hW hWh hbq S hq hiS (by omega)
  have hout3 : OutOK τ3 out := by
    obtain ⟨o1, o2, o3⟩ := hout
    exact ⟨by rw [(fr3.s (by simp)).1, o1], by rw [(fr3.s (by simp)).2, o2], by rw [fr3.v (by simp), o3]⟩
  have hcl3 : WClean τ3 := ⟨fun j hj => by rw [fr3.v (by simp)]; exact hcl.1 j hj, by rw [fr3.v (by simp)]; exact hcl.2⟩
  obtain ⟨τ4, n4, e4, hn4, o4, w4, f4⟩ := inputNode_emit cap τ3 i S out hout3 hcl3 (σ.val (regH .q)) hf1 hlong hshort
    hlt (by omega)
  -- 5. clear the scratch
  have l4 : τ4.val (regH .lt) ≤ 1 := by rw [f4.v (by simp), hlt]; split_ifs <;> omega
  obtain ⟨τ5, e5, v5, f5⟩ := clr_fr cap .f1 τ4 (by rw [f4.v (by simp)]; omega)
  obtain ⟨τ6, e6, v6, f6⟩ := clr_fr cap .g τ5 (by rw [f5.v (by simp), f4.v (by simp)]; omega)
  obtain ⟨τ7, e7, v7, f7⟩ := clr_fr cap .lt τ6 (by rw [f6.v (by simp), f5.v (by simp)]; omega)
  have hf := (((fr3.trans' f4).trans' f5).trans' f6).trans' f7
  refine ⟨τ7, WExec.mono (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 (WExec.seq e5 (WExec.seq e6 e7))))))
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the cost
    have hf4 : τ4.val (regH .f1) ≤ 4 * S + 2 := by rw [f4.v (by simp)]; exact hf1
    have hg5 : τ5.val (regH .g) ≤ 1 := by rw [f5.v (by simp), f4.v (by simp)]; exact hg1
    have hl6 : τ6.val (regH .lt) ≤ 1 := by rw [f6.v (by simp), f5.v (by simp)]; exact l4
    have h1 := cIter_sub S
    omega
  · rw [(f7.s (by simp)).2, (f6.s (by simp)).2, (f5.s (by simp)).2, (f4.s (by simp)).2, s3]
  · rw [f7.v (by simp), f6.v (by simp), f5.v (by simp), f4.v (by simp), c3]
  · obtain ⟨o1, o2, o3'⟩ := o4
    exact ⟨by rw [(f7.s (by simp)).1, (f6.s (by simp)).1, (f5.s (by simp)).1, o1],
      by rw [(f7.s (by simp)).2, (f6.s (by simp)).2, (f5.s (by simp)).2, o2],
      by rw [f7.v (by simp), f6.v (by simp), f5.v (by simp), o3']⟩
  · exact ⟨fun j hj => by rw [f7.v (by simp), f6.v (by simp), f5.v (by simp)]; exact w4.1 j hj,
      by rw [f7.v (by simp), f6.v (by simp), f5.v (by simp)]; exact w4.2⟩
  · refine hz.of_fr hf ?_
    intro u hu
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [zl, v7, f7.v (show HReg.f1 ∉ [HReg.lt] by simp), f6.v (show HReg.f1 ∉ [HReg.g] by simp), v5]
  · rw [f7.v (by simp), v6]
  · refine (hf.mono (by intro x hx; simp at hx ⊢; omega) (fun u hu => hu)).tighten _ ?_
    intro u hu hu'
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hu hu'
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp_all [hz.z _ (show HReg.f1 ∈ zl by simp [zl]), hz.z _ (show HReg.lt ∈ zl by simp [zl]),
        f7.v (show HReg.f1 ∉ [HReg.lt] by simp), f6.v (show HReg.f1 ∉ [HReg.g] by simp),
        f7.v (show HReg.g ∉ [HReg.lt] by simp)]
  · rw [(f7.s (by simp)).1, (f6.s (by simp)).1, (f5.s (by simp)).1, (f4.s (by simp)).1, t3]

/-! ## The end of the emission -/

theorem writeTapeBit_at_length : ∀ (l : List Bool) (b : Bool), writeTapeBit l l.length b = l ++ [b]
  | [], b => by simp [writeTapeBit]
  | x :: l, b => by simp [writeTapeBit, writeTapeBit_at_length l b]

theorem native_constFalse {n : ℕ} :
    PCPPRequestNodeSchema.native (BooleanNode.const false : BooleanNode n) = natWord 0 ++ natWord 0 ++ natWord 0 := rfl

theorem native_constFalse_length {n : ℕ} : (PCPPRequestNodeSchema.native (BooleanNode.const false : BooleanNode n)).length = 9 := by
  rw [native_constFalse]; simp [natWord_length, natBitLength]

/-- **The padding loop** (`sec:gadget-machine`: `D_B` is size-padded to its arity with `const false` nodes): `x`
iterations of
`dec x; const false`. -/
theorem padLoop_run (cap : ℕ) {n : ℕ} : ∀ (m : ℕ) (τ : WState 4 nrH) (o : List Bool), τ.val (regH .x) = m →
    OutOK τ o → WClean τ → 2 * o.length + 18 * m + 100 ≤ cap → m ≤ cap →
    ∃ ρ, WExec cap (.whr (regH .x) (.seq (.dec (regH .x)) emit0)) τ ρ (m * (CheckedPCPP.NodeEmit.nodeCost 1 + 4) + 1) ∧
      OutOK ρ (o ++ (List.replicate m (BooleanNode.const false : BooleanNode n)).flatMap PCPPRequestNodeSchema.native) ∧
      WClean ρ ∧ Fr τ ρ [sO] [.w 7, .x]
  | 0, τ, o, hx, ho, hw, _, _ => ⟨τ, by simpa using (WExec.whrF hx : WExec cap (.whr (regH .x) (.seq (.dec (regH .x)) emit0)) τ τ 1),
      by simpa using ho, hw, fr_refl τ _ _⟩
  | m + 1, τ, o, hx, ho, hw, hcap, hm => by
    have ed := WExec.dec (cap := cap) (regH .x) τ (by omega)
    rw [hx] at ed
    simp only [Nat.add_sub_cancel] at ed
    have hxw : ∀ j : Fin 8, HReg.x ≠ .w j := fun j => by simp
    have ho' : OutOK (τ.setv (regH .x) m) o := by
      obtain ⟨o1, o2, o3⟩ := ho
      exact ⟨by simpa using o1, by simpa using o2, by simp [Function.update_apply, o3]⟩
    have hw' : WClean (τ.setv (regH .x) m) :=
      ⟨fun j hj => by simp [Function.update_apply, hw.1 j hj], by simp [Function.update_apply, hw.2]⟩
    obtain ⟨τ2, e2, o2, w2, f2⟩ := emit_fr cap (τ.setv (regH .x) m) ([], 0) ([], 0) ([], 0)
      (BooleanNode.const false : BooleanNode n) o ho' hw' ⟨tok_nil, tok_nil, tok_nil⟩ (by simp)
      ⟨by rw [fv_nil]; rfl, by rw [fv_nil]; rfl, by rw [fv_nil]; rfl⟩ 1
      (fun j => by fin_cases j <;> simp [PCPPRequestNodeSchema.fields]) (by rw [native_constFalse_length]; omega)
    have hx2 : τ2.val (regH .x) = m := by rw [f2.v (by simp)]; simp
    obtain ⟨ρ, eρ, oρ, wρ, fρ⟩ := padLoop_run cap m τ2 (o ++ PCPPRequestNodeSchema.native
      (BooleanNode.const false : BooleanNode n)) hx2 o2 w2 (by rw [List.length_append, native_constFalse_length]; omega)
      (by omega)
    refine ⟨ρ, WExec.mono (WExec.whrT (by rw [hx]; omega) (WExec.seq ed e2) eρ) (by ring_nf; omega), ?_, wρ, ?_⟩
    · rw [List.replicate_succ, List.flatMap_cons, ← List.append_assoc]; exact oρ
    · have h1 : Fr τ (τ.setv (regH .x) m) [] [.x] := fr_setv τ .x m
      exact ((h1.trans' f2).trans' fρ).mono (by intro y hy; simp at hy ⊢; omega)
        (by intro u hu
            simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hu
            rcases hu with rfl | rfl | rfl | rfl <;> simp)

/-- **The end of the emission, head**: the image `p1` of `o_C`, the output gate `not p1` (`sec:gadget-machine`: "negating
the output"), `x := pd`. -/
theorem emissionEnd_head (cap : ℕ) {n : ℕ} (σ : WState 4 nrH) (hz : CBZ σ) (hx : σ.val (regH .x) = 0)
    (fl : List Bool) (hF : σ.st sF = fl) (hFh : σ.sh sF = 0) (S : ℕ) (hoC : σ.val (regH .oC) ≤ S)
    (hn1 : σ.val (regH .nB1) ≤ S) (hob : σ.val (regH .oB) ≤ S) (hpd : σ.val (regH .pd) ≤ S)
    (out : List Bool) (hout : OutOK σ out) (hcl : WClean σ)
    (hcap : 2 * out.length + 1000 * (S + 2) ^ 2 ≤ cap) :
    ∃ τ1 τ2 τ3 n1 n2 n3, WExec cap (pos .oC .p1) σ τ1 n1 ∧ WExec cap (emit ([], 2) ([regH .p1], 0) ([], 0)) τ1 τ2 n2 ∧
      WExec cap (add .pd .x) τ2 τ3 n3 ∧ n1 + n2 + n3 ≤ 1000 * ((S + 2) ^ 2 + 14) ^ 2 + 200 * (S + 2) ^ 2 ∧
      OutOK τ3 (out ++ PCPPRequestNodeSchema.native
        (BooleanNode.not (posF fl (σ.val (regH .oC)) (σ.val (regH .nB1)) (σ.val (regH .oB))) : BooleanNode n)) ∧
      WClean τ3 ∧ τ3.val (regH .x) = σ.val (regH .pd) ∧ Fr σ τ3 [sO] [.p1, .w 7, .x] := by
  have hsq : S + 2 ≤ (S + 2) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hpf := posF_le fl (σ.val (regH .oC)) (σ.val (regH .nB1)) (σ.val (regH .oB)) S hoC hn1 hob
  have hpc := posCost_le (σ.val (regH .oC)) (σ.val (regH .nB1)) (σ.val (regH .oB)) S hoC hn1 hob
  obtain ⟨τ1, e1, p1, f1⟩ := pos_fr cap .oC .p1 (by simp) (by simp) σ fl hF hFh (hz.z _ (by simp [zl]))
    (hz.z _ (by simp [zl])) (hz.z _ (by simp [zl])) (hz.z _ (by simp [zl]))
    (by have : σ.val (regH .oC) * σ.val (regH .nB1) ≤ S * S := Nat.mul_le_mul hoC hn1
        nlinarith)
  have hout1 : OutOK τ1 out := by
    obtain ⟨o1, o2, o3⟩ := hout
    exact ⟨by rw [(f1.s (by simp)).1, o1], by rw [(f1.s (by simp)).2, o2], by rw [f1.v (by simp), o3]⟩
  have hcl1 : WClean τ1 := ⟨fun j hj => by rw [f1.v (by simp)]; exact hcl.1 j hj, by rw [f1.v (by simp)]; exact hcl.2⟩
  have hV : ∀ j, PCPPRequestNodeSchema.fields (BooleanNode.not (posF fl (σ.val (regH .oC)) (σ.val (regH .nB1))
      (σ.val (regH .oB))) : BooleanNode n) j ≤ (S + 2) ^ 2 + 2 :=
    fun j => by fin_cases j <;> simp [PCPPRequestNodeSchema.fields] <;> omega
  have hnl := native_len_le (BooleanNode.not (posF fl (σ.val (regH .oC)) (σ.val (regH .nB1)) (σ.val (regH .oB))) :
    BooleanNode n) _ hV
  obtain ⟨τ2, e2, o2, w2, f2⟩ := emit_fr cap τ1 ([], 2) ([regH .p1], 0) ([], 0)
    (BooleanNode.not (posF fl (σ.val (regH .oC)) (σ.val (regH .nB1)) (σ.val (regH .oB))) : BooleanNode n) out
    hout1 hcl1 ⟨tok_nil, tok_list [.p1] 0 (by simp), tok_nil⟩ (by simp)
    ⟨by rw [fv_nil]; rfl, by rw [fv_one, p1]; rfl, by rw [fv_nil]; rfl⟩ _ hV (by omega)
  have g2 : ∀ u, u ∉ [HReg.p1, .w 7] → τ2.val (regH u) = σ.val (regH u) := fun u hu => by
    rw [f2.v (by simp at hu ⊢; exact hu.2), f1.v (by simp at hu ⊢; exact hu.1)]
  have ht2 : τ2.val (regH .t) = 0 := by rw [g2 _ (by simp)]; exact hz.z _ (by simp [zl])
  have hxp2 : τ2.val (regH .x) + τ2.val (regH .pd) ≤ cap := by rw [g2 _ (by simp), g2 _ (by simp)]; omega
  obtain ⟨τ3, e3, x3, f3⟩ := add_fr cap .pd .x (by simp) (by simp) (by simp) τ2 ht2 hxp2
  have nc := nodeCost_le ((S + 2) ^ 2 + 2) ((S + 2) ^ 2 + 2) le_rfl
  refine ⟨τ1, τ2, τ3, _, _, _, e1, e2, e3, ?_, ?_, ?_, ?_, ?_⟩
  · rw [g2 _ (by simp)]
    have e : (S + 2) ^ 2 + 2 + 12 = (S + 2) ^ 2 + 14 := by ring
    rw [e] at nc
    omega
  · obtain ⟨o1, o2', o3⟩ := o2
    exact ⟨by rw [(f3.s (by simp)).1, o1], by rw [(f3.s (by simp)).2, o2'], by rw [f3.v (by simp), o3]⟩
  · exact ⟨fun j hj => by rw [f3.v (by simp)]; exact w2.1 j hj, by rw [f3.v (by simp)]; exact w2.2⟩
  · rw [x3, g2 _ (by simp), g2 _ (by simp), hx]; simp
  · exact ((f1.trans' f2).trans' f3).mono (by intro y hy; simp at hy ⊢; omega)
      (by intro u hu
          simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hu
          rcases hu with rfl | rfl | rfl <;> simp)

/-- **The end of the emission** (`sec:gadget-machine`:
"Substituting `O_{B_pf}` for every oracle gate and negating the output
gives the outer verifier `D_B`"; `D_B` size-padded to its arity): the output gate `not (image of o_C)`, the padding
(`pd` nodes `const false`), the output index `sz`, the closing cell. -/
theorem emissionEnd_spec (cap : ℕ) {n : ℕ} (σ : WState 4 nrH) (hz : CBZ σ) (hx : σ.val (regH .x) = 0)
    (fl : List Bool) (hF : σ.st sF = fl) (hFh : σ.sh sF = 0) (S : ℕ) (hoC : σ.val (regH .oC) ≤ S)
    (hn1 : σ.val (regH .nB1) ≤ S) (hob : σ.val (regH .oB) ≤ S) (hpd : σ.val (regH .pd) ≤ S)
    (hsz : σ.val (regH .sz) ≤ (S + 2) ^ 2) (out : List Bool) (hout : OutOK σ out) (hcl : WClean σ)
    (hcap : 2 * out.length + 1000 * (S + 2) ^ 2 ≤ cap) :
    ∃ τ, WExec cap emissionEnd σ τ (2 * cIter S) ∧
      τ.st sO = marks (out ++ PCPPRequestNodeSchema.native
          (BooleanNode.not (posF fl (σ.val (regH .oC)) (σ.val (regH .nB1)) (σ.val (regH .oB))) : BooleanNode n) ++
        (List.replicate (σ.val (regH .pd)) (BooleanNode.const false : BooleanNode n)).flatMap
          PCPPRequestNodeSchema.native ++
        natWord (σ.val (regH .sz))) ++ [false] ∧
      τ.st sW = σ.st sW ∧ τ.st sD = σ.st sD := by
  have hsq : S + 2 ≤ (S + 2) ^ 2 := Nat.le_self_pow (by norm_num) _
  obtain ⟨τ1, τ2, τ3, n1, n2, n3, e1, e2, e3, hn, o3, w3, x3, f3⟩ :=
    emissionEnd_head cap (n := n) σ hz hx fl hF hFh S hoC hn1 hob hpd out hout hcl hcap
  set A := PCPPRequestNodeSchema.native
    (BooleanNode.not (posF fl (σ.val (regH .oC)) (σ.val (regH .nB1)) (σ.val (regH .oB))) : BooleanNode n) with hA
  have hAl : A.length ≤ 6 * ((S + 2) ^ 2 + 2) + 9 := by
    have hpf := posF_le fl (σ.val (regH .oC)) (σ.val (regH .nB1)) (σ.val (regH .oB)) S hoC hn1 hob
    exact native_len_le _ _ (fun j => by fin_cases j <;> simp [PCPPRequestNodeSchema.fields] <;> omega)
  -- the padding loop
  obtain ⟨τ4, e4, o4, w4, f4⟩ := padLoop_run cap (n := n) (σ.val (regH .pd)) τ3 (out ++ A) x3 o3 w3
    (by rw [List.length_append]; omega) (by omega)
  set B := (List.replicate (σ.val (regH .pd)) (BooleanNode.const false : BooleanNode n)).flatMap
    PCPPRequestNodeSchema.native with hB
  have hBl : B.length = 9 * σ.val (regH .pd) := by
    rw [hB, List.length_flatMap]
    simp [native_constFalse_length]
    ring
  -- the output index
  have hsz4 : τ4.val (regH .sz) = σ.val (regH .sz) := by rw [f4.v (by simp), f3.v (by simp)]
  have e5 := fieldN_spec cap τ4 .sz (by simp) (out ++ A ++ B) o4 w4
    (by rw [hsz4]; have := nbl_le (σ.val (regH .sz))
        simp only [List.length_append]; omega)
  have o5 := appendO_outOK τ4 (out ++ A ++ B) (natWord (τ4.val (regH .sz))) o4
  set τ5 := appendO τ4 sO (regH (.w 7)) (marks (natWord (τ4.val (regH .sz)))) with hτ5
  -- the closing cell
  have e6 := WExec.wr (cap := cap) sO false τ5
  have e7 := WExec.fwd (cap := cap) sO (τ5.sets sO (writeTapeBit (τ5.st sO) (τ5.sh sO) false))
  have hfc : CheckedPCPP.NodeEmit.fieldCost (τ4.val (regH .sz)) 1 ≤ 200 * ((S + 2) ^ 2 + 12) ^ 2 := by
    rw [hsz4]; unfold CheckedPCPP.NodeEmit.fieldCost
    have := nbl_le (σ.val (regH .sz))
    have h1 : (natBitLength (σ.val (regH .sz)) + 10) * (100 * σ.val (regH .sz) + 200) ≤
        ((S + 2) ^ 2 + 11) * (100 * (S + 2) ^ 2 + 200) := Nat.mul_le_mul (by omega) (by omega)
    nlinarith
  refine ⟨_, WExec.mono (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 (WExec.seq e5
    (WExec.seq e6 e7)))))) ?_, ?_, ?_, ?_⟩
  · -- the cost
    have hnc1 : CheckedPCPP.NodeEmit.nodeCost 1 ≤ 20000 := by
      unfold CheckedPCPP.NodeEmit.nodeCost CheckedPCPP.NodeEmit.fieldCost; simp [natBitLength]
    have hloop : σ.val (regH .pd) * (CheckedPCPP.NodeEmit.nodeCost 1 + 4) ≤ S * 20004 :=
      Nat.mul_le_mul hpd (by omega)
    have hX4 : (S + 2) ^ 4 = (S + 2) ^ 2 * (S + 2) ^ 2 := by ring
    have h4 : 4 ≤ (S + 2) ^ 2 := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ (S + 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    unfold cIter
    rw [hX4]
    generalize (S + 2) ^ 2 = X at *
    have hXX : 4 * X ≤ X * X := Nat.mul_le_mul_right X h4
    have h14 : (X + 14) ^ 2 ≤ 25 * (X * X) := by nlinarith
    have h12 : (X + 12) ^ 2 ≤ 25 * (X * X) := by nlinarith
    omega
  · simp only [WState.seth_st, WState.sets_st, Function.update_self]
    rw [o5.1, o5.2.1, ← marks_length' (out ++ A ++ B ++ natWord (τ4.val (regH .sz))), writeTapeBit_at_length, hsz4]
  · simp only [WState.seth_st, WState.sets_st, Function.update_of_ne (show sW ≠ sO by decide), hτ5]
    rw [(fr_appendO τ4 _).s (by simp) |>.1, (f4.s (by simp)).1, (f3.s (by simp)).1]
  · simp only [WState.seth_st, WState.sets_st, Function.update_of_ne (show sD ≠ sO by decide), hτ5]
    rw [(fr_appendO τ4 _).s (by simp) |>.1, (f4.s (by simp)).1, (f3.s (by simp)).1]

end NearCubicGates.Close.Succinct.SubstMachine
