import Proof.Gates.Succinct.SubstitutionOracle

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

/-- **`C`'s `const b`** (`sec:gadget-machine`; `Outer.substStepG`). -/
theorem nC0b_spec (cap : ℕ) (σ : WState 4 nrH) (hz : CBZ σ) (preW restW : List Bool) (bb : Bool)
    (hD : σ.st sW = preW ++ natWord bb.toNat ++ natWord 0 ++ restW) (hDh : σ.sh sW = preW.length)
    (out : List Bool) (hout : OutOK σ out) (hcl : WClean σ) {n : ℕ}
    (hcap : σ.val (regH .cdW) + 2 * out.length + 1000 ≤ cap) :
    ∃ τ, WExec cap nC0b σ τ 200000 ∧ τ.sh sW = preW.length + (natWord bb.toNat).length + (natWord 0).length ∧
      τ.val (regH .cdW) = σ.val (regH .cdW) + (natWord bb.toNat).length + (natWord 0).length ∧
      OutOK τ (out ++ PCPPRequestNodeSchema.native (BooleanNode.const bb : BooleanNode n)) ∧ WClean τ ∧ CBZ τ ∧
      Fr σ τ [sW, sO] [.cdW, .w 7] ∧ τ.st sW = σ.st sW := by
  have hb1 : bb.toNat ≤ 1 := by cases bb <;> simp
  have hnb := natWord_length bb.toNat
  have hnb1 := nbl_le bb.toNat
  obtain ⟨τ1, e1, s1, c1, v1, f1, t1⟩ := rd_fr cap sW .cdW .f1 (by simp) (by simp) (by simp) (by simp) (by simp)
    (by simp) (by simp) σ preW (natWord 0 ++ restW) bb.toNat (by rw [hD]; simp [List.append_assoc]) hDh hz.f
    (hz.z _ (by simp [zl])) (hz.z _ (by simp [zl])) (hz.z _ (by simp [zl])) (by omega)
  obtain ⟨τ2, e2, s2, c2, f2, t2⟩ := sk1_fr cap sW .cdW (by simp) (by simp) (by simp) τ1 (preW ++ natWord bb.toNat)
    restW 0 (by rw [t1, hD]) (by rw [s1]; simp) (fun r => by rw [f1.v (by simp)]; exact hz.f r)
    (by rw [f1.v (by simp)]; exact hz.z _ (by simp [zl])) (by rw [f1.v (by simp)]; exact hz.z _ (by simp [zl]))
    (by rw [c1]; have : natBitLength 0 = 1 := by simp [natBitLength]
        omega)
  have hout2 : OutOK τ2 out := by
    obtain ⟨o1, o2, o3⟩ := hout
    refine ⟨?_, ?_, ?_⟩
    · rw [(f2.s (by simp)).1, (f1.s (by simp)).1, o1]
    · rw [(f2.s (by simp)).2, (f1.s (by simp)).2, o2]
    · rw [f2.v (by simp), f1.v (by simp), o3]
  have hcl2 : WClean τ2 := ⟨fun i hi => by rw [f2.v (by simp), f1.v (by simp)]; exact hcl.1 i hi,
    by rw [f2.v (by simp), f1.v (by simp)]; exact hcl.2⟩
  have hv2 : τ2.val (regH .f1) = bb.toNat := by rw [f2.v (by simp), v1]
  obtain ⟨τ3, e3, o3, w3, f3⟩ := emit_fr cap τ2 ([], 0) ([regH .f1], 0) ([], 0) (BooleanNode.const bb : BooleanNode n) out
    hout2 hcl2 ⟨tok_nil, tok_list [.f1] 0 (by simp), tok_nil⟩ (by simp)
    ⟨by rw [fv_nil]; rfl, by rw [fv_one, hv2]; rfl, by rw [fv_nil]; rfl⟩ 1
    (fun i => by fin_cases i <;> simp [PCPPRequestNodeSchema.fields] <;> omega)
    (by have : (PCPPRequestNodeSchema.native (BooleanNode.const bb : BooleanNode n)).length ≤ 9 := by
          cases bb <;> simp [PCPPRequestNodeSchema.native, PCPPRequestNodeSchema.fields, natBitLength] <;> decide
        omega)
  obtain ⟨τ4, e4, v4, f4⟩ := clr_fr cap .f1 τ3 (by rw [f3.v (by simp), hv2]; omega)
  refine ⟨τ4, WExec.mono (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 e4))) ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [f3.v (by simp), hv2]
    have := Nat.le_of_lt_succ (show readCost bb.toNat < 100000 by unfold readCost; nlinarith)
    have : skipCost 0 = 4000 := by simp [skipCost, natBitLength]
    have : CheckedPCPP.NodeEmit.nodeCost 1 ≤ 20000 := by
      unfold CheckedPCPP.NodeEmit.nodeCost CheckedPCPP.NodeEmit.fieldCost; simp [natBitLength]
    omega
  · rw [(f4.s (by simp)).2, (f3.s (by simp)).2, s2]; simp only [List.length_append]
  · rw [f4.v (by simp), f3.v (by simp), c2, c1]
  · obtain ⟨o1, o2, o3'⟩ := o3
    exact ⟨by rw [(f4.s (by simp)).1, o1], by rw [(f4.s (by simp)).2, o2], by rw [f4.v (by simp), o3']⟩
  · exact ⟨fun i hi => by rw [f4.v (by simp)]; exact w3.1 i hi, by rw [f4.v (by simp)]; exact w3.2⟩
  · have hf := ((f1.trans' f2).trans' f3).trans' f4
    refine hz.of_fr hf ?_
    intro u hu; simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl <;> simp [zl, v4]
  · have hf := ((f1.trans' f2).trans' f3).trans' f4
    refine (hf.mono (by intro x hx; simp at hx ⊢; omega) (fun u hu => hu)).tighten _ ?_
    · intro u hu hu'
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hu hu'
      rcases hu with rfl | rfl | rfl | rfl | rfl <;> simp_all [hz.z _ (show HReg.f1 ∈ zl by simp [zl])]
  · rw [(f4.s (by simp)).1, (f3.s (by simp)).1, t2, t1]

theorem node_cost (S c : ℕ) (hc : c ≤ S) :
    readCost c + 4000 + 100 * (S + 2) ^ 2 + CheckedPCPP.NodeEmit.nodeCost ((S + 2) ^ 2 + 2) + 3 * c +
      3 * (S + 2) ^ 2 + 100 ≤ cIter S ∧
    readCost c + readCost c + 100 * (S + 2) ^ 2 + 100 * (S + 2) ^ 2 +
      CheckedPCPP.NodeEmit.nodeCost ((S + 2) ^ 2 + 4) + 6 * c + 6 * (S + 2) ^ 2 + 100 ≤ cIter S := by
  have hsq : S + 2 ≤ (S + 2) ^ 2 := Nat.le_self_pow (by norm_num) _
  have h4' : 4 ≤ (S + 2) ^ 2 := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ (S + 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have r1 := readCost_le c S hc
  have n1 := nodeCost_le ((S + 2) ^ 2 + 2) ((S + 2) ^ 2 + 4) (by omega)
  have n2 := nodeCost_le ((S + 2) ^ 2 + 4) ((S + 2) ^ 2 + 4) le_rfl
  have h4 : (S + 2) ^ 4 = (S + 2) ^ 2 * (S + 2) ^ 2 := by ring
  unfold cIter
  rw [h4]
  generalize (S + 2) ^ 2 = X at *
  have : 1000 * (X + 4 + 12) ^ 2 = 1000 * (X * X) + 32000 * X + 256000 := by ring
  have hXX : 4 * X ≤ X * X := Nat.mul_le_mul_right _ h4'
  constructor <;> nlinarith

theorem nC2_cost (S c pc pf : ℕ) (hc : c ≤ S) (hp : pc ≤ 100 * (S + 2) ^ 2) (hpf : pf ≤ (S + 2) ^ 2) :
    readCost c + 1 + (skipCost 0 + 1 + (pc + 1 + (CheckedPCPP.NodeEmit.nodeCost ((S + 2) ^ 2 + 2) + 1 +
      (3 * c + 1 + 1 + (3 * pf + 1))))) ≤ cIter S := by
  have h1 := (node_cost S c hc).1
  have h2 : skipCost 0 = 4000 := by simp [skipCost, natBitLength]
  have hsq : S + 2 ≤ (S + 2) ^ 2 := Nat.le_self_pow (by norm_num) _
  have h4 := cIter_sub S
  rw [h2]
  generalize CheckedPCPP.NodeEmit.nodeCost ((S + 2) ^ 2 + 2) = NC at *
  generalize readCost c = R at *
  generalize cIter S = CI at *
  generalize (S + 2) ^ 2 = X at *
  omega

/-- **`C`'s `not c`** (`sec:gadget-machine`; `Outer.substStepG`: `not (ref c)`). -/
theorem nC2b_spec (cap : ℕ) (σ : WState 4 nrH) (hz : CBZ σ) (preW restW : List Bool) (c : ℕ)
    (hW : σ.st sW = preW ++ natWord c ++ natWord 0 ++ restW) (hWh : σ.sh sW = preW.length)
    (fl : List Bool) (hF : σ.st sF = fl) (hFh : σ.sh sF = 0) (S : ℕ) (hcS : c ≤ S)
    (hn1 : σ.val (regH .nB1) ≤ S) (hob : σ.val (regH .oB) ≤ S)
    (out : List Bool) (hout : OutOK σ out) (hcl : WClean σ) {n : ℕ}
    (hcap : σ.val (regH .cdW) + 2 * out.length + 2000 * (S + 2) ^ 2 ≤ cap) :
    ∃ τ, WExec cap nC2b σ τ (cIter S) ∧
      τ.sh sW = preW.length + (natWord c).length + (natWord 0).length ∧
      τ.val (regH .cdW) = σ.val (regH .cdW) + (natWord c).length + (natWord 0).length ∧
      OutOK τ (out ++ PCPPRequestNodeSchema.native
        (BooleanNode.not (posF fl c (σ.val (regH .nB1)) (σ.val (regH .oB))) : BooleanNode n)) ∧
      WClean τ ∧ CBZ τ ∧ Fr σ τ [sW, sO] [.cdW, .w 7] ∧ τ.st sW = σ.st sW := by
  have hnb := natWord_length c
  have hnb1 := nbl_le c
  have hsq : S + 2 ≤ (S + 2) ^ 2 := Nat.le_self_pow (by norm_num) _
  obtain ⟨τ1, e1, s1, c1, v1, f1, t1⟩ := rd_fr cap sW .cdW .f1 (by simp) (by simp) (by simp) (by simp) (by simp)
    (by simp) (by simp) σ preW (natWord 0 ++ restW) c (by rw [hW]; simp [List.append_assoc]) hWh hz.f
    (hz.z _ (by simp [zl])) (hz.z _ (by simp [zl])) (hz.z _ (by simp [zl])) (by omega)
  obtain ⟨τ2, e2, s2, c2, f2, t2⟩ := sk1_fr cap sW .cdW (by simp) (by simp) (by simp) τ1 (preW ++ natWord c)
    restW 0 (by rw [t1, hW]) (by rw [s1]; simp) (fun r => by rw [f1.v (by simp)]; exact hz.f r)
    (by rw [f1.v (by simp)]; exact hz.z _ (by simp [zl])) (by rw [f1.v (by simp)]; exact hz.z _ (by simp [zl]))
    (by rw [c1]; have : natBitLength 0 = 1 := by simp [natBitLength]
        omega)
  have g2 : ∀ u, u ∉ [HReg.cdW, .f1] → τ2.val (regH u) = σ.val (regH u) := fun u hu => by
    rw [f2.v (by simp at hu ⊢; exact hu.1), f1.v hu]
  have v2 : τ2.val (regH .f1) = c := by rw [f2.v (by simp), v1]
  have hpf := posF_le fl c (σ.val (regH .nB1)) (σ.val (regH .oB)) S hcS hn1 hob
  obtain ⟨τ3, e3, p3, f3⟩ := pos_fr cap .f1 .p1 (by simp) (by simp) τ2 fl
    (by rw [(f2.s (by simp)).1, (f1.s (by simp)).1, hF]) (by rw [(f2.s (by simp)).2, (f1.s (by simp)).2, hFh])
    (by rw [g2 _ (by simp)]; exact hz.z _ (by simp [zl])) (by rw [g2 _ (by simp)]; exact hz.z _ (by simp [zl]))
    (by rw [g2 _ (by simp)]; exact hz.z _ (by simp [zl])) (by rw [g2 _ (by simp)]; exact hz.z _ (by simp [zl]))
    (by rw [v2, g2 _ (by simp), g2 _ (by simp)]
        have : c * σ.val (regH .nB1) ≤ S * S := Nat.mul_le_mul hcS hn1
        nlinarith)
  rw [v2, g2 _ (by simp), g2 _ (by simp)] at p3 e3
  have g3 : ∀ u, u ∉ [HReg.cdW, .f1, .p1] → τ3.val (regH u) = σ.val (regH u) := fun u hu => by
    rw [f3.v (by simp at hu ⊢; exact hu.2.2), g2 u (by simp at hu ⊢; exact ⟨hu.1, hu.2.1⟩)]
  have hout3 : OutOK τ3 out := by
    obtain ⟨o1, o2, o3⟩ := hout
    refine ⟨?_, ?_, ?_⟩
    · rw [(f3.s (by simp)).1, (f2.s (by simp)).1, (f1.s (by simp)).1, o1]
    · rw [(f3.s (by simp)).2, (f2.s (by simp)).2, (f1.s (by simp)).2, o2]
    · rw [g3 _ (by simp), o3]
  have hcl3 : WClean τ3 := ⟨fun i hi => by rw [g3 _ (by simp)]; exact hcl.1 i hi, by rw [g3 _ (by simp)]; exact hcl.2⟩
  obtain ⟨τ4, e4, o4, w4, f4⟩ := emit_fr cap τ3 ([], 2) ([regH .p1], 0) ([], 0)
    (BooleanNode.not (posF fl c (σ.val (regH .nB1)) (σ.val (regH .oB))) : BooleanNode n) out
    hout3 hcl3 ⟨tok_nil, tok_list [.p1] 0 (by simp), tok_nil⟩ (by simp)
    ⟨by rw [fv_nil]; rfl, by rw [fv_one, p3]; rfl, by rw [fv_nil]; rfl⟩ ((S + 2) ^ 2 + 2)
    (fun i => by fin_cases i <;> simp [PCPPRequestNodeSchema.fields] <;> omega)
    (by have := native_len_le (BooleanNode.not (posF fl c (σ.val (regH .nB1)) (σ.val (regH .oB))) : BooleanNode n)
          ((S + 2) ^ 2 + 2) (fun i => by fin_cases i <;> simp [PCPPRequestNodeSchema.fields] <;> omega)
        omega)
  obtain ⟨τ5, e5, v5, f5⟩ := clr_fr cap .f1 τ4 (by rw [f4.v (by simp), f3.v (by simp), v2]; omega)
  obtain ⟨τ6, e6, v6, f6⟩ := clr_fr cap .p1 τ5 (by rw [f5.v (by simp), f4.v (by simp), p3]; omega)
  refine ⟨τ6, WExec.mono (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 (WExec.seq e5 e6))))) ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [f4.v (by simp), f3.v (by simp), v2, f5.v (by simp), f4.v (by simp), p3]
    exact nC2_cost S c _ _ hcS (posCost_le c _ _ S hcS hn1 hob) hpf
  · rw [(f6.s (by simp)).2, (f5.s (by simp)).2, (f4.s (by simp)).2, (f3.s (by simp)).2, s2]
    simp only [List.length_append]
  · rw [f6.v (by simp), f5.v (by simp), f4.v (by simp), f3.v (by simp), c2, c1]
  · obtain ⟨o1, o2, o3'⟩ := o4
    exact ⟨by rw [(f6.s (by simp)).1, (f5.s (by simp)).1, o1], by rw [(f6.s (by simp)).2, (f5.s (by simp)).2, o2],
      by rw [f6.v (by simp), f5.v (by simp), o3']⟩
  · exact ⟨fun i hi => by rw [f6.v (by simp), f5.v (by simp)]; exact w4.1 i hi,
      by rw [f6.v (by simp), f5.v (by simp)]; exact w4.2⟩
  · have hf := ((((f1.trans' f2).trans' f3).trans' f4).trans' f5).trans' f6
    refine hz.of_fr hf ?_
    intro u hu; simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [zl, v6, f6.v (show HReg.f1 ∉ [HReg.p1] by simp), v5]
  · have hf := ((((f1.trans' f2).trans' f3).trans' f4).trans' f5).trans' f6
    refine (hf.mono (by intro x hx; simp at hx ⊢; omega) (fun u hu => hu)).tighten _ ?_
    · intro u hu hu'
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hu hu'
      rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp_all [hz.z _ (show HReg.f1 ∈ zl by simp [zl]), hz.z _ (show HReg.p1 ∈ zl by simp [zl]),
          f6.v (show HReg.f1 ∉ [HReg.p1] by simp)]
  · rw [(f6.s (by simp)).1, (f5.s (by simp)).1, (f4.s (by simp)).1, (f3.s (by simp)).1, t2, t1]

theorem nC34_cost (S l r pc1 pc2 pf1 pf2 : ℕ) (hl : l ≤ S) (hr : r ≤ S) (hp1 : pc1 ≤ 100 * (S + 2) ^ 2)
    (hp2 : pc2 ≤ 100 * (S + 2) ^ 2) (hf1 : pf1 ≤ (S + 2) ^ 2) (hf2 : pf2 ≤ (S + 2) ^ 2) :
    readCost l + 1 + (readCost r + 1 + (pc1 + 1 + (pc2 + 1 + (CheckedPCPP.NodeEmit.nodeCost ((S + 2) ^ 2 + 4) + 1 +
      (3 * l + 1 + 1 + (3 * r + 1 + 1 + (3 * pf1 + 1 + 1 + (3 * pf2 + 1)))))))) ≤ cIter S := by
  have h1 := (node_cost S l hl).2
  have r1 := readCost_le l S hl
  have r2 := readCost_le r S hr
  have hsq : S + 2 ≤ (S + 2) ^ 2 := Nat.le_self_pow (by norm_num) _
  have h4 := cIter_sub S
  have n2 := nodeCost_le ((S + 2) ^ 2 + 4) ((S + 2) ^ 2 + 4) le_rfl
  have hX4 : (S + 2) ^ 4 = (S + 2) ^ 2 * (S + 2) ^ 2 := by ring
  have hc : cIter S = 100000000 * ((S + 2) ^ 2 * (S + 2) ^ 2) := by unfold cIter; rw [hX4]
  have h4' : 4 ≤ (S + 2) ^ 2 := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ (S + 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  rw [hc]
  generalize CheckedPCPP.NodeEmit.nodeCost ((S + 2) ^ 2 + 4) = NC at *
  generalize readCost l = R1 at *
  generalize readCost r = R2 at *
  generalize (S + 2) ^ 2 = X at *
  have : 1000 * (X + 4 + 12) ^ 2 = 1000 * (X * X) + 32000 * X + 256000 := by ring
  have hXX : 4 * X ≤ X * X := Nat.mul_le_mul_right _ h4'
  nlinarith

/-- **`C`'s `and l r` / `or l r`** (`sec:gadget-machine`; `Outer.substStepG`: the gate on `ref l`, `ref r`). -/
theorem nC34b_spec (cap : ℕ) (tg : ℕ) {n : ℕ} (mk : ℕ → ℕ → BooleanNode n)
    (hmk : ∀ x y, PCPPRequestNodeSchema.fields (mk x y) 0 = tg ∧ PCPPRequestNodeSchema.fields (mk x y) 1 = x ∧
      PCPPRequestNodeSchema.fields (mk x y) 2 = y) (htg : tg ≤ 4)
    (σ : WState 4 nrH) (hz : CBZ σ) (hp2z : σ.val (regH .p2) = 0) (preW restW : List Bool) (l r : ℕ)
    (hW : σ.st sW = preW ++ natWord l ++ natWord r ++ restW) (hWh : σ.sh sW = preW.length)
    (fl : List Bool) (hF : σ.st sF = fl) (hFh : σ.sh sF = 0) (S : ℕ) (hlS : l ≤ S) (hrS : r ≤ S)
    (hn1 : σ.val (regH .nB1) ≤ S) (hob : σ.val (regH .oB) ≤ S)
    (out : List Bool) (hout : OutOK σ out) (hcl : WClean σ)
    (hcap : σ.val (regH .cdW) + 2 * out.length + 2000 * (S + 2) ^ 2 ≤ cap) :
    ∃ τ, WExec cap (nC34b tg) σ τ (cIter S) ∧
      τ.sh sW = preW.length + (natWord l).length + (natWord r).length ∧
      τ.val (regH .cdW) = σ.val (regH .cdW) + (natWord l).length + (natWord r).length ∧
      OutOK τ (out ++ PCPPRequestNodeSchema.native
        (mk (posF fl l (σ.val (regH .nB1)) (σ.val (regH .oB))) (posF fl r (σ.val (regH .nB1)) (σ.val (regH .oB))))) ∧
      WClean τ ∧ CBZ τ ∧ τ.val (regH .p2) = 0 ∧ Fr σ τ [sW, sO] [.cdW, .w 7] ∧ τ.st sW = σ.st sW := by
  have hnl := natWord_length l
  have hnr := natWord_length r
  have hbl := nbl_le l
  have hbr := nbl_le r
  have hsq : S + 2 ≤ (S + 2) ^ 2 := Nat.le_self_pow (by norm_num) _
  obtain ⟨τ1, e1, s1, c1, v1, f1, t1⟩ := rd_fr cap sW .cdW .f1 (by simp) (by simp) (by simp) (by simp) (by simp)
    (by simp) (by simp) σ preW (natWord r ++ restW) l (by rw [hW]; simp [List.append_assoc]) hWh hz.f
    (hz.z _ (by simp [zl])) (hz.z _ (by simp [zl])) (hz.z _ (by simp [zl])) (by omega)
  obtain ⟨τ2, e2, s2, c2, v2, f2, t2⟩ := rd_fr cap sW .cdW .f2 (by simp) (by simp) (by simp) (by simp) (by simp)
    (by simp) (by simp) τ1 (preW ++ natWord l) restW r (by rw [t1, hW]) (by rw [s1]; simp)
    (fun x => by rw [f1.v (by simp)]; exact hz.f x) (by rw [f1.v (by simp)]; exact hz.z _ (by simp [zl]))
    (by rw [f1.v (by simp)]; exact hz.z _ (by simp [zl])) (by rw [f1.v (by simp)]; exact hz.z _ (by simp [zl]))
    (by rw [c1]; omega)
  have g2 : ∀ u, u ∉ [HReg.cdW, .f1, .f2] → τ2.val (regH u) = σ.val (regH u) := fun u hu => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hu
    rw [f2.v (by simp [hu.1, hu.2.2]), f1.v (by simp [hu.1, hu.2.1])]
  have v1' : τ2.val (regH .f1) = l := by rw [f2.v (by simp), v1]
  have hF2 : τ2.st sF = fl ∧ τ2.sh sF = 0 := ⟨by rw [(f2.s (by simp)).1, (f1.s (by simp)).1, hF],
    by rw [(f2.s (by simp)).2, (f1.s (by simp)).2, hFh]⟩
  have hpf1 := posF_le fl l (σ.val (regH .nB1)) (σ.val (regH .oB)) S hlS hn1 hob
  have hpf2 := posF_le fl r (σ.val (regH .nB1)) (σ.val (regH .oB)) S hrS hn1 hob
  obtain ⟨τ3, e3, p3, f3⟩ := pos_fr cap .f1 .p1 (by simp) (by simp) τ2 fl hF2.1 hF2.2
    (by rw [g2 _ (by simp)]; exact hz.z _ (by simp [zl])) (by rw [g2 _ (by simp)]; exact hz.z _ (by simp [zl]))
    (by rw [g2 _ (by simp)]; exact hz.z _ (by simp [zl])) (by rw [g2 _ (by simp)]; exact hz.z _ (by simp [zl]))
    (by rw [v1', g2 _ (by simp), g2 _ (by simp)]
        have : l * σ.val (regH .nB1) ≤ S * S := Nat.mul_le_mul hlS hn1
        nlinarith)
  rw [v1', g2 _ (by simp), g2 _ (by simp)] at p3 e3
  have g3 : ∀ u, u ∉ [HReg.cdW, .f1, .f2, .p1] → τ3.val (regH u) = σ.val (regH u) := fun u hu => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hu
    rw [f3.v (by simp [hu.2.2.2]), g2 u (by simp [hu.1, hu.2.1, hu.2.2.1])]
  have v2' : τ3.val (regH .f2) = r := by rw [f3.v (by simp), v2]
  obtain ⟨τ4, e4, p4, f4⟩ := pos_fr cap .f2 .p2 (by simp) (by simp) τ3 fl
    (by rw [(f3.s (by simp)).1]; exact hF2.1) (by rw [(f3.s (by simp)).2]; exact hF2.2)
    (by rw [g3 _ (by simp)]; exact hp2z) (by rw [g3 _ (by simp)]; exact hz.z _ (by simp [zl]))
    (by rw [g3 _ (by simp)]; exact hz.z _ (by simp [zl])) (by rw [g3 _ (by simp)]; exact hz.z _ (by simp [zl]))
    (by rw [v2', g3 _ (by simp), g3 _ (by simp)]
        have : r * σ.val (regH .nB1) ≤ S * S := Nat.mul_le_mul hrS hn1
        nlinarith)
  rw [v2', g3 _ (by simp), g3 _ (by simp)] at p4 e4
  have g4 : ∀ u, u ∉ [HReg.cdW, .f1, .f2, .p1, .p2] → τ4.val (regH u) = σ.val (regH u) := fun u hu => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hu
    rw [f4.v (by simp [hu.2.2.2.2]), g3 u (by simp [hu.1, hu.2.1, hu.2.2.1, hu.2.2.2.1])]
  have hout4 : OutOK τ4 out := by
    obtain ⟨o1, o2, o3⟩ := hout
    refine ⟨?_, ?_, ?_⟩
    · rw [(f4.s (by simp)).1, (f3.s (by simp)).1, (f2.s (by simp)).1, (f1.s (by simp)).1, o1]
    · rw [(f4.s (by simp)).2, (f3.s (by simp)).2, (f2.s (by simp)).2, (f1.s (by simp)).2, o2]
    · rw [g4 _ (by simp), o3]
  have hcl4 : WClean τ4 := ⟨fun i hi => by rw [g4 _ (by simp)]; exact hcl.1 i hi, by rw [g4 _ (by simp)]; exact hcl.2⟩
  have p3' : τ4.val (regH .p1) = posF fl l (σ.val (regH .nB1)) (σ.val (regH .oB)) := by rw [f4.v (by simp), p3]
  obtain ⟨τ5, e5, o5, w5, f5⟩ := emit_fr cap τ4 ([], tg) ([regH .p1], 0) ([regH .p2], 0)
    (mk (posF fl l (σ.val (regH .nB1)) (σ.val (regH .oB))) (posF fl r (σ.val (regH .nB1)) (σ.val (regH .oB)))) out
    hout4 hcl4 ⟨tok_nil, tok_list [.p1] 0 (by simp), tok_list [.p2] 0 (by simp)⟩ (by simp)
    ⟨by rw [fv_nil, (hmk _ _).1], by rw [fv_one, p3', (hmk _ _).2.1]; rfl, by rw [fv_one, p4, (hmk _ _).2.2]; rfl⟩
    ((S + 2) ^ 2 + 4) (fun i => by fin_cases i <;> simp [(hmk _ _).1, (hmk _ _).2.1, (hmk _ _).2.2] <;> omega)
    (by have := native_len_le (mk (posF fl l (σ.val (regH .nB1)) (σ.val (regH .oB)))
            (posF fl r (σ.val (regH .nB1)) (σ.val (regH .oB)))) ((S + 2) ^ 2 + 4)
          (fun i => by fin_cases i <;> simp [(hmk _ _).1, (hmk _ _).2.1, (hmk _ _).2.2] <;> omega)
        omega)
  obtain ⟨τ6, e6, z6, f6⟩ := clr_fr cap .f1 τ5 (by rw [f5.v (by simp), f4.v (by simp), f3.v (by simp), v1']; omega)
  obtain ⟨τ7, e7, z7, f7⟩ := clr_fr cap .f2 τ6 (by rw [f6.v (by simp), f5.v (by simp), f4.v (by simp), v2']; omega)
  obtain ⟨τ8, e8, z8, f8⟩ := clr_fr cap .p1 τ7 (by rw [f7.v (by simp), f6.v (by simp), f5.v (by simp), p3']; omega)
  obtain ⟨τ9, e9, z9, f9⟩ := clr_fr cap .p2 τ8
    (by rw [f8.v (by simp), f7.v (by simp), f6.v (by simp), f5.v (by simp), p4]; omega)
  refine ⟨τ9, WExec.mono (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 (WExec.seq e5 (WExec.seq e6
    (WExec.seq e7 (WExec.seq e8 e9)))))))) ?_, ?_, ?_, ?_, ?_, ?_, z9, ?_, ?_⟩
  · rw [f5.v (by simp), f4.v (by simp), f3.v (by simp), v1', f6.v (by simp), f5.v (by simp), f4.v (by simp), v2',
      f7.v (by simp), f6.v (by simp), f5.v (by simp), p3', f8.v (by simp), f7.v (by simp), f6.v (by simp),
      f5.v (by simp), p4]
    exact nC34_cost S l r _ _ _ _ hlS hrS (posCost_le l _ _ S hlS hn1 hob) (posCost_le r _ _ S hrS hn1 hob) hpf1 hpf2
  · rw [(f9.s (by simp)).2, (f8.s (by simp)).2, (f7.s (by simp)).2, (f6.s (by simp)).2, (f5.s (by simp)).2,
      (f4.s (by simp)).2, (f3.s (by simp)).2, s2]
    simp only [List.length_append]
  · rw [f9.v (by simp), f8.v (by simp), f7.v (by simp), f6.v (by simp), f5.v (by simp), f4.v (by simp),
      f3.v (by simp), c2, c1]
  · obtain ⟨o1, o2, o3'⟩ := o5
    exact ⟨by rw [(f9.s (by simp)).1, (f8.s (by simp)).1, (f7.s (by simp)).1, (f6.s (by simp)).1, o1],
      by rw [(f9.s (by simp)).2, (f8.s (by simp)).2, (f7.s (by simp)).2, (f6.s (by simp)).2, o2],
      by rw [f9.v (by simp), f8.v (by simp), f7.v (by simp), f6.v (by simp), o3']⟩
  · exact ⟨fun i hi => by rw [f9.v (by simp), f8.v (by simp), f7.v (by simp), f6.v (by simp)]; exact w5.1 i hi,
      by rw [f9.v (by simp), f8.v (by simp), f7.v (by simp), f6.v (by simp)]; exact w5.2⟩
  · have hf := (((((((f1.trans' f2).trans' f3).trans' f4).trans' f5).trans' f6).trans' f7).trans' f8).trans' f9
    refine hz.of_fr hf ?_
    intro u hu; simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [zl, z9, f9.v (show HReg.p1 ∉ [HReg.p2] by simp), z8, f9.v (show HReg.f2 ∉ [HReg.p2] by simp),
        f8.v (show HReg.f2 ∉ [HReg.p1] by simp), z7, f9.v (show HReg.f1 ∉ [HReg.p2] by simp),
        f8.v (show HReg.f1 ∉ [HReg.p1] by simp), f7.v (show HReg.f1 ∉ [HReg.f2] by simp), z6]
  · have hf := (((((((f1.trans' f2).trans' f3).trans' f4).trans' f5).trans' f6).trans' f7).trans' f8).trans' f9
    refine (hf.mono (by intro x hx; simp at hx ⊢; omega) (fun u hu => hu)).tighten _ ?_
    · intro u hu hu'
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hu hu'
      rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp_all [hz.z _ (show HReg.f1 ∈ zl by simp [zl]), hz.z _ (show HReg.p1 ∈ zl by simp [zl]),
          hz.z _ (show HReg.f2 ∈ zl by simp [zl]), f9.v (show HReg.p1 ∉ [HReg.p2] by simp),
          f9.v (show HReg.f2 ∉ [HReg.p2] by simp), f8.v (show HReg.f2 ∉ [HReg.p1] by simp),
          f9.v (show HReg.f1 ∉ [HReg.p2] by simp), f8.v (show HReg.f1 ∉ [HReg.p1] by simp),
          f7.v (show HReg.f1 ∉ [HReg.f2] by simp)]
  · rw [(f9.s (by simp)).1, (f8.s (by simp)).1, (f7.s (by simp)).1, (f6.s (by simp)).1, (f5.s (by simp)).1,
      (f4.s (by simp)).1, (f3.s (by simp)).1, t2, t1]

end NearCubicGates.Close.Succinct.SubstMachine
