import Proof.Gates.Succinct.SubstitutionFrame

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
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.Succinct
open RepairRepresentation (natWord)

theorem regH_surj (r : Fin nrH) : ∃ u, regH u = r := (Fintype.equivFin HReg).surjective r

theorem Fr.tighten {σ τ : WState 4 nrH} {S : List (Fin (4 + 1))} {R : List HReg} (h : Fr σ τ S R) (R' : List HReg)
    (hR : ∀ u ∈ R, u ∉ R' → τ.val (regH u) = σ.val (regH u)) : Fr σ τ S R' := by
  refine ⟨h.1, fun r hr => ?_, h.2.2⟩
  obtain ⟨u, rfl⟩ := (Fintype.equivFin HReg).surjective r
  have hu : u ∉ R' := fun m => hr (List.mem_map_of_mem m)
  by_cases hm : u ∈ R
  · exact hR u hm hu
  · exact h.v hm

theorem Fr.tightenS {σ τ : WState 4 nrH} {S : List (Fin (4 + 1))} {R : List HReg} (h : Fr σ τ S R)
    (S' : List (Fin (4 + 1))) (hS : ∀ x ∈ S, x ∉ S' → τ.st x = σ.st x ∧ τ.sh x = σ.sh x) : Fr σ τ S' R := by
  refine ⟨fun y hy => ?_, h.2.1, h.2.2⟩
  by_cases hm : y ∈ S
  · exact hS y hm hy
  · exact h.1 y hm

/-- **One node of `D_B`**, framed. -/
theorem emit_fr (cap : ℕ) (σ : WState 4 nrH) (a b c : CheckedPCPP.NodeEmit.Field nrH) {n : ℕ} (nd : BooleanNode n)
    (out : List Bool) (hout : OutOK σ out) (hcl : WClean σ) (hok : TOK a ∧ TOK b ∧ TOK c)
    (hlen : a.1.length ≤ 3 ∧ b.1.length ≤ 3 ∧ c.1.length ≤ 3)
    (hd : CheckedPCPP.NodeEmit.fieldVal σ a = PCPPRequestNodeSchema.fields nd 0 ∧
      CheckedPCPP.NodeEmit.fieldVal σ b = PCPPRequestNodeSchema.fields nd 1 ∧
      CheckedPCPP.NodeEmit.fieldVal σ c = PCPPRequestNodeSchema.fields nd 2)
    (V : ℕ) (hV : ∀ i, PCPPRequestNodeSchema.fields nd i ≤ V)
    (hcap : 2 * out.length + 2 * (PCPPRequestNodeSchema.native nd).length + 7 * V + 12 ≤ cap) :
    ∃ τ, WExec cap (emit a b c) σ τ (CheckedPCPP.NodeEmit.nodeCost V) ∧
      OutOK τ (out ++ PCPPRequestNodeSchema.native nd) ∧ WClean τ ∧ Fr σ τ [sO] [.w 7] :=
  ⟨_, emitN_spec cap σ a b c nd out hout hcl hok hlen hd V hV hcap, appendO_outOK σ out _ hout,
    appendO_wclean σ _ hcl, fr_appendO σ _⟩

theorem fv_nil (σ : WState 4 nrH) (k : ℕ) : CheckedPCPP.NodeEmit.fieldVal σ ([], k) = k := by
  simp [CheckedPCPP.NodeEmit.fieldVal, CheckedPCPP.NodeEmit.regSum]

theorem fv_one (σ : WState 4 nrH) (u : HReg) (k : ℕ) :
    CheckedPCPP.NodeEmit.fieldVal σ ([regH u], k) = σ.val (regH u) + k := by
  simp [CheckedPCPP.NodeEmit.fieldVal, CheckedPCPP.NodeEmit.regSum]

theorem fv_two (σ : WState 4 nrH) (u v : HReg) (k : ℕ) :
    CheckedPCPP.NodeEmit.fieldVal σ ([regH u, regH v], k) = σ.val (regH u) + σ.val (regH v) + k := by
  simp [CheckedPCPP.NodeEmit.fieldVal, CheckedPCPP.NodeEmit.regSum]

theorem tok_nil : TOK (([] : List (Fin nrH)), (0 : ℕ)) := fun x hx => by simp at hx

theorem tok_list (l : List HReg) (k : ℕ) (hl : ∀ u ∈ l, (∀ i, u ≠ .w i) ∧ u ≠ .wt) : TOK (l.map regH, k) := by
  intro x hx
  simp only [List.mem_map] at hx
  obtain ⟨u, hu, rfl⟩ := hx
  exact ⟨u, rfl, (hl u hu).1, (hl u hu).2⟩

theorem native_len_le {n : ℕ} (nd : BooleanNode n) (V : ℕ) (hV : ∀ i, PCPPRequestNodeSchema.fields nd i ≤ V) :
    (PCPPRequestNodeSchema.native nd).length ≤ 6 * V + 9 := by
  rw [CheckedPCPP.NodeEmit.native_len, natWord_length, natWord_length, natWord_length]
  have h0 := nbl_le (PCPPRequestNodeSchema.fields nd 0)
  have h1 := nbl_le (PCPPRequestNodeSchema.fields nd 1)
  have h2 := nbl_le (PCPPRequestNodeSchema.fields nd 2)
  have := hV 0; have := hV 1; have := hV 2
  omega

/-- The scratch registers of the copy (all `0` between nodes). -/
def zl : List HReg := [.pk, .pt, .z, .jk, .f1, .f2, .p1, .sk, .lt, .ga, .gb, .gz, .t, .sc, .sb, .cdA]

/-- Clean scratch. -/
structure CBZ (σ : WState 4 nrH) : Prop where
  f : ∀ r, σ.val (regH (.f r)) = 0
  z : ∀ u ∈ zl, σ.val (regH u) = 0

theorem CBZ.of_fr {σ τ : WState 4 nrH} {S : List (Fin (4 + 1))} {R : List HReg} (h : CBZ σ) (hf : Fr σ τ S R)
    (hR : ∀ u ∈ R, (∀ r, u ≠ .f r) ∧ (u ∈ zl → τ.val (regH u) = 0)) : CBZ τ := by
  refine ⟨fun r => ?_, fun u hu => ?_⟩
  · by_cases hm : HReg.f r ∈ R
    · exact absurd rfl ((hR _ hm).1 r)
    · rw [hf.v hm]; exact h.f r
  · by_cases hm : u ∈ R
    · exact (hR u hm).2 hu
    · rw [hf.v hm]; exact h.z u hu

/-- **`B`'s `const b`, copied** (paper §11.4; `Outer.copyNode`). -/
theorem cB0_spec (cap : ℕ) (σ : WState 4 nrH) (hz : CBZ σ) (preD restD : List Bool) (bb : Bool)
    (hD : σ.st sD = preD ++ natWord bb.toNat ++ natWord 0 ++ restD) (hDh : σ.sh sD = preD.length)
    (out : List Bool) (hout : OutOK σ out) (hcl : WClean σ) {n : ℕ}
    (hcap : σ.val (regH .cdB) + 2 * out.length + 1000 ≤ cap) :
    ∃ τ, WExec cap cB0 σ τ 200000 ∧ τ.sh sD = preD.length + (natWord bb.toNat).length + (natWord 0).length ∧
      τ.val (regH .cdB) = σ.val (regH .cdB) + (natWord bb.toNat).length + (natWord 0).length ∧
      OutOK τ (out ++ PCPPRequestNodeSchema.native (BooleanNode.const bb : BooleanNode n)) ∧ WClean τ ∧ CBZ τ ∧
      Fr σ τ [sD, sO] [.cdB, .w 7] ∧ τ.st sD = σ.st sD := by
  have hb1 : bb.toNat ≤ 1 := by cases bb <;> simp
  have hnb := natWord_length bb.toNat
  have hnb1 := nbl_le bb.toNat
  obtain ⟨τ1, e1, s1, c1, v1, f1, t1⟩ := rd_fr cap sD .cdB .f1 (by simp) (by simp) (by simp) (by simp) (by simp)
    (by simp) (by simp) σ preD (natWord 0 ++ restD) bb.toNat (by rw [hD]; simp [List.append_assoc]) hDh hz.f
    (hz.z _ (by simp [zl])) (hz.z _ (by simp [zl])) (hz.z _ (by simp [zl])) (by omega)
  obtain ⟨τ2, e2, s2, c2, f2, t2⟩ := sk1_fr cap sD .cdB (by simp) (by simp) (by simp) τ1 (preD ++ natWord bb.toNat)
    restD 0 (by rw [t1, hD]) (by rw [s1]; simp) (fun r => by rw [f1.v (by simp)]; exact hz.f r)
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

/-- **`B`'s `not c`, copied at offset `cur`** (paper §11.4; `Outer.copyNode`). -/
theorem cB2_spec (cap : ℕ) (σ : WState 4 nrH) (hz : CBZ σ) (preD restD : List Bool) (c : ℕ)
    (hD : σ.st sD = preD ++ natWord c ++ natWord 0 ++ restD) (hDh : σ.sh sD = preD.length)
    (out : List Bool) (hout : OutOK σ out) (hcl : WClean σ) {n : ℕ}
    (hcap : σ.val (regH .cdB) + 2 * out.length + 100 * (σ.val (regH .cur) + c + 10) ≤ cap) :
    ∃ τ, WExec cap cB2 σ τ (readCost c + CheckedPCPP.NodeEmit.nodeCost (σ.val (regH .cur) + c + 2) + 3 * c + 5000) ∧
      τ.sh sD = preD.length + (natWord c).length + (natWord 0).length ∧
      τ.val (regH .cdB) = σ.val (regH .cdB) + (natWord c).length + (natWord 0).length ∧
      OutOK τ (out ++ PCPPRequestNodeSchema.native (BooleanNode.not (σ.val (regH .cur) + c) : BooleanNode n)) ∧
      WClean τ ∧ CBZ τ ∧ Fr σ τ [sD, sO] [.cdB, .w 7] ∧ τ.st sD = σ.st sD := by
  have hnb := natWord_length c
  have hnb1 := nbl_le c
  obtain ⟨τ1, e1, s1, c1, v1, f1, t1⟩ := rd_fr cap sD .cdB .f1 (by simp) (by simp) (by simp) (by simp) (by simp)
    (by simp) (by simp) σ preD (natWord 0 ++ restD) c (by rw [hD]; simp [List.append_assoc]) hDh hz.f
    (hz.z _ (by simp [zl])) (hz.z _ (by simp [zl])) (hz.z _ (by simp [zl])) (by omega)
  obtain ⟨τ2, e2, s2, c2, f2, t2⟩ := sk1_fr cap sD .cdB (by simp) (by simp) (by simp) τ1 (preD ++ natWord c)
    restD 0 (by rw [t1, hD]) (by rw [s1]; simp) (fun r => by rw [f1.v (by simp)]; exact hz.f r)
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
  have hv2 : τ2.val (regH .f1) = c := by rw [f2.v (by simp), v1]
  have hc2 : τ2.val (regH .cur) = σ.val (regH .cur) := by rw [f2.v (by simp), f1.v (by simp)]
  have hnat := natWord_length (σ.val (regH .cur) + c)
  have hnat2 := nbl_le (σ.val (regH .cur) + c)
  obtain ⟨τ3, e3, o3, w3, f3⟩ := emit_fr cap τ2 ([], 2) ([regH .cur, regH .f1], 0) ([], 0)
    (BooleanNode.not (σ.val (regH .cur) + c) : BooleanNode n) out
    hout2 hcl2 ⟨tok_nil, tok_list [.cur, .f1] 0 (by simp), tok_nil⟩ (by simp)
    ⟨by rw [fv_nil]; rfl, by rw [fv_two, hv2, hc2]; rfl, by rw [fv_nil]; rfl⟩ (σ.val (regH .cur) + c + 2)
    (fun i => by fin_cases i <;> simp [PCPPRequestNodeSchema.fields] <;> omega)
    (by have := native_len_le (BooleanNode.not (σ.val (regH .cur) + c) : BooleanNode n) (σ.val (regH .cur) + c + 2)
          (fun i => by fin_cases i <;> simp [PCPPRequestNodeSchema.fields] <;> omega)
        omega)
  obtain ⟨τ4, e4, v4, f4⟩ := clr_fr cap .f1 τ3 (by rw [f3.v (by simp), hv2]; omega)
  refine ⟨τ4, WExec.mono (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 e4))) ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [f3.v (by simp), hv2]
    have : skipCost 0 = 4000 := by simp [skipCost, natBitLength]
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

/-- **`B`'s `and l r` / `or l r`, copied at offset `cur`** (paper §11.4; `Outer.copyNode`). -/
theorem cB34_spec (cap : ℕ) (tg : ℕ) {n : ℕ} (mk : ℕ → ℕ → BooleanNode n)
    (hmk : ∀ x y, PCPPRequestNodeSchema.fields (mk x y) 0 = tg ∧ PCPPRequestNodeSchema.fields (mk x y) 1 = x ∧
      PCPPRequestNodeSchema.fields (mk x y) 2 = y) (htg : tg ≤ 4)
    (σ : WState 4 nrH) (hz : CBZ σ) (preD restD : List Bool) (l r : ℕ)
    (hD : σ.st sD = preD ++ natWord l ++ natWord r ++ restD) (hDh : σ.sh sD = preD.length)
    (out : List Bool) (hout : OutOK σ out) (hcl : WClean σ)
    (hcap : σ.val (regH .cdB) + 2 * out.length + 100 * (σ.val (regH .cur) + l + r + 10) ≤ cap) :
    ∃ τ, WExec cap (cB34 tg) σ τ (readCost l + readCost r +
        CheckedPCPP.NodeEmit.nodeCost (σ.val (regH .cur) + l + r + 4) + 3 * (l + r) + 10) ∧
      τ.sh sD = preD.length + (natWord l).length + (natWord r).length ∧
      τ.val (regH .cdB) = σ.val (regH .cdB) + (natWord l).length + (natWord r).length ∧
      OutOK τ (out ++ PCPPRequestNodeSchema.native (mk (σ.val (regH .cur) + l) (σ.val (regH .cur) + r))) ∧
      WClean τ ∧ CBZ τ ∧ Fr σ τ [sD, sO] [.cdB, .w 7] ∧ τ.st sD = σ.st sD := by
  have hnl := natWord_length l
  have hnr := natWord_length r
  have hbl := nbl_le l
  have hbr := nbl_le r
  obtain ⟨τ1, e1, s1, c1, v1, f1, t1⟩ := rd_fr cap sD .cdB .f1 (by simp) (by simp) (by simp) (by simp) (by simp)
    (by simp) (by simp) σ preD (natWord r ++ restD) l (by rw [hD]; simp [List.append_assoc]) hDh hz.f
    (hz.z _ (by simp [zl])) (hz.z _ (by simp [zl])) (hz.z _ (by simp [zl])) (by omega)
  obtain ⟨τ2, e2, s2, c2, v2, f2, t2⟩ := rd_fr cap sD .cdB .f2 (by simp) (by simp) (by simp) (by simp) (by simp)
    (by simp) (by simp) τ1 (preD ++ natWord l) restD r (by rw [t1, hD]) (by rw [s1]; simp)
    (fun x => by rw [f1.v (by simp)]; exact hz.f x) (by rw [f1.v (by simp)]; exact hz.z _ (by simp [zl]))
    (by rw [f1.v (by simp)]; exact hz.z _ (by simp [zl])) (by rw [f1.v (by simp)]; exact hz.z _ (by simp [zl]))
    (by rw [c1]; omega)
  have hout2 : OutOK τ2 out := by
    obtain ⟨o1, o2, o3⟩ := hout
    refine ⟨?_, ?_, ?_⟩
    · rw [(f2.s (by simp)).1, (f1.s (by simp)).1, o1]
    · rw [(f2.s (by simp)).2, (f1.s (by simp)).2, o2]
    · rw [f2.v (by simp), f1.v (by simp), o3]
  have hcl2 : WClean τ2 := ⟨fun i hi => by rw [f2.v (by simp), f1.v (by simp)]; exact hcl.1 i hi,
    by rw [f2.v (by simp), f1.v (by simp)]; exact hcl.2⟩
  have hv2 : τ2.val (regH .f1) = l := by rw [f2.v (by simp), v1]
  have hc2 : τ2.val (regH .cur) = σ.val (regH .cur) := by rw [f2.v (by simp), f1.v (by simp)]
  obtain ⟨τ3, e3, o3, w3, f3⟩ := emit_fr cap τ2 ([], tg) ([regH .cur, regH .f1], 0) ([regH .cur, regH .f2], 0)
    (mk (σ.val (regH .cur) + l) (σ.val (regH .cur) + r)) out
    hout2 hcl2 ⟨tok_nil, tok_list [.cur, .f1] 0 (by simp), tok_list [.cur, .f2] 0 (by simp)⟩ (by simp)
    ⟨by rw [fv_nil, (hmk _ _).1], by rw [fv_two, hv2, hc2, (hmk _ _).2.1]; rfl,
      by rw [fv_two, v2, hc2, (hmk _ _).2.2]; rfl⟩ (σ.val (regH .cur) + l + r + 4)
    (fun i => by fin_cases i <;> simp [(hmk _ _).1, (hmk _ _).2.1, (hmk _ _).2.2] <;> omega)
    (by have := native_len_le (mk (σ.val (regH .cur) + l) (σ.val (regH .cur) + r)) (σ.val (regH .cur) + l + r + 4)
          (fun i => by fin_cases i <;> simp [(hmk _ _).1, (hmk _ _).2.1, (hmk _ _).2.2] <;> omega)
        omega)
  obtain ⟨τ4, e4, v4, f4⟩ := clr_fr cap .f1 τ3 (by rw [f3.v (by simp), hv2]; omega)
  obtain ⟨τ5, e5, v5, f5⟩ := clr_fr cap .f2 τ4 (by rw [f4.v (by simp), f3.v (by simp), v2]; omega)
  refine ⟨τ5, WExec.mono (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 e5)))) ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [f3.v (by simp), hv2, f4.v (by simp), f3.v (by simp), v2]
    omega
  · rw [(f5.s (by simp)).2, (f4.s (by simp)).2, (f3.s (by simp)).2, s2]; simp only [List.length_append]
  · rw [f5.v (by simp), f4.v (by simp), f3.v (by simp), c2, c1]
  · obtain ⟨o1, o2, o3'⟩ := o3
    exact ⟨by rw [(f5.s (by simp)).1, (f4.s (by simp)).1, o1], by rw [(f5.s (by simp)).2, (f4.s (by simp)).2, o2],
      by rw [f5.v (by simp), f4.v (by simp), o3']⟩
  · exact ⟨fun i hi => by rw [f5.v (by simp), f4.v (by simp)]; exact w3.1 i hi,
      by rw [f5.v (by simp), f4.v (by simp)]; exact w3.2⟩
  · have hf := (((f1.trans' f2).trans' f3).trans' f4).trans' f5
    refine hz.of_fr hf ?_
    intro u hu; simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [zl, v5, f5.v (show HReg.f1 ∉ [HReg.f2] by simp), v4]
  · have hf := (((f1.trans' f2).trans' f3).trans' f4).trans' f5
    refine (hf.mono (by intro x hx; simp at hx ⊢; omega) (fun u hu => hu)).tighten _ ?_
    · intro u hu hu'
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hu hu'
      rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp_all [hz.z _ (show HReg.f1 ∈ zl by simp [zl]), hz.z _ (show HReg.f2 ∈ zl by simp [zl]),
          f5.v (show HReg.f1 ∉ [HReg.f2] by simp)]
  · rw [(f5.s (by simp)).1, (f4.s (by simp)).1, (f3.s (by simp)).1, t2, t1]

theorem readCost_le (x S : ℕ) (h : x ≤ S) : readCost x ≤ 10000 * (S + 2) ^ 2 := by
  unfold readCost; exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)

theorem posCost_le (c n1 ob S : ℕ) (hc : c ≤ S) (hn : n1 ≤ S) (ho : ob ≤ S) : posCost c n1 ob ≤ 100 * (S + 2) ^ 2 := by
  unfold posCost
  have : c * (18 * n1 + 70) ≤ S * (18 * S + 70) := Nat.mul_le_mul hc (by omega)
  nlinarith

theorem posF_le (fl : List Bool) (c n1 ob S : ℕ) (hc : c ≤ S) (hn : n1 ≤ S) (ho : ob ≤ S) :
    posF fl c n1 ob ≤ (S + 2) ^ 2 := by
  unfold posF
  have h1 : (fl.take c).count true ≤ S := (List.count_le_length).trans (by simp; omega)
  have h2 : (fl.take c).count true * n1 ≤ S * S := Nat.mul_le_mul h1 hn
  split_ifs <;> nlinarith

theorem nodeCost_le (V W : ℕ) (h : V ≤ W) : CheckedPCPP.NodeEmit.nodeCost V ≤ 1000 * (W + 12) ^ 2 := by
  unfold CheckedPCPP.NodeEmit.nodeCost CheckedPCPP.NodeEmit.fieldCost
  have := nbl_le V
  have h2 : (natBitLength V + 10) * (100 * V + 200) ≤ (W + 11) * (100 * W + 200) :=
    Nat.mul_le_mul (by omega) (by omega)
  nlinarith

/-- The node a copied input `j` of `B` becomes: the image of the gate's argument `j`, or `false` past `ℓ`. -/
noncomputable def inNode {n : ℕ} (fl : List Bool) (args : List ℕ) (n1 ob j : ℕ) : BooleanNode n :=
  if h : j < args.length then .or (posF fl args[j] n1 ob) (posF fl args[j] n1 ob) else .const false

/-- The cost class of one copied node. -/
def cIter (S : ℕ) : ℕ := 100000000 * (S + 2) ^ 4

theorem cIter_sub (S : ℕ) : 200000 + 1000000 * (S + 2) ^ 2 ≤ cIter S := by
  unfold cIter
  have h1 : 4 ≤ (S + 2) ^ 2 := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ (S + 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have h2 : (S + 2) ^ 4 = (S + 2) ^ 2 * (S + 2) ^ 2 := by ring
  nlinarith

theorem wire_arith (S a b c d e f g h k : ℕ) (ha : a ≤ S) (hb : b ≤ S) (hc : c ≤ 10000 * (S + 2) ^ 2)
    (hd : d ≤ 100 * (S + 2) ^ 2) (he : e ≤ S) (hf : f ≤ 1000 * ((S + 2) ^ 2 + 4 + 12) ^ 2) (hg : g ≤ S)
    (hh : h ≤ (S + 2) ^ 2) (hk : k ≤ S) :
    18 * a + 3 + 1 + (b * (1000 * (S + 1 + 3) + 4) + 1 + 1 + (c + 1 + (d + 1 + (5 * (e + k) + 1 + 1 +
      (f + 1 + (3 * g + 1 + 1 + (3 * h + 1))))))) + 1 ≤ cIter S - 1000000 * (S + 2) ^ 2 := by
  unfold cIter
  have hx : S + 2 ≤ (S + 2) ^ 2 := Nat.le_self_pow (by norm_num) _
  have h4' : 4 ≤ (S + 2) ^ 2 := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ (S + 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have h4 : (S + 2) ^ 4 = (S + 2) ^ 2 * (S + 2) ^ 2 := by ring
  have hb' : b * (1000 * (S + 1 + 3) + 4) ≤ (S + 2) ^ 2 * (1000 * (S + 2) ^ 2 + 2004) := by
    apply Nat.mul_le_mul (by omega); omega
  rw [h4]
  generalize (S + 2) ^ 2 = X at *
  have hf2 : f ≤ 1000 * X * X + 32000 * X + 256000 := by
    have : 1000 * (X + 4 + 12) ^ 2 = 1000 * X * X + 32000 * X + 256000 := by ring
    omega
  have hb2 : b * (1000 * (S + 1 + 3) + 4) ≤ 1000 * X * X + 2004 * X := by
    have : X * (1000 * X + 2004) = 1000 * X * X + 2004 * X := by ring
    omega
  apply Nat.le_sub_of_add_le
  have key : 1000 * X * X + 2004 * X + 1000 * X * X + 32000 * X + 256000 + 20000 * X + 1000000 * X + 100000 ≤
      100000000 * (X * X) := by nlinarith
  generalize X * X = Y at *
  generalize 1000 * X * X = Z at *
  omega

theorem cB1_outer (S j l g h : ℕ) (hj : j ≤ S) (hl : l ≤ S) (hg : g ≤ 1) (hh : h ≤ S) :
    readCost j + 1 + (skipCost 0 + 1 + (30 * (j + l) + 40 + 1 + (cIter S - 1000000 * (S + 2) ^ 2 + 1 +
      (3 * g + 1 + 1 + (3 * h + 1))))) ≤ cIter S := by
  have h1 := readCost_le j S hj
  have h2 := cIter_sub S
  have h3 : skipCost 0 = 4000 := by simp [skipCost, natBitLength]
  have hx : S + 2 ≤ (S + 2) ^ 2 := Nat.le_self_pow (by norm_num) _
  rw [h3]
  generalize cIter S = C at *
  generalize (S + 2) ^ 2 = X at *
  generalize readCost j = R at *
  omega

set_option maxHeartbeats 1600000 in
/-- **`B`'s input `j`, copied** (paper §11.4; `Outer.copyNode`: `or w w` on the argument wire `w` of the gate when
`j < ℓ`, `false` otherwise). -/
theorem cB1_spec (cap : ℕ) (σ : WState 4 nrH) (hz : CBZ σ) (preD restD : List Bool) (j : ℕ)
    (hD : σ.st sD = preD ++ natWord j ++ natWord 0 ++ restD) (hDh : σ.sh sD = preD.length)
    (preA restA : List Bool) (args : List ℕ) (hA : σ.st sW = preA ++ args.flatMap natWord ++ restA)
    (hAh : σ.sh sW = preA.length) (hL : σ.val (regH .L) = args.length)
    (fl : List Bool) (hF : σ.st sF = fl) (hFh : σ.sh sF = 0) (n1 ob : ℕ) (hn1 : σ.val (regH .nB1) = n1)
    (hob : σ.val (regH .oB) = ob) (S : ℕ) (hjS : j ≤ S) (hlS : args.length ≤ S) (hAS : ∀ x ∈ args, x ≤ S)
    (hwS : (args.flatMap natWord).length ≤ S) (hn1S : n1 ≤ S) (hobS : ob ≤ S)
    (out : List Bool) (hout : OutOK σ out) (hcl : WClean σ) {n : ℕ}
    (hcap : σ.val (regH .cdB) + 2 * out.length + 1000 * (S + 2) ^ 2 ≤ cap) :
    ∃ τ, WExec cap cB1 σ τ (cIter S) ∧
      τ.sh sD = preD.length + (natWord j).length + (natWord 0).length ∧
      τ.val (regH .cdB) = σ.val (regH .cdB) + (natWord j).length + (natWord 0).length ∧
      OutOK τ (out ++ PCPPRequestNodeSchema.native (inNode fl args n1 ob j : BooleanNode n)) ∧
      WClean τ ∧ CBZ τ ∧ Fr σ τ [sD, sO] [.cdB, .w 7] ∧ τ.st sD = σ.st sD := by
  have hnj := natWord_length j
  have hbj := nbl_le j
  have hn0 : natBitLength 0 = 1 := by simp [natBitLength]
  have hsq : S + 2 ≤ (S + 2) ^ 2 := Nat.le_self_pow (by norm_num) _
  obtain ⟨τ1, e1, s1, c1, v1, f1, t1⟩ := rd_fr cap sD .cdB .f1 (by simp) (by simp) (by simp) (by simp) (by simp)
    (by simp) (by simp) σ preD (natWord 0 ++ restD) j (by rw [hD]; simp [List.append_assoc]) hDh hz.f
    (hz.z _ (by simp [zl])) (hz.z _ (by simp [zl])) (hz.z _ (by simp [zl])) (by omega)
  obtain ⟨τ2, e2, s2, c2, f2, t2⟩ := sk1_fr cap sD .cdB (by simp) (by simp) (by simp) τ1 (preD ++ natWord j)
    restD 0 (by rw [t1, hD]) (by rw [s1]; simp) (fun r => by rw [f1.v (by simp)]; exact hz.f r)
    (by rw [f1.v (by simp)]; exact hz.z _ (by simp [zl])) (by rw [f1.v (by simp)]; exact hz.z _ (by simp [zl]))
    (by rw [c1]; omega)
  have g2 : ∀ u, u ∉ [HReg.cdB, .f1] → τ2.val (regH u) = σ.val (regH u) := fun u hu => by
    rw [f2.v (by simp at hu ⊢; exact hu.1), f1.v hu]
  have v2 : τ2.val (regH .f1) = j := by rw [f2.v (by simp), v1]
  obtain ⟨τ3, e3, lt3, f3⟩ := less_fr cap .f1 .L (by simp) τ2
    (fun u hu => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
                    rcases hu with rfl | rfl | rfl | rfl | rfl <;> rw [g2 _ (by simp)] <;> exact hz.z _ (by simp [zl]))
    (by rw [v2, g2 _ (by simp), hL]; omega)
  have g3 : ∀ u, u ∉ [HReg.cdB, .f1, .lt] → τ3.val (regH u) = σ.val (regH u) := fun u hu => by
    rw [f3.v (by simp at hu ⊢; exact hu.2.2), g2 u (by simp at hu ⊢; exact ⟨hu.1, hu.2.1⟩)]
  have s3 : ∀ i, i ≠ sD → τ3.st i = σ.st i ∧ τ3.sh i = σ.sh i := fun i hi => by
    rw [(f3.s (by simp)).1, (f3.s (by simp)).2, (f2.s (by simp [hi])).1, (f2.s (by simp [hi])).2,
      (f1.s (by simp [hi])).1, (f1.s (by simp [hi])).2]; exact ⟨rfl, rfl⟩
  have o3 : OutOK τ3 out := ⟨by rw [(s3 sO (by simp)).1]; exact hout.1, by rw [(s3 sO (by simp)).2]; exact hout.2.1,
    by rw [g3 _ (by simp)]; exact hout.2.2⟩
  have w3 : WClean τ3 := ⟨fun i hi => by rw [g3 _ (by simp)]; exact hcl.1 i hi, by rw [g3 _ (by simp)]; exact hcl.2⟩
  have hD3 : τ3.st sD = σ.st sD := by rw [(f3.s (by simp)).1, t2, t1]
  have hDh3 : τ3.sh sD = preD.length + (natWord j).length + (natWord 0).length := by
    rw [(f3.s (by simp)).2, s2]; simp only [List.length_append]
  have hcd3 : τ3.val (regH .cdB) = σ.val (regH .cdB) + (natWord j).length + (natWord 0).length := by
    rw [f3.v (by simp), c2, c1]
  -- the two cases
  have main : ∃ τ, WExec cap (.ifr (regH .lt) wireW emit0) τ3 τ (cIter S - 1000000 * (S + 2) ^ 2) ∧
      OutOK τ (out ++ PCPPRequestNodeSchema.native (inNode fl args n1 ob j : BooleanNode n)) ∧ WClean τ ∧
      (∀ u, u ∉ [HReg.lt, .f1, .cdB, .w 7] → τ.val (regH u) = σ.val (regH u)) ∧
      τ.val (regH .lt) ≤ 1 ∧ τ.val (regH .f1) = j ∧ τ.st sD = σ.st sD ∧
      τ.sh sD = preD.length + (natWord j).length + (natWord 0).length ∧
      τ.val (regH .cdB) = σ.val (regH .cdB) + (natWord j).length + (natWord 0).length ∧
      (∀ i, i ≠ sD → i ≠ sO → τ.st i = σ.st i ∧ τ.sh i = σ.sh i) ∧ τ.cell = σ.cell := by
    have hcell3 : τ3.cell = σ.cell := by rw [f3.2.2, f2.2.2, f1.2.2]
    have hfz3 : ∀ r, τ3.val (regH (.f r)) = 0 := fun r => by rw [g3 _ (by simp)]; exact hz.f r
    by_cases hj : j < args.length
    · -- the wire of argument `j`
      have hL2 : τ2.val (regH .L) = args.length := by rw [g2 _ (by simp), hL]
      have hlt : τ3.val (regH .lt) ≠ 0 := by rw [lt3, v2, hL2]; simp [hj]
      have hjm : args[j] ∈ args := List.getElem_mem hj
      have hsk3 : τ3.val (regH .sk) = 0 := by rw [g3 _ (by simp)]; exact hz.z _ (by simp [zl])
      have ht3 : τ3.val (regH .t) = 0 := by rw [g3 _ (by simp)]; exact hz.z _ (by simp [zl])
      have hf13 : τ3.val (regH .f1) = j := by rw [f3.v (by simp), v2]
      obtain ⟨τ4, e4, v4, f4⟩ := add_fr cap .f1 .sk (by simp) (by simp) (by simp) τ3 ht3
        (by rw [hsk3, hf13]; omega)
      have hsk4 : τ4.val (regH .sk) = j := by rw [v4, hsk3, hf13]; simp
      have hsplit := flatMap_split natWord args j hj
      have htwl : ((args.take j).flatMap natWord).length + (natWord args[j]).length ≤ (args.flatMap natWord).length := by
        rw [hsplit]; simp only [List.length_append]; omega
      have hst4 : τ4.st sW = preA ++ (args.take j).flatMap natWord ++ (natWord args[j] ++ (args.drop (j + 1)).flatMap natWord ++ restA) := by
        rw [(f4.s (by simp)).1, (s3 sW (by simp)).1, hA, hsplit]; simp [List.append_assoc]
      have hsh4 : τ4.sh sW = preA.length := by rw [(f4.s (by simp)).2, (s3 sW (by simp)).2, hAh]
      have hv4 : ∀ u, u ∉ [HReg.cdB, .f1, .lt, .sk] → τ4.val (regH u) = σ.val (regH u) := fun u hu => by
        rw [f4.v (by simp at hu ⊢; exact hu.2.2.2), g3 u (by simp at hu ⊢; exact ⟨hu.1, hu.2.1, hu.2.2.1⟩)]
      have e5 := skipN_spec cap sW RA (fam_inj _ (by simp)) (regH .z) (regH .jk) (regH .sk)
        (famNe _ _ (by simp) (by simp)) (famNe _ _ (by simp) (by simp)) (famNe _ _ (by simp) (by simp)) (by simp)
        (by simp) τ4 preA (natWord args[j] ++ (args.drop (j + 1)).flatMap natWord ++ restA) (args.take j) (S + 1)
        (fun x hx => (nbl_le x).trans (by have := hAS x (List.mem_of_mem_take hx); omega)) hst4 hsh4
        (famZero _ _ (fun r => by rw [hv4 _ (by simp)]; exact hz.f r))
        (by rw [hv4 _ (by simp)]; exact hz.z _ (by simp [zl])) (by rw [hv4 _ (by simp)]; exact hz.z _ (by simp [zl]))
        (by rw [hsk4, List.length_take]; omega)
        (by simp only [RA, fam_cd]; rw [hv4 _ (by simp), hz.z _ (by simp [zl])]; omega)
        (by simp; omega)
      set τ5 := ((τ4.seth sW (preA.length + ((args.take j).flatMap natWord).length)).setv (RA .cd) (τ4.val (RA .cd) + ((args.take j).flatMap natWord).length)).setv
        (regH .sk) 0 with hτ5
      have cd5 : τ5.val (regH .cdA) = ((args.take j).flatMap natWord).length := by
        simp only [τ5, RA, fam_cd, WState.setv_val, Function.update_apply, regH_eq_iff, reduceCtorEq, if_false,
          if_true]; rw [hv4 _ (by simp), hz.z _ (by simp [zl])]; simp
      have hv5 : ∀ u, u ∉ [HReg.cdB, .f1, .lt, .sk, .cdA] → τ5.val (regH u) = σ.val (regH u) := fun u hu => by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hu
        simp only [τ5, RA, fam_cd, WState.setv_val, WState.seth_val, Function.update_apply, regH_eq_iff, hu.2.2.2.1,
          hu.2.2.2.2, if_false]
        exact hv4 u (by simp [hu.1, hu.2.1, hu.2.2.1, hu.2.2.2.1])
      obtain ⟨τ6, e6, s6, c6, v6, f6, t6⟩ := rd_fr cap sW .cdA .f2 (by simp) (by simp) (by simp) (by simp) (by simp)
        (by simp) (by simp) τ5 (preA ++ (args.take j).flatMap natWord) ((args.drop (j + 1)).flatMap natWord ++ restA) args[j]
        (by simp [τ5, hst4, List.append_assoc]) (by simp [τ5]) (fun r => by rw [hv5 _ (by simp)]; exact hz.f r)
        (by rw [hv5 _ (by simp)]; exact hz.z _ (by simp [zl])) (by rw [hv5 _ (by simp)]; exact hz.z _ (by simp [zl]))
        (by rw [hv5 _ (by simp)]; exact hz.z _ (by simp [zl])) (by rw [cd5]; have := hAS _ hjm; omega)
      have hF6 : τ6.st sF = fl ∧ τ6.sh sF = 0 := by
        rw [(f6.s (by simp)).1, (f6.s (by simp)).2]
        simp only [τ5, WState.setv_st, WState.seth_st, WState.setv_sh, WState.seth_sh, Function.update_apply,
          sF_ne_sW, if_false]
        rw [(f4.s (by simp)).1, (f4.s (by simp)).2, (s3 sF (by simp)).1, (s3 sF (by simp)).2]; exact ⟨hF, hFh⟩
      have hv6 : ∀ u, u ∉ [HReg.cdB, .f1, .lt, .sk, .cdA, .f2] → τ6.val (regH u) = σ.val (regH u) := fun u hu => by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hu
        rw [f6.v (by simp [hu.2.2.2.2.1, hu.2.2.2.2.2]), hv5 u (by simp [hu.1, hu.2.1, hu.2.2.1, hu.2.2.2.1, hu.2.2.2.2.1])]
      have hn6 : τ6.val (regH .nB1) = n1 := by rw [hv6 _ (by simp), hn1]
      have ho6 : τ6.val (regH .oB) = ob := by rw [hv6 _ (by simp), hob]
      have hAj := hAS _ hjm
      have hpf := posF_le fl args[j] n1 ob S hAj hn1S hobS
      obtain ⟨τ7, e7, p7, f7⟩ := pos_fr cap .f2 .p1 (by simp) (by simp) τ6 fl hF6.1 hF6.2
        (by rw [hv6 _ (by simp)]; exact hz.z _ (by simp [zl])) (by rw [hv6 _ (by simp)]; exact hz.z _ (by simp [zl]))
        (by rw [hv6 _ (by simp)]; exact hz.z _ (by simp [zl])) (by rw [hv6 _ (by simp)]; exact hz.z _ (by simp [zl]))
        (by rw [v6, hn6, ho6]
            have : args[j] * n1 ≤ S * S := Nat.mul_le_mul hAj hn1S
            nlinarith)
      rw [v6, hn6, ho6] at p7 e7
      have hcd7 : τ7.val (regH .cdA) =
          ((args.take j).flatMap natWord).length + (natWord args[j]).length := by
        rw [f7.v (by simp), c6, cd5]
      have hnaj := natWord_length args[j]
      have e8 := wrewind_spec cap sW (regH .cdA) (((args.take j).flatMap natWord).length + (natWord args[j]).length) τ7
        hcd7 (by rw [hcd7]; omega)
      set τ8 := (τ7.setv (regH .cdA) 0).seth sW (τ7.sh sW - (((args.take j).flatMap natWord).length +
        (natWord args[j]).length)) with hτ8
      have hsh8 : τ8.sh sW = preA.length := by
        simp only [τ8, WState.seth_sh, Function.update_self]
        rw [(f7.s (by simp)).2, s6]; simp only [List.length_append]; omega
      have f8 : Fr τ7 τ8 [sW] [.cdA] := (fr_setv τ7 .cdA 0).trans' (fr_seth _ sW _) |>.mono (by simp) (by simp)
      have hv8 : ∀ u, u ∉ [HReg.cdB, .f1, .lt, .sk, .f2, .p1] → τ8.val (regH u) = σ.val (regH u) := by
        intro u hu
        by_cases hc : u = .cdA
        · subst hc; simp only [τ8, WState.seth_val, WState.setv_val, Function.update_self]
          exact (hz.z _ (by simp [zl])).symm
        · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hu
          rw [f8.v (by simp [hc]), f7.v (by simp [hu.2.2.2.2.2]),
            hv6 u (by simp [hu.1, hu.2.1, hu.2.2.1, hu.2.2.2.1, hu.2.2.2.2.1, hc])]
      have o8 : OutOK τ8 out := by
        refine ⟨?_, ?_, ?_⟩
        · rw [(f8.s (by simp)).1, (f7.s (by simp)).1, (f6.s (by simp)).1]
          simp only [τ5, WState.setv_st, WState.seth_st, Function.update_apply, sO_ne_sW, if_false]
          rw [(f4.s (by simp)).1]; exact o3.1
        · rw [(f8.s (by simp)).2, (f7.s (by simp)).2, (f6.s (by simp)).2]
          simp only [τ5, WState.setv_sh, WState.seth_sh, Function.update_apply, sO_ne_sW, if_false]
          rw [(f4.s (by simp)).2]; exact o3.2.1
        · rw [hv8 _ (by simp), ← hout.2.2]
      have w8 : WClean τ8 := ⟨fun i hi => by rw [hv8 _ (by simp)]; exact hcl.1 i hi, by rw [hv8 _ (by simp)]; exact hcl.2⟩
      have hp8 : τ8.val (regH .p1) = posF fl args[j] n1 ob := by
        rw [f8.v (by simp), p7]
      obtain ⟨τ9, e9, o9, w9, f9⟩ := emit_fr cap τ8 ([], 4) ([regH .p1], 0) ([regH .p1], 0)
        (BooleanNode.or (posF fl args[j] n1 ob) (posF fl args[j] n1 ob) : BooleanNode n) out o8 w8
        ⟨tok_nil, tok_list [.p1] 0 (by simp), tok_list [.p1] 0 (by simp)⟩ (by simp)
        ⟨by rw [fv_nil]; rfl, by rw [fv_one, hp8]; rfl, by rw [fv_one, hp8]; rfl⟩ ((S + 2) ^ 2 + 4)
        (fun i => by fin_cases i <;> simp [PCPPRequestNodeSchema.fields] <;> omega)
        (by have := native_len_le (BooleanNode.or (posF fl args[j] n1 ob) (posF fl args[j] n1 ob) : BooleanNode n)
              ((S + 2) ^ 2 + 4) (fun i => by fin_cases i <;> simp [PCPPRequestNodeSchema.fields] <;> omega)
            omega)
      obtain ⟨τ10, e10, z10, f10⟩ := clr_fr cap .f2 τ9 (by rw [f9.v (by simp), f8.v (by simp), f7.v (by simp), v6]; omega)
      obtain ⟨τ11, e11, z11, f11⟩ := clr_fr cap .p1 τ10 (by rw [f10.v (by simp), f9.v (by simp), hp8]; omega)
      have hcell11 : τ11.cell = σ.cell := by
        rw [f11.2.2, f10.2.2, f9.2.2, f8.2.2, f7.2.2, f6.2.2]
        simp only [τ5, WState.setv_cell, WState.seth_cell]
        rw [f4.2.2, hcell3]
      have hv311 : ∀ u ∈ [HReg.lt, .f1, .cdB], τ11.val (regH u) = τ3.val (regH u) := by
        intro u hu
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
        have h1 : u ≠ .p1 := by rcases hu with rfl | rfl | rfl <;> simp
        have h2 : u ≠ .f2 := by rcases hu with rfl | rfl | rfl <;> simp
        have h3 : u ≠ .w 7 := by rcases hu with rfl | rfl | rfl <;> simp
        have h4 : u ≠ .cdA := by rcases hu with rfl | rfl | rfl <;> simp
        have h5 : u ≠ .sk := by rcases hu with rfl | rfl | rfl <;> simp
        rw [f11.v (by simp [h1]), f10.v (by simp [h2]), f9.v (by simp [h3]), f8.v (by simp [h4]), f7.v (by simp [h1]),
          f6.v (by simp [h4, h2])]
        simp only [τ5, RA, fam_cd, WState.setv_val, WState.seth_val, Function.update_apply, regH_eq_iff, h5, h4,
          if_false]
        rw [f4.v (by simp [h5])]
      have hsame : ∀ i, i ≠ sW → i ≠ sO → τ11.st i = τ3.st i ∧ τ11.sh i = τ3.sh i := by
        intro i h1 h2
        rw [(f11.s (by simp)).1, (f11.s (by simp)).2, (f10.s (by simp)).1, (f10.s (by simp)).2,
          (f9.s (by simp [h2])).1, (f9.s (by simp [h2])).2, (f8.s (by simp [h1])).1, (f8.s (by simp [h1])).2,
          (f7.s (by simp)).1, (f7.s (by simp)).2, (f6.s (by simp [h1])).1, (f6.s (by simp [h1])).2]
        simp only [τ5, WState.setv_st, WState.seth_st, WState.setv_sh, WState.seth_sh, Function.update_apply, h1,
          if_false]
        exact ⟨(f4.s (by simp)).1, (f4.s (by simp)).2⟩
      refine ⟨τ11, WExec.mono (WExec.ifrT hlt (WExec.seq e4 (WExec.seq e5 (WExec.seq e6 (WExec.seq e7 (WExec.seq e8
        (WExec.seq e9 (WExec.seq e10 e11)))))))) ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hcell11⟩
      · rw [hf13, f9.v (by simp), f8.v (by simp), f7.v (by simp), v6, f10.v (by simp), f9.v (by simp), hp8]
        have hw := hwS
        rw [hsplit] at hw; simp only [List.length_append] at hw
        exact wire_arith S j (args.take j).length _ _ ((args.take j).flatMap natWord).length _ args[j]
          (posF fl args[j] n1 ob) (natWord args[j]).length hjS (by simp; omega) (readCost_le _ _ hAj)
          (posCost_le _ _ _ _ hAj hn1S hobS) (by omega) (nodeCost_le _ _ le_rfl) hAj hpf (by omega)
      · simp only [inNode, dif_pos hj]
        exact ⟨by rw [(f11.s (by simp)).1, (f10.s (by simp)).1]; exact o9.1,
          by rw [(f11.s (by simp)).2, (f10.s (by simp)).2]; exact o9.2.1,
          by rw [f11.v (by simp), f10.v (by simp)]; exact o9.2.2⟩
      · exact ⟨fun i hi => by rw [f11.v (by simp), f10.v (by simp)]; exact w9.1 i hi,
          by rw [f11.v (by simp), f10.v (by simp)]; exact w9.2⟩
      · intro u hu
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hu
        by_cases hp : u = .p1
        · subst hp; rw [z11]; exact (hz.z _ (by simp [zl])).symm
        · by_cases hf : u = .f2
          · subst hf; rw [f11.v (by simp), z10]; exact (hz.z _ (by simp [zl])).symm
          · by_cases hs : u = .sk
            · subst hs
              rw [f11.v (by simp), f10.v (by simp), f9.v (by simp), f8.v (by simp), f7.v (by simp), f6.v (by simp)]
              simp only [τ5, WState.setv_val, Function.update_self]
              exact (hz.z _ (by simp [zl])).symm
            · rw [f11.v (by simp [hp]), f10.v (by simp [hf]), f9.v (by simp [hu.2.2.2]),
                hv8 u (by simp [hu.1, hu.2.1, hu.2.2.1, hs, hf, hp])]
      · rw [hv311 .lt (by simp), lt3]; split_ifs <;> omega
      · rw [hv311 .f1 (by simp), hf13]
      · rw [(hsame sD (by simp) (by simp)).1, hD3]
      · rw [(hsame sD (by simp) (by simp)).2, hDh3]
      · rw [hv311 .cdB (by simp), hcd3]
      · intro i h1 h2
        by_cases hW : i = sW
        · subst hW
          refine ⟨?_, ?_⟩
          · rw [(f11.s (by simp)).1, (f10.s (by simp)).1, (f9.s (by simp)).1]
            simp only [τ8, WState.seth_st, WState.setv_st]
            rw [(f7.s (by simp)).1, t6]
            simp only [τ5, WState.setv_st, WState.seth_st]
            rw [(f4.s (by simp)).1, (s3 sW (by simp)).1]
          · rw [(f11.s (by simp)).2, (f10.s (by simp)).2, (f9.s (by simp)).2, hsh8, hAh]
        · rw [(hsame i hW h2).1, (hsame i hW h2).2]; exact s3 i h1
    · -- `false`
      have hlt0 : τ3.val (regH .lt) = 0 := by rw [lt3, v2, g2 _ (by simp), hL]; simp; omega
      obtain ⟨τ9, e9, o9, w9, f9⟩ := emit_fr cap τ3 ([], 0) ([], 0) ([], 0)
        (BooleanNode.const false : BooleanNode n) out o3 w3 ⟨tok_nil, tok_nil, tok_nil⟩ (by simp)
        ⟨by rw [fv_nil]; rfl, by rw [fv_nil]; rfl, by rw [fv_nil]; rfl⟩ 1
        (fun i => by fin_cases i <;> simp [PCPPRequestNodeSchema.fields])
        (by have := native_len_le (BooleanNode.const false : BooleanNode n) 1
              (fun i => by fin_cases i <;> simp [PCPPRequestNodeSchema.fields])
            omega)
      refine ⟨τ9, WExec.mono (WExec.ifrF hlt0 e9) ?_, ?_, w9, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · have := nodeCost_le 1 1 le_rfl
        have := cIter_sub S
        omega
      · simp only [inNode, dif_neg hj]; exact o9
      · intro u hu
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hu
        rw [f9.v (by simp [hu.2.2.2]), g3 u (by simp [hu.1, hu.2.1, hu.2.2.1])]
      · rw [f9.v (by simp), lt3]; split_ifs <;> omega
      · rw [f9.v (by simp), f3.v (by simp), v2]
      · rw [(f9.s (by simp)).1, hD3]
      · rw [(f9.s (by simp)).2, hDh3]
      · rw [f9.v (by simp), hcd3]
      · intro i h1 h2; rw [(f9.s (by simp [h2])).1, (f9.s (by simp [h2])).2]; exact s3 i h1
      · rw [f9.2.2, hcell3]
  obtain ⟨τ9, e9, o9, w9, g9, l9, v9, d9, dh9, cd9, s9, c9⟩ := main
  obtain ⟨τ10, e10, z10, f10⟩ := clr_fr cap .lt τ9 (by omega)
  obtain ⟨τ11, e11, z11, f11⟩ := clr_fr cap .f1 τ10 (by rw [f10.v (by simp), v9]; omega)
  refine ⟨τ11, WExec.mono (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e9 (WExec.seq e10 e11))))) ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [v2, show τ2.val (regH .L) = args.length by rw [g2 _ (by simp), hL],
      f10.v (by simp), v9]
    exact cB1_outer S j args.length _ _ hjS hlS l9 hjS
  · rw [(f11.s (by simp)).2, (f10.s (by simp)).2, dh9]
  · rw [f11.v (by simp), f10.v (by simp), cd9]
  · exact ⟨by rw [(f11.s (by simp)).1, (f10.s (by simp)).1]; exact o9.1,
      by rw [(f11.s (by simp)).2, (f10.s (by simp)).2]; exact o9.2.1,
      by rw [f11.v (by simp), f10.v (by simp)]; exact o9.2.2⟩
  · exact ⟨fun i hi => by rw [f11.v (by simp), f10.v (by simp)]; exact w9.1 i hi,
      by rw [f11.v (by simp), f10.v (by simp)]; exact w9.2⟩
  · refine ⟨fun r => ?_, fun u hu => ?_⟩
    · rw [f11.v (by simp), f10.v (by simp), g9 _ (by simp)]; exact hz.f r
    · by_cases h1 : u = .f1
      · rw [h1]; exact z11
      · by_cases h2 : u = .lt
        · rw [h2, f11.v (by simp)]; exact z10
        · rw [f11.v (by simp [h1]), f10.v (by simp [h2]), g9 u (by simp [h1, h2]; constructor <;> (rintro rfl <;> simp [zl] at hu))]
          exact hz.z u hu
  · refine ⟨fun y hy => ?_, fun r hr => ?_, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
      rw [(f11.s (by simp)).1, (f11.s (by simp)).2, (f10.s (by simp)).1, (f10.s (by simp)).2]
      exact s9 y hy.1 hy.2
    · obtain ⟨u, rfl⟩ := regH_surj r
      have hu : u ∉ [HReg.cdB, .w 7] := fun m => hr (List.mem_map_of_mem m)
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hu
      by_cases h1 : u = .f1
      · subst h1; rw [z11]; exact (hz.z _ (by simp [zl])).symm
      · by_cases h2 : u = .lt
        · subst h2; rw [f11.v (by simp), z10]; exact (hz.z _ (by simp [zl])).symm
        · show τ11.val (regH u) = σ.val (regH u)
          rw [f11.v (by simp [h1]), f10.v (by simp [h2]), g9 u (by simp [h1, h2, hu.1, hu.2])]
    · rw [f11.2.2, f10.2.2, c9]
  · rw [(f11.s (by simp)).1, (f10.s (by simp)).1, d9]

end NearCubicGates.Close.Succinct.SubstMachine
