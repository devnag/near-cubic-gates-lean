import Proof.Gates.Succinct.SubstitutionCopy

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

variable {q ℓ : ℕ}

/-- The image formula is the fold's image (`posM_eq`, `kOf_count`). -/
theorem posM_posF (B : BooleanCircuit q) (C : OracleCircuit ℓ ℓ) (c : ℕ) (hc : c ≤ C.nodes.length) :
    posM B C c = posF (ofl C) c (B.nodes.length - 1) B.output.val := by
  have hB : 1 ≤ B.nodes.length := by have := B.output.isLt; omega
  rw [posM_eq B C c hc hB, kOf_count]
  unfold posF nodeO
  ring_nf

/-- The node the machine writes for node `t` of `B` in the copy at offset `off`. -/
noncomputable def cpNode (fl : List Bool) (args : List ℕ) (n1 ob off : ℕ) : BooleanNode q → BooleanNode q
  | .const b => .const b
  | .input j => inNode fl args n1 ob j.val
  | .not c => .not (off + c)
  | .and l r => .and (off + l) (off + r)
  | .or l r => .or (off + l) (off + r)

/-- **The written node is `Outer.copyNode`** (paper §11.4): the machine's images agree with the fold's references. -/
theorem cpNode_eq (B : BooleanCircuit q) (C : OracleCircuit ℓ ℓ) (i : ℕ) (hi : i < C.nodes.length)
    (args : Fin ℓ → ℕ) (hargs : ∀ j, args j < i) (t : ℕ) (ht : t < B.nodes.length) :
    cpNode (ofl C) (List.ofFn args) (B.nodes.length - 1) B.output.val (accI B C i).1.length B.nodes[t] =
      copyNode (accI B C i).1.length ((List.ofFn fun j => ref (accI B C i).2 (args j)) ++ []) t B.nodes[t] := by
  have hw := B.wellFormed ⟨t, ht⟩
  simp only [List.get_eq_getElem] at hw
  cases h : B.nodes[t] with
  | const b => rfl
  | input j =>
    simp only [cpNode, copyNode, inNode, List.append_nil, List.length_ofFn]
    by_cases hj : j.val < ℓ
    · rw [dif_pos (by simpa using hj), if_pos hj]
      have hr : (List.ofFn fun j => ref (accI B C i).2 (args j)).getD j.val 0 =
          posF (ofl C) ((List.ofFn args)[j.val]'(by simpa using hj)) (B.nodes.length - 1) B.output.val := by
        rw [List.getD_eq_getElem _ _ (by simpa using hj)]
        simp only [List.getElem_ofFn]
        rw [ref_accI B C i hi.le _ (hargs _), posM_posF B C _ (by have := hargs ⟨j.val, hj⟩; omega)]
      rw [hr]
    · rw [dif_neg (by simpa using hj), if_neg hj]
  | not c =>
    rw [h] at hw
    simp only [cpNode, copyNode, copyRef, if_pos (show c < t from hw)]
  | and l r =>
    rw [h] at hw
    simp only [cpNode, copyNode, copyRef, if_pos hw.1, if_pos hw.2]
  | or l r =>
    rw [h] at hw
    simp only [cpNode, copyNode, copyRef, if_pos hw.1, if_pos hw.2]

/-- The length of the first `t` node words of `B`. -/
def lenB (B : BooleanCircuit q) (t : ℕ) : ℕ := ((B.nodes.take t).flatMap PCPPRequestNodeSchema.native).length

theorem desc_split (B : BooleanCircuit q) (t : ℕ) (ht : t < B.nodes.length) :
    PCPPNative.descriptor B = (natWord q ++ natWord B.nodes.length ++ (B.nodes.take t).flatMap PCPPRequestNodeSchema.native) ++
      PCPPRequestNodeSchema.native B.nodes[t] ++
      ((B.nodes.drop (t + 1)).flatMap PCPPRequestNodeSchema.native ++ natWord B.output.val) := by
  rw [PCPPNative.descriptor_eq, flatMap_split' PCPPRequestNodeSchema.native B.nodes t ht]
  simp only [List.append_assoc]

theorem lenB_succ (B : BooleanCircuit q) (t : ℕ) (ht : t < B.nodes.length) :
    lenB B (t + 1) = lenB B t + (PCPPRequestNodeSchema.native B.nodes[t]).length := by
  unfold lenB
  rw [List.take_add_one, List.getElem?_eq_getElem ht, Option.toList_some, List.flatMap_append]; simp

/-- The cost class of one copied node with its tag. -/
def cpIter (S : ℕ) : ℕ := cIter S + 1000000

theorem cpNode_fields_le (fl : List Bool) (args : List ℕ) (n1 ob off S : ℕ) (nd : BooleanNode q) (t : ℕ)
    (hw : nd.WellFormedAt t) (ht : t ≤ S) (hargs : ∀ x ∈ args, x ≤ S) (hn1 : n1 ≤ S) (hob : ob ≤ S)
    (hoff : off ≤ (S + 2) ^ 2) (i : Fin 3) :
    PCPPRequestNodeSchema.fields (cpNode fl args n1 ob off nd) i ≤ 2 * (S + 2) ^ 2 + 4 := by
  have hsq : S + 2 ≤ (S + 2) ^ 2 := Nat.le_self_pow (by norm_num) _
  cases nd with
  | const b => fin_cases i <;> simp [cpNode, PCPPRequestNodeSchema.fields] <;> cases b <;> simp <;> omega
  | input j =>
    simp only [cpNode, inNode]
    split_ifs with hj
    · have := posF_le fl args[j.val] n1 ob S (hargs _ (List.getElem_mem hj)) hn1 hob
      fin_cases i <;> simp [PCPPRequestNodeSchema.fields] <;> omega
    · fin_cases i <;> simp [PCPPRequestNodeSchema.fields]
  | not c => simp [BooleanNode.WellFormedAt] at hw; fin_cases i <;> simp [cpNode, PCPPRequestNodeSchema.fields] <;> omega
  | and l r => simp [BooleanNode.WellFormedAt] at hw; fin_cases i <;> simp [cpNode, PCPPRequestNodeSchema.fields] <;> omega
  | or l r => simp [BooleanNode.WellFormedAt] at hw; fin_cases i <;> simp [cpNode, PCPPRequestNodeSchema.fields] <;> omega

theorem br_cost (S a b c : ℕ) (ha : a ≤ S) (hb : b ≤ S) (hc : c ≤ (S + 2) ^ 2) :
    readCost a + readCost b + CheckedPCPP.NodeEmit.nodeCost (c + a + b + 4) + 3 * (a + b) + 10 ≤ cIter S ∧
      readCost a + CheckedPCPP.NodeEmit.nodeCost (c + a + 2) + 3 * a + 5000 ≤ cIter S := by
  have hsq : S + 2 ≤ (S + 2) ^ 2 := Nat.le_self_pow (by norm_num) _
  have h4' : 4 ≤ (S + 2) ^ 2 := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ (S + 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have r1 := readCost_le a S ha
  have r2 := readCost_le b S hb
  have n1 := nodeCost_le (c + a + b + 4) (3 * (S + 2) ^ 2 + 4) (by omega)
  have n2 := nodeCost_le (c + a + 2) (3 * (S + 2) ^ 2 + 4) (by omega)
  have h4 : (S + 2) ^ 4 = (S + 2) ^ 2 * (S + 2) ^ 2 := by ring
  unfold cIter
  rw [h4]
  generalize (S + 2) ^ 2 = X at *
  have : 1000 * (3 * X + 4 + 12) ^ 2 = 9000 * (X * X) + 96000 * X + 256000 := by ring
  have hXX : 4 * X ≤ X * X := Nat.mul_le_mul_right _ h4'
  constructor <;> nlinarith

set_option maxHeartbeats 3200000 in
/-- **One node of `B`, copied** (paper §11.4; `Outer.copyNode` by `cpNode_eq`). -/
theorem copyStep (cap : ℕ) (B : BooleanCircuit q) (t : ℕ) (ht : t < B.nodes.length) (σ : WState 4 nrH) (hz : CBZ σ)
    (htag : σ.val (regH .tagB) = 0) (hD : σ.st sD = PCPPNative.descriptor B)
    (hDh : σ.sh sD = pB B + lenB B t) (preA restA : List Bool) (args : List ℕ)
    (hA : σ.st sW = preA ++ args.flatMap natWord ++ restA) (hAh : σ.sh sW = preA.length)
    (hL : σ.val (regH .L) = args.length) (fl : List Bool) (hF : σ.st sF = fl) (hFh : σ.sh sF = 0)
    (hn1 : σ.val (regH .nB1) = B.nodes.length - 1) (hob : σ.val (regH .oB) = B.output.val) (S : ℕ)
    (hnB : B.nodes.length ≤ S) (hq : q ≤ S) (hlS : args.length ≤ S) (hAS : ∀ x ∈ args, x ≤ S)
    (hwS : (args.flatMap natWord).length ≤ S) (hcur : σ.val (regH .cur) ≤ (S + 2) ^ 2)
    (out : List Bool) (hout : OutOK σ out) (hcl : WClean σ)
    (hcap : σ.val (regH .cdB) + 2 * out.length + 2000 * (S + 2) ^ 2 ≤ cap) :
    ∃ τ, WExec cap copyBody σ τ (cpIter S) ∧
      OutOK τ (out ++ PCPPRequestNodeSchema.native
        (cpNode fl args (B.nodes.length - 1) B.output.val (σ.val (regH .cur)) B.nodes[t])) ∧
      WClean τ ∧ CBZ τ ∧ τ.sh sD = pB B + lenB B (t + 1) ∧
      τ.val (regH .cdB) = σ.val (regH .cdB) + (PCPPRequestNodeSchema.native B.nodes[t]).length ∧
      Fr σ τ [sD, sO] [.cdB, .w 7] ∧ τ.st sD = σ.st sD := by
  have hsq : S + 2 ≤ (S + 2) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hw := B.wellFormed ⟨t, ht⟩
  simp only [List.get_eq_getElem] at hw
  have hsplit := desc_split B t ht
  set nd := B.nodes[t] with hnd
  set preD0 := natWord q ++ natWord B.nodes.length ++ (B.nodes.take t).flatMap PCPPRequestNodeSchema.native
    with hpreD0
  set restD := (B.nodes.drop (t + 1)).flatMap PCPPRequestNodeSchema.native ++ natWord B.output.val with hrestD
  have hpre0 : preD0.length = pB B + lenB B t := by simp only [preD0, pB, lenB, List.length_append]
  have hnat := CheckedPCPP.NodeEmit.native_fields nd
  have htag5 : PCPPRequestNodeSchema.fields nd 0 ≤ 4 := by
    cases nd <;> simp [PCPPRequestNodeSchema.fields]
  -- the tag
  obtain ⟨τ1, e1, s1, c1, v1, f1, t1⟩ := rd_fr cap sD .cdB .tagB (by simp) (by simp) (by simp) (by simp) (by simp)
    (by simp) (by simp) σ preD0
    (natWord (PCPPRequestNodeSchema.fields nd 1) ++ natWord (PCPPRequestNodeSchema.fields nd 2) ++ restD)
    (PCPPRequestNodeSchema.fields nd 0) (by rw [hD, hsplit, hnat]; simp only [List.append_assoc]) (by rw [hDh, hpre0])
    hz.f (hz.z _ (by simp [zl])) (hz.z _ (by simp [zl])) htag (by omega)
  set σ1 := τ1.setv (regH .tagB) 0 with hσ1
  have g1 : ∀ u, u ∉ [HReg.cdB, .tagB] → σ1.val (regH u) = σ.val (regH u) := fun u hu => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hu
    simp only [σ1, WState.setv_val, Function.update_apply, regH_eq_iff, hu.2, if_false]
    exact f1.v (by simp [hu.1, hu.2])
  have hz1 : CBZ σ1 := ⟨fun r => by rw [g1 _ (by simp)]; exact hz.f r,
    fun u hu => by rw [g1 u (by intro m; simp at m; rcases m with rfl | rfl <;> simp [zl] at hu)]; exact hz.z u hu⟩
  have hs1 : ∀ i, i ≠ sD → σ1.st i = σ.st i ∧ σ1.sh i = σ.sh i := fun i hi => by
    simp only [σ1, WState.setv_st, WState.setv_sh]; exact f1.s (by simp [hi])
  have hD1 : σ1.st sD = preD0 ++ natWord (PCPPRequestNodeSchema.fields nd 0) ++
      (natWord (PCPPRequestNodeSchema.fields nd 1) ++ natWord (PCPPRequestNodeSchema.fields nd 2) ++ restD) := by
    simp only [σ1, WState.setv_st]; rw [t1, hD, hsplit, hnat]; simp only [List.append_assoc]
  have hDh1 : σ1.sh sD = preD0.length + (natWord (PCPPRequestNodeSchema.fields nd 0)).length := by
    simp only [σ1, WState.setv_sh]; exact s1
  have hout1 : OutOK σ1 out := ⟨by rw [(hs1 sO (by simp)).1]; exact hout.1, by rw [(hs1 sO (by simp)).2]; exact hout.2.1,
    by rw [g1 _ (by simp)]; exact hout.2.2⟩
  have hcl1 : WClean σ1 := ⟨fun i hi => by rw [g1 _ (by simp)]; exact hcl.1 i hi, by rw [g1 _ (by simp)]; exact hcl.2⟩
  have hcd1 : σ1.val (regH .cdB) = σ.val (regH .cdB) + (natWord (PCPPRequestNodeSchema.fields nd 0)).length := by
    simp only [σ1, WState.setv_val, Function.update_apply, regH_eq_iff, reduceCtorEq, if_false]; exact c1
  have hcur1 : σ1.val (regH .cur) = σ.val (regH .cur) := g1 _ (by simp)
  have finish : ∀ (v : ℕ) (hv : PCPPRequestNodeSchema.fields nd 0 = v) (hb : v < 5) (P : WM 4 nrH)
      (hP : [cB0, cB1, cB2, cB34 3, cB34 4][v]'(by simpa using hb) = P)
      (τ : WState 4 nrH) (n : ℕ), WExec cap P σ1 τ n → n ≤ cIter S →
      τ.sh sD = preD0.length + (natWord (PCPPRequestNodeSchema.fields nd 0)).length +
        (natWord (PCPPRequestNodeSchema.fields nd 1)).length + (natWord (PCPPRequestNodeSchema.fields nd 2)).length →
      τ.val (regH .cdB) = σ1.val (regH .cdB) + (natWord (PCPPRequestNodeSchema.fields nd 1)).length +
        (natWord (PCPPRequestNodeSchema.fields nd 2)).length →
      OutOK τ (out ++ PCPPRequestNodeSchema.native
        (cpNode fl args (B.nodes.length - 1) B.output.val (σ.val (regH .cur)) nd)) →
      WClean τ → CBZ τ → Fr σ1 τ [sD, sO] [.cdB, .w 7] → τ.st sD = σ1.st sD →
      ∃ τ, WExec cap copyBody σ τ (cpIter S) ∧
        OutOK τ (out ++ PCPPRequestNodeSchema.native
          (cpNode fl args (B.nodes.length - 1) B.output.val (σ.val (regH .cur)) nd)) ∧
        WClean τ ∧ CBZ τ ∧ τ.sh sD = pB B + lenB B (t + 1) ∧
        τ.val (regH .cdB) = σ.val (regH .cdB) + (PCPPRequestNodeSchema.native nd).length ∧
        Fr σ τ [sD, sO] [.cdB, .w 7] ∧ τ.st sD = σ.st sD := by
    intro v hv hb P hP τ n eP hn hsh hcd ho hw hzz hfr hst
    have eC := caseL_spec cap (regH .tagB) [cB0, cB1, cB2, cB34 3, cB34 4] v
      (by simpa using hb) τ1 τ n (by rw [v1, hv]) (by rw [v1]; omega) (by rw [hP]; exact eP)
    have hlen : (PCPPRequestNodeSchema.native nd).length = (natWord (PCPPRequestNodeSchema.fields nd 0)).length +
        (natWord (PCPPRequestNodeSchema.fields nd 1)).length + (natWord (PCPPRequestNodeSchema.fields nd 2)).length := by
      rw [hnat]; simp only [List.length_append]
    refine ⟨τ, WExec.mono (WExec.seq e1 eC) ?_, ho, hw, hzz, ?_, ?_, ?_, ?_⟩
    · have := readCost_le (PCPPRequestNodeSchema.fields nd 0) 4 htag5
      unfold cpIter; omega
    · rw [hsh, hpre0, lenB_succ B t ht, hlen]; ring
    · rw [hcd, hcd1, hlen]; ring
    · have hf := f1.trans' ((fr_setv τ1 .tagB 0).trans' hfr)
      refine (hf.mono (by intro x hx; simp at hx ⊢; omega) (fun u hu => hu)).tighten _ ?_
      intro u hu hu'
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hu hu'
      rcases hu with rfl | rfl | rfl | rfl | rfl
      · exact absurd (Or.inl rfl) hu'
      · rw [hfr.v (by simp)]; simp [σ1, htag]
      · rw [hfr.v (by simp)]; simp [σ1, htag]
      · exact absurd (Or.inl rfl) hu'
      · exact absurd (Or.inr rfl) hu'
    · rw [hst]; simp only [σ1, WState.setv_st]; exact t1
  have hn0 := natWord_length (PCPPRequestNodeSchema.fields nd 0)
  have hb0 := nbl_le (PCPPRequestNodeSchema.fields nd 0)
  have hS4 : 3 + 1000 * (S + 2) ^ 2 ≤ 2000 * (S + 2) ^ 2 := by nlinarith
  have hit := cIter_sub S
  have hcur1' : σ1.val (regH .cur) ≤ (S + 2) ^ 2 := by rw [hcur1]; exact hcur
  have hcd1' : σ1.val (regH .cdB) ≤ σ.val (regH .cdB) + 11 := by rw [hcd1]; omega
  have h4' : 4 ≤ (S + 2) ^ 2 := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ (S + 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  cases hk : nd with
  | const b =>
    rw [hk] at finish hD1 hDh1 hcd1 htag5 hn0
    obtain ⟨τ, eb, sh, cd, ho, hw', hzz, hfr, hst⟩ := cB0_spec cap σ1 hz1 (preD0 ++ natWord 0) restD b
      (by rw [hD1]; simp [PCPPRequestNodeSchema.fields, List.append_assoc]) (by rw [hDh1]; simp [PCPPRequestNodeSchema.fields])
      out hout1 hcl1 (n := q) (by omega)
    exact finish 0 (by simp [PCPPRequestNodeSchema.fields]) (by norm_num) cB0 rfl τ _ eb (by omega)
      (by rw [sh]; simp [PCPPRequestNodeSchema.fields]) (by rw [cd]; simp [PCPPRequestNodeSchema.fields]) ho hw' hzz
      hfr hst
  | input j =>
    rw [hk] at finish hD1 hDh1 hcd1 htag5 hn0
    have hj : j.val ≤ S := by have := j.isLt; omega
    obtain ⟨τ, eb, sh, cd, ho, hw', hzz, hfr, hst⟩ := cB1_spec cap σ1 hz1 (preD0 ++ natWord 1) restD j.val
      (by rw [hD1]; simp [PCPPRequestNodeSchema.fields, List.append_assoc]) (by rw [hDh1]; simp [PCPPRequestNodeSchema.fields])
      preA restA args (by rw [(hs1 sW (by simp)).1, hA]) (by rw [(hs1 sW (by simp)).2, hAh])
      (by rw [g1 _ (by simp), hL]) fl (by rw [(hs1 sF (by simp)).1, hF]) (by rw [(hs1 sF (by simp)).2, hFh])
      (B.nodes.length - 1) B.output.val (by rw [g1 _ (by simp), hn1]) (by rw [g1 _ (by simp), hob]) S hj hlS hAS hwS
      (by omega) (by have := B.output.isLt; omega) out hout1 hcl1 (n := q)
      (by omega)
    exact finish 1 (by simp [PCPPRequestNodeSchema.fields]) (by norm_num) cB1 rfl τ _ eb le_rfl
      (by rw [sh]; simp [PCPPRequestNodeSchema.fields]) (by rw [cd]; simp [PCPPRequestNodeSchema.fields]) ho hw' hzz
      hfr hst
  | not c =>
    rw [hk] at finish hD1 hDh1 hcd1 htag5 hn0 hw
    have hc : c ≤ S := by simp [BooleanNode.WellFormedAt] at hw; omega
    obtain ⟨τ, eb, sh, cd, ho, hw', hzz, hfr, hst⟩ := cB2_spec cap σ1 hz1 (preD0 ++ natWord 2) restD c
      (by rw [hD1]; simp [PCPPRequestNodeSchema.fields, List.append_assoc]) (by rw [hDh1]; simp [PCPPRequestNodeSchema.fields])
      out hout1 hcl1 (n := q) (by omega)
    rw [hcur1] at ho eb
    exact finish 2 (by simp [PCPPRequestNodeSchema.fields]) (by norm_num) cB2 rfl τ _ eb (br_cost S c c _ hc hc hcur).2
      (by rw [sh]; simp [PCPPRequestNodeSchema.fields]) (by rw [cd]; simp [PCPPRequestNodeSchema.fields]) ho hw' hzz
      hfr hst
  | and l r =>
    rw [hk] at finish hD1 hDh1 hcd1 htag5 hn0 hw
    have hl : l ≤ S := by simp [BooleanNode.WellFormedAt] at hw; omega
    have hr : r ≤ S := by simp [BooleanNode.WellFormedAt] at hw; omega
    obtain ⟨τ, eb, sh, cd, ho, hw', hzz, hfr, hst⟩ := cB34_spec cap 3 (n := q) BooleanNode.and
      (fun x y => by simp [PCPPRequestNodeSchema.fields]) (by norm_num) σ1 hz1 (preD0 ++ natWord 3) restD l r
      (by rw [hD1]; simp [PCPPRequestNodeSchema.fields, List.append_assoc]) (by rw [hDh1]; simp [PCPPRequestNodeSchema.fields])
      out hout1 hcl1 (by omega)
    rw [hcur1] at ho eb
    exact finish 3 (by simp [PCPPRequestNodeSchema.fields]) (by norm_num) (cB34 3) rfl τ _ eb (br_cost S l r _ hl hr hcur).1
      (by rw [sh]; simp [PCPPRequestNodeSchema.fields]) (by rw [cd]; simp [PCPPRequestNodeSchema.fields]) ho hw' hzz
      hfr hst
  | or l r =>
    rw [hk] at finish hD1 hDh1 hcd1 htag5 hn0 hw
    have hl : l ≤ S := by simp [BooleanNode.WellFormedAt] at hw; omega
    have hr : r ≤ S := by simp [BooleanNode.WellFormedAt] at hw; omega
    obtain ⟨τ, eb, sh, cd, ho, hw', hzz, hfr, hst⟩ := cB34_spec cap 4 (n := q) BooleanNode.or
      (fun x y => by simp [PCPPRequestNodeSchema.fields]) (by norm_num) σ1 hz1 (preD0 ++ natWord 4) restD l r
      (by rw [hD1]; simp [PCPPRequestNodeSchema.fields, List.append_assoc]) (by rw [hDh1]; simp [PCPPRequestNodeSchema.fields])
      out hout1 hcl1 (by omega)
    rw [hcur1] at ho eb
    exact finish 4 (by simp [PCPPRequestNodeSchema.fields]) (by norm_num) (cB34 4) rfl τ _ eb (br_cost S l r _ hl hr hcur).1
      (by rw [sh]; simp [PCPPRequestNodeSchema.fields]) (by rw [cd]; simp [PCPPRequestNodeSchema.fields]) ho hw' hzz
      hfr hst

end NearCubicGates.Close.Succinct.SubstMachine
