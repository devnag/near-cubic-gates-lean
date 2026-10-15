import Proof.Gates.Succinct.SubstitutionOracleNode

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

/-- The header of `D_B`'s descriptor. -/
def hdrD (o : OracleOutput) (B : BooleanCircuit q) : List Bool := natWord q ++ natWord (szv o B + 1 + (q - (szv o B + 1)))

/-- The registers during the emission loop, after `i` nodes of `C`. -/
def VM (o : OracleOutput) (B : BooleanCircuit q) (i : ℕ) : HReg → ℕ := fun u =>
  if u = .cdW then lenC o i else if u = .cur then (accI B o.circuit i).1.length else
  if u = .iC then o.circuit.nodes.length - i else
  if u = .w 7 then 2 * (hdrD o B ++ (accI B o.circuit i).1.flatMap PCPPRequestNodeSchema.native).length else
  V3 o B u

/-- **The emission loop's invariant** after `i` nodes of `C`. -/
def MInv (o : OracleOutput) (B : BooleanCircuit q) (i : ℕ) (τ : WState 4 nrH) : Prop :=
  τ.st sW = o.word ∧ τ.sh sW = pC o + lenC o i ∧ τ.st sD = PCPPNative.descriptor B ∧ τ.sh sD = pB B ∧
    τ.st sF = ofl o.circuit ∧ τ.sh sF = 0 ∧ τ.st sL = natWord o.ell ∧ τ.sh sL = 0 ∧
    OutOK τ (hdrD o B ++ (accI B o.circuit i).1.flatMap PCPPRequestNodeSchema.native) ∧ WClean τ ∧
    RV τ (VM o B i) ∧ τ.cell = false

theorem VM_zl (o : OracleOutput) (B : BooleanCircuit q) (i : ℕ) (u : HReg) (hu : u ∈ zl) : VM o B i u = 0 := by
  simp only [zl, List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [VM, V3, V2, V1]

theorem VM_f (o : OracleOutput) (B : BooleanCircuit q) (i : ℕ) (r : FReg) : VM o B i (.f r) = 0 := by
  simp [VM, V3, V2, V1]

theorem MInv.cbz {o : OracleOutput} {B : BooleanCircuit q} {i : ℕ} {τ : WState 4 nrH} (h : MInv o B i τ) : CBZ τ :=
  ⟨fun r => by rw [h.2.2.2.2.2.2.2.2.2.2.1]; exact VM_f o B i r,
    fun u hu => by rw [h.2.2.2.2.2.2.2.2.2.2.1]; exact VM_zl o B i u hu⟩

theorem accI_prefix (B : BooleanCircuit q) (C : OracleCircuit ℓ ℓ) :
    ∀ i j, i ≤ j → j ≤ C.nodes.length → (accI B C i).1 <+: (accI B C j).1
  | i, 0, h, _ => by have : i = 0 := by omega
                     subst this; exact List.prefix_refl _
  | i, j + 1, h, hj => by
    rcases Nat.lt_or_ge i (j + 1) with hlt | hge
    · have ih := accI_prefix B C i j (by omega) (by omega)
      rw [accI_succ B C j (by omega)]
      refine ih.trans ?_
      cases C.nodes[j] <;> simp [substStepG]
    · have : i = j + 1 := by omega
      subst this; exact List.prefix_refl _

/-- The full descriptor of `D_B` (what the output stream finally holds, without its frame). -/
noncomputable def fullD (o : OracleOutput) (B : BooleanCircuit q) : List Bool :=
  PCPPNative.descriptor (substCircuit o.circuit B).padToArity

theorem out_le (o : OracleOutput) (B : BooleanCircuit q) (i : ℕ) (hi : i ≤ o.circuit.nodes.length) :
    (hdrD o B ++ (accI B o.circuit i).1.flatMap PCPPRequestNodeSchema.native).length ≤ (fullD o B).length := by
  unfold fullD
  rw [descriptor_D B o.circuit, szv_eq]
  have hp := accI_prefix B o.circuit i o.circuit.nodes.length hi le_rfl
  obtain ⟨t, ht⟩ := hp
  rw [← ht]
  simp only [hdrD, List.flatMap_append, List.length_append]
  omega

/-- The per-node cost class of the emission loop. -/
def nIter (S : ℕ) : ℕ := oIter S + cIter S + 1000000

/-- The register capacity of one substitution. -/
noncomputable def capH (o : OracleOutput) (B : BooleanCircuit q) : ℕ :=
  2 * (fullD o B).length + 10000 * (sizeS o B + 2) ^ 4

theorem szv_le (o : OracleOutput) (B : BooleanCircuit q) : szv o B ≤ (sizeS o B + 2) ^ 2 := by
  obtain ⟨hzC, hzB, -⟩ := sizes_le o B
  have hk := kOf_le o
  unfold szv
  have : kOf o.circuit o.circuit.nodes.length * (B.nodes.length - 1) ≤ sizeS o B * sizeS o B :=
    Nat.mul_le_mul (by omega) (by omega)
  nlinarith

theorem cur_le (o : OracleOutput) (B : BooleanCircuit q) (i : ℕ) (hi : i ≤ o.circuit.nodes.length) :
    (accI B o.circuit i).1.length ≤ (sizeS o B + 2) ^ 2 := by
  have := (accI_prefix B o.circuit i _ hi le_rfl).length_le
  rw [szv_eq] at this; exact this.trans (szv_le o B)

/-- The kind lemmas' common end: node `i`'s image `E` appended. -/
theorem nodeFinish (_cap : ℕ) (o : OracleOutput) (B : BooleanCircuit q) (i : ℕ) (hi : i < o.circuit.nodes.length)
    (τ : WState 4 nrH) (hI : MInv o B i τ) (σ1 τ' : WState 4 nrH) (rest : List Bool) (E : List (BooleanNode q))
    (hrest : oracleNodeWord o.circuit.nodes[i] = natWord (otag o.circuit.nodes[i]) ++ rest)
    (hE : (accI B o.circuit (i + 1)).1 = (accI B o.circuit i).1 ++ E)
    (h1st : ∀ j, j ≠ sW → σ1.st j = τ.st j ∧ σ1.sh j = τ.sh j) (h1W : σ1.st sW = τ.st sW)
    (h1sh : σ1.sh sW = τ.sh sW + (natWord (otag o.circuit.nodes[i])).length)
    (h1v : ∀ u, u ∉ [HReg.cdW, .iC] → σ1.val (regH u) = τ.val (regH u))
    (h1cd : σ1.val (regH .cdW) = τ.val (regH .cdW) + (natWord (otag o.circuit.nodes[i])).length)
    (h1iC : σ1.val (regH .iC) = o.circuit.nodes.length - i - 1) (h1c : σ1.cell = τ.cell)
    (hsh : τ'.sh sW = σ1.sh sW + rest.length) (hcd : τ'.val (regH .cdW) = σ1.val (regH .cdW) + rest.length)
    (hcur : τ'.val (regH .cur) = σ1.val (regH .cur) + E.length)
    (hout : OutOK τ' (hdrD o B ++ (accI B o.circuit i).1.flatMap PCPPRequestNodeSchema.native ++
      E.flatMap PCPPRequestNodeSchema.native)) (hw : WClean τ')
    (hfr : Fr σ1 τ' [sW, sO] [.cdW, .w 7, .cur]) (hst : τ'.st sW = σ1.st sW) :
    MInv o B (i + 1) τ' ∧ τ'.val (regH .iC) = o.circuit.nodes.length - i - 1 := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ := hI
  have hv : ∀ u, τ.val (regH u) = VM o B i u := a11
  have hls := lenC_succ o i hi
  have hwl : (oracleNodeWord o.circuit.nodes[i]).length = (natWord (otag o.circuit.nodes[i])).length + rest.length := by
    rw [hrest, List.length_append]
  have hout' : OutOK τ' (hdrD o B ++ (accI B o.circuit (i + 1)).1.flatMap PCPPRequestNodeSchema.native) := by
    rw [hE, List.flatMap_append, ← List.append_assoc]; exact hout
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hout', hw, ?_, ?_⟩, ?_⟩
  · rw [hst, h1W, a1]
  · rw [hsh, h1sh, a2, hls, hwl]; ring
  · rw [(hfr.s (by simp)).1, (h1st sD (by simp)).1, a3]
  · rw [(hfr.s (by simp)).2, (h1st sD (by simp)).2, a4]
  · rw [(hfr.s (by simp)).1, (h1st sF (by simp)).1, a5]
  · rw [(hfr.s (by simp)).2, (h1st sF (by simp)).2, a6]
  · rw [(hfr.s (by simp)).1, (h1st sL (by simp)).1, a7]
  · rw [(hfr.s (by simp)).2, (h1st sL (by simp)).2, a8]
  · intro u
    by_cases hc : u = .cdW
    · subst hc; rw [hcd, h1cd, hv]; simp [VM, hls, hwl]; ring
    · by_cases hu : u = .cur
      · subst hu; rw [hcur, h1v _ (by simp), hv]; simp [VM, hE]
      · by_cases hw7 : u = .w 7
        · subst hw7; rw [hout'.2.2]; simp [VM]
        · by_cases hiC : u = .iC
          · subst hiC; rw [hfr.v (by simp), h1iC]; simp [VM]; omega
          · rw [hfr.v (by simp [hc, hu, hw7]), h1v u (by simp [hc, hiC]), hv]
            simp [VM, hc, hu, hw7, hiC]
  · rw [hfr.2.2, h1c, a12]
  · rw [hfr.v (by simp), h1iC]

/-- The state after the tag of node `i` of `C` is read and the tag register cleared. -/
structure KCtx (cap : ℕ) (o : OracleOutput) (B : BooleanCircuit q) (i : ℕ) (τ σ1 : WState 4 nrH) : Prop where
  hi : i < o.circuit.nodes.length
  hI : MInv o B i τ
  st : ∀ j, j ≠ sW → σ1.st j = τ.st j ∧ σ1.sh j = τ.sh j
  W : σ1.st sW = τ.st sW
  sh : σ1.sh sW = τ.sh sW + (natWord (otag (o.circuit.nodes[i]'hi))).length
  v : ∀ u, u ∉ [HReg.cdW, .iC] → σ1.val (regH u) = τ.val (regH u)
  cd : σ1.val (regH .cdW) = τ.val (regH .cdW) + (natWord (otag (o.circuit.nodes[i]'hi))).length
  iC : σ1.val (regH .iC) = o.circuit.nodes.length - i - 1
  c : σ1.cell = τ.cell
  cap : capH o B ≤ cap

/-- The rest of a node word after its tag. -/
def orest : OracleNode ℓ ℓ → List Bool
  | .const b => natWord b.toNat ++ natWord 0
  | .input j => natWord j.val ++ natWord 0
  | .not c => natWord c ++ natWord 0
  | .and l r => natWord l ++ natWord r
  | .or l r => natWord l ++ natWord r
  | .oracle args => (List.ofFn args).flatMap natWord

theorem node_word (nd : OracleNode ℓ ℓ) : oracleNodeWord nd = natWord (otag nd) ++ orest nd := by
  cases nd with
  | oracle args =>
    simp only [oracleNodeWord, otag, orest, List.flatMap, List.map_ofFn]; rfl
  | _ => simp [oracleNodeWord, otag, orest]

/-- The state facts a kind lemma needs, from the context. -/
theorem KCtx.facts {cap : ℕ} {o : OracleOutput} {B : BooleanCircuit q} {i : ℕ} {τ σ1 : WState 4 nrH}
    (h : KCtx cap o B i τ σ1) :
    σ1.st sW = (natWord o.ell ++ natWord o.circuit.nodes.length ++ (o.circuit.nodes.take i).flatMap oracleNodeWord ++
        natWord (otag (o.circuit.nodes[i]'h.hi))) ++ orest (o.circuit.nodes[i]'h.hi) ++
      ((o.circuit.nodes.drop (i + 1)).flatMap oracleNodeWord ++ natWord o.circuit.output.val) ∧
    σ1.sh sW = (natWord o.ell ++ natWord o.circuit.nodes.length ++ (o.circuit.nodes.take i).flatMap oracleNodeWord ++
        natWord (otag (o.circuit.nodes[i]'h.hi))).length ∧
    σ1.st sF = ofl o.circuit ∧ σ1.sh sF = 0 ∧ σ1.st sD = PCPPNative.descriptor B ∧ σ1.sh sD = pB B ∧
    σ1.st sL = natWord o.ell ∧ σ1.sh sL = 0 ∧
    OutOK σ1 (hdrD o B ++ (accI B o.circuit i).1.flatMap PCPPRequestNodeSchema.native) ∧ WClean σ1 ∧ CBZ σ1 ∧
    (∀ u, u ∉ [HReg.cdW, .iC] → σ1.val (regH u) = VM o B i u) := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ := h.hI
  have hv : ∀ u, u ∉ [HReg.cdW, .iC] → σ1.val (regH u) = VM o B i u := fun u hu => by rw [h.v u hu]; exact a11 u
  have hsplit := word_split o i h.hi
  rw [node_word] at hsplit
  refine ⟨by rw [h.W, a1, hsplit]; simp only [List.append_assoc], ?_, by rw [(h.st sF (by simp)).1, a5],
    by rw [(h.st sF (by simp)).2, a6], by rw [(h.st sD (by simp)).1, a3], by rw [(h.st sD (by simp)).2, a4],
    by rw [(h.st sL (by simp)).1, a7], by rw [(h.st sL (by simp)).2, a8], ?_, ?_, ?_, hv⟩
  · rw [h.sh, a2]; simp only [pC, lenC, List.length_append]
  · exact ⟨by rw [(h.st sO (by simp)).1]; exact a9.1, by rw [(h.st sO (by simp)).2]; exact a9.2.1,
      by rw [h.v _ (by simp)]; exact a9.2.2⟩
  · exact ⟨fun j hj => by rw [h.v _ (by simp)]; exact a10.1 j hj, by rw [h.v _ (by simp)]; exact a10.2⟩
  · exact ⟨fun r => by rw [hv _ (by simp)]; exact VM_f o B i r,
      fun u hu => by rw [hv u (by intro m; simp at m; rcases m with rfl | rfl <;> simp [zl] at hu)]
                     exact VM_zl o B i u hu⟩

theorem capH_ge (o : OracleOutput) (B : BooleanCircuit q) : 10000 * (sizeS o B + 2) ^ 4 ≤ capH o B := by
  unfold capH; omega

theorem sq4 (S : ℕ) : (S + 2) ^ 2 ≤ (S + 2) ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)

/-- **A plain node of `C`, then `cur += 1`.** -/
theorem kindWrap {cap : ℕ} {o : OracleOutput} {B : BooleanCircuit q} {i : ℕ} {τ σ1 : WState 4 nrH}
    (h : KCtx cap o B i τ σ1) (P : WM 4 nrH) (τ2 : WState 4 nrH) (n : ℕ) (e2 : WExec cap P σ1 τ2 n)
    (E : List (BooleanNode q)) (hEl : E.length = 1)
    (hE : (accI B o.circuit (i + 1)).1 = (accI B o.circuit i).1 ++ E)
    (hsh2 : τ2.sh sW = σ1.sh sW + (orest (o.circuit.nodes[i]'h.hi)).length)
    (hcd2 : τ2.val (regH .cdW) = σ1.val (regH .cdW) + (orest (o.circuit.nodes[i]'h.hi)).length)
    (hout2 : OutOK τ2 (hdrD o B ++ (accI B o.circuit i).1.flatMap PCPPRequestNodeSchema.native ++
      E.flatMap PCPPRequestNodeSchema.native)) (hw2 : WClean τ2)
    (hf2 : Fr σ1 τ2 [sW, sO] [.cdW, .w 7]) (hst2 : τ2.st sW = σ1.st sW) :
    ∃ τ3, WExec cap (.seq P (.inc (regH .cur))) σ1 τ3 (n + 4) ∧ MInv o B (i + 1) τ3 ∧
      τ3.val (regH .iC) = o.circuit.nodes.length - i - 1 := by
  have F := h.facts
  have hc2 : τ2.val (regH .cur) = (accI B o.circuit i).1.length := by
    rw [hf2.v (by simp), F.2.2.2.2.2.2.2.2.2.2.2 _ (by simp)]; simp [VM]
  have hcl := cur_le o B i h.hi.le
  have hcp := capH_ge o B
  have h4 := sq4 (sizeS o B)
  have h5 : 1 ≤ (sizeS o B + 2) ^ 4 := Nat.one_le_pow _ _ (by omega)
  have e3 := WExec.inc (cap := cap) (regH .cur) τ2 (by rw [hc2]; have := h.cap; omega)
  refine ⟨_, WExec.seq e2 e3, nodeFinish cap o B i h.hi τ h.hI σ1 _ (orest (o.circuit.nodes[i]'h.hi)) E
    (node_word _) hE h.st h.W h.sh h.v h.cd h.iC h.c (by simp [hsh2]) (by simp [hcd2])
    (by simp [hc2, hEl, F.2.2.2.2.2.2.2.2.2.2.2 _ (show HReg.cur ∉ [HReg.cdW, .iC] by simp), VM])
    ⟨by simp [hout2.1], by simp [hout2.2.1], by simp [Function.update_apply, hout2.2.2]⟩
    ⟨fun j hj => by simp [Function.update_apply, hw2.1 j hj], by simp [Function.update_apply, hw2.2]⟩
    ((hf2.trans' (fr_setv τ2 .cur _)).mono (by simp) (by simp)) (by simp [hst2])⟩

theorem KCtx.cd_le {cap : ℕ} {o : OracleOutput} {B : BooleanCircuit q} {i : ℕ} {τ σ1 : WState 4 nrH}
    (h : KCtx cap o B i τ σ1) :
    σ1.val (regH .cdW) + (orest (o.circuit.nodes[i]'h.hi)).length + pC o ≤ o.word.length := by
  have := lenC_le o (i + 1)
  rw [lenC_succ o i h.hi, node_word, List.length_append] at this
  have hτ : τ.val (regH .cdW) = lenC o i := by rw [h.hI.2.2.2.2.2.2.2.2.2.2.1]; simp [VM]
  rw [h.cd, hτ]; omega

theorem KCtx.cap_le {cap : ℕ} {o : OracleOutput} {B : BooleanCircuit q} {i : ℕ} {τ σ1 : WState 4 nrH}
    (h : KCtx cap o B i τ σ1) :
    σ1.val (regH .cdW) + 2 * (hdrD o B ++ (accI B o.circuit i).1.flatMap PCPPRequestNodeSchema.native).length +
      (PCPPNative.descriptor B).length + 2 * (sizeS o B * (12 * (sizeS o B + 2) ^ 2 + 40)) +
      2000 * (sizeS o B + 2) ^ 2 ≤ cap := by
  have h1 := h.cd_le
  have h2 := out_le o B i h.hi.le
  have h3 := h.cap
  have h4 := sq4 (sizeS o B)
  obtain ⟨hzC, hzB, hzq, hwh, hlb, hdl, hnCw⟩ := sizes_le o B
  have hS : sizeS o B = o.word.length + (PCPPNative.descriptor B).length + q + 1 := rfl
  have h5 : sizeS o B * (12 * (sizeS o B + 2) ^ 2 + 40) ≤ 100 * (sizeS o B + 2) ^ 4 := by
    have hX : sizeS o B + 2 ≤ (sizeS o B + 2) ^ 2 := Nat.le_self_pow (by norm_num) _
    have : (sizeS o B + 2) ^ 4 = (sizeS o B + 2) ^ 2 * (sizeS o B + 2) ^ 2 := by ring
    nlinarith
  have h6 : sizeS o B + 2 ≤ (sizeS o B + 2) ^ 4 := Nat.le_self_pow (by norm_num) _
  unfold capH at h3
  omega

/-- **`C`'s `const b`.** -/
theorem kind0 {cap : ℕ} {o : OracleOutput} {B : BooleanCircuit q} {i : ℕ} {τ σ1 : WState 4 nrH}
    (h : KCtx cap o B i τ σ1) (b : Bool) (hk : o.circuit.nodes[i]'h.hi = .const b) :
    ∃ τ3, WExec cap nC0 σ1 τ3 (200004) ∧ MInv o B (i + 1) τ3 ∧
      τ3.val (regH .iC) = o.circuit.nodes.length - i - 1 := by
  have F := h.facts
  have hc := h.cap_le
  rw [hk] at F
  obtain ⟨τ2, e2, sh2, cd2, o2, w2, z2, f2, st2⟩ := nC0b_spec cap σ1 F.2.2.2.2.2.2.2.2.2.2.1
    (natWord o.ell ++ natWord o.circuit.nodes.length ++ (o.circuit.nodes.take i).flatMap oracleNodeWord ++ natWord 0)
    ((o.circuit.nodes.drop (i + 1)).flatMap oracleNodeWord ++ natWord o.circuit.output.val) b
    (by rw [F.1]; simp [otag, orest, List.append_assoc]) (by rw [F.2.1]; simp [otag])
    (hdrD o B ++ (accI B o.circuit i).1.flatMap PCPPRequestNodeSchema.native) F.2.2.2.2.2.2.2.2.1
    F.2.2.2.2.2.2.2.2.2.1 (n := q) (by have : 1 ≤ (sizeS o B + 2) ^ 2 := Nat.one_le_pow _ _ (by omega)
                                       omega)
  have hE : (accI B o.circuit (i + 1)).1 = (accI B o.circuit i).1 ++ [BooleanNode.const b] := by
    rw [accI_succ B o.circuit i h.hi]; simp [hk, substStepG]
  exact kindWrap h nC0b τ2 200000 e2 [BooleanNode.const b] rfl hE
    (by rw [sh2, F.2.1]; simp only [hk, orest, otag, List.length_append]; omega)
    (by rw [cd2]; simp only [hk, orest, List.length_append]; omega)
    (by simpa using o2) w2 f2 st2

theorem KCtx.vals {cap : ℕ} {o : OracleOutput} {B : BooleanCircuit q} {i : ℕ} {τ σ1 : WState 4 nrH}
    (h : KCtx cap o B i τ σ1) :
    σ1.val (regH .nB1) = B.nodes.length - 1 ∧ σ1.val (regH .oB) = B.output.val ∧ σ1.val (regH .p2) = 0 ∧
      σ1.val (regH .q) = q ∧ σ1.val (regH .bq) = hc q + 1 ∧ σ1.val (regH .nB) = B.nodes.length ∧
      σ1.val (regH .cur) = (accI B o.circuit i).1.length ∧ σ1.val (regH .g) = 0 ∧ σ1.val (regH .tagB) = 0 ∧
      σ1.val (regH .tC) = 0 ∧ σ1.val (regH .cdB) = 0 ∧ σ1.val (regH .L) = 0 ∧ σ1.val (regH .cdL) = 0 := by
  have hv := h.facts.2.2.2.2.2.2.2.2.2.2.2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [hv _ (by simp)] <;> simp [VM, V3, V2, V1]

theorem refC (o : OracleOutput) (B : BooleanCircuit q) (i c : ℕ) (hi : i < o.circuit.nodes.length) (hc : c < i) :
    ref (accI B o.circuit i).2 c = posF (ofl o.circuit) c (B.nodes.length - 1) B.output.val := by
  rw [ref_accI B o.circuit i hi.le c hc, posM_posF B o.circuit c (by omega)]

/-- **`C`'s `not c`.** -/
theorem kind2 {cap : ℕ} {o : OracleOutput} {B : BooleanCircuit q} {i : ℕ} {τ σ1 : WState 4 nrH}
    (h : KCtx cap o B i τ σ1) (c : ℕ) (hk : o.circuit.nodes[i]'h.hi = .not c) :
    ∃ τ3, WExec cap nC2 σ1 τ3 (cIter (sizeS o B) + 4) ∧ MInv o B (i + 1) τ3 ∧
      τ3.val (regH .iC) = o.circuit.nodes.length - i - 1 := by
  have F := h.facts
  have hc := h.cap_le
  have V := h.vals
  have hi := h.hi
  have hw := o.circuit.wellFormed ⟨i, h.hi⟩
  simp only [List.get_eq_getElem, hk, OracleNode.WellFormedAt] at hw
  obtain ⟨hzC, hzB, hzq, hwh, hlb, hdl, hnCw⟩ := sizes_le o B
  have hoB := B.output.isLt
  rw [hk] at F
  obtain ⟨τ2, e2, sh2, cd2, o2, w2, z2, f2, st2⟩ := nC2b_spec cap σ1 F.2.2.2.2.2.2.2.2.2.2.1
    (natWord o.ell ++ natWord o.circuit.nodes.length ++ (o.circuit.nodes.take i).flatMap oracleNodeWord ++ natWord 2)
    ((o.circuit.nodes.drop (i + 1)).flatMap oracleNodeWord ++ natWord o.circuit.output.val) c
    (by rw [F.1]; simp [otag, orest, List.append_assoc]) (by rw [F.2.1]; simp [otag])
    (ofl o.circuit) F.2.2.1 F.2.2.2.1 (sizeS o B) (by omega) (by rw [V.1]; omega) (by rw [V.2.1]; omega)
    (hdrD o B ++ (accI B o.circuit i).1.flatMap PCPPRequestNodeSchema.native) F.2.2.2.2.2.2.2.2.1
    F.2.2.2.2.2.2.2.2.2.1 (n := q) (by omega)
  rw [V.1, V.2.1, ← refC o B i c h.hi hw] at o2
  have hE : (accI B o.circuit (i + 1)).1 = (accI B o.circuit i).1 ++ [BooleanNode.not (ref (accI B o.circuit i).2 c)] := by
    rw [accI_succ B o.circuit i h.hi]; simp [hk, substStepG]
  exact kindWrap h nC2b τ2 _ e2 [BooleanNode.not (ref (accI B o.circuit i).2 c)] rfl hE
    (by rw [sh2, F.2.1]; simp only [hk, orest, otag, List.length_append]; omega)
    (by rw [cd2]; simp only [hk, orest, List.length_append]; omega)
    (by simpa using o2) w2 f2 st2

/-- **`C`'s `and l r` / `or l r`.** -/
theorem kind34 {cap : ℕ} {o : OracleOutput} {B : BooleanCircuit q} {i : ℕ} {τ σ1 : WState 4 nrH}
    (h : KCtx cap o B i τ σ1) (tg : ℕ) (mk : ℕ → ℕ → BooleanNode q)
    (hmk : ∀ x y, PCPPRequestNodeSchema.fields (mk x y) 0 = tg ∧ PCPPRequestNodeSchema.fields (mk x y) 1 = x ∧
      PCPPRequestNodeSchema.fields (mk x y) 2 = y) (htg : tg ≤ 4) (l r : ℕ)
    (hword : orest (o.circuit.nodes[i]'h.hi) = natWord l ++ natWord r)
    (hlr : l < i ∧ r < i)
    (hstep : (accI B o.circuit (i + 1)).1 = (accI B o.circuit i).1 ++
      [mk (ref (accI B o.circuit i).2 l) (ref (accI B o.circuit i).2 r)]) :
    ∃ τ3, WExec cap (nC34 tg) σ1 τ3 (cIter (sizeS o B) + 4) ∧ MInv o B (i + 1) τ3 ∧
      τ3.val (regH .iC) = o.circuit.nodes.length - i - 1 := by
  have F := h.facts
  have hc := h.cap_le
  have V := h.vals
  have hi := h.hi
  obtain ⟨hzC, hzB, hzq, hwh, hlb, hdl, hnCw⟩ := sizes_le o B
  have hoB := B.output.isLt
  obtain ⟨τ2, e2, sh2, cd2, o2, w2, z2, p2, f2, st2⟩ := nC34b_spec cap tg mk hmk htg σ1 F.2.2.2.2.2.2.2.2.2.2.1 V.2.2.1
    (natWord o.ell ++ natWord o.circuit.nodes.length ++ (o.circuit.nodes.take i).flatMap oracleNodeWord ++
      natWord (otag (o.circuit.nodes[i]'h.hi)))
    ((o.circuit.nodes.drop (i + 1)).flatMap oracleNodeWord ++ natWord o.circuit.output.val) l r
    (by rw [F.1, hword]; simp [List.append_assoc]) F.2.1
    (ofl o.circuit) F.2.2.1 F.2.2.2.1 (sizeS o B) (by omega) (by omega) (by rw [V.1]; omega) (by rw [V.2.1]; omega)
    (hdrD o B ++ (accI B o.circuit i).1.flatMap PCPPRequestNodeSchema.native) F.2.2.2.2.2.2.2.2.1
    F.2.2.2.2.2.2.2.2.2.1 (by omega)
  rw [V.1, V.2.1, ← refC o B i l h.hi hlr.1, ← refC o B i r h.hi hlr.2] at o2
  exact kindWrap h (nC34b tg) τ2 _ e2 _ rfl hstep
    (by rw [sh2, F.2.1, hword]; simp only [List.length_append]; omega)
    (by rw [cd2, hword]; simp only [List.length_append]; omega)
    (by simpa using o2) w2 f2 st2

theorem copy_map (B : BooleanCircuit q) (C : OracleCircuit ℓ ℓ) (i : ℕ) (hi : i < C.nodes.length)
    (args : Fin ℓ → ℕ) (hargs : ∀ j, args j < i) :
    copyNodesFrom (accI B C i).1.length ((List.ofFn fun j => ref (accI B C i).2 (args j)) ++ []) 0 B.nodes =
      B.nodes.map (cpNode (ofl C) (List.ofFn args) (B.nodes.length - 1) B.output.val (accI B C i).1.length) := by
  apply List.ext_getElem (by simp [copyNodesFrom_length])
  intro t h1 h2
  rw [copyNodesFrom_getElem, List.getElem_map, cpNode_eq B C i hi args hargs t (by simpa using h2)]
  simp

/-- **An oracle gate of `C`.** -/
theorem kind5 {cap : ℕ} {o : OracleOutput} {B : BooleanCircuit q} {i : ℕ} {τ σ1 : WState 4 nrH}
    (h : KCtx cap o B i τ σ1) (args : Fin o.ell → ℕ) (hk : o.circuit.nodes[i]'h.hi = .oracle args) :
    ∃ τ3, WExec cap nC5 σ1 τ3 (oIter (sizeS o B)) ∧ MInv o B (i + 1) τ3 ∧
      τ3.val (regH .iC) = o.circuit.nodes.length - i - 1 := by
  have F := h.facts
  have hc := h.cap_le
  have V := h.vals
  have hi := h.hi
  have hw := o.circuit.wellFormed ⟨i, h.hi⟩
  simp only [List.get_eq_getElem, hk, OracleNode.WellFormedAt] at hw
  obtain ⟨hzC, hzB, hzq, hwh, hlb, hdl, hnCw⟩ := sizes_le o B
  have hS : sizeS o B = o.word.length + (PCPPNative.descriptor B).length + q + 1 := rfl
  have hcd := h.cd_le
  rw [hk] at F hcd
  simp only [orest] at F hcd
  have hcl := cur_le o B i h.hi.le
  obtain ⟨τ2, e2, o2, sh2, cd2, cur2, w2, z2, f2, st2⟩ := nC5_spec cap B σ1 F.2.2.2.2.2.2.2.2.2.2.1 V.2.2.2.2.2.2.2.2.1
    V.2.2.2.2.2.2.2.2.2.1 V.2.2.2.2.2.2.2.2.2.2.1 V.2.2.2.2.2.2.2.2.2.2.2.1 V.2.2.2.2.2.2.2.2.2.2.2.2
    F.2.2.2.2.1 F.2.2.2.2.2.1 o.ell F.2.2.2.2.2.2.1 F.2.2.2.2.2.2.2.1
    (natWord o.ell ++ natWord o.circuit.nodes.length ++ (o.circuit.nodes.take i).flatMap oracleNodeWord ++ natWord 5)
    ((o.circuit.nodes.drop (i + 1)).flatMap oracleNodeWord ++ natWord o.circuit.output.val) (List.ofFn args)
    (by simp) (by rw [F.1]; simp [otag, List.append_assoc]) (by rw [F.2.1]; simp [otag])
    (ofl o.circuit) F.2.2.1 F.2.2.2.1 V.2.2.2.2.2.1 V.1 V.2.1 (sizeS o B) (by omega) (by omega)
    (fun x hx => by simp only [List.mem_ofFn] at hx; obtain ⟨j, rfl⟩ := hx; have := hw j; omega)
    (by omega) (by omega) (by rw [V.2.2.2.2.2.2.1]; exact hcl)
    (hdrD o B ++ (accI B o.circuit i).1.flatMap PCPPRequestNodeSchema.native) F.2.2.2.2.2.2.2.2.1
    F.2.2.2.2.2.2.2.2.2.1 (by omega)
  rw [V.2.2.2.2.2.2.1] at o2
  have hE : (accI B o.circuit (i + 1)).1 = (accI B o.circuit i).1 ++
      B.nodes.map (cpNode (ofl o.circuit) (List.ofFn args) (B.nodes.length - 1) B.output.val
        (accI B o.circuit i).1.length) := by
    rw [accI_succ B o.circuit i h.hi, ← copy_map B o.circuit i h.hi args hw]
    simp [hk, substStepG]
  exact ⟨τ2, e2, nodeFinish cap o B i h.hi τ h.hI σ1 τ2 _ _ (node_word _) hE h.st h.W h.sh h.v h.cd h.iC h.c
    (by rw [sh2, F.2.1, hk]; simp only [orest, otag, List.length_append])
    (by rw [cd2, hk]; simp only [orest]) (by rw [cur2]; simp)
    (by simpa using o2) w2 f2 st2⟩

end NearCubicGates.Close.Succinct.SubstMachine
