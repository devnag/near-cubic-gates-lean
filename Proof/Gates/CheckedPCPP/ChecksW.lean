import Proof.Gates.CheckedPCPP.NodeEmit
import Proof.Gates.CheckedPCPP.CheckedSem
import Proof.Gates.CheckedPCPP.MatSem
import Proof.Gates.WordPrograms.Hoare

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.CheckedPCPP.ChecksW

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.RepairOrdinary.Streaming NearCubicWires.SourceInterfaces
open NearCubicGates.PublishedSources.PCPP NearCubicGates.Close.Gadget NearCubicGates.Close.WordPrograms
open NearCubicGates.Close.CheckedPCPP.NodeEmit

/-! ## The parity chain of one row, column by column -/

section Sem
variable (E : LinearCodeFamily) (q : ℕ)

/-- The support elements of row `j` among the first `i` columns, as input coordinates of the checked circuit. -/
def colList (j : Fin (E.length q)) (i : ℕ) : List (Fin (q + E.length q)) :=
  (((List.finRange q).take i).filter (· ∈ E.support q j)).map (Fin.castAdd (E.length q))

theorem colList_zero (j : Fin (E.length q)) : colList E q j 0 = [] := by simp [colList]

theorem colList_succ (j : Fin (E.length q)) (i : ℕ) (hi : i < q) :
    colList E q j (i + 1) = colList E q j i ++
      (if (⟨i, hi⟩ : Fin q) ∈ E.support q j then [Fin.castAdd (E.length q) ⟨i, hi⟩] else []) := by
  unfold colList
  rw [take_succ_finRange q i hi, List.filter_append, List.map_append]
  congr 1
  by_cases h : (⟨i, hi⟩ : Fin q) ∈ E.support q j <;> simp [h]

theorem colList_full (j : Fin (E.length q)) :
    colList E q j q = (canonList (E.support q j)).map (Fin.castAdd (E.length q)) := by
  unfold colList canonList
  rw [List.take_of_length_le (by simp)]

theorem colList_length_le (j : Fin (E.length q)) (i : ℕ) : (colList E q j i).length ≤ i := by
  unfold colList
  rw [List.length_map]
  exact (List.length_filter_le _ _).trans (by simp)

/-- The parity-chain nodes of row `j` after the first `i` columns (the constant at `k0`). -/
def pfx (j : Fin (E.length q)) (k0 i : ℕ) : List (BooleanNode (q + E.length q)) × ℕ :=
  parityFromNodes (k0 + 1) (colList E q j i) k0

theorem pfx_succ_mem (j : Fin (E.length q)) (k0 i : ℕ) (hi : i < q) (hm : (⟨i, hi⟩ : Fin q) ∈ E.support q j) :
    pfx E q j k0 (i + 1) = ((pfx E q j k0 i).1 ++ ([.input (Fin.castAdd (E.length q) ⟨i, hi⟩)] ++
      xorNodes (k0 + 1 + 5 * (colList E q j i).length + 1) (pfx E q j k0 i).2 (k0 + 1 + 5 * (colList E q j i).length)),
      k0 + 1 + 5 * (colList E q j i).length + 4) := by
  unfold pfx
  rw [colList_succ E q j i hi, if_pos hm, parityFromNodes_append, parityFromNodes_single]

theorem pfx_succ_nmem (j : Fin (E.length q)) (k0 i : ℕ) (hi : i < q) (hm : (⟨i, hi⟩ : Fin q) ∉ E.support q j) :
    pfx E q j k0 (i + 1) = pfx E q j k0 i := by
  unfold pfx
  rw [colList_succ E q j i hi, if_neg hm, List.append_nil]

theorem colList_succ_length (j : Fin (E.length q)) (i : ℕ) (hi : i < q) :
    (colList E q j (i + 1)).length =
      (colList E q j i).length + (if (⟨i, hi⟩ : Fin q) ∈ E.support q j then 1 else 0) := by
  rw [colList_succ E q j i hi]
  by_cases h : (⟨i, hi⟩ : Fin q) ∈ E.support q j <;> simp [h]

end Sem

/-! ## Byte bounds -/

theorem natWord_len (x : ℕ) : (natWord x).length = 2 * natBitLength x + 1 := by
  simp only [natWord, WilliamsPublishedForm.framedNatBits, List.length_append, List.length_replicate,
    List.length_cons, WilliamsPublishedForm.fixedWidthNatBits, List.length_ofFn]
  omega

theorem native_len_le {n : ℕ} (nd : BooleanNode n) (V : ℕ) (hV : ∀ i, PCPPRequestNodeSchema.fields nd i ≤ V) :
    (PCPPRequestNodeSchema.native nd).length ≤ 6 * V + 9 := by
  rw [native_len, natWord_len, natWord_len, natWord_len]
  have := natBitLength_le (PCPPRequestNodeSchema.fields nd 0)
  have := natBitLength_le (PCPPRequestNodeSchema.fields nd 1)
  have := natBitLength_le (PCPPRequestNodeSchema.fields nd 2)
  have := hV 0; have := hV 1; have := hV 2
  omega

theorem flatMap_native_le {n : ℕ} (V : ℕ) :
    ∀ nds : List (BooleanNode n), (∀ nd ∈ nds, ∀ i, PCPPRequestNodeSchema.fields nd i ≤ V) →
      (nds.flatMap PCPPRequestNodeSchema.native).length ≤ nds.length * (6 * V + 9)
  | [], _ => by simp
  | nd :: nds, h => by
    have h1 := native_len_le nd V (h nd (by simp))
    have h2 := flatMap_native_le V nds (fun x hx => h x (by simp [hx]))
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    nlinarith

/-! ## Registers and templates -/

variable {ns nr : ℕ} (cap : ℕ) (G : Fin 18 ↪ Fin nr)

/-- The node writer's registers `G 0 … G 7`. -/
def Rw : Fin 8 ↪ Fin nr :=
  ⟨fun i => G (Fin.castLE (by decide) i), fun a b h => by
    have := G.injective h
    exact Fin.ext (by simpa [Fin.ext_iff] using this)⟩

theorem Rw_apply (i : Fin 8) : Rw G i = G (Fin.castLE (by decide) i) := rfl

theorem G_ne {a b : Fin 18} (h : a ≠ b) : G a ≠ G b := G.injective.ne h

theorem Rw_ne (i : Fin 8) (b : Fin 18) (hb : 8 ≤ b.val) : Rw G i ≠ G b := by
  rw [Rw_apply]; apply G_ne; intro e; have := congrArg Fin.val e; simp at this; omega

theorem T_ne : ∀ i : Fin 8, G 8 ≠ Rw G i := fun i => (Rw_ne G i 8 (by decide)).symm

/-- A node template whose fields read the registers `G a` (indices `a ≥ 9`). -/
def mkT (a b c : List (Fin 18) × ℕ) : NodeT nr := ![(a.1.map G, a.2), (b.1.map G, b.2), (c.1.map G, c.2)]

theorem fieldOK_G (srcs : List (Fin 18)) (c : ℕ) (h : ∀ a ∈ srcs, 9 ≤ a.val) :
    FieldOK (Rw G) (G 8) (srcs.map G, c) := by
  intro a ha
  simp only [List.mem_map] at ha
  obtain ⟨b, hb, rfl⟩ := ha
  have hb9 := h b hb
  refine ⟨fun i => (Rw_ne G i b (by omega)).symm, G_ne G ?_⟩
  intro e; subst e; simp at hb9

/-- A template reading only registers `G 9 … G 17`, at most three per field, fits a node when it describes it. -/
theorem fits_mkT {n : ℕ} (V : ℕ) (σ : WState ns nr) (a b c : List (Fin 18) × ℕ) (nd : BooleanNode n)
    (hg : ∀ x ∈ a.1 ++ b.1 ++ c.1, 9 ≤ x.val) (hl : a.1.length ≤ 3 ∧ b.1.length ≤ 3 ∧ c.1.length ≤ 3)
    (hd : ∀ j, fieldVal σ (mkT G a b c j) = PCPPRequestNodeSchema.fields nd j)
    (hV : ∀ j, PCPPRequestNodeSchema.fields nd j ≤ V) : Fits (Rw G) (G 8) V σ (mkT G a b c) nd := by
  refine ⟨fun j => ?_, fun j => ?_, hd, hV⟩
  · fin_cases j
    · exact fieldOK_G G a.1 a.2 (fun x hx => hg x (by simp [hx]))
    · exact fieldOK_G G b.1 b.2 (fun x hx => hg x (by simp [hx]))
    · exact fieldOK_G G c.1 c.2 (fun x hx => hg x (by simp [hx]))
  · fin_cases j <;> simp [mkT, hl.1, hl.2.1, hl.2.2]

/-- `input I`. -/
def tIn : NodeT nr := mkT G ([], 1) ([13], 0) ([], 0)
/-- `or ACC K`. -/
def tOrAK : NodeT nr := mkT G ([], 4) ([11], 0) ([10], 0)
/-- `and ACC K`. -/
def tAndAK : NodeT nr := mkT G ([], 3) ([11], 0) ([10], 0)
/-- `not (K + 2)`. -/
def tNot2 : NodeT nr := mkT G ([], 2) ([10], 2) ([], 0)
/-- `and (K + 1) (K + 3)`. -/
def tAnd13 : NodeT nr := mkT G ([], 3) ([10], 1) ([10], 3)

variable (OUT MAT : Fin (ns + 1))

/-- One support element `i` of the row: `input i` and the XOR with the accumulator; `ACC := K + 4`, `K := K + 5`. -/
def elemW : WM ns nr :=
  .seq (nodesW OUT (Rw G) (G 8) [tIn G, tOrAK G, tAndAK G, tNot2 G, tAnd13 G])
    (.seq (setR (G 11) (G 8) [G 10] 4) (incN (G 10) 5))

/-- The cost of `elemW` with fields at most `V`. -/
def elemCost (V : ℕ) : ℕ := 5 * (nodeCost V + 1) + 21 * V + 50

theorem elemW_spec {n : ℕ} (V : ℕ) (σ : WState ns nr) (hcl : Clean (Rw G) (G 8) σ)
    (ho : σ.sh OUT = (σ.st OUT).length) (i : Fin n) (hI : σ.val (G 13) = i.val)
    (hV : σ.val (G 10) + 4 ≤ V) (hA : σ.val (G 11) ≤ V) (hiV : i.val ≤ V)
    (hcap : σ.val (G 7) + 5 * (12 * V + 18) + 5 * (7 * V + 12) + 2 * V + 10 ≤ cap) :
    WExec cap (elemW G OUT) σ
      (((appendO σ OUT (G 7) (marks (([BooleanNode.input i] ++
          xorNodes (σ.val (G 10) + 1) (σ.val (G 11)) (σ.val (G 10))).flatMap PCPPRequestNodeSchema.native))).setv
        (G 11) (σ.val (G 10) + 4)).setv (G 10) (σ.val (G 10) + 5))
      (elemCost V) := by
  set k := σ.val (G 10) with hk
  set r := σ.val (G 11) with hr
  have h7 : Rw G 7 = G 7 := rfl
  have hnds : List.Forall₂ (Fits (Rw G) (G 8) V σ) [tIn G, tOrAK G, tAndAK G, tNot2 G, tAnd13 G]
      ([BooleanNode.input i] ++ xorNodes (k + 1) r k) := by
    simp only [xorNodes, List.cons_append, List.nil_append]
    refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_
      (List.Forall₂.cons ?_ List.Forall₂.nil)))) <;>
    refine fits_mkT G V σ _ _ _ _ (by decide) (by decide) (fun j => ?_) (fun j => ?_) <;> fin_cases j <;>
      simp [mkT, fieldVal, regSum, PCPPRequestNodeSchema.fields, hI] <;> first | rfl | omega
  have hfV : ∀ nd ∈ ([BooleanNode.input i] ++ xorNodes (k + 1) r k : List (BooleanNode n)),
      ∀ j, PCPPRequestNodeSchema.fields nd j ≤ V := by
    intro nd hnd j
    simp only [xorNodes, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hnd
    rcases hnd with rfl | rfl | rfl | rfl | rfl <;> fin_cases j <;> simp [PCPPRequestNodeSchema.fields] <;> omega
  have hlen5 : ([BooleanNode.input i] ++ xorNodes (k + 1) r k : List (BooleanNode n)).length = 5 := by
    simp [xorNodes]
  have hb := flatMap_native_le V _ hfV
  rw [hlen5] at hb
  have h1 := nodesW_spec cap OUT (Rw G) (G 8) (T_ne G) V _ _ σ hnds hcl ho (by rw [hlen5, h7]; omega)
  rw [hlen5, h7] at h1
  set σ1 := appendO σ OUT (G 7) (marks (([BooleanNode.input i] ++ xorNodes (k + 1) r k).flatMap
    PCPPRequestNodeSchema.native)) with hσ1
  have hT1 : σ1.val (G 8) = 0 := by
    simp [hσ1, Function.update_of_ne (G_ne G (show (8 : Fin 18) ≠ 7 by decide))]; exact hcl.2
  have hk1 : σ1.val (G 10) = k := by
    simp [hσ1, Function.update_of_ne (G_ne G (show (10 : Fin 18) ≠ 7 by decide))]; rfl
  have hr1 : σ1.val (G 11) = r := by
    simp [hσ1, Function.update_of_ne (G_ne G (show (11 : Fin 18) ≠ 7 by decide))]; rfl
  have h2 := setR_spec cap (D := G 11) (T := G 8) (G_ne G (by decide)) [G 10] 4 σ1
    (by intro a ha; simp at ha; subst ha; exact ⟨G_ne G (by decide), G_ne G (by decide)⟩) hT1
    (by rw [hr1]; omega) (by simp [regSum, hk1]; omega)
  simp only [regSum, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero, hk1, hr1] at h2
  have h3 := incN_spec cap (G 10) 5 (σ1.setv (G 11) (k + 4))
    (by simp [Function.update_of_ne (G_ne G (show (10 : Fin 18) ≠ 11 by decide)), hk1]; omega)
  simp only [WState.setv_val, Function.update_of_ne (G_ne G (show (10 : Fin 18) ≠ 11 by decide)), hk1] at h3
  refine WExec.cast cap (WExec.seq h1 (WExec.seq h2 h3)) rfl ?_
  unfold elemCost; simp only [List.length_cons, List.length_nil]; omega

/-! ## One row's parity chain -/

/-- One column: if the matrix cell is set, the element's nodes; then the next cell and column. -/
def colBody : WMX ns nr :=
  .seq (.ifs MAT (.wm (elemW G OUT)) WMX.skip) (.seq (WMX.fwd MAT) (WMX.inc (G 13)))

/-- The parity chain of one row: `q` columns (`G 9 = q` counts, `G 15` scratch). -/
def colLoop : WMX ns nr := repK (G 9) (G 15) (colBody G OUT MAT)

theorem sameExcept_appendO (σ : WState ns nr) {S : List (Fin (ns + 1))} {Rg : List (Fin nr)} {o : Fin (ns + 1)}
    {OP : Fin nr} (ho : o ∈ S) (hOP : OP ∈ Rg) (u : List Bool) : SameExcept σ (appendO σ o OP u) S Rg :=
  ⟨fun y hy => by
    have hne : y ≠ o := fun e => hy (e ▸ ho)
    simp [Function.update_of_ne hne], fun r hr => by
    have hne : r ≠ OP := fun e => hr (e ▸ hOP)
    simp [Function.update_of_ne hne], by simp⟩

section Col
variable (E : LinearCodeFamily) (q : ℕ) (j : Fin (E.length q)) (k0 V : ℕ) (σh : WState ns nr)

/-- The state after the first `i` columns of row `j` (the constant node at `k0` is already written: `σh`). -/
structure ColInv (i : ℕ) (τ : WState ns nr) : Prop where
  out : τ.st OUT = σh.st OUT ++ marks ((pfx E q j k0 i).1.flatMap PCPPRequestNodeSchema.native)
  outh : τ.sh OUT = (τ.st OUT).length
  pos : τ.val (G 7) = σh.val (G 7) + (marks ((pfx E q j k0 i).1.flatMap PCPPRequestNodeSchema.native)).length
  posb : (marks ((pfx E q j k0 i).1.flatMap PCPPRequestNodeSchema.native)).length ≤
    5 * (colList E q j i).length * (12 * V + 18)
  acc : τ.val (G 11) = (pfx E q j k0 i).2
  accle : τ.val (G 11) ≤ τ.val (G 10)
  kk : τ.val (G 10) = k0 + 1 + 5 * (colList E q j i).length
  col : τ.val (G 13) = i
  math : τ.sh MAT = j.val * q + i
  mat : τ.st MAT = σh.st MAT
  clean : Clean (Rw G) (G 8) τ
  fr : SameExcept σh τ [OUT, MAT] [G 7, G 9, G 10, G 11, G 13, G 15]

theorem colInv_setv (i : ℕ) (τ : WState ns nr) (h : ColInv G OUT MAT E q j k0 V σh i τ) (r : Fin 18)
    (hr : r = 9 ∨ r = 15) (v : ℕ) : ColInv G OUT MAT E q j k0 V σh i (τ.setv (G r) v) := by
  have hne : ∀ b : Fin 18, b ≠ 9 → b ≠ 15 → G b ≠ G r := by
    intro b h1 h2; apply G_ne; rcases hr with rfl | rfl <;> assumption
  refine ⟨h.out, h.outh, ?_, h.posb, ?_, ?_, ?_, ?_, h.math, h.mat, ⟨fun a ha => ?_, ?_⟩, ?_⟩
  · simp [Function.update_of_ne (hne 7 (by decide) (by decide)), h.pos]
  · simp [Function.update_of_ne (hne 11 (by decide) (by decide)), h.acc]
  · simp [Function.update_of_ne (hne 11 (by decide) (by decide)), Function.update_of_ne (hne 10 (by decide) (by decide)),
      h.accle]
  · simp [Function.update_of_ne (hne 10 (by decide) (by decide)), h.kk]
  · simp [Function.update_of_ne (hne 13 (by decide) (by decide)), h.col]
  · have : Rw G a ≠ G r := by rw [Rw_apply]; apply hne <;> (intro e; have := congrArg Fin.val e; simp at this; omega)
    simp [Function.update_of_ne this, h.clean.1 a ha]
  · simp [Function.update_of_ne (hne 8 (by decide) (by decide)), h.clean.2]
  · refine h.fr.trans ⟨fun _ _ => ⟨rfl, rfl⟩, fun a ha => ?_, rfl⟩
    have : a ≠ G r := by intro e; subst e; rcases hr with rfl | rfl <;> simp at ha
    simp [Function.update_of_ne this]

/-- The cost of one column. -/
def colCost (V : ℕ) : ℕ := elemCost V + 8

theorem colBody_runs (hOM : OUT ≠ MAT) (hmat : ∀ p, readTapeBit (σh.st MAT) p = matBit E q p)
    (hV : k0 + 5 * q + 5 ≤ V)
    (hcap : σh.val (G 7) + 5 * q * (12 * V + 18) + 97 * V + 160 ≤ cap) (hIc : q + 1 ≤ cap)
    (i : ℕ) (hi : i < q) (τ : WState ns nr) (h : ColInv G OUT MAT E q j k0 V σh i τ) :
    Runs cap (colBody G OUT MAT) τ (colCost V) (fun τ' => ColInv G OUT MAT E q j k0 V σh (i + 1) τ' ∧
      τ'.val (G 9) = τ.val (G 9) ∧ τ'.val (G 15) = τ.val (G 15)) := by
  have hl := colList_length_le E q j i
  have hbit : wbit τ MAT = decide ((⟨i, hi⟩ : Fin q) ∈ E.support q j) := by
    unfold wbit; rw [h.mat, h.math, hmat, matBit_at E q ⟨i, hi⟩ j]
  have hMO : MAT ≠ OUT := Ne.symm hOM
  by_cases hm : (⟨i, hi⟩ : Fin q) ∈ E.support q j
  · -- the element's nodes
    have hK := h.kk
    have e1 := elemW_spec cap G OUT V τ h.clean h.outh (Fin.castAdd (E.length q) (⟨i, hi⟩ : Fin q))
      (by rw [h.col]; rfl) (by rw [hK]; omega) (by have := h.accle; rw [hK] at this; omega) (by simp; omega)
      (by rw [h.pos]; have := h.posb; nlinarith)
    set nds := ([BooleanNode.input (Fin.castAdd (E.length q) (⟨i, hi⟩ : Fin q))] ++
      xorNodes (τ.val (G 10) + 1) (τ.val (G 11)) (τ.val (G 10))) with hnds
    have hfV : ∀ nd ∈ nds, ∀ j, PCPPRequestNodeSchema.fields nd j ≤ V := by
      intro nd hnd j'
      simp only [hnds, xorNodes, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false] at hnd
      have := h.accle
      rcases hnd with rfl | rfl | rfl | rfl | rfl <;> fin_cases j' <;> simp [PCPPRequestNodeSchema.fields] <;> omega
    have hb := flatMap_native_le V nds hfV
    have hlen5 : nds.length = 5 := by simp [hnds, xorNodes]
    rw [hlen5] at hb
    set τ1 := ((appendO τ OUT (G 7) (marks (nds.flatMap PCPPRequestNodeSchema.native))).setv (G 11)
      (τ.val (G 10) + 4)).setv (G 10) (τ.val (G 10) + 5) with hτ1
    have e2 := WXExec.fwd cap MAT τ1
    have e3 := WXExec.inc cap (G 13) (τ1.seth MAT (τ1.sh MAT + 1)) (by
      simp [hτ1, Function.update_of_ne (G_ne G (show (13 : Fin 18) ≠ 10 by decide)),
        Function.update_of_ne (G_ne G (show (13 : Fin 18) ≠ 11 by decide)),
        Function.update_of_ne (G_ne G (show (13 : Fin 18) ≠ 7 by decide)), h.col]; omega)
    have hps := pfx_succ_mem E q j k0 i hi hm
    have hcs : (colList E q j (i + 1)).length = (colList E q j i).length + 1 := by
      rw [colList_succ_length E q j i hi, if_pos hm]
    have hpk : k0 + 1 + 5 * (colList E q j i).length = τ.val (G 10) := hK.symm
    rw [hpk] at hps
    have hacc : (pfx E q j k0 i).2 = τ.val (G 11) := h.acc.symm
    rw [hacc] at hps
    refine ⟨_, WXExec.mono (WXExec.seq (WXExec.ifsT (by rw [hbit]; simp [hm]) (WXExec.wm e1)) (WXExec.seq e2 e3))
      (by unfold colCost; omega), ?_, ?_, ?_⟩
    · have hmk : ∀ u v : List Bool, marks (u ++ v) = marks u ++ marks v := NodeEmit.marks_append
      have hmarks : marks ((pfx E q j k0 (i + 1)).1.flatMap PCPPRequestNodeSchema.native) =
          marks ((pfx E q j k0 i).1.flatMap PCPPRequestNodeSchema.native) ++
            marks (nds.flatMap PCPPRequestNodeSchema.native) := by
        rw [hps, List.flatMap_append, hmk]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ⟨fun a ha => ?_, ?_⟩, ?_⟩
      · simp [hτ1, Function.update_of_ne hMO, h.out, hmarks]
      · simp [hτ1, Function.update_of_ne hOM, Function.update_of_ne hMO, h.outh]
      · simp [hτ1, Function.update_of_ne (G_ne G (show (7 : Fin 18) ≠ 13 by decide)),
          Function.update_of_ne (G_ne G (show (7 : Fin 18) ≠ 10 by decide)),
          Function.update_of_ne (G_ne G (show (7 : Fin 18) ≠ 11 by decide)), h.pos, hmarks]; ring
      · rw [hmarks, List.length_append, hcs, marks_len, marks_len]
        have := h.posb; rw [marks_len] at this; nlinarith
      · simp [hτ1, Function.update_of_ne (G_ne G (show (11 : Fin 18) ≠ 13 by decide)),
          Function.update_of_ne (G_ne G (show (11 : Fin 18) ≠ 10 by decide)), hps]
      · simp [hτ1, Function.update_of_ne (G_ne G (show (11 : Fin 18) ≠ 13 by decide)),
          Function.update_of_ne (G_ne G (show (11 : Fin 18) ≠ 10 by decide)),
          Function.update_of_ne (G_ne G (show (10 : Fin 18) ≠ 13 by decide))]
      · simp [hτ1, Function.update_of_ne (G_ne G (show (10 : Fin 18) ≠ 13 by decide)), hcs, hK]; ring
      · simp [hτ1, h.col]
      · simp [hτ1, Function.update_of_ne hMO, h.math]; ring
      · simp [hτ1, h.mat, Function.update_of_ne hMO]
      · have h13 : Rw G a ≠ G 13 := Rw_ne G a 13 (by decide)
        have h10 : Rw G a ≠ G 10 := Rw_ne G a 10 (by decide)
        have h11 : Rw G a ≠ G 11 := Rw_ne G a 11 (by decide)
        have h7 : Rw G a ≠ G 7 := by
          rw [Rw_apply]; apply G_ne; intro e; apply ha; ext; have := congrArg Fin.val e; simpa using this
        simp [hτ1, Function.update_of_ne h13, Function.update_of_ne h10, Function.update_of_ne h11,
          Function.update_of_ne h7, h.clean.1 a ha]
      · simp [hτ1, Function.update_of_ne (G_ne G (show (8 : Fin 18) ≠ 13 by decide)),
          Function.update_of_ne (G_ne G (show (8 : Fin 18) ≠ 10 by decide)),
          Function.update_of_ne (G_ne G (show (8 : Fin 18) ≠ 11 by decide)),
          Function.update_of_ne (G_ne G (show (8 : Fin 18) ≠ 7 by decide)), h.clean.2]
      · refine h.fr.trans ⟨fun x hx => ?_, fun r hr => ?_, by simp [hτ1]⟩
        · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
          simp [hτ1, Function.update_of_ne hx.1, Function.update_of_ne hx.2]
        · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
          simp [hτ1, Function.update_of_ne hr.1, Function.update_of_ne hr.2.2.1,
            Function.update_of_ne hr.2.2.2.1, Function.update_of_ne hr.2.2.2.2.1]
    · simp [hτ1, Function.update_of_ne (G_ne G (show (9 : Fin 18) ≠ 13 by decide)),
        Function.update_of_ne (G_ne G (show (9 : Fin 18) ≠ 10 by decide)),
        Function.update_of_ne (G_ne G (show (9 : Fin 18) ≠ 11 by decide)),
        Function.update_of_ne (G_ne G (show (9 : Fin 18) ≠ 7 by decide))]
    · simp [hτ1, Function.update_of_ne (G_ne G (show (15 : Fin 18) ≠ 13 by decide)),
        Function.update_of_ne (G_ne G (show (15 : Fin 18) ≠ 10 by decide)),
        Function.update_of_ne (G_ne G (show (15 : Fin 18) ≠ 11 by decide)),
        Function.update_of_ne (G_ne G (show (15 : Fin 18) ≠ 7 by decide))]
  · -- not in the support: skip the cell
    have hbit' : wbit τ MAT = false := by rw [hbit]; simp [hm]
    have e2 := WXExec.fwd cap MAT τ
    have e3 := WXExec.inc cap (G 13) (τ.seth MAT (τ.sh MAT + 1)) (by simp [h.col]; omega)
    have hps := pfx_succ_nmem E q j k0 i hi hm
    have hcs : (colList E q j (i + 1)).length = (colList E q j i).length := by
      rw [colList_succ_length E q j i hi, if_neg hm]; rfl
    refine ⟨_, WXExec.mono (WXExec.seq (WXExec.ifsF hbit' (WXExec.skip cap τ)) (WXExec.seq e2 e3))
      (by unfold colCost elemCost; omega), ?_, ?_, ?_⟩
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ⟨fun a ha => ?_, ?_⟩, ?_⟩
      · simp [Function.update_of_ne hMO, h.out, hps]
      · simp [Function.update_of_ne hOM, h.outh]
      · simp [Function.update_of_ne (G_ne G (show (7 : Fin 18) ≠ 13 by decide)), h.pos, hps]
      · rw [hps, hcs]; exact h.posb
      · simp [Function.update_of_ne (G_ne G (show (11 : Fin 18) ≠ 13 by decide)), h.acc, hps]
      · simp [Function.update_of_ne (G_ne G (show (11 : Fin 18) ≠ 13 by decide)),
          Function.update_of_ne (G_ne G (show (10 : Fin 18) ≠ 13 by decide)), h.accle]
      · simp [Function.update_of_ne (G_ne G (show (10 : Fin 18) ≠ 13 by decide)), h.kk, hcs]
      · simp [h.col]
      · simp [h.math]; ring
      · simp [h.mat]
      · have h13 : Rw G a ≠ G 13 := Rw_ne G a 13 (by decide)
        simp [Function.update_of_ne h13, h.clean.1 a ha]
      · simp [Function.update_of_ne (G_ne G (show (8 : Fin 18) ≠ 13 by decide)), h.clean.2]
      · refine h.fr.trans ⟨fun x hx => ?_, fun r hr => ?_, by simp⟩
        · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
          simp [Function.update_of_ne hx.2]
        · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
          simp [Function.update_of_ne hr.2.2.2.2.1]
    · simp [Function.update_of_ne (G_ne G (show (9 : Fin 18) ≠ 13 by decide))]
    · simp [Function.update_of_ne (G_ne G (show (15 : Fin 18) ≠ 13 by decide))]

theorem colLoop_runs (hOM : OUT ≠ MAT) (hmat : ∀ p, readTapeBit (σh.st MAT) p = matBit E q p)
    (hV : k0 + 5 * q + 5 ≤ V) (hcap : σh.val (G 7) + 5 * q * (12 * V + 18) + 97 * V + 160 ≤ cap)
    (h2q : 2 * q + 1 ≤ cap) (h0 : ColInv G OUT MAT E q j k0 V σh 0 σh) (hQ : σh.val (G 9) = q)
    (hCQ : σh.val (G 15) = 0) :
    Runs cap (colLoop G OUT MAT) σh (q * (colCost V + 8) + 7 * q + 3)
      (fun τ => ColInv G OUT MAT E q j k0 V σh q τ ∧ τ.val (G 9) = q ∧ τ.val (G 15) = 0) :=
  Runs.rep (G_ne G (by decide)) (colCost V) q (ColInv G OUT MAT E q j k0 V σh) (by omega)
    (fun k τ v h => colInv_setv G OUT MAT E q j k0 V σh k τ h 9 (Or.inl rfl) v)
    (fun k τ v h => colInv_setv G OUT MAT E q j k0 V σh k τ h 15 (Or.inr rfl) v)
    (fun k hk τ h => colBody_runs cap G OUT MAT E q j k0 V σh hOM hmat hV hcap (by omega) k hk τ h) σh h0 hQ hCQ

end Col

/-! ## One row: the constant, the parity chain, the code bit, the XOR, the negation, the conjunction -/

/-- `const false`. -/
def tConst : NodeT nr := mkT G ([], 0) ([], 0) ([], 0)
/-- `input (q + J)`. -/
def tInQJ : NodeT nr := mkT G ([], 1) ([9, 14], 0) ([], 0)
/-- `or K ACC`. -/
def tOrKA : NodeT nr := mkT G ([], 4) ([10], 0) ([11], 0)
/-- `and K ACC`. -/
def tAndKA : NodeT nr := mkT G ([], 3) ([10], 0) ([11], 0)
/-- `not (K + 4)`. -/
def tNot4 : NodeT nr := mkT G ([], 2) ([10], 4) ([], 0)
/-- `and RR (K + 5)`. -/
def tAndR5 : NodeT nr := mkT G ([], 3) ([12], 0) ([10], 5)

/-- The row head: `const false` at `K`; `ACC := K`, `K := K + 1`. -/
def rowHead : WM ns nr :=
  .seq (nodeW OUT (Rw G) (G 8) (tConst G)) (.seq (setR (G 11) (G 8) [G 10] 0) (incN (G 10) 1))

/-- The row tail: the code bit, the XOR with the parity, the negation, the conjunction; `RR := K + 6`,
`K := K + 7`. -/
def rowTail : WM ns nr :=
  .seq (nodesW OUT (Rw G) (G 8) [tInQJ G, tOrKA G, tAndKA G, tNot2 G, tAnd13 G, tNot4 G, tAndR5 G])
    (.seq (setR (G 12) (G 8) [G 10] 6) (incN (G 10) 7))

/-- The cost of the head. -/
def headCost (V : ℕ) : ℕ := nodeCost V + 3 * V + 18 * V + 20

theorem rowHead_spec {n : ℕ} (V : ℕ) (σ : WState ns nr) (hcl : Clean (Rw G) (G 8) σ)
    (ho : σ.sh OUT = (σ.st OUT).length) (hV : σ.val (G 10) + 1 ≤ V) (hA : σ.val (G 11) ≤ V)
    (hcap : σ.val (G 7) + 2 * (6 * V + 9) + 7 * V + 12 + V ≤ cap) :
    WExec cap (rowHead G OUT) σ
      (((appendO σ OUT (G 7) (marks (PCPPRequestNodeSchema.native (BooleanNode.const false : BooleanNode n)))).setv
        (G 11) (σ.val (G 10))).setv (G 10) (σ.val (G 10) + 1)) (headCost V) := by
  have hf : Fits (Rw G) (G 8) V σ (tConst G) (BooleanNode.const false : BooleanNode n) :=
    fits_mkT G V σ _ _ _ _ (by decide) (by decide) (fun j => by fin_cases j <;> rfl)
      (fun j => by fin_cases j <;> simp [PCPPRequestNodeSchema.fields])
  have hb := native_len_le (BooleanNode.const false : BooleanNode n) V hf.2.2.2
  have h1 := nodeW_spec cap OUT (Rw G) (G 8) (T_ne G) (tConst G) hf.1 _ σ hf.2.2.1 hf.2.1 V hf.2.2.2 hcl ho
    (by rw [show Rw G 7 = G 7 from rfl]; omega)
  set σ1 := appendO σ OUT (Rw G 7) (marks (PCPPRequestNodeSchema.native (BooleanNode.const false : BooleanNode n)))
    with hσ1
  have hT1 : σ1.val (G 8) = 0 := by
    simp [hσ1, Rw_apply, Function.update_of_ne (G_ne G (show (8 : Fin 18) ≠ 7 by decide))]; exact hcl.2
  have hk1 : σ1.val (G 10) = σ.val (G 10) := by
    simp [hσ1, Rw_apply, Function.update_of_ne (G_ne G (show (10 : Fin 18) ≠ 7 by decide))]
  have hr1 : σ1.val (G 11) = σ.val (G 11) := by
    simp [hσ1, Rw_apply, Function.update_of_ne (G_ne G (show (11 : Fin 18) ≠ 7 by decide))]
  have h2 := setR_spec cap (D := G 11) (T := G 8) (G_ne G (by decide)) [G 10] 0 σ1
    (by intro a ha; simp at ha; subst ha; exact ⟨G_ne G (by decide), G_ne G (by decide)⟩) hT1
    (by rw [hr1]; omega) (by simp [regSum, hk1]; omega)
  simp only [regSum, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero, hk1, hr1,
    List.length_cons, List.length_nil] at h2
  have h3 := incN_spec cap (G 10) 1 (σ1.setv (G 11) (σ.val (G 10)))
    (by simp [Function.update_of_ne (G_ne G (show (10 : Fin 18) ≠ 11 by decide)), hk1]; omega)
  simp only [WState.setv_val, Function.update_of_ne (G_ne G (show (10 : Fin 18) ≠ 11 by decide)), hk1] at h3
  exact WExec.cast cap (WExec.seq h1 (WExec.seq h2 h3)) rfl (by unfold headCost; omega)

/-- The tail's seven nodes at `K = k`, accumulator `a`, conjunction `r`, row `j`. -/
def tailNodes (q L k a r j : ℕ) (hj : j < L) : List (BooleanNode (q + L)) :=
  [.input (Fin.natAdd q ⟨j, hj⟩)] ++ xorNodes (k + 1) k a ++ [.not (k + 4)] ++ [.and r (k + 5)]

/-- The cost of the tail. -/
def tailCost (V : ℕ) : ℕ := 7 * (nodeCost V + 1) + 21 * V + 70

theorem rowTail_spec (V L j : ℕ) (hj : j < L) (σ : WState ns nr) (hcl : Clean (Rw G) (G 8) σ)
    (ho : σ.sh OUT = (σ.st OUT).length) (q : ℕ) (hQ : σ.val (G 9) = q) (hJ : σ.val (G 14) = j)
    (hV : σ.val (G 10) + 5 ≤ V) (hA : σ.val (G 11) ≤ V) (hR : σ.val (G 12) ≤ V) (hqj : q + j ≤ V) (h4 : 4 ≤ V)
    (hcap : σ.val (G 7) + 7 * (12 * V + 18) + 7 * (7 * V + 12) + 2 * V + 20 ≤ cap) :
    WExec cap (rowTail G OUT) σ
      (((appendO σ OUT (G 7) (marks ((tailNodes q L (σ.val (G 10)) (σ.val (G 11)) (σ.val (G 12)) j hj).flatMap
          PCPPRequestNodeSchema.native))).setv (G 12) (σ.val (G 10) + 6)).setv (G 10) (σ.val (G 10) + 7))
      (tailCost V) := by
  set k := σ.val (G 10) with hk
  set a := σ.val (G 11) with ha
  set r := σ.val (G 12) with hr
  have hnds : List.Forall₂ (Fits (Rw G) (G 8) V σ)
      [tInQJ G, tOrKA G, tAndKA G, tNot2 G, tAnd13 G, tNot4 G, tAndR5 G] (tailNodes q L k a r j hj) := by
    simp only [tailNodes, xorNodes, List.cons_append, List.nil_append]
    refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_
      (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ List.Forall₂.nil)))))) <;>
    refine fits_mkT G V σ _ _ _ _ (by decide) (by decide) (fun j => ?_) (fun j => ?_) <;> fin_cases j <;>
      simp [mkT, fieldVal, regSum, PCPPRequestNodeSchema.fields, hQ, hJ] <;> first | rfl | omega
  have hfV : ∀ nd ∈ tailNodes q L k a r j hj, ∀ i, PCPPRequestNodeSchema.fields nd i ≤ V := by
    intro nd hnd i
    simp only [tailNodes, xorNodes, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hnd
    rcases hnd with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> fin_cases i <;>
      simp [PCPPRequestNodeSchema.fields] <;> omega
  have hlen7 : (tailNodes q L k a r j hj).length = 7 := by simp [tailNodes, xorNodes]
  have hb := flatMap_native_le V _ hfV
  rw [hlen7] at hb
  have h1 := nodesW_spec cap OUT (Rw G) (G 8) (T_ne G) V _ _ σ hnds hcl ho
    (by rw [hlen7, show Rw G 7 = G 7 from rfl]; omega)
  rw [hlen7] at h1
  set σ1 := appendO σ OUT (Rw G 7) (marks ((tailNodes q L k a r j hj).flatMap PCPPRequestNodeSchema.native))
    with hσ1
  have hT1 : σ1.val (G 8) = 0 := by
    simp [hσ1, Rw_apply, Function.update_of_ne (G_ne G (show (8 : Fin 18) ≠ 7 by decide))]; exact hcl.2
  have hk1 : σ1.val (G 10) = k := by
    simp [hσ1, Rw_apply, Function.update_of_ne (G_ne G (show (10 : Fin 18) ≠ 7 by decide))]; rfl
  have hr1 : σ1.val (G 12) = r := by
    simp [hσ1, Rw_apply, Function.update_of_ne (G_ne G (show (12 : Fin 18) ≠ 7 by decide))]; rfl
  have h2 := setR_spec cap (D := G 12) (T := G 8) (G_ne G (by decide)) [G 10] 6 σ1
    (by intro a ha; simp at ha; subst ha; exact ⟨G_ne G (by decide), G_ne G (by decide)⟩) hT1
    (by rw [hr1]; omega) (by simp [regSum, hk1]; omega)
  simp only [regSum, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero, hk1, hr1,
    List.length_cons, List.length_nil] at h2
  have h3 := incN_spec cap (G 10) 7 (σ1.setv (G 12) (k + 6))
    (by simp [Function.update_of_ne (G_ne G (show (10 : Fin 18) ≠ 12 by decide)), hk1]; omega)
  simp only [WState.setv_val, Function.update_of_ne (G_ne G (show (10 : Fin 18) ≠ 12 by decide)), hk1] at h3
  exact WExec.cast cap (WExec.seq h1 (WExec.seq h2 h3)) rfl (by unfold tailCost; omega)

/-! ## The rows -/

section Rows
variable (E : LinearCodeFamily) (q : ℕ)

theorem canonList_length_le {n : ℕ} (S : Finset (Fin n)) : (canonList S).length ≤ n := by
  unfold canonList; exact (List.length_filter_le _ _).trans (by simp)

theorem checksNodes_length_le : ∀ (k : ℕ) (js : List (Fin (E.length q))) (r : ℕ),
    (checksNodes E q k js r).1.length ≤ js.length * (5 * q + 8)
  | _, [], _ => by simp [checksNodes]
  | k, j :: rest, r => by
    have := checksNodes_length_le (k + (checkNodes E q k j).1.length + 1) rest (k + (checkNodes E q k j).1.length)
    have hc := checkNodes_length E q k j
    have hl := canonList_length_le (E.support q j)
    simp only [checksNodes, List.length_append, List.length_cons, List.length_nil] at this ⊢
    nlinarith

/-- The check nodes of the first `j` rows from index `m`, conjoined onto `o`. -/
def cs (m o j : ℕ) : List (BooleanNode (q + E.length q)) × ℕ :=
  checksNodes E q m ((List.finRange (E.length q)).take j) o

theorem cs_succ (m o j : ℕ) (hj : j < E.length q) :
    cs E q m o (j + 1) = ((cs E q m o j).1 ++
      (checksNodes E q (m + (cs E q m o j).1.length) [⟨j, hj⟩] (cs E q m o j).2).1,
      (checksNodes E q (m + (cs E q m o j).1.length) [⟨j, hj⟩] (cs E q m o j).2).2) := by
  unfold cs
  rw [take_succ_finRange _ j hj, checksNodes_append]

theorem pfx_full_length (j : Fin (E.length q)) (k0 : ℕ) :
    (pfx E q j k0 q).1.length = 5 * (colList E q j q).length := by
  unfold pfx; rw [parityFromNodes_length]

/-- One row's nodes as the machine writes them: the constant, the parity chain, the tail. -/
theorem row_nodes (k0 rr : ℕ) (j : Fin (E.length q)) :
    (checksNodes E q k0 [j] rr).1 = [BooleanNode.const false] ++ (pfx E q j k0 q).1 ++
      tailNodes q (E.length q) (k0 + 1 + 5 * (colList E q j q).length) (pfx E q j k0 q).2 rr j.val j.isLt ∧
    (checksNodes E q k0 [j] rr).2 = k0 + 1 + 5 * (colList E q j q).length + 6 := by
  rw [checksNodes_single]
  have hk : k0 + (parityNodes k0 ((canonList (E.support q j)).map (Fin.castAdd (E.length q)))).1.length =
      k0 + 1 + 5 * (colList E q j q).length := by
    simp only [parityNodes, List.length_append, List.length_cons, List.length_nil, parityFromNodes_length,
      colList_full]
    ring
  have hp : parityNodes k0 ((canonList (E.support q j)).map (Fin.castAdd (E.length q))) =
      ([BooleanNode.const false] ++ (pfx E q j k0 q).1, (pfx E q j k0 q).2) := by
    simp only [parityNodes, pfx, colList_full]
  constructor
  · simp only [checkNodes]
    rw [hk, hp]
    simp only [tailNodes, List.append_assoc]
  · simp only [checkNodes, List.length_append, List.length_cons, List.length_nil]
    rw [hp]
    simp only [List.length_append, List.length_cons, List.length_nil, pfx_full_length, xorNodes]
    ring

end Rows

/-- One row: head, parity chain, tail; `I := 0`, `J := J + 1`. -/
def rowBody : WMX ns nr :=
  .seq (.wm (rowHead G OUT)) (.seq (colLoop G OUT MAT) (.seq (.wm (rowTail G OUT))
    (.seq (.wm (WM.clear (G 13))) (WMX.inc (G 14)))))

/-- All check rows: `L` rows (`G 16 = L` counts, `G 17` scratch). -/
def checksW : WMX ns nr := repK (G 16) (G 17) (rowBody G OUT MAT)

section RowInvS
variable (E : LinearCodeFamily) (q m o V : ℕ) (σ0 : WState ns nr)

/-- The state after the first `j` rows. -/
structure RowInv (j : ℕ) (τ : WState ns nr) : Prop where
  out : τ.st OUT = σ0.st OUT ++ marks ((cs E q m o j).1.flatMap PCPPRequestNodeSchema.native)
  outh : τ.sh OUT = (τ.st OUT).length
  pos : τ.val (G 7) = σ0.val (G 7) + (marks ((cs E q m o j).1.flatMap PCPPRequestNodeSchema.native)).length
  posb : (marks ((cs E q m o j).1.flatMap PCPPRequestNodeSchema.native)).length ≤ j * (5 * q + 8) * (12 * V + 18)
  rr : τ.val (G 12) = (cs E q m o j).2
  rrle : τ.val (G 12) < τ.val (G 10)
  kk : τ.val (G 10) = m + (cs E q m o j).1.length
  accle : τ.val (G 11) ≤ τ.val (G 10)
  row : τ.val (G 14) = j
  col : τ.val (G 13) = 0
  qq : τ.val (G 9) = q
  cq : τ.val (G 15) = 0
  math : τ.sh MAT = j * q
  mat : τ.st MAT = σ0.st MAT
  clean : Clean (Rw G) (G 8) τ
  fr : SameExcept σ0 τ [OUT, MAT] [G 7, G 9, G 10, G 11, G 12, G 13, G 14, G 15, G 16, G 17]

theorem rowInv_setv (j : ℕ) (τ : WState ns nr) (h : RowInv G OUT MAT E q m o V σ0 j τ) (r : Fin 18)
    (hr : r = 16 ∨ r = 17) (v : ℕ) : RowInv G OUT MAT E q m o V σ0 j (τ.setv (G r) v) := by
  have hne : ∀ b : Fin 18, b ≠ 16 → b ≠ 17 → G b ≠ G r := by
    intro b h1 h2; apply G_ne; rcases hr with rfl | rfl <;> assumption
  refine ⟨h.out, h.outh, ?_, h.posb, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, h.math, h.mat, ⟨fun a ha => ?_, ?_⟩, ?_⟩
  · simp [Function.update_of_ne (hne 7 (by decide) (by decide)), h.pos]
  · simp [Function.update_of_ne (hne 12 (by decide) (by decide)), h.rr]
  · simp [Function.update_of_ne (hne 12 (by decide) (by decide)), Function.update_of_ne (hne 10 (by decide) (by decide)),
      h.rrle]
  · simp [Function.update_of_ne (hne 10 (by decide) (by decide)), h.kk]
  · simp [Function.update_of_ne (hne 11 (by decide) (by decide)), Function.update_of_ne (hne 10 (by decide) (by decide)),
      h.accle]
  · simp [Function.update_of_ne (hne 14 (by decide) (by decide)), h.row]
  · simp [Function.update_of_ne (hne 13 (by decide) (by decide)), h.col]
  · simp [Function.update_of_ne (hne 9 (by decide) (by decide)), h.qq]
  · simp [Function.update_of_ne (hne 15 (by decide) (by decide)), h.cq]
  · have : Rw G a ≠ G r := by rw [Rw_apply]; apply hne <;> (intro e; have := congrArg Fin.val e; simp at this; omega)
    simp [Function.update_of_ne this, h.clean.1 a ha]
  · simp [Function.update_of_ne (hne 8 (by decide) (by decide)), h.clean.2]
  · refine h.fr.trans ⟨fun _ _ => ⟨rfl, rfl⟩, fun a ha => ?_, rfl⟩
    have : a ≠ G r := by intro e; subst e; rcases hr with rfl | rfl <;> simp at ha
    simp [Function.update_of_ne this]

theorem tailNodes_fields_le (L k a r j : ℕ) (hj : j < L) (V : ℕ) (hk : k + 5 ≤ V) (ha : a ≤ V) (hr : r ≤ V)
    (hqj : q + j ≤ V) (h4 : 4 ≤ V) :
    ∀ nd ∈ tailNodes q L k a r j hj, ∀ i, PCPPRequestNodeSchema.fields nd i ≤ V := by
  intro nd hnd i
  simp only [tailNodes, xorNodes, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false] at hnd
  rcases hnd with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> fin_cases i <;>
    simp [PCPPRequestNodeSchema.fields] <;> omega

/-- The cost of one row. -/
def rowCost (q V : ℕ) : ℕ := headCost V + (q * (colCost V + 8) + 7 * q + 3) + tailCost V + 3 * q + 12

theorem rowBody_runs (hOM : OUT ≠ MAT) (hmat : ∀ p, readTapeBit (σ0.st MAT) p = matBit E q p)
    (hV : m + E.length q * (5 * q + 8) + q + E.length q + 8 ≤ V)
    (hcap : σ0.val (G 7) + E.length q * (5 * q + 8) * (12 * V + 18) + 100 * V + 200 ≤ cap)
    (j : ℕ) (hj : j < E.length q) (τ : WState ns nr) (h : RowInv G OUT MAT E q m o V σ0 j τ) :
    Runs cap (rowBody G OUT MAT) τ (rowCost q V) (fun τ' => RowInv G OUT MAT E q m o V σ0 (j + 1) τ' ∧
      τ'.val (G 16) = τ.val (G 16) ∧ τ'.val (G 17) = τ.val (G 17)) := by
  have hMO : MAT ≠ OUT := Ne.symm hOM
  set L := E.length q with hL
  set jj : Fin L := ⟨j, hj⟩ with hjj
  set X := (5 * q + 8) * (12 * V + 18) with hX
  have hjX : (j + 1) * X ≤ L * X := Nat.mul_le_mul_right _ (by omega)
  have hcsl : (cs E q m o j).1.length ≤ j * (5 * q + 8) := by
    have := checksNodes_length_le E q m ((List.finRange L).take j) o
    simp only [List.length_take, List.length_finRange] at this
    unfold cs; rw [min_eq_left hj.le] at this; exact this
  have hjq : (j + 1) * (5 * q + 8) ≤ L * (5 * q + 8) := Nat.mul_le_mul_right _ (by omega)
  have hposb := h.posb
  rw [show j * (5 * q + 8) * (12 * V + 18) = j * X by rw [hX]; ring] at hposb
  set k0 := τ.val (G 10) with hk0
  have hk0m : k0 = m + (cs E q m o j).1.length := h.kk
  have hjq' : j * (5 * q + 8) + (5 * q + 8) ≤ L * (5 * q + 8) := by
    have e : (j + 1) * (5 * q + 8) = j * (5 * q + 8) + (5 * q + 8) := by ring
    omega
  have hk0V : k0 + 5 * q + 8 + q + L + 8 ≤ V := by omega
  have hXq : X = 5 * q * (12 * V + 18) + 96 * V + 144 := by rw [hX]; ring
  have hLX : L * (5 * q + 8) * (12 * V + 18) = L * X := by rw [hX]; ring
  have hjX' : j * X + X ≤ L * X := by
    have e : (j + 1) * X = j * X + X := by ring
    omega
  have hτ7 : τ.val (G 7) + X + 100 * V + 200 ≤ cap := by
    have := h.pos
    omega
  have hacc0 := h.accle
  -- 1. the head
  have e1 := rowHead_spec cap G OUT (n := q + L) V τ h.clean h.outh (by omega) (by omega) (by omega)
  set σh := ((appendO τ OUT (G 7) (marks (PCPPRequestNodeSchema.native (BooleanNode.const false :
    BooleanNode (q + L))))).setv (G 11) k0).setv (G 10) (k0 + 1) with hσh
  have hcb := native_len_le (BooleanNode.const false : BooleanNode (q + L)) V (fun i => by
    fin_cases i <;> simp [PCPPRequestNodeSchema.fields])
  have hσh7 : σh.val (G 7) = τ.val (G 7) +
      (marks (PCPPRequestNodeSchema.native (BooleanNode.const false : BooleanNode (q + L)))).length := by
    simp [hσh, Function.update_of_ne (G_ne G (show (7 : Fin 18) ≠ 10 by decide)),
      Function.update_of_ne (G_ne G (show (7 : Fin 18) ≠ 11 by decide))]
  have hc0 : ColInv G OUT MAT E q jj k0 V σh 0 σh := by
    have hm0 : marks ([] : List Bool) = [] := rfl
    refine ⟨by simp [pfx, colList_zero, parityFromNodes, hm0], ?_, by simp [pfx, colList_zero, parityFromNodes, hm0],
      by simp [pfx, colList_zero, parityFromNodes, hm0], ?_, ?_, ?_, ?_, ?_, rfl, ⟨fun a ha => ?_, ?_⟩,
      SameExcept.refl _ _ _⟩
    · simp [hσh, h.outh]
    · simp [hσh, pfx, colList_zero, parityFromNodes]
    · simp [hσh]
    · simp [hσh, colList_zero]
    · simp [hσh, Function.update_of_ne (G_ne G (show (13 : Fin 18) ≠ 10 by decide)),
        Function.update_of_ne (G_ne G (show (13 : Fin 18) ≠ 11 by decide)),
        Function.update_of_ne (G_ne G (show (13 : Fin 18) ≠ 7 by decide)), h.col]
    · simp [hσh, Function.update_of_ne hMO, h.math, hjj]
    · have h10 : Rw G a ≠ G 10 := Rw_ne G a 10 (by decide)
      have h11 : Rw G a ≠ G 11 := Rw_ne G a 11 (by decide)
      have h7 : Rw G a ≠ G 7 := by
        rw [Rw_apply]; apply G_ne; intro e; apply ha; ext; have := congrArg Fin.val e; simpa using this
      simp [hσh, Function.update_of_ne h10, Function.update_of_ne h11, Function.update_of_ne h7, h.clean.1 a ha]
    · simp [hσh, Function.update_of_ne (G_ne G (show (8 : Fin 18) ≠ 10 by decide)),
        Function.update_of_ne (G_ne G (show (8 : Fin 18) ≠ 11 by decide)),
        Function.update_of_ne (G_ne G (show (8 : Fin 18) ≠ 7 by decide)), h.clean.2]
  have hσhQ : σh.val (G 9) = q := by
    simp [hσh, Function.update_of_ne (G_ne G (show (9 : Fin 18) ≠ 10 by decide)),
      Function.update_of_ne (G_ne G (show (9 : Fin 18) ≠ 11 by decide)),
      Function.update_of_ne (G_ne G (show (9 : Fin 18) ≠ 7 by decide)), h.qq]
  have hσhC : σh.val (G 15) = 0 := by
    simp [hσh, Function.update_of_ne (G_ne G (show (15 : Fin 18) ≠ 10 by decide)),
      Function.update_of_ne (G_ne G (show (15 : Fin 18) ≠ 11 by decide)),
      Function.update_of_ne (G_ne G (show (15 : Fin 18) ≠ 7 by decide)), h.cq]
  have hσhM : σh.st MAT = σ0.st MAT := by simp [hσh, Function.update_of_ne hMO, h.mat]
  -- 2. the parity chain
  have hcm := marks_len (PCPPRequestNodeSchema.native (BooleanNode.const false : BooleanNode (q + L)))
  obtain ⟨τc, ec, hcI, hcQ, hcC⟩ := colLoop_runs cap G OUT MAT E q jj k0 V σh hOM
    (by rw [hσhM]; exact hmat) (by omega) (by rw [hσh7]; omega) (by omega) hc0 hσhQ hσhC
  have hcl := colList_length_le E q jj q
  have hcR : τc.val (G 12) = τ.val (G 12) := by
    rw [hcI.fr.val (by simp)]
    simp [hσh, Function.update_of_ne (G_ne G (show (12 : Fin 18) ≠ 10 by decide)),
      Function.update_of_ne (G_ne G (show (12 : Fin 18) ≠ 11 by decide)),
      Function.update_of_ne (G_ne G (show (12 : Fin 18) ≠ 7 by decide))]
  have hcJ : τc.val (G 14) = j := by
    rw [hcI.fr.val (by simp)]
    simp [hσh, Function.update_of_ne (G_ne G (show (14 : Fin 18) ≠ 10 by decide)),
      Function.update_of_ne (G_ne G (show (14 : Fin 18) ≠ 11 by decide)),
      Function.update_of_ne (G_ne G (show (14 : Fin 18) ≠ 7 by decide)), h.row]
  have hRk : τ.val (G 12) < k0 := h.rrle
  have hcposb := hcI.posb
  -- 3. the tail
  have hcolX : 5 * (colList E q jj q).length * (12 * V + 18) ≤ 5 * q * (12 * V + 18) :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hcl)
  have hcacc := hcI.accle
  rw [hcI.kk] at hcacc
  have e3 := rowTail_spec cap G OUT V L j hj τc hcI.clean hcI.outh q hcQ hcJ (by rw [hcI.kk]; omega)
    (by omega) (by rw [hcR]; omega) (by omega) (by omega)
    (by rw [hcI.pos, hσh7]; omega)
  rw [hcI.kk, hcI.acc, hcR] at e3
  set τt := ((appendO τc OUT (G 7) (marks ((tailNodes q L (k0 + 1 + 5 * (colList E q jj q).length)
    (pfx E q jj k0 q).2 (τ.val (G 12)) j hj).flatMap PCPPRequestNodeSchema.native))).setv (G 12)
    (k0 + 1 + 5 * (colList E q jj q).length + 6)).setv (G 10) (k0 + 1 + 5 * (colList E q jj q).length + 7) with hτt
  have hτtI : τt.val (G 13) = q := by
    simp [hτt, Function.update_of_ne (G_ne G (show (13 : Fin 18) ≠ 10 by decide)),
      Function.update_of_ne (G_ne G (show (13 : Fin 18) ≠ 12 by decide)),
      Function.update_of_ne (G_ne G (show (13 : Fin 18) ≠ 7 by decide)), hcI.col]
  -- 4. column register back to 0, next row
  have e4 := wclear_spec (cap := cap) (G 13) q τt hτtI (by omega)
  have e5 := WXExec.inc cap (G 14) (τt.setv (G 13) 0) (by
    simp [Function.update_of_ne (G_ne G (show (14 : Fin 18) ≠ 13 by decide)), hτt,
      Function.update_of_ne (G_ne G (show (14 : Fin 18) ≠ 10 by decide)),
      Function.update_of_ne (G_ne G (show (14 : Fin 18) ≠ 12 by decide)),
      Function.update_of_ne (G_ne G (show (14 : Fin 18) ≠ 7 by decide)), hcJ]; omega)
  -- the row's nodes
  obtain ⟨hrn1, hrn2⟩ := row_nodes E q k0 (τ.val (G 12)) jj
  have hrr : τ.val (G 12) = (cs E q m o j).2 := h.rr
  have hcs1 := cs_succ E q m o j hj
  rw [← hk0m, ← hrr] at hcs1
  have hcacc' := hcI.accle
  rw [hcI.kk, hcI.acc] at hcacc'
  have htf := tailNodes_fields_le q L (k0 + 1 + 5 * (colList E q jj q).length) (pfx E q jj k0 q).2 (τ.val (G 12))
    j hj V (by omega) (by omega) (by omega) (by omega) (by omega)
  have htb := flatMap_native_le V _ htf
  have htl : (tailNodes q L (k0 + 1 + 5 * (colList E q jj q).length) (pfx E q jj k0 q).2 (τ.val (G 12)) j hj).length
      = 7 := by simp [tailNodes, xorNodes]
  rw [htl] at htb
  have hmk : ∀ u v : List Bool, marks (u ++ v) = marks u ++ marks v := NodeEmit.marks_append
  have hbytes : marks ((cs E q m o (j + 1)).1.flatMap PCPPRequestNodeSchema.native) =
      marks ((cs E q m o j).1.flatMap PCPPRequestNodeSchema.native) ++
        marks (PCPPRequestNodeSchema.native (BooleanNode.const false : BooleanNode (q + L))) ++
        marks ((pfx E q jj k0 q).1.flatMap PCPPRequestNodeSchema.native) ++
        marks ((tailNodes q L (k0 + 1 + 5 * (colList E q jj q).length) (pfx E q jj k0 q).2 (τ.val (G 12)) j
          hj).flatMap PCPPRequestNodeSchema.native) := by
    rw [hcs1, hrn1]
    simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, hmk, List.append_assoc]
    rfl
  refine ⟨_, WXExec.mono (WXExec.seq (WXExec.wm e1) (WXExec.seq ec (WXExec.seq (WXExec.wm e3)
    (WXExec.seq (WXExec.wm e4) e5)))) (by unfold rowCost; omega), ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ⟨fun a ha => ?_, ?_⟩, ?_⟩
    · simp [hτt, hcI.out, hσh, h.out, hbytes, List.append_assoc]
    · simp [hτt, hcI.out, hcI.outh, List.append_assoc]; omega
    · simp [hτt, Function.update_of_ne (G_ne G (show (7 : Fin 18) ≠ 14 by decide)),
        Function.update_of_ne (G_ne G (show (7 : Fin 18) ≠ 13 by decide)),
        Function.update_of_ne (G_ne G (show (7 : Fin 18) ≠ 10 by decide)),
        Function.update_of_ne (G_ne G (show (7 : Fin 18) ≠ 12 by decide)), hcI.pos, hσh7, h.pos, hbytes]
      ring
    · rw [hbytes]
      simp only [List.length_append, marks_len] at hcposb hposb ⊢
      have e : (j + 1) * (5 * q + 8) * (12 * V + 18) = j * X + X := by rw [hX]; ring
      rw [e]
      omega
    · simp [hτt, Function.update_of_ne (G_ne G (show (12 : Fin 18) ≠ 14 by decide)),
        Function.update_of_ne (G_ne G (show (12 : Fin 18) ≠ 13 by decide)),
        Function.update_of_ne (G_ne G (show (12 : Fin 18) ≠ 10 by decide)), hcs1]
      exact hrn2.symm
    · simp [hτt, Function.update_of_ne (G_ne G (show (12 : Fin 18) ≠ 14 by decide)),
        Function.update_of_ne (G_ne G (show (12 : Fin 18) ≠ 13 by decide)),
        Function.update_of_ne (G_ne G (show (12 : Fin 18) ≠ 10 by decide)),
        Function.update_of_ne (G_ne G (show (10 : Fin 18) ≠ 14 by decide)),
        Function.update_of_ne (G_ne G (show (10 : Fin 18) ≠ 13 by decide))]
    · have hlen : (cs E q m o (j + 1)).1.length =
          (cs E q m o j).1.length + (1 + 5 * (colList E q jj q).length + 7) := by
        rw [hcs1, List.length_append]
        have := congrArg List.length hrn1
        simp only [List.length_append, List.length_cons, List.length_nil, pfx_full_length, tailNodes, xorNodes]
          at this
        rw [this]
      simp only [hτt, WState.setv_val, Function.update_of_ne (G_ne G (show (10 : Fin 18) ≠ 14 by decide)),
        Function.update_of_ne (G_ne G (show (10 : Fin 18) ≠ 13 by decide)), Function.update_self]
      rw [hlen]; omega
    · have := hcI.accle
      rw [hcI.kk] at this
      simp [hτt, Function.update_of_ne (G_ne G (show (11 : Fin 18) ≠ 14 by decide)),
        Function.update_of_ne (G_ne G (show (11 : Fin 18) ≠ 13 by decide)),
        Function.update_of_ne (G_ne G (show (11 : Fin 18) ≠ 10 by decide)),
        Function.update_of_ne (G_ne G (show (11 : Fin 18) ≠ 12 by decide)),
        Function.update_of_ne (G_ne G (show (11 : Fin 18) ≠ 7 by decide)),
        Function.update_of_ne (G_ne G (show (10 : Fin 18) ≠ 14 by decide)),
        Function.update_of_ne (G_ne G (show (10 : Fin 18) ≠ 13 by decide))]
      omega
    · simp [hcJ, hτt, Function.update_of_ne (G_ne G (show (14 : Fin 18) ≠ 13 by decide)),
        Function.update_of_ne (G_ne G (show (14 : Fin 18) ≠ 10 by decide)),
        Function.update_of_ne (G_ne G (show (14 : Fin 18) ≠ 12 by decide)),
        Function.update_of_ne (G_ne G (show (14 : Fin 18) ≠ 7 by decide))]
    · simp [Function.update_of_ne (G_ne G (show (13 : Fin 18) ≠ 14 by decide))]
    · simp [hτt, Function.update_of_ne (G_ne G (show (9 : Fin 18) ≠ 14 by decide)),
        Function.update_of_ne (G_ne G (show (9 : Fin 18) ≠ 13 by decide)),
        Function.update_of_ne (G_ne G (show (9 : Fin 18) ≠ 10 by decide)),
        Function.update_of_ne (G_ne G (show (9 : Fin 18) ≠ 12 by decide)),
        Function.update_of_ne (G_ne G (show (9 : Fin 18) ≠ 7 by decide)), hcQ]
    · simp [hτt, Function.update_of_ne (G_ne G (show (15 : Fin 18) ≠ 14 by decide)),
        Function.update_of_ne (G_ne G (show (15 : Fin 18) ≠ 13 by decide)),
        Function.update_of_ne (G_ne G (show (15 : Fin 18) ≠ 10 by decide)),
        Function.update_of_ne (G_ne G (show (15 : Fin 18) ≠ 12 by decide)),
        Function.update_of_ne (G_ne G (show (15 : Fin 18) ≠ 7 by decide)), hcC]
    · simp [hτt, Function.update_of_ne hMO, hcI.math]; ring
    · simp [hτt, Function.update_of_ne hMO, hcI.mat, hσhM]
    · have h14 : Rw G a ≠ G 14 := Rw_ne G a 14 (by decide)
      have h13 : Rw G a ≠ G 13 := Rw_ne G a 13 (by decide)
      have h10 : Rw G a ≠ G 10 := Rw_ne G a 10 (by decide)
      have h12 : Rw G a ≠ G 12 := Rw_ne G a 12 (by decide)
      have h7 : Rw G a ≠ G 7 := by
        rw [Rw_apply]; apply G_ne; intro e; apply ha; ext; have := congrArg Fin.val e; simpa using this
      simp [hτt, Function.update_of_ne h14, Function.update_of_ne h13, Function.update_of_ne h10,
        Function.update_of_ne h12, Function.update_of_ne h7, hcI.clean.1 a ha]
    · simp [hτt, Function.update_of_ne (G_ne G (show (8 : Fin 18) ≠ 14 by decide)),
        Function.update_of_ne (G_ne G (show (8 : Fin 18) ≠ 13 by decide)),
        Function.update_of_ne (G_ne G (show (8 : Fin 18) ≠ 10 by decide)),
        Function.update_of_ne (G_ne G (show (8 : Fin 18) ≠ 12 by decide)),
        Function.update_of_ne (G_ne G (show (8 : Fin 18) ≠ 7 by decide)), hcI.clean.2]
    · refine h.fr.trans ⟨fun x hx => ?_, fun r hr => ?_, by simp [hτt, hcI.fr.cell, hσh]⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
        have hxs : x ∉ [OUT, MAT] := by simp [hx.1, hx.2]
        simp [hτt, Function.update_of_ne hx.1, hcI.fr.st hxs, hcI.fr.sh hxs, hσh]
      · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        have hrs : r ∉ [G 7, G 9, G 10, G 11, G 13, G 15] := by
          simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1]
        simp [hτt, Function.update_of_ne hr.2.2.2.2.2.2.1, Function.update_of_ne hr.2.2.2.2.2.1,
          Function.update_of_ne hr.2.2.1, Function.update_of_ne hr.2.2.2.2.1, Function.update_of_ne hr.1,
          hcI.fr.val hrs, hσh, Function.update_of_ne hr.2.2.2.1]
  · simp [hτt, Function.update_of_ne (G_ne G (show (16 : Fin 18) ≠ 14 by decide)),
      Function.update_of_ne (G_ne G (show (16 : Fin 18) ≠ 13 by decide)),
      Function.update_of_ne (G_ne G (show (16 : Fin 18) ≠ 10 by decide)),
      Function.update_of_ne (G_ne G (show (16 : Fin 18) ≠ 12 by decide)),
      Function.update_of_ne (G_ne G (show (16 : Fin 18) ≠ 7 by decide)), hcI.fr.val (show G 16 ∉ _ by simp), hσh,
      Function.update_of_ne (G_ne G (show (16 : Fin 18) ≠ 11 by decide))]
  · simp [hτt, Function.update_of_ne (G_ne G (show (17 : Fin 18) ≠ 14 by decide)),
      Function.update_of_ne (G_ne G (show (17 : Fin 18) ≠ 13 by decide)),
      Function.update_of_ne (G_ne G (show (17 : Fin 18) ≠ 10 by decide)),
      Function.update_of_ne (G_ne G (show (17 : Fin 18) ≠ 12 by decide)),
      Function.update_of_ne (G_ne G (show (17 : Fin 18) ≠ 7 by decide)), hcI.fr.val (show G 17 ∉ _ by simp), hσh,
      Function.update_of_ne (G_ne G (show (17 : Fin 18) ≠ 11 by decide))]

theorem rowInv_zero (ho : σ0.sh OUT = (σ0.st OUT).length) (ho' : o < m) (hK : σ0.val (G 10) = m)
    (hA : σ0.val (G 11) ≤ m) (hRR : σ0.val (G 12) = o) (hJ : σ0.val (G 14) = 0) (hI : σ0.val (G 13) = 0)
    (hQ : σ0.val (G 9) = q) (hCQ : σ0.val (G 15) = 0) (hM : σ0.sh MAT = 0) (hcl : Clean (Rw G) (G 8) σ0) :
    RowInv G OUT MAT E q m o V σ0 0 σ0 := by
  have hm0 : marks ([] : List Bool) = [] := rfl
  have hc0 : cs E q m o 0 = ([], o) := by simp [cs, checksNodes]
  exact ⟨by simp [hc0, hm0], ho, by simp [hc0, hm0], by simp [hc0, hm0], by simp [hc0, hRR], by rw [hRR, hK]; exact ho',
    by simp [hc0, hK], by rw [hK]; exact hA, hJ, hI, hQ, hCQ, by simp [hM], rfl, hcl, SameExcept.refl _ _ _⟩

/-- The cost of all rows. -/
def checksCost (q L V : ℕ) : ℕ := L * (rowCost q V + 8) + 7 * L + 3

theorem checksW_runs (hOM : OUT ≠ MAT) (hmat : ∀ p, readTapeBit (σ0.st MAT) p = matBit E q p)
    (hV : m + E.length q * (5 * q + 8) + q + E.length q + 8 ≤ V)
    (hcap : σ0.val (G 7) + E.length q * (5 * q + 8) * (12 * V + 18) + 100 * V + 200 ≤ cap)
    (h0 : RowInv G OUT MAT E q m o V σ0 0 σ0) (hLL : σ0.val (G 16) = E.length q) (hCL : σ0.val (G 17) = 0) :
    Runs cap (checksW G OUT MAT) σ0 (checksCost q (E.length q) V)
      (fun τ => RowInv G OUT MAT E q m o V σ0 (E.length q) τ ∧ τ.val (G 16) = E.length q ∧ τ.val (G 17) = 0) :=
  Runs.rep (G_ne G (by decide)) (rowCost q V) (E.length q) (RowInv G OUT MAT E q m o V σ0) (by omega)
    (fun k τ v h => rowInv_setv G OUT MAT E q m o V σ0 k τ h 16 (Or.inl rfl) v)
    (fun k τ v h => rowInv_setv G OUT MAT E q m o V σ0 k τ h 17 (Or.inr rfl) v)
    (fun k hk τ h => rowBody_runs cap G OUT MAT E q m o V σ0 hOM hmat hV hcap k hk τ h) σ0 h0 hLL hCL

theorem cs_full (m o : ℕ) :
    cs E q m o (E.length q) = checksNodes E q m (List.finRange (E.length q)) o := by
  unfold cs; rw [List.take_of_length_le (by simp)]

end RowInvS

end NearCubicGates.Close.CheckedPCPP.ChecksW
