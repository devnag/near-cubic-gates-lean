import Proof.Wire_3_5.PrimAsmWriteNat
import Proof.Wire_3_5.FinalPassHashTable
import Proof.Wire_3_5.FinalPassWordLib
import Proof.PCP.PCPPRequestNodeSchema

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.CheckedPCPP.NodeEmit

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.RepairOrdinary.Streaming NearCubicWires.SourceInterfaces

variable {ns nr : ℕ} (cap : ℕ)

/-! ## Register sums -/

/-- `W := W + A`, `A` kept (`T` scratch, `0` before and after). -/
def addW (A W T : Fin nr) : WM ns nr := .seq (NearCubicWires.WireExponent3_5.FinalPass.Hash4.wdup A W T) (WM.move T A)

theorem addW_spec {A W T : Fin nr} (hAW : A ≠ W) (hAT : A ≠ T) (hWT : W ≠ T) (σ : WState ns nr)
    (hT : σ.val T = 0) (hcap : σ.val W + σ.val A ≤ cap) :
    WExec cap (addW A W T) σ (σ.setv W (σ.val W + σ.val A)) (18 * σ.val A + 3) := by
  have h1 := NearCubicWires.WireExponent3_5.FinalPass.Hash4.wdup_spec (cap := cap) A W T hAW hAT hWT (σ.val A) σ rfl
    (by omega) (by omega) (by rw [hT]; omega)
  have h2 := wmove_spec (cap := cap) T A (Ne.symm hAT) (σ.val A)
    (((σ.setv A 0).setv W (σ.val W + σ.val A)).setv T (σ.val T + σ.val A)) (by simp [hT])
    (by simp [hT]; omega) (by simp [Function.update_apply, hAT, hAW, hT]; omega)
  refine WExec.cast cap (WExec.seq h1 h2) ?_ (by omega)
  apply WState.eq <;> try rfl
  funext r
  simp only [WState.setv_val, Function.update_apply]
  by_cases r1 : r = A
  · rw [r1]; simp [hAW, hAT, hT, Ne.symm hAT]
  · by_cases r2 : r = T
    · rw [r2]; simp [Ne.symm hAT, Ne.symm hWT, hT]
    · simp [r1, r2]

/-- `W := W + Σ srcs`. -/
def sumW (W T : Fin nr) : List (Fin nr) → WM ns nr
  | [] => .skip
  | a :: as => .seq (addW a W T) (sumW W T as)

/-- The sum of the registers `srcs`. -/
def regSum (σ : WState ns nr) (srcs : List (Fin nr)) : ℕ := (srcs.map σ.val).sum

theorem regSum_setv (σ : WState ns nr) (srcs : List (Fin nr)) (r : Fin nr) (hr : r ∉ srcs) (x : ℕ) :
    regSum (σ.setv r x) srcs = regSum σ srcs := by
  unfold regSum
  congr 1
  apply List.map_congr_left
  intro a ha
  have : a ≠ r := fun e => hr (e ▸ ha)
  simp [Function.update_of_ne this]

theorem sumW_spec {W T : Fin nr} (hWT : W ≠ T) :
    ∀ (srcs : List (Fin nr)) (σ : WState ns nr), (∀ a ∈ srcs, a ≠ W ∧ a ≠ T) → σ.val T = 0 →
      σ.val W + regSum σ srcs ≤ cap →
      WExec cap (sumW W T srcs) σ (σ.setv W (σ.val W + regSum σ srcs)) (18 * regSum σ srcs + 4 * srcs.length)
  | [], σ, _, _, _ => by
    simp only [sumW, regSum, List.map_nil, List.sum_nil, Nat.add_zero, wsetv_same]
    exact WExec.mono (WExec.skip σ) (by omega)
  | a :: as, σ, hs, hT, hcap => by
    have ha := hs a (by simp)
    have h1 := addW_spec cap ha.1 ha.2 hWT σ hT (by simp [regSum] at hcap; omega)
    have hWas : W ∉ as := fun h => (hs W (by simp [h])).1 rfl
    have hrs : regSum (σ.setv W (σ.val W + σ.val a)) as = regSum σ as := regSum_setv σ as W hWas _
    have h2 := sumW_spec hWT as (σ.setv W (σ.val W + σ.val a)) (fun b hb => hs b (by simp [hb]))
      (by simp [Function.update_of_ne (Ne.symm hWT), hT])
      (by simp only [WState.setv_val, Function.update_self, hrs]
          simp only [regSum, List.map_cons, List.sum_cons] at hcap ⊢; omega)
    rw [hrs] at h2
    refine WExec.cast cap (WExec.seq h1 h2) ?_ (by simp [regSum]; ring_nf; omega)
    simp only [wsetv_setv, WState.setv_val, Function.update_self, regSum, List.map_cons, List.sum_cons]
    congr 1
    omega

/-- `W := W + c`. -/
def incN (W : Fin nr) : ℕ → WM ns nr
  | 0 => .skip
  | c + 1 => .seq (.inc W) (incN W c)

theorem incN_spec (W : Fin nr) : ∀ (c : ℕ) (σ : WState ns nr), σ.val W + c ≤ cap →
    WExec cap (incN W c) σ (σ.setv W (σ.val W + c)) (4 * c)
  | 0, σ, _ => by simp only [incN, Nat.add_zero, wsetv_same]; exact WExec.skip σ
  | c + 1, σ, hc => by
    have h1 := WExec.inc (cap := cap) W σ (by omega)
    have h2 := incN_spec W c (σ.setv W (σ.val W + 1)) (by simp; omega)
    refine WExec.cast cap (WExec.seq h1 h2) ?_ (by omega)
    simp only [wsetv_setv, WState.setv_val, Function.update_self]
    congr 1
    omega

/-! ## One field, one node -/

/-- A field template: a register sum plus a constant. -/
abbrev Field (nr : ℕ) := List (Fin nr) × ℕ

/-- The value of a field template. -/
def fieldVal (σ : WState ns nr) (f : Field nr) : ℕ := regSum σ f.1 + f.2

variable (o : Fin (ns + 1)) (R : Fin 8 ↪ Fin nr) (T : Fin nr)

/-- Write `marks (natWord (Σ srcs + c))` to `o` (accumulator `R 0`, scratch `R 1 … R 6`, `T`, position `R 7`). -/
def fieldW (f : Field nr) : WM ns nr :=
  .seq (sumW (R 0) T f.1) (.seq (incN (R 0) f.2) (.seq (writeNatM o R) (WM.clear (R 0))))

/-- The registers the writer uses. -/
def Clean (σ : WState ns nr) : Prop := (∀ i : Fin 8, i ≠ 7 → σ.val (R i) = 0) ∧ σ.val T = 0

/-- A field template that does not read the writer's registers. -/
def FieldOK (f : Field nr) : Prop := ∀ a ∈ f.1, (∀ i : Fin 8, a ≠ R i) ∧ a ≠ T

/-- The cost of one field of value `v` read from `k` registers. -/
def fieldCost (v k : ℕ) : ℕ := 25 * v + 4 * k + 4 + (natBitLength v + 10) * (100 * v + 200)

theorem natBitLength_le (v : ℕ) : natBitLength v ≤ v + 1 := by
  have := Nat.log_lt_self 2 (show v + 1 ≠ 0 by omega)
  have := Nat.log_mono_right (show v ≤ v + 1 by omega) (b := 2)
  simp only [natBitLength]; omega

theorem fieldW_spec (hTR : ∀ i : Fin 8, T ≠ R i) (f : Field nr) (hf : FieldOK R T f) (σ : WState ns nr)
    (hcl : Clean R T σ) (ho : σ.sh o = (σ.st o).length)
    (hcap : fieldVal σ f + σ.val (R 7) + 6 * natBitLength (fieldVal σ f) + 6 ≤ cap) :
    WExec cap (fieldW o R T f) σ (appendO σ o (R 7) (marks (natWord (fieldVal σ f))))
      (fieldCost (fieldVal σ f) f.1.length) := by
  have hR : ∀ i j : Fin 8, R i = R j ↔ i = j := fun i j => R.injective.eq_iff
  have h0 : σ.val (R 0) = 0 := hcl.1 0 (by decide)
  set v := fieldVal σ f with hv
  have h1 := sumW_spec cap (W := R 0) (T := T) (Ne.symm (hTR 0)) f.1 σ
    (fun a ha => ⟨(hf a ha).1 0, (hf a ha).2⟩) hcl.2 (by rw [h0]; unfold fieldVal at hv; omega)
  rw [h0, Nat.zero_add] at h1
  set σ1 := σ.setv (R 0) (regSum σ f.1) with hσ1
  have h2 := incN_spec cap (R 0) f.2 σ1 (by simp [hσ1]; unfold fieldVal at hv; omega)
  have hv1 : σ1.val (R 0) + f.2 = v := by simp [hσ1, fieldVal, hv]
  rw [hv1] at h2
  set σ2 := σ1.setv (R 0) v with hσ2
  have hz : ∀ i : Fin 8, i ≠ 0 → σ2.val (R i) = σ.val (R i) := by
    intro i hi; simp [hσ2, hσ1, Function.update_of_ne (R.injective.ne hi)]
  have h3 := writeNatM_spec cap o R σ2 (by rw [hz 1 (by decide)]; exact hcl.1 1 (by decide))
    (by rw [hz 2 (by decide)]; exact hcl.1 2 (by decide)) (by rw [hz 3 (by decide)]; exact hcl.1 3 (by decide))
    (by rw [hz 4 (by decide)]; exact hcl.1 4 (by decide)) (by rw [hz 5 (by decide)]; exact hcl.1 5 (by decide))
    (by rw [hz 6 (by decide)]; exact hcl.1 6 (by decide)) (by simp [hσ2, hσ1, ho])
    (by rw [hz 7 (by decide)]; simp [hσ2]; omega)
  have hv2 : σ2.val (R 0) = v := by simp [hσ2]
  rw [hv2] at h3
  have h4 := wclear_spec (cap := cap) (R 0) v (appendO σ2 o (R 7) (marks (natWord v)))
    (by simp [Function.update_of_ne (R.injective.ne (show (0 : Fin 8) ≠ 7 by decide)), hv2])
    (by simp [Function.update_of_ne (R.injective.ne (show (0 : Fin 8) ≠ 7 by decide)), hv2]
        have := natBitLength_le v; omega)
  refine WExec.cast cap (WExec.seq h1 (WExec.seq h2 (WExec.seq h3 h4))) ?_ ?_
  · rw [← appendO_setv σ2 o (R 7) (R 0) (R.injective.ne (show (0 : Fin 8) ≠ 7 by decide))]
    congr 1
    simp only [hσ2, hσ1, wsetv_setv]
    rw [← h0, wsetv_same]
  · have hb : v ≤ v := le_rfl
    have hs : regSum σ f.1 ≤ v := by unfold fieldVal at hv; omega
    have hc : f.2 ≤ v := by unfold fieldVal at hv; omega
    unfold fieldCost
    nlinarith

/-- A node template: three field templates. -/
abbrev NodeT (nr : ℕ) := Fin 3 → Field nr

/-- Write the three fields of one node. -/
def nodeW (t : NodeT nr) : WM ns nr :=
  .seq (fieldW o R T (t 0)) (.seq (fieldW o R T (t 1)) (fieldW o R T (t 2)))

/-- The template `t` describes the node `nd` in `σ`. -/
def Describes {n : ℕ} (σ : WState ns nr) (t : NodeT nr) (nd : BooleanNode n) : Prop :=
  ∀ i, fieldVal σ (t i) = PCPPRequestNodeSchema.fields nd i

theorem fieldVal_appendO (σ : WState ns nr) (f : Field nr) (hf : FieldOK R T f) (u : List Bool) :
    fieldVal (appendO σ o (R 7) u) f = fieldVal σ f := by
  unfold fieldVal
  congr 1
  unfold appendO
  rw [regSum_setv _ _ _ (fun h => ((hf _ h).1 7) rfl)]
  rfl

theorem clean_appendO (σ : WState ns nr) (h : Clean R T σ) (hTR : ∀ i : Fin 8, T ≠ R i) (u : List Bool) :
    Clean R T (appendO σ o (R 7) u) := by
  refine ⟨fun i hi => ?_, ?_⟩
  · simp [Function.update_of_ne (R.injective.ne hi), h.1 i hi]
  · simp [Function.update_of_ne (hTR 7), h.2]

/-- The cost of one node whose fields are at most `V`. -/
def nodeCost (V : ℕ) : ℕ := 3 * fieldCost V 3 + 2

theorem fieldCost_mono {v v' k k' : ℕ} (hv : v ≤ v') (hk : k ≤ k') : fieldCost v k ≤ fieldCost v' k' := by
  unfold fieldCost
  have : natBitLength v ≤ natBitLength v' := by
    unfold natBitLength
    exact Nat.add_le_add_right (Nat.log_mono_right hv) 1
  have := Nat.mul_le_mul (Nat.add_le_add_right this 10) (Nat.add_le_add_right (Nat.mul_le_mul_left 100 hv) 200)
  omega

/-- The native bytes of a node are its three fields. -/
theorem native_fields {n : ℕ} (nd : BooleanNode n) :
    PCPPRequestNodeSchema.native nd = natWord (PCPPRequestNodeSchema.fields nd 0) ++
      natWord (PCPPRequestNodeSchema.fields nd 1) ++ natWord (PCPPRequestNodeSchema.fields nd 2) := rfl

theorem marks_append (u v : List Bool) : marks (u ++ v) = marks u ++ marks v := by
  simp [marks, List.flatMap_append]

theorem marks_len (w : List Bool) : (marks w).length = 2 * w.length := by
  induction w with
  | nil => rfl
  | cons b w ih => simp [marks, List.flatMap_cons] at ih ⊢; omega

theorem native_len {n : ℕ} (nd : BooleanNode n) : (PCPPRequestNodeSchema.native nd).length =
    (natWord (PCPPRequestNodeSchema.fields nd 0)).length + (natWord (PCPPRequestNodeSchema.fields nd 1)).length +
      (natWord (PCPPRequestNodeSchema.fields nd 2)).length := by
  rw [native_fields]; simp only [List.length_append]

theorem nodeW_spec (hTR : ∀ i : Fin 8, T ≠ R i) (t : NodeT nr) (ht : ∀ i, FieldOK R T (t i)) {n : ℕ}
    (nd : BooleanNode n) (σ : WState ns nr) (hd : Describes σ t nd) (hlen : ∀ i, (t i).1.length ≤ 3)
    (V : ℕ) (hV : ∀ i, PCPPRequestNodeSchema.fields nd i ≤ V)
    (hcl : Clean R T σ) (ho : σ.sh o = (σ.st o).length)
    (hcap : σ.val (R 7) + 2 * (PCPPRequestNodeSchema.native nd).length + 7 * V + 12 ≤ cap) :
    WExec cap (nodeW o R T t) σ (appendO σ o (R 7) (marks (PCPPRequestNodeSchema.native nd))) (nodeCost V) := by
  have hbl : ∀ x, natBitLength x ≤ x + 1 := natBitLength_le
  have hnl := native_len nd
  have m0 := marks_len (natWord (PCPPRequestNodeSchema.fields nd 0))
  have m1 := marks_len (natWord (PCPPRequestNodeSchema.fields nd 1))
  have b0 := hbl (PCPPRequestNodeSchema.fields nd 0)
  have b1 := hbl (PCPPRequestNodeSchema.fields nd 1)
  have b2 := hbl (PCPPRequestNodeSchema.fields nd 2)
  have v0 := hV 0
  have v1 := hV 1
  have v2 := hV 2
  have e0 := hd 0
  have h1 := fieldW_spec cap o R T hTR (t 0) (ht 0) σ hcl ho (by rw [e0]; omega)
  rw [e0] at h1
  set σ1 := appendO σ o (R 7) (marks (natWord (PCPPRequestNodeSchema.fields nd 0))) with hσ1
  have r1 : σ1.val (R 7) = σ.val (R 7) + (marks (natWord (PCPPRequestNodeSchema.fields nd 0))).length := by
    simp [hσ1]
  have e1 : fieldVal σ1 (t 1) = PCPPRequestNodeSchema.fields nd 1 := by
    rw [hσ1, fieldVal_appendO o R T σ (t 1) (ht 1)]; exact hd 1
  have h2 := fieldW_spec cap o R T hTR (t 1) (ht 1) σ1 (clean_appendO o R T σ hcl hTR _)
    (by simp [hσ1, ho]) (by rw [e1, r1]; omega)
  rw [e1] at h2
  set σ2 := appendO σ1 o (R 7) (marks (natWord (PCPPRequestNodeSchema.fields nd 1))) with hσ2
  have r2 : σ2.val (R 7) = σ1.val (R 7) + (marks (natWord (PCPPRequestNodeSchema.fields nd 1))).length := by
    simp [hσ2]
  have e2 : fieldVal σ2 (t 2) = PCPPRequestNodeSchema.fields nd 2 := by
    rw [hσ2, fieldVal_appendO o R T σ1 (t 2) (ht 2), hσ1, fieldVal_appendO o R T σ (t 2) (ht 2)]; exact hd 2
  have h3 := fieldW_spec cap o R T hTR (t 2) (ht 2) σ2
    (clean_appendO o R T σ1 (clean_appendO o R T σ hcl hTR _) hTR _)
    (by simp [hσ2, hσ1, ho]; omega) (by rw [e2, r2, r1]; omega)
  rw [e2] at h3
  refine WExec.cast cap (WExec.seq h1 (WExec.seq h2 h3)) ?_ ?_
  · rw [hσ2, hσ1, appendO_append, appendO_append, native_fields, marks_append, marks_append, List.append_assoc]
  · unfold nodeCost
    have c0 := fieldCost_mono (hV 0) (hlen 0)
    have c1 := fieldCost_mono (hV 1) (hlen 1)
    have c2 := fieldCost_mono (hV 2) (hlen 2)
    omega

/-! ## Lists of nodes, register updates -/

/-- Write the nodes of a list of templates. -/
def nodesW : List (NodeT nr) → WM ns nr
  | [] => .skip
  | t :: ts => .seq (nodeW o R T t) (nodesW ts)

/-- A template fits a node: it reads no writer register, has at most three sources per field, describes the node in
`σ`, and the node's fields are at most `V`. -/
def Fits {n : ℕ} (V : ℕ) (σ : WState ns nr) (t : NodeT nr) (nd : BooleanNode n) : Prop :=
  (∀ i, FieldOK R T (t i)) ∧ (∀ i, (t i).1.length ≤ 3) ∧ Describes σ t nd ∧
    ∀ i, PCPPRequestNodeSchema.fields nd i ≤ V

theorem fits_appendO {n : ℕ} (V : ℕ) (σ : WState ns nr) (t : NodeT nr) (nd : BooleanNode n) (h : Fits R T V σ t nd)
    (u : List Bool) : Fits R T V (appendO σ o (R 7) u) t nd :=
  ⟨h.1, h.2.1, fun i => by rw [fieldVal_appendO o R T σ (t i) (h.1 i)]; exact h.2.2.1 i, h.2.2.2⟩

theorem nodesW_spec (hTR : ∀ i : Fin 8, T ≠ R i) {n : ℕ} (V : ℕ) :
    ∀ (ts : List (NodeT nr)) (nds : List (BooleanNode n)) (σ : WState ns nr),
      List.Forall₂ (Fits R T V σ) ts nds → Clean R T σ → σ.sh o = (σ.st o).length →
      σ.val (R 7) + 2 * (nds.flatMap PCPPRequestNodeSchema.native).length + (7 * V + 12) * nds.length ≤ cap →
      WExec cap (nodesW o R T ts) σ (appendO σ o (R 7) (marks (nds.flatMap PCPPRequestNodeSchema.native)))
        (nds.length * (nodeCost V + 1))
  | [], [], σ, _, _, _, _ => by
    simp only [nodesW, List.flatMap_nil, List.length_nil, Nat.zero_mul]
    rw [show marks ([] : List Bool) = [] from rfl, appendO_nil]
    exact WExec.skip σ
  | t :: ts, nd :: nds, σ, hf, hcl, ho, hcap => by
    obtain ⟨hf1, hfs⟩ := List.forall₂_cons.1 hf
    have h1 := nodeW_spec cap o R T hTR t hf1.1 nd σ hf1.2.2.1 hf1.2.1 V hf1.2.2.2 hcl ho (by
      simp only [List.flatMap_cons, List.length_append, List.length_cons] at hcap; nlinarith)
    have hfs' : List.Forall₂ (Fits R T V (appendO σ o (R 7) (marks (PCPPRequestNodeSchema.native nd)))) ts nds :=
      hfs.imp (fun a b h => fits_appendO o R T V σ a b h _)
    have h2 := nodesW_spec hTR V ts nds _ hfs' (clean_appendO o R T σ hcl hTR _) (by simp [ho]) (by
      simp only [appendO_val, Function.update_self, marks_len]
      simp only [List.flatMap_cons, List.length_append, List.length_cons] at hcap; nlinarith)
    refine WExec.cast cap (WExec.seq h1 h2) ?_ (by simp only [List.length_cons]; ring_nf; omega)
    rw [appendO_append, List.flatMap_cons, marks_append]

/-- `D := Σ srcs + c` (`D` not a source; `T` scratch). -/
def setR (D T : Fin nr) (srcs : List (Fin nr)) (c : ℕ) : WM ns nr :=
  .seq (WM.clear D) (.seq (sumW D T srcs) (incN D c))

theorem setR_spec {D T : Fin nr} (hDT : D ≠ T) (srcs : List (Fin nr)) (c : ℕ) (σ : WState ns nr)
    (hs : ∀ a ∈ srcs, a ≠ D ∧ a ≠ T) (hT : σ.val T = 0) (hD : σ.val D ≤ cap) (hcap : regSum σ srcs + c ≤ cap) :
    WExec cap (setR D T srcs c) σ (σ.setv D (regSum σ srcs + c))
      (3 * σ.val D + 18 * regSum σ srcs + 4 * srcs.length + 4 * c + 3) := by
  have h1 := wclear_spec (cap := cap) D (σ.val D) σ rfl hD
  have hDs : D ∉ srcs := fun h => (hs D h).1 rfl
  have hr : regSum (σ.setv D 0) srcs = regSum σ srcs := regSum_setv σ srcs D hDs 0
  have h2 := sumW_spec cap hDT srcs (σ.setv D 0) hs (by simp [Function.update_of_ne (Ne.symm hDT), hT])
    (by simp [hr]; omega)
  rw [hr] at h2
  simp only [WState.setv_val, Function.update_self, Nat.zero_add, wsetv_setv] at h2
  have h3 := incN_spec cap D c (σ.setv D (regSum σ srcs)) (by simp; omega)
  simp only [WState.setv_val, Function.update_self, wsetv_setv] at h3
  exact WExec.cast cap (WExec.seq h1 (WExec.seq h2 h3)) rfl (by omega)

end NearCubicGates.Close.CheckedPCPP.NodeEmit
