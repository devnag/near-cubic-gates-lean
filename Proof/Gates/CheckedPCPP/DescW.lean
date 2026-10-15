import Proof.Gates.CheckedPCPP.ChecksW
import Proof.Gates.Codec.Copy
import Proof.Gates.Codec.Frame

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.CheckedPCPP.DescW

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat (readNatM readNatM_spec enc stp)
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.SourceInterfaces NearCubicWires.Bindings.CLW20Lemma311
open NearCubicGates.PublishedSources.PCPP NearCubicGates.Close.Gadget NearCubicGates.Close.WordPrograms
open NearCubicGates.Close.CheckedPCPP.NodeEmit NearCubicGates.Close.CheckedPCPP.ChecksW

variable {ns nr : ℕ} (cap : ℕ)

/-! ## Copying a marked word -/

theorem rtb_app (pre r : List Bool) (k : ℕ) : readTapeBit (pre ++ r) (pre.length + k) = readTapeBit r k := by
  simp [readTapeBit, List.getD_eq_getElem?_getD, List.getElem?_append_right]

theorem rtb_app0 (pre r : List Bool) : readTapeBit (pre ++ r) pre.length = readTapeBit r 0 := by
  simpa using rtb_app pre r 0

/-- Append `marks w` from stream `s` (holding `marks w`, then a cell reading `false`) to `o`. -/
def copyMarks (s o : Fin (ns + 1)) (OP : Fin nr) : WM ns nr := .whs s (.seq (.fwd s) (Codec.frameCell s o OP))

theorem copyMarks_spec (s o : Fin (ns + 1)) (hso : s ≠ o) (OP : Fin nr) :
    ∀ (w pre rest : List Bool) (σ : WState ns nr), σ.st s = pre ++ marks w ++ rest → readTapeBit rest 0 = false →
      σ.sh s = pre.length → σ.sh o = (σ.st o).length → σ.val OP + 2 * w.length ≤ cap →
      WExec cap (copyMarks s o OP) σ ((appendO σ o OP (marks w)).seth s (pre.length + 2 * w.length))
        (22 * w.length + 1)
  | [], pre, rest, σ, hst, hr, hsh, _, _ => by
    have hb : wbit σ s = false := by
      unfold wbit; rw [hst, hsh]; simp only [marks, List.flatMap_nil, List.append_nil]; rw [rtb_app0, hr]
    have e : (appendO σ o OP (marks [])).seth s (pre.length + 2 * ([] : List Bool).length) = σ := by
      rw [show marks ([] : List Bool) = [] from rfl, NearCubicWires.WireExponent3_5.PrimAsm.WriteNat.appendO_nil]
      apply WState.eq <;> try rfl
      funext x; by_cases hx : x = s
      · subst hx; simp [hsh]
      · simp [Function.update_of_ne hx]
    rw [e]
    exact WExec.whsF hb
  | b :: w, pre, rest, σ, hst, hr, hsh, ho, hc => by
    have hm : marks (b :: w) = true :: b :: marks w := by simp [marks]
    have hb : wbit σ s = true := by
      unfold wbit; rw [hst, hsh, hm, List.append_assoc, rtb_app0]; rfl
    have h1 := WExec.fwd (cap := cap) s σ
    have h2 := Codec.frameCell_spec cap s o hso OP (σ.seth s (σ.sh s + 1)) (by simp [Ne.symm hso, ho])
      (by simp; simp at hc; omega)
    have hbit : readTapeBit ((σ.seth s (σ.sh s + 1)).st s) ((σ.seth s (σ.sh s + 1)).sh s) = b := by
      simp only [WState.seth_st, WState.seth_sh, Function.update_self]
      rw [hst, hsh, hm, List.append_assoc, rtb_app pre _ 1]; rfl
    rw [hbit] at h2
    set σ2 := (appendO (σ.seth s (σ.sh s + 1)) o OP [true, b]).seth s ((σ.seth s (σ.sh s + 1)).sh s + 1) with hσ2
    have ih := copyMarks_spec s o hso OP w (pre ++ [true, b]) rest σ2
      (by simp [hσ2, Function.update_of_ne hso, hst, hm])
      hr (by simp [hσ2, hsh]) (by simp [hσ2, Function.update_of_ne (Ne.symm hso), ho])
      (by simp [hσ2, Function.update_of_ne (Ne.symm hso)]; simp at hc; omega)
    refine WExec.cast cap (WExec.whsT hb (WExec.seq h1 h2) ih) ?_ (by simp; ring_nf; omega)
    apply WState.eq
    · funext x; by_cases hx : x = s
      · subst hx; simp [hσ2, Function.update_of_ne hso]; omega
      · by_cases hxo : x = o
        · subst hxo; simp [hσ2, Function.update_of_ne hx, hm]; omega
        · simp [hσ2, Function.update_of_ne hx, Function.update_of_ne hxo]
    · funext x; by_cases hxo : x = o
      · subst hxo; simp [hσ2, Function.update_of_ne (Ne.symm hso), hm]
      · simp [hσ2, Function.update_of_ne hxo]
    · funext r; by_cases hr' : r = OP
      · subst hr'; simp [hσ2, hm]; omega
      · simp [hσ2, Function.update_of_ne hr']
    · simp [hσ2]

/-! ## Copying `D`'s nodes -/

/-- Copy one node's three marked `natWord` fields from `s` to `o`. -/
def copy3 (s o : Fin (ns + 1)) (R : Fin 8 ↪ Fin nr) : WM ns nr :=
  .seq (Codec.copyNat true s o R) (.seq (Codec.copyNat true s o R) (Codec.copyNat true s o R))

theorem marks_len' (w : List Bool) : (marks w).length = 2 * w.length := by
  induction w with
  | nil => rfl
  | cons b w ih => simp [marks, List.flatMap_cons] at ih ⊢; omega

theorem enc_true (w : List Bool) : NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.enc true w = marks w := rfl

theorem copy3_words (s o : Fin (ns + 1)) (hso : s ≠ o) (R : Fin 8 ↪ Fin nr) (x0 x1 x2 : ℕ)
    (pre rest : List Bool) (σ : WState ns nr)
    (hst : σ.st s = pre ++ (marks (natWord x0) ++ marks (natWord x1) ++ marks (natWord x2)) ++ rest)
    (hsh : σ.sh s = pre.length) (ho : σ.sh o = (σ.st o).length) (h1 : σ.val (R 1) = 0) (h2 : σ.val (R 2) = 0)
    (hcap : σ.val (R 7) + 2 * ((natWord x0).length + (natWord x1).length + (natWord x2).length) + 2 ≤ cap) :
    WExec cap (copy3 s o R) σ
      ((appendO σ o (R 7) (marks (natWord x0) ++ marks (natWord x1) ++ marks (natWord x2))).seth s
        (pre.length + 2 * ((natWord x0).length + (natWord x1).length + (natWord x2).length)))
      (60 * ((natWord x0).length + (natWord x1).length + (natWord x2).length) + 182) := by
  have hR7 : ∀ i : Fin 8, i ≠ 7 → R i ≠ R 7 := fun i hi => R.injective.ne hi
  have m0 := marks_len' (natWord x0)
  have m1 := marks_len' (natWord x1)
  have m2 := marks_len' (natWord x2)
  have e1 := Codec.copyNat_spec cap true s o hso R x0 pre (marks (natWord x1) ++ marks (natWord x2) ++ rest)
    σ (by rw [hst, enc_true]; simp only [List.append_assoc]) hsh ho h1 h2 (by omega)
  simp only [stp, if_true] at e1
  have e2 := Codec.copyNat_spec cap true s o hso R x1 (pre ++ marks (natWord x0)) (marks (natWord x2) ++ rest)
    ((appendO σ o (R 7) (marks (natWord x0))).seth s (pre.length + 2 * (natWord x0).length))
    (by simp only [WState.seth_st, appendO_st, Function.update_of_ne hso, hst, enc_true, List.append_assoc])
    (by simp only [WState.seth_sh, Function.update_self, List.length_append, m0])
    (by simp only [WState.seth_sh, WState.seth_st, appendO_st, appendO_sh, Function.update_of_ne (Ne.symm hso),
      Function.update_self, List.length_append, ho])
    (by simp only [WState.seth_val, appendO_val, Function.update_of_ne (hR7 1 (by decide)), h1])
    (by simp only [WState.seth_val, appendO_val, Function.update_of_ne (hR7 2 (by decide)), h2])
    (by simp only [WState.seth_val, appendO_val, Function.update_self]; omega)
  simp only [stp, if_true] at e2
  have e3 := Codec.copyNat_spec cap true s o hso R x2 (pre ++ marks (natWord x0) ++ marks (natWord x1)) rest
    ((appendO ((appendO σ o (R 7) (marks (natWord x0))).seth s (pre.length + 2 * (natWord x0).length)) o (R 7)
      (marks (natWord x1))).seth s ((pre ++ marks (natWord x0)).length + 2 * (natWord x1).length))
    (by simp only [WState.seth_st, appendO_st, Function.update_of_ne hso, hst, enc_true, List.append_assoc])
    (by simp only [WState.seth_sh, Function.update_self, List.length_append, m0, m1])
    (by simp only [WState.seth_sh, WState.seth_st, appendO_st, appendO_sh, Function.update_of_ne (Ne.symm hso),
      Function.update_self, List.length_append, ho])
    (by simp only [WState.seth_val, appendO_val, Function.update_of_ne (hR7 1 (by decide)), h1])
    (by simp only [WState.seth_val, appendO_val, Function.update_of_ne (hR7 2 (by decide)), h2])
    (by simp only [WState.seth_val, appendO_val, Function.update_self]; omega)
  simp only [stp, if_true] at e3
  refine WExec.cast cap (WExec.seq e1 (WExec.seq e2 e3)) ?_ (by omega)
  apply WState.eq
  · funext x; by_cases hx : x = s
    · subst hx
      simp only [WState.seth_sh, appendO_sh, Function.update_self, List.length_append, m0, m1]; ring
    · by_cases hxo : x = o
      · subst hxo
        simp only [WState.seth_sh, appendO_sh, appendO_st, WState.seth_st, Function.update_of_ne hx,
          Function.update_self, Function.update_of_ne (Ne.symm hso), List.length_append, m0, m1, m2]; ring
      · simp only [WState.seth_sh, appendO_sh, Function.update_of_ne hx, Function.update_of_ne hxo]
  · funext x; by_cases hxo : x = o
    · subst hxo
      simp only [WState.seth_st, appendO_st, Function.update_self, Function.update_of_ne (Ne.symm hso),
        List.append_assoc]
    · simp only [WState.seth_st, appendO_st, Function.update_of_ne hxo]
  · funext r; by_cases hr : r = R 7
    · subst hr
      simp only [WState.seth_val, appendO_val, Function.update_self, List.length_append, m0, m1, m2]; ring
    · simp only [WState.seth_val, appendO_val, Function.update_of_ne hr]
  · simp only [WState.seth_cell, appendO_cell]

theorem copy3_spec (s o : Fin (ns + 1)) (hso : s ≠ o) (R : Fin 8 ↪ Fin nr) {n : ℕ} (nd : BooleanNode n)
    (pre rest : List Bool) (σ : WState ns nr) (hst : σ.st s = pre ++ marks (PCPPRequestNodeSchema.native nd) ++ rest)
    (hsh : σ.sh s = pre.length) (ho : σ.sh o = (σ.st o).length) (h1 : σ.val (R 1) = 0) (h2 : σ.val (R 2) = 0)
    (hcap : σ.val (R 7) + 2 * (PCPPRequestNodeSchema.native nd).length + 2 ≤ cap) :
    WExec cap (copy3 s o R) σ
      ((appendO σ o (R 7) (marks (PCPPRequestNodeSchema.native nd))).seth s
        (pre.length + (marks (PCPPRequestNodeSchema.native nd)).length))
      (60 * (PCPPRequestNodeSchema.native nd).length + 182) := by
  have hn := native_fields nd
  have hm : marks (PCPPRequestNodeSchema.native nd) = marks (natWord (PCPPRequestNodeSchema.fields nd 0)) ++
      marks (natWord (PCPPRequestNodeSchema.fields nd 1)) ++ marks (natWord (PCPPRequestNodeSchema.fields nd 2)) := by
    rw [hn, NodeEmit.marks_append, NodeEmit.marks_append]
  have hl : (PCPPRequestNodeSchema.native nd).length = (natWord (PCPPRequestNodeSchema.fields nd 0)).length +
      (natWord (PCPPRequestNodeSchema.fields nd 1)).length + (natWord (PCPPRequestNodeSchema.fields nd 2)).length := by
    rw [hn]; simp only [List.length_append]
  have e := copy3_words cap s o hso R _ _ _ pre rest σ (by rw [hst, hm]) hsh ho h1 h2 (by rw [← hl]; exact hcap)
  rw [← hm, ← hl, ← marks_len'] at e
  exact e

/-! ## Registers -/

/-- The check writer's registers inside the descriptor writer's (`H 18` is the node-copy counter). -/
def Gof (H : Fin 19 ↪ Fin nr) : Fin 18 ↪ Fin nr :=
  ⟨fun i => H (Fin.castLE (by decide) i), fun a b h => by
    have := H.injective h
    exact Fin.ext (by simpa [Fin.ext_iff] using this)⟩

variable (H : Fin 19 ↪ Fin nr)

theorem H_ne {a b : Fin 19} (h : a ≠ b) : H a ≠ H b := H.injective.ne h
theorem RH (i : Fin 8) : Rw (Gof H) i = H (Fin.castLE (by decide) i) := rfl
theorem GH (a : Fin 18) : Gof H a = H (Fin.castLE (by decide) a) := rfl

theorem pow_bitlen_le (x : ℕ) : 2 ^ natBitLength x ≤ 2 * x + 2 := by
  unfold natBitLength
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · simp
  · have := Nat.pow_log_le_self 2 (show x ≠ 0 by omega)
    rw [pow_succ]; omega

/-- Read one marked `natWord` of `DD` into `G a` (scratch `R 1 … R 4`). -/
def readG (DD : Fin (ns + 1)) (a : Fin 18) : WM ns nr :=
  readNatM true DD (Rw (Gof H) 1) (Rw (Gof H) 2) (Gof H a) (Rw (Gof H) 3) (Rw (Gof H) 4)

/-- The cost bound of one read of a value at most `V`. -/
def readCost (V : ℕ) : ℕ := (V + 3) * (80 * V + 120)

theorem readG_spec (DD : Fin (ns + 1)) (a : Fin 18) (ha : 8 ≤ a.val) (x V : ℕ) (hx : x ≤ V) (pre rest : List Bool)
    (σ : WState ns nr) (hst : σ.st DD = pre ++ marks (natWord x) ++ rest) (hsh : σ.sh DD = pre.length)
    (hcl : ∀ i : Fin 8, i ≠ 7 → σ.val (Rw (Gof H) i) = 0) (hcap : σ.val (Gof H a) + 4 * V + 4 ≤ cap) :
    WExec cap (readG H DD a) σ ((σ.seth DD (pre.length + 2 * (natWord x).length)).setv (Gof H a) (σ.val (Gof H a) + x))
      (readCost V) := by
  have hRG : ∀ i : Fin 8, Rw (Gof H) i ≠ Gof H a := fun i => Rw_ne (Gof H) i a ha
  have hRR : ∀ i j : Fin 8, i ≠ j → Rw (Gof H) i ≠ Rw (Gof H) j := fun i j h => (Rw (Gof H)).injective.ne h
  have hp := pow_bitlen_le x
  have hb := natBitLength_le x
  have e := readNatM_spec cap true DD _ _ _ _ _ (hRR 1 2 (by decide)) (hRG 1) (hRR 1 3 (by decide))
    (hRR 1 4 (by decide)) (hRG 2) (hRR 2 3 (by decide)) (hRR 2 4 (by decide)) (hRG 3)
    (hRR 3 4 (by decide)) (fun h => hRG 4 h.symm) x pre rest σ (by rw [hst, enc_true]) hsh (hcl 1 (by decide)) (hcl 2 (by decide))
    (hcl 3 (by decide)) (hcl 4 (by decide)) (by rw [pow_succ]; omega)
  simp only [stp, if_true] at e
  refine WExec.mono e ?_
  unfold readCost
  have h1 : natBitLength x + 2 ≤ V + 3 := by omega
  have h2 : 40 * 2 ^ natBitLength x + 40 ≤ 80 * V + 120 := by omega
  exact Nat.mul_le_mul h1 h2

theorem frame_eq_marks' : ∀ l : List Bool, RepairOrdinary.frame l = marks l ++ [false]
  | [] => rfl
  | b :: l => by simp [RepairOrdinary.frame, marks, frame_eq_marks' l]

theorem marks_flatMap' {α : Type} (u : α → List Bool) (xs : List α) :
    marks (xs.flatMap u) = xs.flatMap fun x => marks (u x) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.flatMap_cons, NodeEmit.marks_append, ih]

theorem length_le_bytes {n : ℕ} : ∀ nds : List (BooleanNode n),
    nds.length ≤ (nds.flatMap PCPPRequestNodeSchema.native).length
  | [] => le_rfl
  | nd :: nds => by
    have := length_le_bytes nds
    have h3 : 1 ≤ (PCPPRequestNodeSchema.native nd).length := by
      rw [native_len, ChecksW.natWord_len]; omega
    simp only [List.flatMap_cons, List.length_append, List.length_cons]; omega

/-! ## The front: header, `D`'s nodes to `SN`, output index -/

section Front
@[simp] theorem g0 : Gof H 0 = H 0 := rfl
@[simp] theorem g1 : Gof H 1 = H 1 := rfl
@[simp] theorem g2 : Gof H 2 = H 2 := rfl
@[simp] theorem g3 : Gof H 3 = H 3 := rfl
@[simp] theorem g4 : Gof H 4 = H 4 := rfl
@[simp] theorem g5 : Gof H 5 = H 5 := rfl
@[simp] theorem g6 : Gof H 6 = H 6 := rfl
@[simp] theorem g7 : Gof H 7 = H 7 := rfl
@[simp] theorem g8 : Gof H 8 = H 8 := rfl
@[simp] theorem g9 : Gof H 9 = H 9 := rfl
@[simp] theorem g10 : Gof H 10 = H 10 := rfl
@[simp] theorem g11 : Gof H 11 = H 11 := rfl
@[simp] theorem g12 : Gof H 12 = H 12 := rfl
@[simp] theorem g13 : Gof H 13 = H 13 := rfl
@[simp] theorem g14 : Gof H 14 = H 14 := rfl
@[simp] theorem g15 : Gof H 15 = H 15 := rfl
@[simp] theorem g16 : Gof H 16 = H 16 := rfl
@[simp] theorem g17 : Gof H 17 = H 17 := rfl
@[simp] theorem r0 : Rw (Gof H) 0 = H 0 := rfl
@[simp] theorem r1 : Rw (Gof H) 1 = H 1 := rfl
@[simp] theorem r2 : Rw (Gof H) 2 = H 2 := rfl
@[simp] theorem r3 : Rw (Gof H) 3 = H 3 := rfl
@[simp] theorem r4 : Rw (Gof H) 4 = H 4 := rfl
@[simp] theorem r5 : Rw (Gof H) 5 = H 5 := rfl
@[simp] theorem r6 : Rw (Gof H) 6 = H 6 := rfl
@[simp] theorem r7 : Rw (Gof H) 7 = H 7 := rfl

/-- Read `q`, `m`; copy `D`'s `m` nodes to `SN`; read the output index `o`; rewind `SN`. -/
def frontW (DD SN : Fin (ns + 1)) : WM ns nr :=
  .seq (readG H DD 9) (.seq (readG H DD 10) (.seq (setR (H 18) (H 8) [H 10] 0)
    (.seq (Codec.listLoop (H 18) (copy3 DD SN (Rw (Gof H)))) (.seq (readG H DD 12) (WM.rewind SN (H 7))))))

/-- The front's cost. -/
def frontCost (V : ℕ) : ℕ := 3 * readCost V + 21 * V + 7 + (246 * V + 1) + (10 * V + 1) + 5

theorem frontW_spec (DD SN : Fin (ns + 1)) (hDS : DD ≠ SN) (D : Circuit) (V : ℕ)
    (hV : (PCPPNative.descriptor D.D).length ≤ V) (hcap : 4 * V + 8 ≤ cap) (σ : WState ns nr)
    (hDD : σ.st DD = RepairOrdinary.frame (PCPPNative.descriptor D.D)) (hDDh : σ.sh DD = 0)
    (hSN : σ.st SN = []) (hSNh : σ.sh SN = 0) (hreg : ∀ i : Fin 19, i ≠ 16 → σ.val (H i) = 0) :
    ∃ τ, WExec cap (frontW H DD SN) σ τ (frontCost V) ∧
      τ.st SN = marks (D.D.nodes.flatMap PCPPRequestNodeSchema.native) ∧ τ.sh SN = 0 ∧
      τ.val (H 9) = D.n ∧ τ.val (H 10) = D.D.nodes.length ∧ τ.val (H 12) = D.D.output.val ∧
      SameExcept σ τ [DD, SN] [H 9, H 10, H 12] := by
  set q := D.n
  set m := D.D.nodes.length
  set o := D.D.output.val
  set bytes := D.D.nodes.flatMap PCPPRequestNodeSchema.native with hbytes
  have hdesc : PCPPNative.descriptor D.D = natWord q ++ natWord m ++ bytes ++ natWord o :=
    PCPPNative.descriptor_eq D.D
  have hl : (PCPPNative.descriptor D.D).length = (natWord q).length + (natWord m).length + bytes.length +
      (natWord o).length := by rw [hdesc]; simp only [List.length_append]
  have hmb : m ≤ bytes.length := length_le_bytes D.D.nodes
  have hqm : q ≤ m := D.sizeAtLeast
  have hom : o < m := D.D.output.isLt
  have hbV : bytes.length ≤ V := by omega
  have hnq : q ≤ V := by omega
  have hframe : σ.st DD = marks (natWord q) ++ marks (natWord m) ++ D.D.nodes.flatMap
      (fun nd => marks (PCPPRequestNodeSchema.native nd)) ++ (marks (natWord o) ++ [false]) := by
    rw [hDD, frame_eq_marks', hdesc]
    simp only [NodeEmit.marks_append, hbytes, marks_flatMap', List.append_assoc]
  have hz : ∀ i : Fin 19, i ≠ 16 → σ.val (H i) = 0 := hreg
  -- read q
  have e1 := readG_spec cap H DD 9 (by decide) q V hnq [] (marks (natWord m) ++ D.D.nodes.flatMap
      (fun nd => marks (PCPPRequestNodeSchema.native nd)) ++ (marks (natWord o) ++ [false])) σ
    (by rw [hframe]; simp only [List.nil_append, List.append_assoc]) (by simp [hDDh])
    (fun i hi => by rw [RH]; exact hz _ (by intro e; have := congrArg Fin.val e; simp at this; omega))
    (by simp [hz 9 (by decide)]; omega)
  simp only [g9, List.length_nil, Nat.zero_add, hz 9 (by decide)] at e1
  set σ1 := (σ.seth DD (2 * (natWord q).length)).setv (H 9) q with hσ1
  -- read m
  have e2 := readG_spec cap H DD 10 (by decide) m V (by omega) (marks (natWord q))
      (D.D.nodes.flatMap (fun nd => marks (PCPPRequestNodeSchema.native nd)) ++ (marks (natWord o) ++ [false])) σ1
    (by simp only [hσ1, WState.setv_st, WState.seth_st, hframe, List.append_assoc])
    (by simp [hσ1, marks_len'])
    (fun i hi => by
      rw [RH]
      have h1 : H (Fin.castLE (by decide) i) ≠ H 9 := H_ne H (by intro e; have := congrArg Fin.val e; simp at this; omega)
      simp only [hσ1, WState.setv_val, WState.seth_val, Function.update_of_ne h1]
      exact hz _ (by intro e; have := congrArg Fin.val e; simp at this; omega))
    (by simp [hσ1, hz 10 (by decide)]; omega)
  simp only [g10] at e2
  have hσ1_10 : σ1.val (H 10) = 0 := by simp [hσ1, hz 10 (by decide)]
  rw [hσ1_10, Nat.zero_add] at e2
  set σ2 := (σ1.seth DD ((marks (natWord q)).length + 2 * (natWord m).length)).setv (H 10) m with hσ2
  -- counter := m
  have e3 := setR_spec cap (D := H 18) (T := H 8) (H_ne H (by decide)) [H 10] 0 σ2
    (by intro a ha; simp at ha; subst ha; exact ⟨H_ne H (by decide), H_ne H (by decide)⟩)
    (by simp [hσ2, hσ1, hz 8 (by decide)]) (by simp [hσ2, hσ1, hz 18 (by decide)])
    (by simp [regSum, hσ2]; omega)
  have hσ2_18 : σ2.val (H 18) = 0 := by simp [hσ2, hσ1, hz 18 (by decide)]
  have hrs : regSum σ2 [H 10] = m := by simp [regSum, hσ2]
  rw [hσ2_18, hrs] at e3
  set σ3 := σ2.setv (H 18) (m + 0) with hσ3
  -- copy the nodes
  have hok : ∀ τ : WState ns nr, (τ.val (H 1) = 0 ∧ τ.val (H 2) = 0) →
      τ.val (Rw (Gof H) 1) = 0 ∧ τ.val (Rw (Gof H) 2) = 0 := fun τ h => h
  have e4 := Codec.copyLoop_spec cap DD SN hDS (H 18) (Rw (Gof H) 7) (by simp) (copy3 DD SN (Rw (Gof H)))
    (fun nd => marks (PCPPRequestNodeSchema.native nd)) PCPPRequestNodeSchema.native
    (fun nd => 60 * (PCPPRequestNodeSchema.native nd).length + 182)
    (fun τ => τ.val (H 1) = 0 ∧ τ.val (H 2) = 0) (2 * bytes.length)
    (fun τ x h => h) (fun τ x h => by simp; exact h) (fun τ w h => by simp; exact h) D.D.nodes
    (by
      intro x _ pre rest τ hτ hst hsh ho hV'
      have := copy3_spec cap DD SN hDS (Rw (Gof H)) x pre rest τ hst hsh ho hτ.1 hτ.2
        (by rw [marks_len'] at hV'; omega)
      exact this)
    (marks (natWord q) ++ marks (natWord m)) (marks (natWord o) ++ [false]) σ3
    (by simp [hσ3, hσ2, hσ1, hz 1 (by decide), hz 2 (by decide)])
    (by simp only [hσ3, hσ2, hσ1, WState.setv_st, WState.seth_st, hframe])
    (by simp [hσ3, hσ2, hσ1, marks_len'])
    (by simp [hσ3, hσ2, hσ1, Function.update_of_ne (Ne.symm hDS), hSN, hSNh])
    (by simp [hσ3]; rfl) (by omega)
    (by simp [hσ3, hσ2, hσ1, hz 7 (by decide), marks_len', hbytes, List.length_flatMap])
  set σ4 := ((appendO σ3 SN (Rw (Gof H) 7) (marks (D.D.nodes.flatMap PCPPRequestNodeSchema.native))).setv (H 18)
    0).seth DD ((marks (natWord q) ++ marks (natWord m)).length +
      (D.D.nodes.flatMap fun nd => marks (PCPPRequestNodeSchema.native nd)).length) with hσ4
  -- read o
  have hσ4_12 : σ4.val (H 12) = 0 := by simp [hσ4, hσ3, hσ2, hσ1, hz 12 (by decide)]
  have e5 := readG_spec cap H DD 12 (by decide) o V (by omega)
      (marks (natWord q) ++ marks (natWord m) ++ D.D.nodes.flatMap (fun nd => marks (PCPPRequestNodeSchema.native nd)))
      [false] σ4
    (by simp only [hσ4, hσ3, hσ2, hσ1, WState.seth_st, WState.setv_st, appendO_st, Function.update_of_ne hDS, hframe,
          List.append_assoc])
    (by simp [hσ4]; omega)
    (fun i hi => by
      rw [RH]
      have hi' : i.val ≠ 7 := fun h => hi (Fin.ext h)
      have hlt := i.isLt
      have h16 : (Fin.castLE (by decide) i : Fin 19) ≠ 16 := by
        intro e; have := congrArg Fin.val e; simp at this; omega
      simp only [hσ4, hσ3, hσ2, hσ1, WState.seth_val, WState.setv_val, appendO_val, r7, Function.update_apply,
        EmbeddingLike.apply_eq_iff_eq, Fin.ext_iff, Fin.val_castLE]
      split_ifs <;> first | omega | exact hz _ h16)
    (by rw [g12, hσ4_12]; omega)
  simp only [g12] at e5
  rw [hσ4_12, Nat.zero_add] at e5
  set σ5 := (σ4.seth DD ((marks (natWord q) ++ marks (natWord m) ++
    D.D.nodes.flatMap (fun nd => marks (PCPPRequestNodeSchema.native nd))).length + 2 * (natWord o).length)).setv
      (H 12) o with hσ5
  -- rewind SN
  have h7 : σ5.val (H 7) = (marks bytes).length := by
    simp [hσ5, hσ4, hσ3, hσ2, hσ1, hz 7 (by decide), marks_len', hbytes, List.length_flatMap]
  have e6 := wrewind_spec (cap := cap) SN (H 7) (marks bytes).length σ5 h7 (by rw [h7, marks_len']; omega)
  have hSNsh : σ5.sh SN = (marks bytes).length := by
    simp [hσ5, hσ4, hσ3, hσ2, hσ1, Function.update_of_ne (Ne.symm hDS), hSNh, hbytes]
  refine ⟨_, WExec.mono (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 (WExec.seq e5 e6))))) ?_,
    ?_, ?_, ?_, ?_, ?_, ⟨fun x hx => ?_, fun r hr => ?_, by simp [hσ5, hσ4, hσ3, hσ2, hσ1]⟩⟩
  · -- cost
    have hloop : ((D.D.nodes.map fun x => 60 * (PCPPRequestNodeSchema.native x).length + 182 + 4).sum + 1) ≤
        246 * V + 1 := by
      have : ∀ nds : List (BooleanNode q), (nds.map fun x => 60 * (PCPPRequestNodeSchema.native x).length + 182 + 4).sum
          = 60 * (nds.flatMap PCPPRequestNodeSchema.native).length + 186 * nds.length := by
        intro nds; induction nds with
        | nil => rfl
        | cons x xs ih => simp only [List.map_cons, List.sum_cons, ih, List.flatMap_cons, List.length_append,
            List.length_cons]; ring
      rw [this, ← hbytes]; omega
    have hrw : 5 * (marks bytes).length + 1 ≤ 10 * V + 1 := by rw [marks_len']; omega
    unfold frontCost
    simp only [List.length_cons, List.length_nil] at hloop ⊢
    omega
  · simp [hσ5, hσ4, hσ3, hσ2, hσ1, Function.update_of_ne (Ne.symm hDS), hSN, hbytes]
  · simp [hSNsh]
  · simp [hσ5, hσ4, hσ3, hσ2, hσ1]; rfl
  · simp [hσ5, hσ4, hσ3, hσ2, hσ1]; rfl
  · simp [hσ5]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    simp [hσ5, hσ4, hσ3, hσ2, hσ1, Function.update_of_ne hx.1, Function.update_of_ne hx.2]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    by_cases h7r : r = H 7
    · subst h7r; simp [hz 7 (by decide)]
    · by_cases h18 : r = H 18
      · subst h18; simp [hσ5, hσ4, hz 18 (by decide)]
      · simp [hσ5, hσ4, hσ3, hσ2, hσ1, Function.update_of_ne h7r, Function.update_of_ne h18,
          Function.update_of_ne hr.1, Function.update_of_ne hr.2.1, Function.update_of_ne hr.2.2]

/-- The back: rewind `SC`; write the header, `D`'s nodes, the checks, the output index and the closing `false`. -/
def backW (SN SC OUT : Fin (ns + 1)) : WM ns nr :=
  .seq (WM.rewind SC (H 7)) (.seq (fieldW OUT (Rw (Gof H)) (H 8) ([H 9, H 16], 0))
    (.seq (fieldW OUT (Rw (Gof H)) (H 8) ([H 10], 0)) (.seq (copyMarks SN OUT (H 7))
    (.seq (copyMarks SC OUT (H 7)) (.seq (fieldW OUT (Rw (Gof H)) (H 8) ([H 12], 0)) (emitC OUT (H 7) false))))))

def descW (DD SN SC OUT MAT : Fin (ns + 1)) : WMX ns nr :=
  .seq (.wm (frontW H DD SN)) (.seq (checksW (Gof H) SC MAT) (.wm (backW H SN SC OUT)))

/-- The back's cost. -/
def backCost (V : ℕ) : ℕ := 16 * (V * (12 * V + 18)) + 3 * fieldCost V 3 + 22 * V + 20

def descCost (q L V : ℕ) : ℕ := frontCost V + 1 + checksCost q L V + 1 + backCost V

end Front

/-- The checked circuit's native descriptor, as the machine writes it. -/
theorem checked_frame (E : LinearCodeFamily) (D : Circuit) :
    RepairOrdinary.frame (PCPPNative.descriptor (checkedCircuit E D).D) =
      marks (natWord (D.n + E.length D.n)) ++
      marks (natWord (D.D.nodes.length +
        (checksNodes E D.n D.D.nodes.length (List.finRange (E.length D.n)) D.D.output.val).1.length)) ++
      marks (D.D.nodes.flatMap PCPPRequestNodeSchema.native) ++
      marks ((checksNodes E D.n D.D.nodes.length (List.finRange (E.length D.n)) D.D.output.val).1.flatMap
        PCPPRequestNodeSchema.native) ++
      marks (natWord (checksNodes E D.n D.D.nodes.length (List.finRange (E.length D.n)) D.D.output.val).2) ++
      [false] := by
  rw [frame_eq_marks', checkedDesc_eq]
  simp only [NodeEmit.marks_append, List.append_assoc]

/-- The back, on generic contents: `SN` holds `marks w1`, `SC` holds `marks w2` (head at its end), `OUT` is empty. -/
theorem backW_spec (SN SC OUT : Fin (ns + 1)) (hSC : SN ≠ SC) (hSO : SN ≠ OUT) (hCO : SC ≠ OUT)
    (w1 w2 : List Bool) (a K R V : ℕ) (σ : WState ns nr)
    (hSN : σ.st SN = marks w1) (hSNh : σ.sh SN = 0) (hSCs : σ.st SC = marks w2) (hSCh : σ.sh SC = (marks w2).length)
    (h7 : σ.val (H 7) = (marks w2).length) (hO : σ.st OUT = []) (hOh : σ.sh OUT = 0)
    (ha : σ.val (H 9) + σ.val (H 16) = a) (hK : σ.val (H 10) = K) (hR : σ.val (H 12) = R)
    (hcl : Clean (Rw (Gof H)) (H 8) σ) (haV : a ≤ V) (hKV : K ≤ V) (hRV : R ≤ V) (h1V : w1.length ≤ V)
    (h2V : 2 * w2.length ≤ V * (12 * V + 18)) (hcap : 200 * (V + 1) * (V + 1) ≤ cap) :
    ∃ τ, WExec cap (backW H SN SC OUT) σ τ (16 * (V * (12 * V + 18)) + 3 * fieldCost V 3 + 22 * V + 20) ∧
      τ.st OUT = marks (natWord a) ++ marks (natWord K) ++ marks w1 ++ marks w2 ++ marks (natWord R) ++ [false] ∧
      τ.sh OUT = (τ.st OUT).length ∧ τ.val (H 7) = (τ.st OUT).length ∧ Clean (Rw (Gof H)) (H 8) τ ∧
      SameExcept σ τ [SN, SC, OUT] [H 7] := by
  have bl := natBitLength_le
  have la := ChecksW.natWord_len a
  have lK := ChecksW.natWord_len K
  have lR := ChecksW.natWord_len R
  have hba := bl a
  have hbK := bl K
  have hbR := bl R
  have m1 := marks_len' w1
  have m2 := marks_len' w2
  have ma := marks_len' (natWord a)
  have mK := marks_len' (natWord K)
  have mR := marks_len' (natWord R)
  have hVV : V ≤ V * (12 * V + 18) := by nlinarith
  have hcapV : V * (12 * V + 18) + 40 * V + 60 ≤ cap := by nlinarith
  -- 1. rewind SC
  have b1 := wrewind_spec (cap := cap) SC (H 7) (marks w2).length σ h7 (by omega)
  rw [hSCh, Nat.sub_self] at b1
  set τ1 := (σ.setv (H 7) 0).seth SC 0 with hτ1
  have s1 : τ1.st OUT = [] := by simp only [hτ1, WState.seth_st, WState.setv_st, hO]
  have t1 : τ1.sh OUT = 0 := by simp only [hτ1, WState.seth_sh, WState.setv_sh, Function.update_of_ne hCO.symm, hOh]
  have v1 : τ1.val (H 7) = 0 := by simp [hτ1]
  have hcl1 : Clean (Rw (Gof H)) (H 8) τ1 := ⟨fun i hi => by
      have : Rw (Gof H) i ≠ H 7 := by
        rw [RH]; exact H_ne H (by intro e; apply hi; ext; have := congrArg Fin.val e; simpa using this)
      simp [hτ1, Function.update_of_ne this, hcl.1 i hi], by simp [hτ1, hcl.2]⟩
  -- 2. natWord a
  have hfa : fieldVal τ1 ([H 9, H 16], 0) = a := by simp [fieldVal, regSum, hτ1, ← ha]
  have b2 := fieldW_spec cap OUT (Rw (Gof H)) (H 8) (T_ne (Gof H)) ([H 9, H 16], 0) (fieldOK_G (Gof H) [9, 16] 0
    (by decide)) τ1 hcl1 (by rw [s1, t1]; rfl) (by rw [hfa, show Rw (Gof H) 7 = H 7 from rfl, v1]; omega)
  rw [hfa] at b2
  set τ2 := appendO τ1 OUT (H 7) (marks (natWord a)) with hτ2
  have s2 : τ2.st OUT = marks (natWord a) := by simp [hτ2, s1]
  have t2 : τ2.sh OUT = (marks (natWord a)).length := by simp [hτ2, t1]
  have v2 : τ2.val (H 7) = (marks (natWord a)).length := by simp [hτ2, v1]
  have hcl2 := clean_appendO OUT _ _ τ1 hcl1 (T_ne (Gof H)) (marks (natWord a))
  -- 3. natWord K
  have hfK : fieldVal τ2 ([H 10], 0) = K := by simp [fieldVal, regSum, hτ2, hτ1, hK]
  have b3 := fieldW_spec cap OUT (Rw (Gof H)) (H 8) (T_ne (Gof H)) ([H 10], 0) (fieldOK_G (Gof H) [10] 0
    (by decide)) τ2 hcl2 (by rw [s2, t2]) (by rw [hfK, show Rw (Gof H) 7 = H 7 from rfl, v2]; omega)
  rw [hfK] at b3
  set τ3 := appendO τ2 OUT (H 7) (marks (natWord K)) with hτ3
  have s3 : τ3.st OUT = marks (natWord a) ++ marks (natWord K) := by simp [hτ3, s2]
  have t3 : τ3.sh OUT = (marks (natWord a) ++ marks (natWord K)).length := by simp [hτ3, t2]
  have v3 : τ3.val (H 7) = (marks (natWord a) ++ marks (natWord K)).length := by simp [hτ3, v2]
  have hcl3 := clean_appendO OUT _ _ τ2 hcl2 (T_ne (Gof H)) (marks (natWord K))
  have sn3 : τ3.st SN = marks w1 ∧ τ3.sh SN = 0 := by
    simp [hτ3, hτ2, hτ1, Function.update_of_ne hSO, Function.update_of_ne hSC, hSN, hSNh]
  -- 4. D's nodes
  have b4 := copyMarks_spec cap SN OUT hSO (H 7) w1 [] [] τ3 (by rw [sn3.1]; simp) rfl (by rw [sn3.2]; rfl)
    (by rw [s3, t3]) (by rw [v3]; simp only [List.length_append]; omega)
  set τ4 := (appendO τ3 OUT (H 7) (marks w1)).seth SN (0 + 2 * w1.length) with hτ4
  have s4 : τ4.st OUT = marks (natWord a) ++ marks (natWord K) ++ marks w1 := by simp [hτ4, s3]
  have t4 : τ4.sh OUT = (marks (natWord a) ++ marks (natWord K) ++ marks w1).length := by
    simp [hτ4, Function.update_of_ne hSO.symm, t3]; omega
  have v4 : τ4.val (H 7) = (marks (natWord a) ++ marks (natWord K) ++ marks w1).length := by simp [hτ4, v3]; omega
  have hcl4 : Clean (Rw (Gof H)) (H 8) τ4 := clean_appendO OUT _ _ τ3 hcl3 (T_ne (Gof H)) (marks w1)
  have sc4 : τ4.st SC = marks w2 ∧ τ4.sh SC = 0 := by
    simp [hτ4, hτ3, hτ2, hτ1, Function.update_of_ne hCO, Function.update_of_ne hSC.symm, hSCs]
  -- 5. the checks
  have b5 := copyMarks_spec cap SC OUT hCO (H 7) w2 [] [] τ4 (by rw [sc4.1]; simp) rfl (by rw [sc4.2]; rfl)
    (by rw [s4, t4]) (by rw [v4]; simp only [List.length_append]; omega)
  set τ5 := (appendO τ4 OUT (H 7) (marks w2)).seth SC (0 + 2 * w2.length) with hτ5
  have s5 : τ5.st OUT = marks (natWord a) ++ marks (natWord K) ++ marks w1 ++ marks w2 := by simp [hτ5, s4]
  have t5 : τ5.sh OUT = (marks (natWord a) ++ marks (natWord K) ++ marks w1 ++ marks w2).length := by
    simp [hτ5, Function.update_of_ne hCO.symm, t4]; omega
  have v5 : τ5.val (H 7) = (marks (natWord a) ++ marks (natWord K) ++ marks w1 ++ marks w2).length := by
    simp [hτ5, v4]; omega
  have hcl5 : Clean (Rw (Gof H)) (H 8) τ5 := clean_appendO OUT _ _ τ4 hcl4 (T_ne (Gof H)) (marks w2)
  -- 6. the output index
  have hfR : fieldVal τ5 ([H 12], 0) = R := by simp [fieldVal, regSum, hτ5, hτ4, hτ3, hτ2, hτ1, hR]
  have b6 := fieldW_spec cap OUT (Rw (Gof H)) (H 8) (T_ne (Gof H)) ([H 12], 0) (fieldOK_G (Gof H) [12] 0
    (by decide)) τ5 hcl5 (by rw [s5, t5])
    (by rw [hfR, show Rw (Gof H) 7 = H 7 from rfl, v5]; simp only [List.length_append]; omega)
  rw [hfR] at b6
  set τ6 := appendO τ5 OUT (H 7) (marks (natWord R)) with hτ6
  have s6 : τ6.st OUT = marks (natWord a) ++ marks (natWord K) ++ marks w1 ++ marks w2 ++ marks (natWord R) := by
    simp [hτ6, s5]
  have t6 : τ6.sh OUT = (τ6.st OUT).length := by rw [s6]; simp [hτ6, t5]; omega
  have v6 : τ6.val (H 7) = (τ6.st OUT).length := by rw [s6]; simp [hτ6, v5]; omega
  -- 7. the closing `false`
  have b7 := Codec.emitBit_spec cap OUT (H 7) false τ6 t6
    (by rw [v6, s6]; simp only [List.length_append]; omega)
  refine ⟨appendO τ6 OUT (H 7) [false], WExec.mono (WExec.seq b1 (WExec.seq b2 (WExec.seq b3 (WExec.seq b4
    (WExec.seq b5 (WExec.seq b6 b7)))))) ?_, ?_, ?_, ?_, ?_, ⟨fun x hx => ?_, fun r hr => ?_, ?_⟩⟩
  · have c2 := fieldCost_mono haV (show [H 9, H 16].length ≤ 3 by simp)
    have c3 := fieldCost_mono hKV (show [H 10].length ≤ 3 by simp)
    have c6 := fieldCost_mono hRV (show [H 12].length ≤ 3 by simp)
    simp only [List.length_cons, List.length_nil] at c2 c3 c6 ⊢
    omega
  · simp [s6]
  · simp [t6, s6]; omega
  · simp [v6, s6]; omega
  · exact clean_appendO OUT _ _ τ6 (clean_appendO OUT _ _ τ5 hcl5 (T_ne (Gof H)) _) (T_ne (Gof H)) [false]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    simp [hτ6, hτ5, hτ4, hτ3, hτ2, hτ1, Function.update_of_ne hx.1, Function.update_of_ne hx.2.1,
      Function.update_of_ne hx.2.2]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp [hτ6, hτ5, hτ4, hτ3, hτ2, hτ1, Function.update_of_ne hr]
  · simp [hτ6, hτ5, hτ4, hτ3, hτ2, hτ1]

theorem descW_runs (DD SN SC OUT MAT : Fin (ns + 1)) (hS : [DD, SN, SC, OUT, MAT].Nodup) (E : LinearCodeFamily)
    (D : Circuit) (V : ℕ)
    (hV : (PCPPNative.descriptor D.D).length + E.length D.n * (5 * D.n + 8) + D.n + E.length D.n + 8 ≤ V)
    (hcap : 200 * (V + 1) * (V + 1) ≤ cap) (σ : WState ns nr)
    (hDD : σ.st DD = RepairOrdinary.frame (PCPPNative.descriptor D.D)) (hDDh : σ.sh DD = 0)
    (hSN : σ.st SN = []) (hSNh : σ.sh SN = 0) (hSC : σ.st SC = []) (hSCh : σ.sh SC = 0)
    (hOUT : σ.st OUT = []) (hOUTh : σ.sh OUT = 0)
    (hmat : ∀ p, readTapeBit (σ.st MAT) p = matBit E D.n p) (hMATh : σ.sh MAT = 0)
    (hreg : ∀ i : Fin 19, i ≠ 16 → σ.val (H i) = 0) (hL : σ.val (H 16) = E.length D.n) :
    ∃ τ, WXExec cap (descW H DD SN SC OUT MAT) σ τ (descCost D.n (E.length D.n) V) ∧
      τ.st OUT = RepairOrdinary.frame (PCPPNative.descriptor (checkedCircuit E D).D) ∧
      τ.sh OUT = (τ.st OUT).length ∧ τ.val (H 7) = (τ.st OUT).length ∧ τ.st MAT = σ.st MAT ∧
      τ.val (H 9) = D.n ∧ τ.val (H 16) = E.length D.n ∧ Clean (Rw (Gof H)) (H 8) τ ∧
      SameExcept σ τ [DD, SN, SC, OUT, MAT] (List.ofFn H) ∧ (τ.st OUT).length ≤ V * (12 * V + 18) + 14 * V + 20 ∧
      τ.sh MAT = E.length D.n * D.n := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hS
  obtain ⟨⟨hDS, hDC, hDO, hDM⟩, ⟨hSC', hSO, hSM⟩, ⟨hCO, hCM⟩, hOM, -⟩ := hS
  set L := E.length D.n with hLdef
  set q := D.n with hq
  set m := D.D.nodes.length with hm
  set o := D.D.output.val with ho
  have hV' : (PCPPNative.descriptor D.D).length + L * (5 * q + 8) + q + L + 8 ≤ V := hV
  clear hV
  set bytes := D.D.nodes.flatMap PCPPRequestNodeSchema.native with hbytes
  have hdl : (PCPPNative.descriptor D.D).length = (natWord q).length + (natWord m).length + bytes.length +
      (natWord o).length := by rw [PCPPNative.descriptor_eq D.D]; simp only [List.length_append]; rfl
  have hmb : m ≤ bytes.length := length_le_bytes D.D.nodes
  have hqm : q ≤ m := D.sizeAtLeast
  have hom : o < m := D.D.output.isLt
  have hVL : L * (5 * q + 8) ≤ V := by omega
  have hLq : E.length q = L := rfl
  have hV := hV'
  have hX : L * (5 * q + 8) * (12 * V + 18) ≤ V * (12 * V + 18) := Nat.mul_le_mul_right _ hVL
  have hcap' : 4 * V + 8 ≤ cap := by nlinarith
  -- front
  obtain ⟨σf, ef, hfSN, hfSNh, hf9, hf10, hf12, hffr⟩ := frontW_spec cap H DD SN hDS D V (by omega) hcap' σ hDD hDDh
    hSN hSNh hreg
  have hfv : ∀ i : Fin 19, i ≠ 9 → i ≠ 10 → i ≠ 12 → σf.val (H i) = σ.val (H i) := by
    intro i h9 h10 h12
    exact hffr.val (by simp [H.injective.eq_iff, h9, h10, h12])
  have hfst : ∀ x, x ≠ DD → x ≠ SN → σf.st x = σ.st x ∧ σf.sh x = σ.sh x := by
    intro x h1 h2; exact hffr.1 x (by simp [h1, h2])
  -- the checks
  have h0 := rowInv_zero (Gof H) SC MAT E q m o V σf
    (by rw [(hfst SC (Ne.symm hDC) (Ne.symm hSC')).2, (hfst SC (Ne.symm hDC) (Ne.symm hSC')).1, hSC, hSCh]; rfl) hom
    (by rw [g10]; exact hf10) (by rw [g11, hfv 11 (by decide) (by decide) (by decide), hreg 11 (by decide)]; omega)
    (by rw [g12]; exact hf12) (by rw [g14, hfv 14 (by decide) (by decide) (by decide), hreg 14 (by decide)])
    (by rw [g13, hfv 13 (by decide) (by decide) (by decide), hreg 13 (by decide)]) (by rw [g9]; exact hf9)
    (by rw [g15, hfv 15 (by decide) (by decide) (by decide), hreg 15 (by decide)])
    (by rw [(hfst MAT (Ne.symm hDM) (Ne.symm hSM)).2, hMATh])
    ⟨fun i hi => by
      rw [RH, hfv _ (by intro e; have := congrArg Fin.val e; simp at this; omega)
        (by intro e; have := congrArg Fin.val e; simp at this; omega)
        (by intro e; have := congrArg Fin.val e; simp at this; omega)]
      exact hreg _ (by intro e; have := congrArg Fin.val e; simp at this; omega),
     by rw [g8, hfv 8 (by decide) (by decide) (by decide), hreg 8 (by decide)]⟩
  have hfmat : σf.st MAT = σ.st MAT := (hfst MAT (Ne.symm hDM) (Ne.symm hSM)).1
  have h7f : σf.val (H 7) = 0 := by rw [hfv 7 (by decide) (by decide) (by decide), hreg 7 (by decide)]
  obtain ⟨σc, ec, hcI, hc16, hc17⟩ := checksW_runs cap (Gof H) SC MAT E q m o V σf hCM
    (by rw [hfmat]; exact hmat) (by rw [hLq]; omega) (by rw [g7, h7f, hLq]; nlinarith) h0
    (by rw [g16, hfv 16 (by decide) (by decide) (by decide), hL])
    (by rw [g17, hfv 17 (by decide) (by decide) (by decide), hreg 17 (by decide)])
  have hcsf := cs_full E q m o
  set chk := checksNodes E q m (List.finRange L) o with hchk
  set cbytes := chk.1.flatMap PCPPRequestNodeSchema.native with hcbytes
  -- facts after the checks
  have hcSC : σc.st SC = marks cbytes := by
    rw [hcI.out, (hfst SC (Ne.symm hDC) (Ne.symm hSC')).1, hSC, hcsf]; rfl
  have hcSCh : σc.sh SC = (marks cbytes).length := by rw [hcI.outh, hcSC]
  have hc7 : σc.val (H 7) = (marks cbytes).length := by
    rw [← g7, hcI.pos, g7, h7f, Nat.zero_add, hcsf]
  have hcposb := hcI.posb
  rw [hcsf, marks_len'] at hcposb
  have hcposb' : 2 * cbytes.length ≤ L * (5 * q + 8) * (12 * V + 18) := hcposb
  have hcb : 2 * cbytes.length ≤ V * (12 * V + 18) := by omega
  have hcl := hcI.clean
  have hcK : σc.val (H 10) = m + chk.1.length := by rw [← g10, hcI.kk, hcsf]
  have hcRR : σc.val (H 12) = chk.2 := by rw [← g12, hcI.rr, hcsf]
  have hcRRK : σc.val (H 12) < σc.val (H 10) := by rw [← g12, ← g10]; exact hcI.rrle
  have hcQ : σc.val (H 9) = q := by rw [← g9]; exact hcI.qq
  have hchkl : chk.1.length ≤ L * (5 * q + 8) := by
    have := checksNodes_length_le E q m (List.finRange L) o
    simpa using this
  have hcfr := hcI.fr
  have hcst : ∀ x, x ≠ SC → x ≠ MAT → σc.st x = σf.st x ∧ σc.sh x = σf.sh x := by
    intro x h1 h2; exact hcfr.1 x (by simp [h1, h2])
  have hcOUT : σc.st OUT = [] ∧ σc.sh OUT = 0 := by
    rw [(hcst OUT (Ne.symm hCO) hOM).1, (hcst OUT (Ne.symm hCO) hOM).2, (hfst OUT (Ne.symm hDO) (Ne.symm hSO)).1,
      (hfst OUT (Ne.symm hDO) (Ne.symm hSO)).2, hOUT, hOUTh]; exact ⟨rfl, rfl⟩
  have hcSN : σc.st SN = marks bytes ∧ σc.sh SN = 0 := by
    rw [(hcst SN hSC' hSM).1, (hcst SN hSC' hSM).2, hfSN, hfSNh]; exact ⟨rfl, rfl⟩
  have hc16' : σc.val (H 16) = L := by rw [← g16]; exact hc16
  have hR : chk.2 < m + chk.1.length := by rw [← hcRR, ← hcK]; exact hcRRK
  obtain ⟨τ, eb, hbout, hbouth, hb7, hbcl, hbfr⟩ := backW_spec cap H SN SC OUT hSC' hSO hCO bytes cbytes (q + L)
    (m + chk.1.length) chk.2 V σc hcSN.1 hcSN.2 hcSC hcSCh hc7 hcOUT.1 hcOUT.2 (by rw [hcQ, hc16'])
    hcK hcRR hcl (by omega) (by omega) (by omega) (by omega) hcb hcap
  have hout : τ.st OUT = RepairOrdinary.frame (PCPPNative.descriptor (checkedCircuit E D).D) := by
    rw [checked_frame, hbout]
  refine ⟨τ, WXExec.mono (WXExec.seq (WXExec.wm ef) (WXExec.seq ec (WXExec.wm eb))) ?_, hout, hbouth, hb7, ?_, ?_,
    ?_, hbcl, ?_, ?_, ?_⟩
  · unfold descCost backCost
    have e : checksCost q (E.length q) V = checksCost q L V := rfl
    omega
  · rw [hbfr.st (by simp [Ne.symm hSM, Ne.symm hCM, Ne.symm hOM]), hcI.mat, hfmat]
  · rw [hbfr.val (by simp), hcQ]
  · rw [hbfr.val (by simp), hc16']
  · refine ⟨fun x hx => ?_, fun r hr => ?_, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
      obtain ⟨h1, h2, h3, h4, h5⟩ := hx
      rw [hbfr.st (by simp [h2, h3, h4]), hbfr.sh (by simp [h2, h3, h4])]
      exact ⟨((hcst x h3 h5).1.trans (hfst x h1 h2).1), ((hcst x h3 h5).2.trans (hfst x h1 h2).2)⟩
    · have hne : ∀ i : Fin 19, r ≠ H i := fun i e => hr (by rw [e, List.mem_ofFn]; exact ⟨i, rfl⟩)
      rw [hbfr.val (by simp [hne 7]),
        hcfr.val (by simp [hne 7, hne 9, hne 10, hne 11, hne 12, hne 13, hne 14, hne 15, hne 16, hne 17]),
        hffr.val (by simp [hne 9, hne 10, hne 12])]
    · rw [hbfr.cell, hcfr.cell, hffr.cell]
  · rw [hbout]
    have la := ChecksW.natWord_len (q + L)
    have lK := ChecksW.natWord_len (m + chk.1.length)
    have lR := ChecksW.natWord_len chk.2
    have b1 := natBitLength_le (q + L)
    have b2 := natBitLength_le (m + chk.1.length)
    have b3 := natBitLength_le chk.2
    have hR' : chk.2 < m + chk.1.length := hR
    simp only [List.length_append, marks_len', List.length_cons, List.length_nil]
    omega
  · rw [hbfr.sh (by simp [Ne.symm hSM, Ne.symm hCM, Ne.symm hOM]), hcI.math]

end NearCubicGates.Close.CheckedPCPP.DescW
