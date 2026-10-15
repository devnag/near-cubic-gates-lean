import Proof.Gates.CheckedPCPP.DescW

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.CheckedPCPP.FrameIn

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat (enc stp)
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.SourceInterfaces NearCubicGates.Close.WordPrograms
open NearCubicGates.Close.CheckedPCPP.NodeEmit NearCubicGates.Close.CheckedPCPP.DescW

variable {ns nr : ℕ} (cap : ℕ)

/-! ## Re-marking one frame -/

/-- Append `marks (frame w)` for the frame `frame w` on `s`. -/
def remark (s o : Fin (ns + 1)) (OP : Fin nr) : WM ns nr :=
  .seq (.whs s (.seq (Codec.frameCell s o OP) (Codec.frameCell s o OP))) (Codec.frameCell s o OP)

theorem frame_len (w : List Bool) : (RepairOrdinary.frame w).length = 2 * w.length + 1 := by
  induction w with
  | nil => rfl
  | cons b w ih => simp [RepairOrdinary.frame, ih]; ring

theorem remark_loop (s o : Fin (ns + 1)) (hso : s ≠ o) (OP : Fin nr) :
    ∀ (w pre rest : List Bool) (σ : WState ns nr), σ.st s = pre ++ RepairOrdinary.frame w ++ rest →
      σ.sh s = pre.length → σ.sh o = (σ.st o).length → σ.val OP + 4 * w.length ≤ cap →
      WExec cap (.whs s (.seq (Codec.frameCell s o OP) (Codec.frameCell s o OP))) σ
        ((appendO σ o OP (w.flatMap fun b => [true, true, true, b])).seth s (pre.length + 2 * w.length))
        (39 * w.length + 1)
  | [], pre, rest, σ, hst, hsh, _, _ => by
    have hb : wbit σ s = false := by
      unfold wbit; rw [hst, hsh]; simp [RepairOrdinary.frame, rtb_app0]; rfl
    have e : (appendO σ o OP (([] : List Bool).flatMap fun b => [true, true, true, b])).seth s
        (pre.length + 2 * ([] : List Bool).length) = σ := by
      simp only [List.flatMap_nil, NearCubicWires.WireExponent3_5.PrimAsm.WriteNat.appendO_nil, List.length_nil,
        Nat.mul_zero, Nat.add_zero, ← hsh]
      exact wseth_same σ s
    rw [e]
    exact WExec.whsF hb
  | b :: w, pre, rest, σ, hst, hsh, ho, hc => by
    have hb : wbit σ s = true := by
      unfold wbit; rw [hst, hsh]; simp [RepairOrdinary.frame, rtb_app0]; rfl
    have h1 := Codec.frameCell_spec cap s o hso OP σ ho (by simp at hc; omega)
    have hr1 : readTapeBit (σ.st s) (σ.sh s) = true := by rw [hst, hsh]; simp [RepairOrdinary.frame, rtb_app0]; rfl
    rw [hr1] at h1
    set σ1 := (appendO σ o OP [true, true]).seth s (σ.sh s + 1) with hσ1
    have h2 := Codec.frameCell_spec cap s o hso OP σ1 (by simp [hσ1, ho, Function.update_of_ne (Ne.symm hso)])
      (by simp [hσ1]; simp at hc; omega)
    have hr2 : readTapeBit (σ1.st s) (σ1.sh s) = b := by
      simp only [hσ1, WState.seth_st, WState.seth_sh, Function.update_self, appendO_st, Function.update_of_ne hso]
      rw [hst, hsh, show pre ++ RepairOrdinary.frame (b :: w) ++ rest = pre ++ (true :: b :: (RepairOrdinary.frame w ++
        rest)) by simp [RepairOrdinary.frame], rtb_app pre _ 1]; rfl
    rw [hr2] at h2
    set σ2 := (appendO σ1 o OP [true, b]).seth s (σ1.sh s + 1) with hσ2
    have ih := remark_loop s o hso OP w (pre ++ [true, b]) rest σ2
      (by simp [hσ2, hσ1, Function.update_of_ne hso, hst, RepairOrdinary.frame])
      (by simp [hσ2, hσ1, hsh]) (by simp [hσ2, hσ1, Function.update_of_ne (Ne.symm hso), ho])
      (by simp [hσ2, hσ1]; simp at hc; omega)
    refine WExec.cast cap (WExec.whsT hb (WExec.seq h1 h2) ih) ?_ (by simp; ring_nf; omega)
    apply WState.eq
    · funext x; by_cases hx : x = s
      · subst hx; simp [hσ2, hσ1, Function.update_of_ne hso, hsh]; ring
      · by_cases hxo : x = o
        · subst hxo; simp [hσ2, hσ1, Function.update_of_ne hx]; ring
        · simp [hσ2, hσ1, Function.update_of_ne hx, Function.update_of_ne hxo]
    · funext x; by_cases hxo : x = o
      · subst hxo; simp [hσ2, hσ1, Function.update_of_ne (Ne.symm hso)]
      · simp [hσ2, hσ1, Function.update_of_ne hxo]
    · funext r; by_cases hr : r = OP
      · subst hr; simp [hσ2, hσ1]; ring
      · simp [hσ2, hσ1, Function.update_of_ne hr]
    · simp [hσ2, hσ1]

theorem marks_frame (w : List Bool) :
    marks (RepairOrdinary.frame w) = (w.flatMap fun b => [true, true, true, b]) ++ [true, false] := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    rw [show RepairOrdinary.frame (b :: w) = true :: b :: RepairOrdinary.frame w from rfl]
    simp only [marks, List.flatMap_cons] at ih ⊢
    rw [ih]; simp

theorem remark_spec (s o : Fin (ns + 1)) (hso : s ≠ o) (OP : Fin nr) (w pre rest : List Bool) (σ : WState ns nr)
    (hst : σ.st s = pre ++ RepairOrdinary.frame w ++ rest) (hsh : σ.sh s = pre.length)
    (ho : σ.sh o = (σ.st o).length) (hc : σ.val OP + 4 * w.length + 2 ≤ cap) :
    WExec cap (remark s o OP) σ
      ((appendO σ o OP (marks (RepairOrdinary.frame w))).seth s (pre.length + (RepairOrdinary.frame w).length))
      (39 * w.length + 20) := by
  have h1 := remark_loop cap s o hso OP w pre rest σ hst hsh ho (by omega)
  set σ1 := (appendO σ o OP (w.flatMap fun b => [true, true, true, b])).seth s (pre.length + 2 * w.length) with hσ1
  have h2 := Codec.frameCell_spec cap s o hso OP σ1 (by simp [hσ1, ho, Function.update_of_ne (Ne.symm hso)])
    (by simp [hσ1]; omega)
  have hr : readTapeBit (σ1.st s) (σ1.sh s) = false := by
    simp only [hσ1, WState.seth_st, WState.seth_sh, Function.update_self, appendO_st, Function.update_of_ne hso]
    rw [hst]
    have : pre ++ RepairOrdinary.frame w ++ rest = (pre ++ marks w) ++ (false :: rest) := by
      rw [show RepairOrdinary.frame w = marks w ++ [false] from frame_eq_marks' w]; simp
    rw [this, show pre.length + 2 * w.length = (pre ++ marks w).length by simp [marks_len']]
    rw [rtb_app0]; rfl
  rw [hr] at h2
  refine WExec.cast cap (WExec.seq h1 h2) ?_ (by omega)
  apply WState.eq
  · funext x; by_cases hx : x = s
    · subst hx; simp [hσ1, Function.update_of_ne hso, frame_len]; ring
    · by_cases hxo : x = o
      · subst hxo; simp [hσ1, Function.update_of_ne hx, marks_frame]; ring
      · simp [hσ1, Function.update_of_ne hx, Function.update_of_ne hxo]
  · funext x; by_cases hxo : x = o
    · subst hxo; simp [hσ1, Function.update_of_ne (Ne.symm hso), marks_frame]
    · simp [hσ1, Function.update_of_ne hxo]
  · funext r; by_cases hr : r = OP
    · subst hr; simp [hσ1, marks_frame]; ring
    · simp [hσ1, Function.update_of_ne hr]
  · simp [hσ1]

/-! ## Copying a raw descriptor -/

/-- Copy one node's three `natWord` fields (encoding `ε`) from `s`, appending them marked to `o`. -/
def copy3e (ε : Bool) (s o : Fin (ns + 1)) (R : Fin 8 ↪ Fin nr) : WM ns nr :=
  .seq (Codec.copyNat ε s o R) (.seq (Codec.copyNat ε s o R) (Codec.copyNat ε s o R))

theorem copy3e_words (ε : Bool) (s o : Fin (ns + 1)) (hso : s ≠ o) (R : Fin 8 ↪ Fin nr) (x0 x1 x2 : ℕ)
    (pre rest : List Bool) (σ : WState ns nr)
    (hst : σ.st s = pre ++ (enc ε (natWord x0) ++ enc ε (natWord x1) ++ enc ε (natWord x2)) ++ rest)
    (hsh : σ.sh s = pre.length) (ho : σ.sh o = (σ.st o).length) (h1 : σ.val (R 1) = 0) (h2 : σ.val (R 2) = 0)
    (hcap : σ.val (R 7) + 2 * ((natWord x0).length + (natWord x1).length + (natWord x2).length) + 2 ≤ cap) :
    WExec cap (copy3e ε s o R) σ
      ((appendO σ o (R 7) (marks (natWord x0) ++ marks (natWord x1) ++ marks (natWord x2))).seth s
        (pre.length + stp ε * ((natWord x0).length + (natWord x1).length + (natWord x2).length)))
      (60 * ((natWord x0).length + (natWord x1).length + (natWord x2).length) + 182) := by
  have hR7 : ∀ i : Fin 8, i ≠ 7 → R i ≠ R 7 := fun i hi => R.injective.ne hi
  have m0 := marks_len' (natWord x0)
  have m1 := marks_len' (natWord x1)
  have m2 := marks_len' (natWord x2)
  have l0 := NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.enc_length ε (natWord x0)
  have l1 := NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.enc_length ε (natWord x1)
  have e1 := Codec.copyNat_spec cap ε s o hso R x0 pre (enc ε (natWord x1) ++ enc ε (natWord x2) ++ rest)
    σ (by rw [hst]; simp only [List.append_assoc]) hsh ho h1 h2 (by omega)
  have e2 := Codec.copyNat_spec cap ε s o hso R x1 (pre ++ enc ε (natWord x0)) (enc ε (natWord x2) ++ rest)
    ((appendO σ o (R 7) (marks (natWord x0))).seth s (pre.length + stp ε * (natWord x0).length))
    (by simp only [WState.seth_st, appendO_st, Function.update_of_ne hso, hst, List.append_assoc])
    (by simp only [WState.seth_sh, Function.update_self, List.length_append, l0])
    (by simp only [WState.seth_sh, WState.seth_st, appendO_st, appendO_sh, Function.update_of_ne (Ne.symm hso),
      Function.update_self, List.length_append, ho])
    (by simp only [WState.seth_val, appendO_val, Function.update_of_ne (hR7 1 (by decide)), h1])
    (by simp only [WState.seth_val, appendO_val, Function.update_of_ne (hR7 2 (by decide)), h2])
    (by simp only [WState.seth_val, appendO_val, Function.update_self]; omega)
  have e3 := Codec.copyNat_spec cap ε s o hso R x2 (pre ++ enc ε (natWord x0) ++ enc ε (natWord x1)) rest
    ((appendO ((appendO σ o (R 7) (marks (natWord x0))).seth s (pre.length + stp ε * (natWord x0).length)) o (R 7)
      (marks (natWord x1))).seth s ((pre ++ enc ε (natWord x0)).length + stp ε * (natWord x1).length))
    (by simp only [WState.seth_st, appendO_st, Function.update_of_ne hso, hst, List.append_assoc])
    (by simp only [WState.seth_sh, Function.update_self, List.length_append, l0, l1])
    (by simp only [WState.seth_sh, WState.seth_st, appendO_st, appendO_sh, Function.update_of_ne (Ne.symm hso),
      Function.update_self, List.length_append, ho])
    (by simp only [WState.seth_val, appendO_val, Function.update_of_ne (hR7 1 (by decide)), h1])
    (by simp only [WState.seth_val, appendO_val, Function.update_of_ne (hR7 2 (by decide)), h2])
    (by simp only [WState.seth_val, appendO_val, Function.update_self]; omega)
  refine WExec.cast cap (WExec.seq e1 (WExec.seq e2 e3)) ?_ (by omega)
  apply WState.eq
  · funext x; by_cases hx : x = s
    · subst hx
      simp only [WState.seth_sh, appendO_sh, Function.update_self, List.length_append, l0, l1]; ring
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

theorem copy3e_spec (ε : Bool) (s o : Fin (ns + 1)) (hso : s ≠ o) (R : Fin 8 ↪ Fin nr) {n : ℕ} (nd : BooleanNode n)
    (pre rest : List Bool) (σ : WState ns nr) (hst : σ.st s = pre ++ enc ε (PCPPRequestNodeSchema.native nd) ++ rest)
    (hsh : σ.sh s = pre.length) (ho : σ.sh o = (σ.st o).length) (h1 : σ.val (R 1) = 0) (h2 : σ.val (R 2) = 0)
    (hcap : σ.val (R 7) + 2 * (PCPPRequestNodeSchema.native nd).length + 2 ≤ cap) :
    WExec cap (copy3e ε s o R) σ
      ((appendO σ o (R 7) (marks (PCPPRequestNodeSchema.native nd))).seth s
        (pre.length + stp ε * (PCPPRequestNodeSchema.native nd).length))
      (60 * (PCPPRequestNodeSchema.native nd).length + 182) := by
  have hn := native_fields nd
  have hm : marks (PCPPRequestNodeSchema.native nd) = marks (natWord (PCPPRequestNodeSchema.fields nd 0)) ++
      marks (natWord (PCPPRequestNodeSchema.fields nd 1)) ++ marks (natWord (PCPPRequestNodeSchema.fields nd 2)) := by
    rw [hn, NodeEmit.marks_append, NodeEmit.marks_append]
  have he : enc ε (PCPPRequestNodeSchema.native nd) = enc ε (natWord (PCPPRequestNodeSchema.fields nd 0)) ++
      enc ε (natWord (PCPPRequestNodeSchema.fields nd 1)) ++ enc ε (natWord (PCPPRequestNodeSchema.fields nd 2)) := by
    rw [hn, NearCubicWires.WireExponent3_5.PrimAsm.CopyNat.enc_append,
      NearCubicWires.WireExponent3_5.PrimAsm.CopyNat.enc_append]
  have hl : (PCPPRequestNodeSchema.native nd).length = (natWord (PCPPRequestNodeSchema.fields nd 0)).length +
      (natWord (PCPPRequestNodeSchema.fields nd 1)).length + (natWord (PCPPRequestNodeSchema.fields nd 2)).length := by
    rw [hn]; simp only [List.length_append]
  have e := copy3e_words cap ε s o hso R _ _ _ pre rest σ (by rw [hst, he]) hsh ho h1 h2 (by rw [← hl]; exact hcap)
  rw [← hm, ← hl] at e
  exact e

/-- Copy a raw native descriptor: `natWord n`, the node list, `natWord o`. -/
def copyDesc (s o : Fin (ns + 1)) (R : Fin 8 ↪ Fin nr) : WM ns nr :=
  .seq (Codec.copyNat false s o R) (.seq (Codec.copyList false s o R (copy3e false s o R))
    (Codec.copyNat false s o R))

/-- A bound on the cost of copying a descriptor of length `D`. -/
def copyDescCost (D : ℕ) : ℕ := 600 * (D + 11) * (D + 11)

theorem pow_bitLen_le (x : ℕ) : 2 ^ natBitLength x ≤ 2 * x + 2 := DescW.pow_bitlen_le x

theorem copyDesc_spec (s o : Fin (ns + 1)) (hso : s ≠ o) (R : Fin 8 ↪ Fin nr) {n : ℕ} (c : BooleanCircuit n)
    (pre rest : List Bool) (σ : WState ns nr) (hst : σ.st s = pre ++ PCPPNative.descriptor c ++ rest)
    (hsh : σ.sh s = pre.length) (ho : σ.sh o = (σ.st o).length) (hz : ∀ i : Fin 8, i ≠ 7 → σ.val (R i) = 0)
    (hcap : σ.val (R 7) + 16 * (PCPPNative.descriptor c).length + 16 ≤ cap) :
    WExec cap (copyDesc s o R) σ
      ((appendO σ o (R 7) (marks (PCPPNative.descriptor c))).seth s (pre.length + (PCPPNative.descriptor c).length))
      (copyDescCost (PCPPNative.descriptor c).length) := by
  have hR7 : ∀ i : Fin 8, i ≠ 7 → R i ≠ R 7 := fun i hi => R.injective.ne hi
  have hd : PCPPNative.descriptor c = natWord n ++ Interfaces.listWord PCPPRequestNodeSchema.native c.nodes ++
      natWord c.output.val := by
    rw [PCPPNative.descriptor_eq]; simp [Interfaces.listWord, List.append_assoc]
  set D := (PCPPNative.descriptor c).length with hD
  have hl : D = (natWord n).length + (Interfaces.listWord PCPPRequestNodeSchema.native c.nodes).length +
      (natWord c.output.val).length := by rw [hD, hd]; simp only [List.length_append]
  have hlw : (Interfaces.listWord PCPPRequestNodeSchema.native c.nodes).length =
      (natWord c.nodes.length).length + (c.nodes.flatMap PCPPRequestNodeSchema.native).length := by
    simp [Interfaces.listWord]
  have hmb : c.nodes.length ≤ (c.nodes.flatMap PCPPRequestNodeSchema.native).length := DescW.length_le_bytes c.nodes
  have enc0 : ∀ w : List Bool, enc false w = w := fun w => rfl
  have stp0 : stp false = 1 := rfl
  -- natWord n
  have e1 := Codec.copyNat_spec cap false s o hso R n pre
    (Interfaces.listWord PCPPRequestNodeSchema.native c.nodes ++ natWord c.output.val ++ rest) σ
    (by rw [hst, hd, enc0]; simp only [List.append_assoc]) hsh ho (hz 1 (by decide)) (hz 2 (by decide)) (by omega)
  rw [stp0, Nat.one_mul] at e1
  set σ1 := (appendO σ o (R 7) (marks (natWord n))).seth s (pre.length + (natWord n).length) with hσ1
  -- the node list
  have e2 := Codec.copyList_spec cap false s o hso R (copy3e false s o R) PCPPRequestNodeSchema.native
    (fun nd => 60 * (PCPPRequestNodeSchema.native nd).length + 182)
    (fun τ => τ.val (R 1) = 0 ∧ τ.val (R 2) = 0)
    (σ1.val (R 7) + (marks (Interfaces.listWord PCPPRequestNodeSchema.native c.nodes)).length)
    (fun τ x h => h)
    (fun τ x h => by simp [Function.update_of_ne (R.injective.ne (show (1 : Fin 8) ≠ 0 by decide)),
      Function.update_of_ne (R.injective.ne (show (2 : Fin 8) ≠ 0 by decide)), h.1, h.2])
    (fun τ w h => by simp [Function.update_of_ne (hR7 1 (by decide)), Function.update_of_ne (hR7 2 (by decide)),
      h.1, h.2]) c.nodes
    (by
      intro x _ pre' rest' τ hτ hst' hsh' ho' hV'
      have := copy3e_spec cap false s o hso R x pre' rest' τ hst' hsh' ho' hτ.1 hτ.2
        (by rw [marks_len'] at hV'; have := marks_len' (Interfaces.listWord PCPPRequestNodeSchema.native c.nodes)
            have hσ17 : σ1.val (R 7) = σ.val (R 7) + (marks (natWord n)).length := by simp [hσ1]
            rw [hσ17, marks_len'] at hV'
            omega)
      exact this)
    (pre ++ natWord n) (natWord c.output.val ++ rest) σ1
    (by simp [hσ1, Function.update_of_ne (hR7 1 (by decide)), Function.update_of_ne (hR7 2 (by decide)),
      hz 1 (by decide), hz 2 (by decide)])
    (by simp only [hσ1, WState.seth_st, appendO_st, Function.update_of_ne hso, hst, hd, enc0, List.append_assoc])
    (by simp [hσ1, hsh])
    (by simp [hσ1, Function.update_of_ne (Ne.symm hso), ho])
    (fun i hi => by
      simp only [hσ1, WState.seth_val, appendO_val, Function.update_of_ne (hR7 i hi)]; exact hz i hi)
    (by have := pow_bitLen_le c.nodes.length; rw [pow_succ]; omega) (by omega)
    (by
      have := natBitLength_le c.nodes.length
      simp only [hσ1, WState.seth_val, appendO_val, Function.update_self, marks_len']; omega) le_rfl
  rw [stp0, Nat.one_mul] at e2
  set σ2 := (appendO σ1 o (R 7) (marks (Interfaces.listWord PCPPRequestNodeSchema.native c.nodes))).seth s
    ((pre ++ natWord n).length + (Interfaces.listWord PCPPRequestNodeSchema.native c.nodes).length) with hσ2
  -- natWord o
  have e3 := Codec.copyNat_spec cap false s o hso R c.output.val
    (pre ++ natWord n ++ Interfaces.listWord PCPPRequestNodeSchema.native c.nodes) rest σ2
    (by simp only [hσ2, hσ1, WState.seth_st, appendO_st, Function.update_of_ne hso, hst, hd, enc0, List.append_assoc])
    (by simp [hσ2]; omega)
    (by simp [hσ2, hσ1, Function.update_of_ne (Ne.symm hso), ho]; ring)
    (by simp [hσ2, hσ1, Function.update_of_ne (hR7 1 (by decide)), hz 1 (by decide)])
    (by simp [hσ2, hσ1, Function.update_of_ne (hR7 2 (by decide)), hz 2 (by decide)])
    (by simp only [hσ2, hσ1, WState.seth_val, appendO_val, Function.update_self, marks_len']; omega)
  rw [stp0, Nat.one_mul] at e3
  refine WExec.cast cap (WExec.seq e1 (WExec.seq e2 e3)) ?_ ?_
  · apply WState.eq
    · funext x; by_cases hx : x = s
      · subst hx; simp [hσ2, hσ1, Function.update_of_ne hso, hl]; ring
      · by_cases hxo : x = o
        · subst hxo; simp [hσ2, hσ1, Function.update_of_ne hx, hd, NodeEmit.marks_append, marks_len']; ring
        · simp [hσ2, hσ1, Function.update_of_ne hx, Function.update_of_ne hxo]
    · funext x; by_cases hxo : x = o
      · subst hxo; simp [hσ2, hσ1, Function.update_of_ne (Ne.symm hso), hd, NodeEmit.marks_append]
      · simp [hσ2, hσ1, Function.update_of_ne hxo]
    · funext r; by_cases hr : r = R 7
      · subst hr; simp [hσ2, hσ1, hd, NodeEmit.marks_append, marks_len']; ring
      · simp [hσ2, hσ1, Function.update_of_ne hr]
    · simp [hσ2, hσ1]
  · -- cost
    unfold copyDescCost Codec.copyListCost
    have hm : c.nodes.length ≤ D := by omega
    have hb := natBitLength_le c.nodes.length
    have hp := pow_bitLen_le c.nodes.length
    have hsum : (List.map (fun c => c + 4) (List.map (fun nd => 60 * (PCPPRequestNodeSchema.native nd).length + 182)
        c.nodes)).sum = 60 * (c.nodes.flatMap PCPPRequestNodeSchema.native).length + 186 * c.nodes.length := by
      clear hσ1 hσ2 e1 e2 e3
      induction c.nodes with
      | nil => rfl
      | cons x xs ih => simp only [List.map_cons, List.sum_cons, ih, List.flatMap_cons, List.length_append,
          List.length_cons]; ring
    rw [hsum]
    have h1 : (natBitLength c.nodes.length + 2) * (40 * 2 ^ natBitLength c.nodes.length + 40) ≤ (D + 3) * (80 * D + 120) :=
      Nat.mul_le_mul (by omega) (by omega)
    have h2 : (natBitLength c.nodes.length + 10) * (100 * c.nodes.length + 200) ≤ (D + 11) * (100 * D + 200) :=
      Nat.mul_le_mul (by omega) (by omega)
    nlinarith

/-! ## The entry framing -/

/-- `A := frame h ++ frame d` for `h = frame x ++ frame t` on `HS` and the raw descriptor `d` on `DS`; `A` rewound. -/
def frameInW (HS DS A : Fin (ns + 1)) (R : Fin 8 ↪ Fin nr) : WM ns nr :=
  .seq (remark HS A (R 7)) (.seq (remark HS A (R 7)) (.seq (emitC A (R 7) false) (.seq (copyDesc DS A R)
    (.seq (emitC A (R 7) false) (WM.rewind A (R 7))))))

/-- The cost of the entry framing. -/
def frameInCost (h d : ℕ) : ℕ := 80 * h + 60 + copyDescCost d + 30 + 5 * (2 * h + 2 * d + 2) + 1

theorem frameInW_spec (HS DS A : Fin (ns + 1)) (hS : [HS, DS, A].Nodup) (R : Fin 8 ↪ Fin nr) (x t : List Bool)
    {n : ℕ} (c : BooleanCircuit n) (σ : WState ns nr)
    (hHS : σ.st HS = RepairOrdinary.frame x ++ RepairOrdinary.frame t) (hHSh : σ.sh HS = 0)
    (hDS : σ.st DS = PCPPNative.descriptor c) (hDSh : σ.sh DS = 0) (hA : σ.st A = []) (hAh : σ.sh A = 0)
    (hz : ∀ i : Fin 8, σ.val (R i) = 0)
    (hcap : 16 * (RepairOrdinary.frame x ++ RepairOrdinary.frame t).length +
      16 * (PCPPNative.descriptor c).length + 40 ≤ cap) :
    ∃ τ, WExec cap (frameInW HS DS A R) σ τ
        (frameInCost (RepairOrdinary.frame x ++ RepairOrdinary.frame t).length (PCPPNative.descriptor c).length) ∧
      τ.st A = RepairOrdinary.frame (RepairOrdinary.frame x ++ RepairOrdinary.frame t) ++
        RepairOrdinary.frame (PCPPNative.descriptor c) ∧ τ.sh A = 0 ∧ (∀ i : Fin 8, τ.val (R i) = 0) ∧
      SameExcept σ τ [HS, DS, A] [] := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hS
  obtain ⟨⟨hHD, hHA⟩, hDA, -⟩ := hS
  have hfx := frame_len x
  have hft := frame_len t
  have hhl : (RepairOrdinary.frame x ++ RepairOrdinary.frame t).length =
      (RepairOrdinary.frame x).length + (RepairOrdinary.frame t).length := by simp
  have mx := marks_len' (RepairOrdinary.frame x)
  have mt := marks_len' (RepairOrdinary.frame t)
  have md := marks_len' (PCPPNative.descriptor c)
  have hAS : A ≠ HS := Ne.symm hHA
  have hAD : A ≠ DS := Ne.symm hDA
  have hDH : DS ≠ HS := Ne.symm hHD
  -- 1, 2. the two frames of h
  have e1 := remark_spec cap HS A hHA (R 7) x [] (RepairOrdinary.frame t) σ (by rw [hHS]; simp) (by simp [hHSh])
    (by rw [hA, hAh]; rfl) (by rw [hz 7]; omega)
  set σ1 := (appendO σ A (R 7) (marks (RepairOrdinary.frame x))).seth HS ([].length + (RepairOrdinary.frame x).length)
    with hσ1
  have s1A : σ1.st A = marks (RepairOrdinary.frame x) := by simp [hσ1, hA]
  have t1A : σ1.sh A = (marks (RepairOrdinary.frame x)).length := by simp [hσ1, Function.update_of_ne hAS, hAh]
  have v1 : σ1.val (R 7) = (marks (RepairOrdinary.frame x)).length := by simp [hσ1, hz 7]
  have e2 := remark_spec cap HS A hHA (R 7) t (RepairOrdinary.frame x) [] σ1
    (by simp [hσ1, Function.update_of_ne hHA, hHS]) (by simp [hσ1]) (by rw [s1A, t1A]) (by rw [v1]; omega)
  set σ2 := (appendO σ1 A (R 7) (marks (RepairOrdinary.frame t))).seth HS
    ((RepairOrdinary.frame x).length + (RepairOrdinary.frame t).length) with hσ2
  have s2A : σ2.st A = marks (RepairOrdinary.frame x) ++ marks (RepairOrdinary.frame t) := by simp [hσ2, s1A]
  have t2A : σ2.sh A = (σ2.st A).length := by
    rw [s2A]; simp [hσ2, Function.update_of_ne hAS, t1A]
  have v2 : σ2.val (R 7) = (σ2.st A).length := by rw [s2A]; simp [hσ2, v1]
  -- 3. close frame h
  have e3 := Codec.emitBit_spec cap A (R 7) false σ2 t2A (by rw [v2, s2A]; simp only [List.length_append]; omega)
  set σ3 := appendO σ2 A (R 7) [false] with hσ3
  have s3A : σ3.st A = marks (RepairOrdinary.frame x) ++ marks (RepairOrdinary.frame t) ++ [false] := by
    simp [hσ3, s2A]
  have t3A : σ3.sh A = (σ3.st A).length := by rw [s3A]; simp [hσ3, t2A, s2A]; omega
  have v3 : σ3.val (R 7) = (σ3.st A).length := by rw [s3A]; simp [hσ3, v2, s2A]; omega
  have hR3 : ∀ i : Fin 8, i ≠ 7 → σ3.val (R i) = 0 := by
    intro i hi; simp [hσ3, hσ2, hσ1, Function.update_of_ne (R.injective.ne hi), hz i]
  have d3 : σ3.st DS = PCPPNative.descriptor c ∧ σ3.sh DS = 0 := by
    simp [hσ3, hσ2, hσ1, Function.update_of_ne hDA, Function.update_of_ne hDH, hDS, hDSh]
  -- 4. copy d
  have e4 := copyDesc_spec cap DS A hDA R c [] [] σ3 (by rw [d3.1]; simp) (by rw [d3.2]; rfl) t3A hR3
    (by rw [v3, s3A]; simp only [List.length_append, List.length_cons, List.length_nil]; omega)
  set σ4 := (appendO σ3 A (R 7) (marks (PCPPNative.descriptor c))).seth DS
    ([].length + (PCPPNative.descriptor c).length) with hσ4
  have s4A : σ4.st A = marks (RepairOrdinary.frame x) ++ marks (RepairOrdinary.frame t) ++ [false] ++
      marks (PCPPNative.descriptor c) := by simp [hσ4, s3A]
  have t4A : σ4.sh A = (σ4.st A).length := by rw [s4A]; simp [hσ4, Function.update_of_ne hAD, t3A, s3A]; omega
  have v4 : σ4.val (R 7) = (σ4.st A).length := by rw [s4A]; simp [hσ4, v3, s3A]; omega
  -- 5. close frame d
  have e5 := Codec.emitBit_spec cap A (R 7) false σ4 t4A
    (by rw [v4, s4A]; simp only [List.length_append, List.length_cons, List.length_nil]; omega)
  set σ5 := appendO σ4 A (R 7) [false] with hσ5
  have hA5 : σ5.st A = RepairOrdinary.frame (RepairOrdinary.frame x ++ RepairOrdinary.frame t) ++
      RepairOrdinary.frame (PCPPNative.descriptor c) := by
    have : σ5.st A = σ4.st A ++ [false] := by simp [hσ5]
    rw [this, s4A, frame_eq_marks' (RepairOrdinary.frame x ++ RepairOrdinary.frame t),
      frame_eq_marks' (PCPPNative.descriptor c), NodeEmit.marks_append]
    simp
  have h7 : σ5.val (R 7) = (σ5.st A).length := by
    have : σ5.st A = σ4.st A ++ [false] := by simp [hσ5]
    rw [this]; simp [hσ5, v4]
  have hAsh : σ5.sh A = (σ5.st A).length := by
    have : σ5.st A = σ4.st A ++ [false] := by simp [hσ5]
    rw [this]; simp [hσ5, t4A]
  have hlenA : (σ5.st A).length = 2 * (RepairOrdinary.frame x ++ RepairOrdinary.frame t).length +
      2 * (PCPPNative.descriptor c).length + 2 := by
    rw [hA5]; simp only [List.length_append, frame_len]; ring
  have e6 := wrewind_spec (cap := cap) A (R 7) (σ5.st A).length σ5 h7 (by rw [h7, hlenA]; omega)
  refine ⟨_, WExec.mono (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 (WExec.seq e5 e6))))) ?_, ?_, ?_, ?_,
    ⟨fun y hy => ?_, fun r _ => ?_, ?_⟩⟩
  · unfold frameInCost; rw [hlenA, hhl]; omega
  · simp [hA5]
  · simp [hAsh]
  · intro i
    by_cases hi : i = 7
    · subst hi; simp
    · simp only [WState.seth_val, WState.setv_val, Function.update_of_ne (R.injective.ne hi)]
      simp [hσ5, hσ4, hσ3, hσ2, hσ1, Function.update_of_ne (R.injective.ne hi), hz i]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    simp [hσ5, hσ4, hσ3, hσ2, hσ1, Function.update_of_ne hy.1, Function.update_of_ne hy.2.1,
      Function.update_of_ne hy.2.2]
  · by_cases hr7 : r = R 7
    · subst hr7; simp [hz 7]
    · simp [hσ5, hσ4, hσ3, hσ2, hσ1, Function.update_of_ne hr7]
  · simp [hσ5, hσ4, hσ3, hσ2, hσ1]

end NearCubicGates.Close.CheckedPCPP.FrameIn
