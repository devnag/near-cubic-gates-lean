import Proof.Gates.Codec.FieldInt

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace NearCubicGates.Close.Codec

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.RepairOrdinary.RadixSemantics
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat NearCubicWires.RepairOrdinary.Streaming
open NearCubicGates.Close.Worker.Format

variable {ns nr : ℕ} (cap : ℕ)

/-! ## Positions and repeated reads -/

theorem readCount_le (l : List Bool) : (readCount l).1 ≤ l.length := by
  induction l with
  | nil => simp [readCount]
  | cons b l ih => cases b <;> simp [readCount] <;> omega

theorem fieldLen_le (w : List Bool) (p : ℕ) : fieldLen w p ≤ w.length :=
  (readCount_le _).trans (by simp)

/-- `i` steps of a position map. -/
def iter (nxt : ℕ → ℕ) : ℕ → ℕ → ℕ
  | p, 0 => p
  | p, i + 1 => iter nxt (nxt p) i

theorem iter_succ' (nxt : ℕ → ℕ) (p i : ℕ) : iter nxt p (i + 1) = nxt (iter nxt p i) := by
  induction i generalizing p with
  | zero => rfl
  | succ i ih => exact ih (nxt p)

theorem readMany_iter {α : Type} (rd : List Bool → α × List Bool) (w : List Bool) (val : ℕ → α) (nxt : ℕ → ℕ)
    (h : ∀ p, rd (w.drop p) = (val p, w.drop (nxt p))) :
    ∀ n p, readMany rd n (w.drop p) = ((List.range n).map (fun i => val (iter nxt p i)), w.drop (iter nxt p n))
  | 0, p => by simp [readMany, iter]
  | n + 1, p => by
    simp only [readMany, h p, readMany_iter rd w val nxt h n (nxt p)]
    rw [List.range_succ_eq_map]
    simp [iter]

/-! ## Duplicating a register -/

/-- `C := C + Q` (`Q` kept, scratch `D = 0` before and after). -/
def dupR (Q C D : Fin nr) : WM ns nr := .seq (.whr Q (.seq (.dec Q) (.seq (.inc C) (.inc D)))) (WM.move D Q)

theorem dupLoop_spec (Q C D : Fin nr) (hQC : Q ≠ C) (hQD : Q ≠ D) (hCD : C ≠ D) :
    ∀ (m : ℕ) (σ : WState ns nr), σ.val Q = m → m ≤ cap → σ.val C + m ≤ cap → σ.val D + m ≤ cap →
      WExec cap (.whr Q (.seq (.dec Q) (.seq (.inc C) (.inc D)))) σ
        (((σ.setv Q 0).setv C (σ.val C + m)).setv D (σ.val D + m)) (11 * m + 1)
  | 0, σ, h0, _, _, _ => by
    refine WExec.cast cap (WExec.whrF h0) ?_ le_rfl
    apply WState.eq <;> try rfl
    funext r; simp only [WState.setv_val, Function.update_apply]
    split_ifs with h1 h2 h3 <;> subst_vars <;> simp [h0]
  | m + 1, σ, hm, hc, hC, hD => by
    have e1 := WExec.dec (cap := cap) Q σ (by omega)
    set σ1 := σ.setv Q (σ.val Q - 1) with hσ1
    have e2 := WExec.inc (cap := cap) C σ1 (by simp [hσ1, Function.update_of_ne (Ne.symm hQC)]; omega)
    set σ2 := σ1.setv C (σ1.val C + 1) with hσ2
    have e3 := WExec.inc (cap := cap) D σ2 (by
      simp [hσ2, hσ1, Function.update_apply, Ne.symm hQD, Ne.symm hCD]; omega)
    set σ3 := σ2.setv D (σ2.val D + 1) with hσ3
    have hrest := dupLoop_spec Q C D hQC hQD hCD m σ3
      (by simp [hσ3, hσ2, hσ1, Function.update_apply, hQC, hQD]; omega) (by omega)
      (by simp [hσ3, hσ2, hσ1, Function.update_apply, hCD, Ne.symm hQC]; omega)
      (by simp [hσ3, hσ2, hσ1, Function.update_apply, Ne.symm hQD, Ne.symm hCD]; omega)
    refine WExec.cast cap (WExec.whrT (by omega) (WExec.seq e1 (WExec.seq e2 e3)) hrest) ?_ (by omega)
    apply WState.eq <;> try rfl
    funext r
    simp only [hσ3, hσ2, hσ1, WState.setv_val, Function.update_apply]
    by_cases hr : r = D
    · simp [hr, hQC, hQD, hCD, Ne.symm hQC, Ne.symm hQD, Ne.symm hCD]; omega
    by_cases hr' : r = C
    · simp [hr, hr', hQC, hQD, hCD, Ne.symm hQC, Ne.symm hQD, Ne.symm hCD]; omega
    by_cases hr'' : r = Q
    · simp [hr, hr', hr'', hQC, hQD, hCD, Ne.symm hQC, Ne.symm hQD, Ne.symm hCD]
    · simp [hr, hr', hr'']

theorem dupR_spec (Q C D : Fin nr) (hQC : Q ≠ C) (hQD : Q ≠ D) (hCD : C ≠ D) (σ : WState ns nr)
    (hD : σ.val D = 0) (hc : σ.val Q + σ.val C ≤ cap) :
    WExec cap (dupR Q C D) σ (σ.setv C (σ.val C + σ.val Q)) (18 * σ.val Q + 3) := by
  set m := σ.val Q with hm
  have e1 := dupLoop_spec cap Q C D hQC hQD hCD m σ rfl (by omega) (by omega) (by omega)
  set σ1 := ((σ.setv Q 0).setv C (σ.val C + m)).setv D (σ.val D + m) with hσ1
  have e2 := wmove_spec cap D Q (Ne.symm hQD) m σ1 (by simp [hσ1, hD])
    (by simp [hσ1]; omega) (by simp [hσ1, Function.update_apply, hQC, hQD]; omega)
  refine WExec.cast cap (WExec.seq e1 e2) ?_ (by omega)
  apply WState.eq <;> try rfl
  funext r
  simp only [hσ1, WState.setv_val, Function.update_apply]
  by_cases hr : r = Q
  · subst hr; simp [hQD, hQC, hD]; omega
  by_cases hr' : r = D
  · subst hr'; simp [hr, Ne.symm hCD, Ne.symm hQD, hD]
  by_cases hr'' : r = C
  · subst hr''; simp [hr, hr', Ne.symm hQC]
  · simp [hr, hr', hr'']

/-! ## The gate transcoder -/

def fIntCost (n : ℕ) : ℕ := 3 * n ^ 2 + 100 * n + 150

/-- The value of the integer field at `p`. -/
def ival (w : List Bool) (p : ℕ) : ℤ := (readInt (w.drop p)).1

theorem readInt_pos (w : List Bool) (p : ℕ) : readInt (w.drop p) = (ival w p, w.drop (intEnd w p)) :=
  Prod.ext rfl (by rw [readInt_drop])

theorem ofFn_getD_eq {α : Type} (l : List α) (n : ℕ) (hl : l.length = n) (d : α) :
    (List.ofFn fun i : Fin n => l.getD i.val d) = l := by
  subst hl
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]

def gateVals (w : List Bool) (p q : ℕ) : List ℤ := (List.range q).map fun i => ival w (iter (intEnd w) p i)

def gateEnd (w : List Bool) (p q : ℕ) : ℕ := intEnd w (iter (intEnd w) p q)

theorem readGate_drop (w : List Bool) (p q : ℕ) :
    (readGate q (w.drop p)).2 = w.drop (gateEnd w p q) ∧
      Interfaces.gateWord (readGate q (w.drop p)).1 =
        natWord q ++ (gateVals w p q).flatMap Interfaces.intWord ++ Interfaces.intWord (ival w (iter (intEnd w) p q)) := by
  have hm := readMany_iter readInt w (ival w) (intEnd w) (readInt_pos w) q p
  unfold readGate
  rw [hm, readInt_pos]
  refine ⟨rfl, ?_⟩
  unfold Interfaces.gateWord Interfaces.listWord
  simp only
  rw [ofFn_getD_eq _ q (by simp) 0]
  simp [gateVals]

theorem flatMap_take_length_le {α : Type} (f : α → List Bool) (l : List α) (i : ℕ) :
    ((l.take i).flatMap f).length ≤ (l.flatMap f).length := by
  conv_rhs => rw [← List.take_append_drop i l]
  rw [List.flatMap_append, List.length_append]; omega

/-- The gate transcoder: `RQ 0` holds `q`, `RQ 7` is the output counter. -/
def gateW (W o : Fin (ns + 1)) (X : Fin 5 ↪ Fin nr) (F : Fin nr) (RQ : Fin 8 ↪ Fin nr) (C D : Fin nr) : WM ns nr :=
  .seq (writeNatM o RQ) (.seq (dupR (RQ 0) C D) (.seq (repLoop C (intW W o X F (RQ 7))) (intW W o X F (RQ 7))))

def fGateCost (q n : ℕ) : ℕ := (natBitLength q + 10) * (100 * q + 200) + 18 * q + (q + 1) * (fIntCost n + 4) + 10

theorem intW_spec' (W o : Fin (ns + 1)) (X : Fin 5 ↪ Fin nr) (F OP : Fin nr) (hWo : W ≠ o) (hOP : ∀ i, X i ≠ OP)
    (hFX : ∀ i, X i ≠ F) (hFO : F ≠ OP) (σ : WState ns nr) (hX : ∀ i, σ.val (X i) = 0) (hF : σ.val F = 0)
    (ho : σ.sh o = (σ.st o).length) (hOc : σ.val OP + 4 * (σ.st W).length + 12 ≤ cap) :
    WExec cap (intW W o X F OP) σ
      (appendO (σ.seth W (intEnd (σ.st W) (σ.sh W))) o OP (marks (Interfaces.intWord (ival (σ.st W) (σ.sh W)))))
      (fIntCost (σ.st W).length) := by
  have hl := fieldLen_le (σ.st W) (σ.sh W + 1)
  refine WExec.mono (intW_spec cap W o X F OP hWo hOP hFX hFO σ hX hF ho (by omega) (by omega)) ?_
  unfold fIntCost
  have : fieldLen (σ.st W) (σ.sh W + 1) ^ 2 ≤ (σ.st W).length ^ 2 := Nat.pow_le_pow_left hl 2
  omega

theorem gateW_spec (W o : Fin (ns + 1)) (X : Fin 5 ↪ Fin nr) (F : Fin nr) (RQ : Fin 8 ↪ Fin nr) (C D : Fin nr)
    (hWo : W ≠ o) (hXO : ∀ i, X i ≠ RQ 7) (hXF : ∀ i, X i ≠ F) (hFO : F ≠ RQ 7) (hXC : ∀ i, X i ≠ C) (hFC : F ≠ C)
    (hQC : RQ 0 ≠ C) (hQD : RQ 0 ≠ D) (hCD : C ≠ D) (hCO : C ≠ RQ 7) (hDO : D ≠ RQ 7)
    (σ : WState ns nr) (q : ℕ) (hq : σ.val (RQ 0) = q) (hX : ∀ i, σ.val (X i) = 0) (hF : σ.val F = 0)
    (hR : ∀ i : Fin 8, i ≠ 0 → i ≠ 7 → σ.val (RQ i) = 0) (hC0 : σ.val C = 0) (hD0 : σ.val D = 0)
    (ho : σ.sh o = (σ.st o).length) (hcap : (σ.st W).length + q + 1 ≤ cap)
    (hOc : σ.val (RQ 7) + q + 2 * (Interfaces.gateWord (readGate q ((σ.st W).drop (σ.sh W))).1).length +
      4 * (σ.st W).length + 6 * natBitLength q + 12 ≤ cap) :
    WExec cap (gateW W o X F RQ C D) σ
      (appendO (σ.seth W (gateEnd (σ.st W) (σ.sh W) q)) o (RQ 7)
        (marks (Interfaces.gateWord (readGate q ((σ.st W).drop (σ.sh W))).1)))
      (fGateCost q (σ.st W).length) := by
  set w := σ.st W with hw
  set p := σ.sh W with hp
  set n := w.length with hn
  set OP := RQ 7 with hOPdef
  obtain ⟨hend, hword⟩ := readGate_drop w p q
  rw [hword] at hOc ⊢
  set f : ℕ → ℤ := fun i => ival w (iter (intEnd w) p i) with hf
  set out : ℕ → List Bool := fun i => natWord q ++ ((List.range i).map f).flatMap Interfaces.intWord with hout
  have hgv : gateVals w p q = (List.range q).map f := rfl
  have hout_le : ∀ i ≤ q, (out i).length ≤ (natWord q ++ (gateVals w p q).flatMap Interfaces.intWord ++
      Interfaces.intWord (ival w (iter (intEnd w) p q))).length := by
    intro i hi
    have htake : (List.range i).map f = ((List.range q).map f).take i := by
      rw [← List.map_take, List.take_range, Nat.min_eq_left hi]
    simp only [hout, hgv, List.length_append, htake]
    have := flatMap_take_length_le Interfaces.intWord ((List.range q).map f) i
    omega
  -- `natWord q`
  have e1 := writeNatM_spec cap o RQ σ (hR 1 (by decide) (by decide)) (hR 2 (by decide) (by decide))
    (hR 3 (by decide) (by decide)) (hR 4 (by decide) (by decide)) (hR 5 (by decide) (by decide))
    (hR 6 (by decide) (by decide)) ho (by have h7 : σ.val (RQ 7) = σ.val OP := rfl; rw [hq]; omega)
  rw [hq] at e1
  set σ1 := appendO σ o OP (marks (natWord q)) with hσ1
  -- `C := q`
  have hQO : RQ 0 ≠ OP := RQ.injective.ne (by decide)
  have hσ1Q : σ1.val (RQ 0) = q := by
    simp [hσ1, appendO, Function.update_of_ne hQO, hq]
  have e2 := dupR_spec cap (RQ 0) C D hQC hQD hCD σ1 (by simp [hσ1, appendO, Function.update_of_ne hDO, hD0])
    (by rw [hσ1Q]; simp [hσ1, appendO, Function.update_of_ne hCO, hC0]; omega)
  have hσ1C : σ1.val C = 0 := by simp [hσ1, appendO, Function.update_of_ne hCO, hC0]
  rw [hσ1Q, hσ1C, Nat.zero_add] at e2
  -- the loop states
  set g : ℕ → WState ns nr := fun i => (appendO (σ.seth W (iter (intEnd w) p i)) o OP (marks (out i))).setv C (q - i)
    with hg
  have hsW : σ.seth W p = σ := by
    apply WState.eq <;> try rfl
    funext j; by_cases hj : j = W
    · subst hj; simp [hp]
    · simp [Function.update_of_ne hj]
  have hg0 : g 0 = σ1.setv C q := by
    simp only [hg, hσ1, hout, iter, List.range_zero, List.map_nil, List.flatMap_nil, List.append_nil, Nat.sub_zero, hsW]
  have hgC : ∀ i ≤ q, (g i).val C = q - i := fun i _ => by simp [hg]
  have hbody : ∀ i < q, WExec cap (intW W o X F OP) ((g i).setv C (q - i - 1)) (g (i + 1)) (fIntCost n) := by
    intro i hi
    set τ := (g i).setv C (q - i - 1) with hτ
    have hτW : τ.st W = w := by simp [hτ, hg, appendO, Function.update_of_ne hWo, hw]
    have hτp : τ.sh W = iter (intEnd w) p i := by simp [hτ, hg, appendO, Function.update_of_ne hWo]
    have e := intW_spec' cap W o X F OP hWo hXO hXF hFO τ
      (fun k => by simp [hτ, hg, appendO, Function.update_apply, hXC k, hXO k, hX])
      (by simp [hτ, hg, appendO, Function.update_apply, hFC, hFO, hF])
      (by simp [hτ, hg, appendO, Function.update_apply, Ne.symm hWo, ho])
      (by
        have := hout_le i hi.le
        rw [hτW]
        simp [hτ, hg, appendO, Function.update_apply, Ne.symm hCO, marks_length]
        omega)
    rw [hτW, hτp] at e
    refine WExec.cast cap e ?_ le_rfl
    have hpos : iter (intEnd w) p (i + 1) = intEnd w (iter (intEnd w) p i) := iter_succ' _ _ _
    have hout1 : out (i + 1) = out i ++ Interfaces.intWord (f i) := by
      simp only [hout, List.range_succ, List.map_append, List.flatMap_append, List.map_cons, List.map_nil,
        List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]
    apply WState.eq
    · funext j; by_cases hj : j = W
      · subst hj; simp [hτ, hg, appendO, hWo, hpos]
      · by_cases hjo : j = o
        · subst hjo; simp [hτ, hg, appendO, hj, Ne.symm hWo, hout1, marksApp, marks_length, hf]; omega
        · simp [hτ, hg, appendO, Function.update_of_ne hj, Function.update_of_ne hjo]
    · funext j; by_cases hjo : j = o
      · subst hjo; simp [hτ, hg, appendO, hout1, marksApp, hf]
      · simp [hτ, hg, appendO, Function.update_of_ne hjo]
    · funext r
      simp only [hτ, hg, appendO_val, WState.setv_val, WState.seth_val, Function.update_apply]
      by_cases hr : r = OP
      · subst hr; simp [hCO, Ne.symm hCO, hout1, marksApp, marks_length, hf]; omega
      by_cases hrC : r = C
      · subst hrC; simp [hr]; omega
      · simp [hr, hrC]
    · simp [hτ, hg]
  have e3 := repLoop_spec cap C (intW W o X F OP) q (fIntCost n) g hgC (by omega) hbody
  rw [hg0] at e3
  -- the threshold
  set τ := g q with hτ
  have hτW : τ.st W = w := by simp [hτ, hg, appendO, Function.update_of_ne hWo, hw]
  have hτp : τ.sh W = iter (intEnd w) p q := by simp [hτ, hg, appendO, Function.update_of_ne hWo]
  have e4 := intW_spec' cap W o X F OP hWo hXO hXF hFO τ
    (fun k => by simp [hτ, hg, appendO, Function.update_apply, hXC k, hXO k, hX])
    (by simp [hτ, hg, appendO, Function.update_apply, hFC, hFO, hF])
    (by simp [hτ, hg, appendO, Function.update_apply, Ne.symm hWo, ho])
    (by
      have := hout_le q le_rfl
      rw [hτW]
      simp [hτ, hg, appendO, Function.update_apply, Ne.symm hCO, marks_length]
      omega)
  rw [hτW, hτp] at e4
  refine WExec.cast cap (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 e4))) ?_ ?_
  · apply WState.eq
    · funext j; by_cases hj : j = W
      · subst hj; simp [hτ, hg, appendO, hWo, gateEnd]
      · by_cases hjo : j = o
        · subst hjo; simp [hτ, hg, appendO, hj, Ne.symm hWo, hout, hgv, marksApp, marks_length]; omega
        · simp [hτ, hg, appendO, Function.update_of_ne hj, Function.update_of_ne hjo]
    · funext j; by_cases hjo : j = o
      · subst hjo; simp [hτ, hg, appendO, hout, hgv, marksApp, hf]
      · simp [hτ, hg, appendO, Function.update_of_ne hjo]
    · funext r
      simp only [hτ, hg, appendO_val, WState.setv_val, WState.seth_val, Function.update_apply]
      by_cases hr : r = OP
      · subst hr; simp [hCO, Ne.symm hCO, hout, hgv, marksApp, marks_length]; omega
      by_cases hrC : r = C
      · subst hrC; simp [hr, hC0]
      · simp [hr, hrC]
    · simp [hτ, hg]
  · unfold fGateCost; nlinarith

end NearCubicGates.Close.Codec
