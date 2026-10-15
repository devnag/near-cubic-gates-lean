import Proof.Gates.CheckedPCPP.ChecksW
import Proof.Gates.CheckedPCPP.Composite
import Proof.Gates.CheckedPCPP.DescW

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.CheckedPCPP.SupW

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.RepairOrdinary.Streaming NearCubicWires.SourceInterfaces
open NearCubicGates.PublishedSources.PCPP NearCubicGates.Close.Gadget NearCubicGates.Close.WordPrograms
open NearCubicGates.Close.CheckedPCPP.NodeEmit NearCubicGates.Close.CheckedPCPP.ChecksW

/-! ## Semantics -/

section Sem
variable (E : LinearCodeFamily) (q : ℕ)

/-- The support elements of row `j` among the first `i` columns. -/
def sl (j : Fin (E.length q)) (i : ℕ) : List (Fin q) := ((List.finRange q).take i).filter (· ∈ E.support q j)

theorem sl_zero (j : Fin (E.length q)) : sl E q j 0 = [] := by simp [sl]

theorem sl_succ (j : Fin (E.length q)) (i : ℕ) (hi : i < q) :
    sl E q j (i + 1) = sl E q j i ++ (if (⟨i, hi⟩ : Fin q) ∈ E.support q j then [⟨i, hi⟩] else []) := by
  unfold sl
  rw [take_succ_finRange q i hi, List.filter_append]
  congr 1
  by_cases h : (⟨i, hi⟩ : Fin q) ∈ E.support q j <;> simp [h]

theorem sl_full (j : Fin (E.length q)) : sl E q j q = canonList (E.support q j) := by
  unfold sl canonList
  rw [List.take_of_length_le (by simp)]

theorem sl_length_le (j : Fin (E.length q)) (i : ℕ) : (sl E q j i).length ≤ i := by
  unfold sl
  exact (List.length_filter_le _ _).trans (by simp)

/-- The record of row `j`. -/
def rowRec (j : Fin (E.length q)) : List Bool :=
  Interfaces.listWord natWord ((canonList (E.support q j)).map Fin.val)

theorem rowRec_eq (j : Fin (E.length q)) :
    rowRec E q j = natWord (sl E q j q).length ++ (sl E q j q).flatMap (fun i => natWord i.val) := by
  simp only [rowRec, Interfaces.listWord, sl_full, List.length_map, List.flatMap_map]

/-- The records of the first `j` rows. -/
def recs (j : ℕ) : List Bool := ((List.finRange (E.length q)).take j).flatMap (rowRec E q)

theorem recs_full : recs E q (E.length q) = CheckedPCPP.supportsWord E q := by
  unfold recs CheckedPCPP.supportsWord rowRec
  rw [List.take_of_length_le (by simp)]

theorem recs_succ (j : ℕ) (hj : j < E.length q) : recs E q (j + 1) = recs E q j ++ rowRec E q ⟨j, hj⟩ := by
  unfold recs
  rw [take_succ_finRange _ j hj, List.flatMap_append]
  simp

end Sem

/-! ## Byte bounds -/

theorem natWord_le (x : ℕ) : (natWord x).length ≤ 2 * x + 3 := by
  rw [ChecksW.natWord_len]; have := NodeEmit.natBitLength_le x; omega

theorem flat_le {q : ℕ} (l : List (Fin q)) : (l.flatMap fun i => natWord i.val).length ≤ l.length * (2 * q + 3) := by
  induction l with
  | nil => simp
  | cons i l ih =>
    have := natWord_le i.val
    have := i.isLt
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    nlinarith

theorem rowRec_le (E : LinearCodeFamily) (q : ℕ) (j : Fin (E.length q)) :
    (rowRec E q j).length ≤ (q + 1) * (2 * q + 3) := by
  rw [rowRec_eq, List.length_append]
  have h1 := natWord_le (sl E q j q).length
  have h2 := flat_le (sl E q j q)
  have h3 := sl_length_le E q j q
  have : (sl E q j q).length * (2 * q + 3) ≤ q * (2 * q + 3) := Nat.mul_le_mul_right _ h3
  nlinarith

theorem recs_le (E : LinearCodeFamily) (q : ℕ) : ∀ j, j ≤ E.length q → (recs E q j).length ≤ j * ((q + 1) * (2 * q + 3))
  | 0, _ => by simp [recs]
  | j + 1, hj => by
    rw [recs_succ E q j (by omega), List.length_append]
    have := recs_le E q j (by omega)
    have := rowRec_le E q ⟨j, by omega⟩
    nlinarith

/-! ## Programs -/

variable {ns nr : ℕ} (cap : ℕ) (G : Fin 18 ↪ Fin nr) (SUP MAT : Fin (ns + 1))

/-- Count pass, one column. -/
def cntBody : WMX ns nr := .seq (.ifs MAT (WMX.inc (G 10)) WMX.skip) (WMX.fwd MAT)

/-- Index pass, one column. -/
def emBody : WMX ns nr :=
  .seq (.ifs MAT (.wm (fieldW SUP (Rw G) (G 8) ([G 11], 0))) WMX.skip) (.seq (WMX.fwd MAT) (WMX.inc (G 11)))

/-- One row. -/
def rowS : WMX ns nr :=
  .seq (repK (G 9) (G 15) (cntBody G MAT)) (.seq (.wm (fieldW SUP (Rw G) (G 8) ([G 10], 0)))
    (.seq (addR (G 9) (G 12) (G 8)) (.seq (.wm (WM.rewind MAT (G 12))) (.seq (repK (G 9) (G 15) (emBody G SUP MAT))
    (.seq (.wm (WM.clear (G 11))) (.wm (WM.clear (G 10))))))))

def supW : WMX ns nr := .seq (repK (G 16) (G 17) (rowS G SUP MAT)) (.wm (emitC SUP (G 7) false))

/-! ## The count pass -/

section Passes
variable (E : LinearCodeFamily) (q : ℕ) (j : Fin (E.length q))

/-- The count pass after `i` columns (relative to the row's start state `σr`). -/
structure CntInv (σr : WState ns nr) (i : ℕ) (τ : WState ns nr) : Prop where
  cnt : τ.val (G 10) = (sl E q j i).length
  math : τ.sh MAT = j.val * q + i
  mat : τ.st MAT = σr.st MAT
  fr : SameExcept σr τ [MAT] [G 10, G 9, G 15]

theorem cntInv_setv (σr : WState ns nr) (i : ℕ) (τ : WState ns nr) (h : CntInv G MAT E q j σr i τ) (r : Fin 18)
    (hr : r = 9 ∨ r = 15) (v : ℕ) : CntInv G MAT E q j σr i (τ.setv (G r) v) := by
  have h10 : G 10 ≠ G r := by apply G_ne; rcases hr with rfl | rfl <;> decide
  refine ⟨by simp [Function.update_of_ne h10, h.cnt], h.math, h.mat, h.fr.trans ⟨fun _ _ => ⟨rfl, rfl⟩, fun a ha => ?_, rfl⟩⟩
  have : a ≠ G r := by intro e; subst e; rcases hr with rfl | rfl <;> simp at ha
  simp [Function.update_of_ne this]

theorem cntBody_runs (σr : WState ns nr) (hmat : ∀ p, readTapeBit (σr.st MAT) p = matBit E q p)
    (hcap : q + 1 ≤ cap) (i : ℕ) (hi : i < q) (τ : WState ns nr) (h : CntInv G MAT E q j σr i τ) :
    Runs cap (cntBody G MAT) τ 6 (fun τ' => CntInv G MAT E q j σr (i + 1) τ' ∧
      τ'.val (G 9) = τ.val (G 9) ∧ τ'.val (G 15) = τ.val (G 15)) := by
  have hbit : wbit τ MAT = decide ((⟨i, hi⟩ : Fin q) ∈ E.support q j) := by
    unfold wbit; rw [h.mat, h.math, hmat, matBit_at E q ⟨i, hi⟩ j]
  have hl := sl_length_le E q j i
  by_cases hm : (⟨i, hi⟩ : Fin q) ∈ E.support q j
  · have e1 := WXExec.inc cap (G 10) τ (by rw [h.cnt]; omega)
    have e2 := WXExec.fwd cap MAT (τ.setv (G 10) (τ.val (G 10) + 1))
    refine ⟨_, WXExec.mono (WXExec.seq (WXExec.ifsT (by rw [hbit]; simp [hm]) e1) e2) (by omega), ⟨?_, ?_, ?_, ?_⟩,
      ?_, ?_⟩
    · simp [h.cnt, sl_succ E q j i hi, hm]
    · simp [h.math]; ring
    · simp [h.mat]
    · refine h.fr.trans ⟨fun x hx => ?_, fun r hr => ?_, by simp⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; simp [Function.update_of_ne hx]
      · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr; simp [Function.update_of_ne hr.1]
    · simp [Function.update_of_ne (G_ne G (show (9 : Fin 18) ≠ 10 by decide))]
    · simp [Function.update_of_ne (G_ne G (show (15 : Fin 18) ≠ 10 by decide))]
  · have e2 := WXExec.fwd cap MAT τ
    refine ⟨_, WXExec.mono (WXExec.seq (WXExec.ifsF (by rw [hbit]; simp [hm]) (WXExec.skip cap τ)) e2) (by omega),
      ⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
    · simp [h.cnt, sl_succ E q j i hi, hm]
    · simp [h.math]; ring
    · simp [h.mat]
    · refine h.fr.trans ⟨fun x hx => ?_, fun r _ => rfl, rfl⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; simp [Function.update_of_ne hx]
    · rfl
    · rfl

/-! ## The index pass -/

/-- The index pass after `i` columns (relative to its start state `σe`). -/
structure EmInv (σe : WState ns nr) (i : ℕ) (τ : WState ns nr) : Prop where
  out : τ.st SUP = σe.st SUP ++ marks ((sl E q j i).flatMap fun x => natWord x.val)
  outh : τ.sh SUP = (τ.st SUP).length
  pos : τ.val (G 7) = σe.val (G 7) + (marks ((sl E q j i).flatMap fun x => natWord x.val)).length
  col : τ.val (G 11) = i
  math : τ.sh MAT = j.val * q + i
  mat : τ.st MAT = σe.st MAT
  clean : Clean (Rw G) (G 8) τ
  fr : SameExcept σe τ [SUP, MAT] [G 7, G 11, G 9, G 15]

theorem emInv_setv (σe : WState ns nr) (i : ℕ) (τ : WState ns nr) (h : EmInv G SUP MAT E q j σe i τ) (r : Fin 18)
    (hr : r = 9 ∨ r = 15) (v : ℕ) : EmInv G SUP MAT E q j σe i (τ.setv (G r) v) := by
  have hne : ∀ b : Fin 18, b ≠ 9 → b ≠ 15 → G b ≠ G r := by
    intro b h1 h2; apply G_ne; rcases hr with rfl | rfl <;> assumption
  refine ⟨h.out, h.outh, ?_, ?_, h.math, h.mat, ⟨fun a ha => ?_, ?_⟩, ?_⟩
  · simp [Function.update_of_ne (hne 7 (by decide) (by decide)), h.pos]
  · simp [Function.update_of_ne (hne 11 (by decide) (by decide)), h.col]
  · have : Rw G a ≠ G r := by rw [Rw_apply]; apply hne <;> (intro e; have := congrArg Fin.val e; simp at this; omega)
    simp [Function.update_of_ne this, h.clean.1 a ha]
  · simp [Function.update_of_ne (hne 8 (by decide) (by decide)), h.clean.2]
  · refine h.fr.trans ⟨fun _ _ => ⟨rfl, rfl⟩, fun a ha => ?_, rfl⟩
    have : a ≠ G r := by intro e; subst e; rcases hr with rfl | rfl <;> simp at ha
    simp [Function.update_of_ne this]

theorem emBody_runs (hSM : SUP ≠ MAT) (σe : WState ns nr) (hmat : ∀ p, readTapeBit (σe.st MAT) p = matBit E q p)
    (hcap : σe.val (G 7) + 2 * q * (2 * q + 3) + 8 * q + 12 ≤ cap) (i : ℕ) (hi : i < q) (τ : WState ns nr)
    (h : EmInv G SUP MAT E q j σe i τ) :
    Runs cap (emBody G SUP MAT) τ (fieldCost q 3 + 7) (fun τ' => EmInv G SUP MAT E q j σe (i + 1) τ' ∧
      τ'.val (G 9) = τ.val (G 9) ∧ τ'.val (G 15) = τ.val (G 15)) := by
  have hbit : wbit τ MAT = decide ((⟨i, hi⟩ : Fin q) ∈ E.support q j) := by
    unfold wbit; rw [h.mat, h.math, hmat, matBit_at E q ⟨i, hi⟩ j]
  have hl := sl_length_le E q j i
  have hMS : MAT ≠ SUP := Ne.symm hSM
  have hfl := flat_le (sl E q j i)
  have hfl2 : (sl E q j i).length * (2 * q + 3) ≤ q * (2 * q + 3) := Nat.mul_le_mul_right _ (by omega)
  by_cases hm : (⟨i, hi⟩ : Fin q) ∈ E.support q j
  · have hfv : fieldVal τ ([G 11], 0) = i := by simp [fieldVal, regSum, h.col]
    have e1 := fieldW_spec cap SUP (Rw G) (G 8) (T_ne G) ([G 11], 0) (fieldOK_G G [11] 0 (by decide)) τ h.clean h.outh
      (by
        rw [hfv, show Rw G 7 = G 7 from rfl, h.pos, marks_len]
        have := NodeEmit.natBitLength_le i
        nlinarith)
    rw [hfv, show Rw G 7 = G 7 from rfl] at e1
    simp only [List.length_cons, List.length_nil, Nat.zero_add] at e1
    have hfc := fieldCost_mono (v := i) (v' := q) (k := 1) (k' := 3) (by omega) (by omega)
    set τ1 := appendO τ SUP (G 7) (marks (natWord i)) with hτ1
    have e2 := WXExec.fwd cap MAT τ1
    have e3 := WXExec.inc cap (G 11) (τ1.seth MAT (τ1.sh MAT + 1)) (by
      simp [hτ1, Function.update_of_ne (G_ne G (show (11 : Fin 18) ≠ 7 by decide)), h.col]; omega)
    have hsl : (sl E q j (i + 1)).flatMap (fun x => natWord x.val) =
        (sl E q j i).flatMap (fun x => natWord x.val) ++ natWord i := by
      rw [sl_succ E q j i hi, if_pos hm]; simp
    refine ⟨_, WXExec.mono (WXExec.seq (WXExec.ifsT (by rw [hbit]; simp [hm]) (WXExec.wm e1)) (WXExec.seq e2 e3))
      (by omega), ⟨?_, ?_, ?_, ?_, ?_, ?_, ⟨fun a ha => ?_, ?_⟩, ?_⟩, ?_, ?_⟩
    · simp [hτ1, Function.update_of_ne hMS, h.out, hsl, NodeEmit.marks_append]
    · simp [hτ1, Function.update_of_ne hSM, Function.update_of_ne hMS, h.outh]
    · simp [hτ1, Function.update_of_ne (G_ne G (show (7 : Fin 18) ≠ 11 by decide)), h.pos, hsl,
        NodeEmit.marks_append]; ring
    · simp [hτ1, h.col]
    · simp [hτ1, Function.update_of_ne hMS, h.math]; ring
    · simp [hτ1, Function.update_of_ne hMS, h.mat]
    · have h11 : Rw G a ≠ G 11 := Rw_ne G a 11 (by decide)
      have h7 : Rw G a ≠ G 7 := by
        rw [Rw_apply]; apply G_ne; intro e; apply ha; ext; have := congrArg Fin.val e; simpa using this
      simp [hτ1, Function.update_of_ne h11, Function.update_of_ne h7, h.clean.1 a ha]
    · simp [hτ1, Function.update_of_ne (G_ne G (show (8 : Fin 18) ≠ 11 by decide)),
        Function.update_of_ne (G_ne G (show (8 : Fin 18) ≠ 7 by decide)), h.clean.2]
    · refine h.fr.trans ⟨fun x hx => ?_, fun r hr => ?_, by simp [hτ1]⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
        simp [hτ1, Function.update_of_ne hx.1, Function.update_of_ne hx.2]
      · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        simp [hτ1, Function.update_of_ne hr.1, Function.update_of_ne hr.2.1]
    · simp [hτ1, Function.update_of_ne (G_ne G (show (9 : Fin 18) ≠ 11 by decide)),
        Function.update_of_ne (G_ne G (show (9 : Fin 18) ≠ 7 by decide))]
    · simp [hτ1, Function.update_of_ne (G_ne G (show (15 : Fin 18) ≠ 11 by decide)),
        Function.update_of_ne (G_ne G (show (15 : Fin 18) ≠ 7 by decide))]
  · have e2 := WXExec.fwd cap MAT τ
    have e3 := WXExec.inc cap (G 11) (τ.seth MAT (τ.sh MAT + 1)) (by simp [h.col]; omega)
    have hsl : sl E q j (i + 1) = sl E q j i := by rw [sl_succ E q j i hi, if_neg hm, List.append_nil]
    refine ⟨_, WXExec.mono (WXExec.seq (WXExec.ifsF (by rw [hbit]; simp [hm]) (WXExec.skip cap τ))
      (WXExec.seq e2 e3)) (by unfold fieldCost; omega), ⟨?_, ?_, ?_, ?_, ?_, ?_, ⟨fun a ha => ?_, ?_⟩, ?_⟩, ?_, ?_⟩
    · simp [Function.update_of_ne hMS, h.out, hsl]
    · simp [Function.update_of_ne hSM, h.outh]
    · simp [Function.update_of_ne (G_ne G (show (7 : Fin 18) ≠ 11 by decide)), h.pos, hsl]
    · simp [h.col]
    · simp [h.math]; ring
    · simp [h.mat]
    · have h11 : Rw G a ≠ G 11 := Rw_ne G a 11 (by decide)
      simp [Function.update_of_ne h11, h.clean.1 a ha]
    · simp [Function.update_of_ne (G_ne G (show (8 : Fin 18) ≠ 11 by decide)), h.clean.2]
    · refine h.fr.trans ⟨fun x hx => ?_, fun r hr => ?_, by simp⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
        simp [Function.update_of_ne hx.2]
      · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        simp [Function.update_of_ne hr.2.1]
    · simp [Function.update_of_ne (G_ne G (show (9 : Fin 18) ≠ 11 by decide))]
    · simp [Function.update_of_ne (G_ne G (show (15 : Fin 18) ≠ 11 by decide))]

end Passes

/-! ## Rows -/

section Rows
variable (E : LinearCodeFamily) (q : ℕ) (σ0 : WState ns nr)

/-- The state after the first `j` rows. -/
structure SRowInv (j : ℕ) (τ : WState ns nr) : Prop where
  out : τ.st SUP = σ0.st SUP ++ marks (recs E q j)
  outh : τ.sh SUP = (τ.st SUP).length
  pos : τ.val (G 7) = σ0.val (G 7) + (marks (recs E q j)).length
  cnt : τ.val (G 10) = 0
  col : τ.val (G 11) = 0
  qq : τ.val (G 9) = q
  qc : τ.val (G 12) = 0
  cq : τ.val (G 15) = 0
  math : τ.sh MAT = j * q
  mat : τ.st MAT = σ0.st MAT
  clean : Clean (Rw G) (G 8) τ
  fr : SameExcept σ0 τ [SUP, MAT] [G 7, G 9, G 10, G 11, G 12, G 15, G 16, G 17]

theorem sRowInv_setv (j : ℕ) (τ : WState ns nr) (h : SRowInv G SUP MAT E q σ0 j τ) (r : Fin 18)
    (hr : r = 16 ∨ r = 17) (v : ℕ) : SRowInv G SUP MAT E q σ0 j (τ.setv (G r) v) := by
  have hne : ∀ b : Fin 18, b ≠ 16 → b ≠ 17 → G b ≠ G r := by
    intro b h1 h2; apply G_ne; rcases hr with rfl | rfl <;> assumption
  refine ⟨h.out, h.outh, ?_, ?_, ?_, ?_, ?_, ?_, h.math, h.mat, ⟨fun a ha => ?_, ?_⟩, ?_⟩
  · simp [Function.update_of_ne (hne 7 (by decide) (by decide)), h.pos]
  · simp [Function.update_of_ne (hne 10 (by decide) (by decide)), h.cnt]
  · simp [Function.update_of_ne (hne 11 (by decide) (by decide)), h.col]
  · simp [Function.update_of_ne (hne 9 (by decide) (by decide)), h.qq]
  · simp [Function.update_of_ne (hne 12 (by decide) (by decide)), h.qc]
  · simp [Function.update_of_ne (hne 15 (by decide) (by decide)), h.cq]
  · have : Rw G a ≠ G r := by rw [Rw_apply]; apply hne <;> (intro e; have := congrArg Fin.val e; simp at this; omega)
    simp [Function.update_of_ne this, h.clean.1 a ha]
  · simp [Function.update_of_ne (hne 8 (by decide) (by decide)), h.clean.2]
  · refine h.fr.trans ⟨fun _ _ => ⟨rfl, rfl⟩, fun a ha => ?_, rfl⟩
    have : a ≠ G r := by intro e; subst e; rcases hr with rfl | rfl <;> simp at ha
    simp [Function.update_of_ne this]

/-- The cost of one row. -/
def rowCostS (q : ℕ) : ℕ := (q * (6 + 8) + 7 * q + 3) + 1 + (fieldCost q 3 + 1) + (18 * q + 3) + 1 + (5 * q + 1) + 1 +
  (q * (fieldCost q 3 + 7 + 8) + 7 * q + 3) + 1 + (3 * q + 1) + 1 + (3 * q + 1)

theorem rowS_runs (hSM : SUP ≠ MAT) (hmat : ∀ p, readTapeBit (σ0.st MAT) p = matBit E q p)
    (hcap : σ0.val (G 7) + 2 * (E.length q * ((q + 1) * (2 * q + 3))) + 2 * q * (2 * q + 3) + 16 * q + 24 ≤ cap)
    (j : ℕ) (hj : j < E.length q) (τ : WState ns nr) (h : SRowInv G SUP MAT E q σ0 j τ) :
    Runs cap (rowS G SUP MAT) τ (rowCostS q) (fun τ' => SRowInv G SUP MAT E q σ0 (j + 1) τ' ∧
      τ'.val (G 16) = τ.val (G 16) ∧ τ'.val (G 17) = τ.val (G 17)) := by
  have hMS : MAT ≠ SUP := Ne.symm hSM
  set jj : Fin (E.length q) := ⟨j, hj⟩ with hjj
  have hrl := recs_le E q j hj.le
  have hjL : j * ((q + 1) * (2 * q + 3)) ≤ E.length q * ((q + 1) * (2 * q + 3)) := Nat.mul_le_mul_right _ hj.le
  have hτmat : ∀ p, readTapeBit (τ.st MAT) p = matBit E q p := by rw [h.mat]; exact hmat
  -- 1. count
  have c0 : CntInv G MAT E q jj τ 0 τ := ⟨by rw [h.cnt, sl_zero]; rfl, by rw [h.math, hjj]; simp, rfl,
    SameExcept.refl _ _ _⟩
  obtain ⟨τ1, e1, hc1, hc1Q, hc1C⟩ := Runs.rep (cap := cap) (G_ne G (show (9 : Fin 18) ≠ 15 by decide)) 6 q
    (CntInv G MAT E q jj τ) (by omega)
    (fun k σ v hk => cntInv_setv G MAT E q jj τ k σ hk 9 (Or.inl rfl) v)
    (fun k σ v hk => cntInv_setv G MAT E q jj τ k σ hk 15 (Or.inr rfl) v)
    (fun k hk σ hk' => cntBody_runs cap G MAT E q jj τ hτmat (by omega) k hk σ hk') τ c0 h.qq h.cq
  have h1v : ∀ r, r ∉ [G 10, G 9, G 15] → τ1.val r = τ.val r := fun r hr => hc1.fr.val hr
  have h1s : ∀ x, x ≠ MAT → τ1.st x = τ.st x ∧ τ1.sh x = τ.sh x := fun x hx => hc1.fr.1 x (by simp [hx])
  have hcl1 : Clean (Rw G) (G 8) τ1 := ⟨fun i hi => by
      rw [h1v _ (by simp [Rw_ne G i 10 (by decide), Rw_ne G i 9 (by decide), Rw_ne G i 15 (by decide)])]
      exact h.clean.1 i hi, by rw [h1v _ (by simp [G_ne G (show (8 : Fin 18) ≠ 10 by decide),
        G_ne G (show (8 : Fin 18) ≠ 9 by decide), G_ne G (show (8 : Fin 18) ≠ 15 by decide)])]; exact h.clean.2⟩
  have hsq := sl_length_le E q jj q
  -- 2. write the count
  have hfv : fieldVal τ1 ([G 10], 0) = (sl E q jj q).length := by simp [fieldVal, regSum, hc1.cnt]
  have h17 : τ1.val (G 7) = τ.val (G 7) := h1v _ (by simp [G_ne G (show (7 : Fin 18) ≠ 10 by decide),
    G_ne G (show (7 : Fin 18) ≠ 9 by decide), G_ne G (show (7 : Fin 18) ≠ 15 by decide)])
  have e2 := fieldW_spec cap SUP (Rw G) (G 8) (T_ne G) ([G 10], 0) (fieldOK_G G [10] 0 (by decide)) τ1 hcl1
    (by rw [(h1s SUP hSM).1, (h1s SUP hSM).2]; exact h.outh)
    (by
      rw [hfv, show Rw G 7 = G 7 from rfl, h17, h.pos, marks_len]
      have := NodeEmit.natBitLength_le (sl E q jj q).length
      nlinarith)
  rw [hfv, show Rw G 7 = G 7 from rfl] at e2
  simp only [List.length_cons, List.length_nil, Nat.zero_add] at e2
  set τ2 := appendO τ1 SUP (G 7) (marks (natWord (sl E q jj q).length)) with hτ2
  -- 3. copy q, 4. rewind the matrix row
  have e3 := addR_spec cap (A := G 9) (B := G 12) (T := G 8) (G_ne G (by decide)) (G_ne G (by decide))
    (G_ne G (by decide)) τ2 (by simp [hτ2, Function.update_of_ne (G_ne G (show (8 : Fin 18) ≠ 7 by decide))]; exact hcl1.2)
    (by simp [hτ2, Function.update_of_ne (G_ne G (show (12 : Fin 18) ≠ 7 by decide)),
      Function.update_of_ne (G_ne G (show (9 : Fin 18) ≠ 7 by decide)), hc1Q, h.qq,
      h1v (G 12) (by simp [G_ne G (show (12 : Fin 18) ≠ 10 by decide), G_ne G (show (12 : Fin 18) ≠ 9 by decide),
        G_ne G (show (12 : Fin 18) ≠ 15 by decide)]), h.qc]; omega)
  have h2_12 : τ2.val (G 12) = 0 := by
    simp [hτ2, Function.update_of_ne (G_ne G (show (12 : Fin 18) ≠ 7 by decide)),
      h1v (G 12) (by simp [G_ne G (show (12 : Fin 18) ≠ 10 by decide), G_ne G (show (12 : Fin 18) ≠ 9 by decide),
        G_ne G (show (12 : Fin 18) ≠ 15 by decide)]), h.qc]
  have h2_9 : τ2.val (G 9) = q := by
    simp [hτ2, Function.update_of_ne (G_ne G (show (9 : Fin 18) ≠ 7 by decide)), hc1Q, h.qq]
  rw [h2_12, h2_9, Nat.zero_add] at e3
  have e4 := wrewind_spec (cap := cap) MAT (G 12) q (τ2.setv (G 12) q) (by simp) (by simp; omega)
  have hmat1 : τ1.sh MAT = j * q + q := by rw [hc1.math]
  set τ4 := ((τ2.setv (G 12) q).setv (G 12) 0).seth MAT ((τ2.setv (G 12) q).sh MAT - q) with hτ4
  have h4math : τ4.sh MAT = j * q := by simp [hτ4, hτ2, Function.update_of_ne hMS, hmat1]
  have h4_11 : τ4.val (G 11) = 0 := by
    simp [hτ4, hτ2, Function.update_of_ne (G_ne G (show (11 : Fin 18) ≠ 12 by decide)),
      Function.update_of_ne (G_ne G (show (11 : Fin 18) ≠ 7 by decide)),
      h1v (G 11) (by simp [G_ne G (show (11 : Fin 18) ≠ 10 by decide), G_ne G (show (11 : Fin 18) ≠ 9 by decide),
        G_ne G (show (11 : Fin 18) ≠ 15 by decide)]), h.col]
  have hcl4 : Clean (Rw G) (G 8) τ4 := by
    have h2 := clean_appendO SUP (Rw G) (G 8) τ1 hcl1 (T_ne G) (marks (natWord (sl E q jj q).length))
    refine ⟨fun i hi => ?_, ?_⟩
    · have : Rw G i ≠ G 12 := Rw_ne G i 12 (by decide)
      simp only [hτ4, WState.seth_val, WState.setv_val, Function.update_of_ne this]
      exact h2.1 i hi
    · simp only [hτ4, WState.seth_val, WState.setv_val, Function.update_of_ne (G_ne G (show (8 : Fin 18) ≠ 12 by decide))]
      exact h2.2
  have h4_9 : τ4.val (G 9) = q := by
    simp [hτ4, Function.update_of_ne (G_ne G (show (9 : Fin 18) ≠ 12 by decide)), h2_9]
  have h4_15 : τ4.val (G 15) = 0 := by
    simp [hτ4, hτ2, Function.update_of_ne (G_ne G (show (15 : Fin 18) ≠ 12 by decide)),
      Function.update_of_ne (G_ne G (show (15 : Fin 18) ≠ 7 by decide)), hc1C, h.cq]
  have h4mat : τ4.st MAT = σ0.st MAT := by
    simp [hτ4, hτ2, Function.update_of_ne hMS, hc1.mat, h.mat]
  have h4out : τ4.st SUP = σ0.st SUP ++ marks (recs E q j) ++ marks (natWord (sl E q jj q).length) := by
    simp [hτ4, hτ2, (h1s SUP hSM).1, h.out]
  have h4outh : τ4.sh SUP = (τ4.st SUP).length := by
    simp [hτ4, hτ2, Function.update_of_ne hSM, (h1s SUP hSM).1, (h1s SUP hSM).2, h.outh]
  have h4pos : τ4.val (G 7) = σ0.val (G 7) + (marks (recs E q j)).length +
      (marks (natWord (sl E q jj q).length)).length := by
    simp [hτ4, hτ2, Function.update_of_ne (G_ne G (show (7 : Fin 18) ≠ 12 by decide)), h17, h.pos]
  have e0 : EmInv G SUP MAT E q jj τ4 0 τ4 := by
    have hm0 : marks ([] : List Bool) = [] := rfl
    refine ⟨by simp [sl_zero, hm0], h4outh, by simp [sl_zero, hm0], h4_11, by rw [h4math, hjj]; simp, rfl, hcl4,
      SameExcept.refl _ _ _⟩
  obtain ⟨τ5, e5, hc5, hc5Q, hc5C⟩ := Runs.rep (cap := cap) (G_ne G (show (9 : Fin 18) ≠ 15 by decide))
    (fieldCost q 3 + 7) q (EmInv G SUP MAT E q jj τ4) (by omega)
    (fun k σ v hk => emInv_setv G SUP MAT E q jj τ4 k σ hk 9 (Or.inl rfl) v)
    (fun k σ v hk => emInv_setv G SUP MAT E q jj τ4 k σ hk 15 (Or.inr rfl) v)
    (fun k hk σ hk' => emBody_runs cap G SUP MAT E q jj hSM τ4 (by rw [h4mat]; exact hmat)
      (by
        rw [h4pos, marks_len, marks_len]
        have := NodeEmit.natBitLength_le (sl E q jj q).length
        rw [ChecksW.natWord_len]
        nlinarith) k hk σ hk') τ4 e0 h4_9 h4_15
  have h5v : ∀ r, r ∉ [G 7, G 11, G 9, G 15] → τ5.val r = τ4.val r := fun r hr => hc5.fr.val hr
  -- 6, 7. clear the column and the count
  have e6 := wclear_spec (cap := cap) (G 11) q τ5 hc5.col (by rw [hc5.col]; omega)
  have h5_10 : τ5.val (G 10) = (sl E q jj q).length := by
    rw [h5v _ (by simp [G_ne G (show (10 : Fin 18) ≠ 7 by decide), G_ne G (show (10 : Fin 18) ≠ 11 by decide),
      G_ne G (show (10 : Fin 18) ≠ 9 by decide), G_ne G (show (10 : Fin 18) ≠ 15 by decide)])]
    simp [hτ4, hτ2, Function.update_of_ne (G_ne G (show (10 : Fin 18) ≠ 12 by decide)),
      Function.update_of_ne (G_ne G (show (10 : Fin 18) ≠ 7 by decide)), hc1.cnt]
  have e7 := wclear_spec (cap := cap) (G 10) (sl E q jj q).length (τ5.setv (G 11) 0)
    (by simp [Function.update_of_ne (G_ne G (show (10 : Fin 18) ≠ 11 by decide)), h5_10])
    (by simp [Function.update_of_ne (G_ne G (show (10 : Fin 18) ≠ 11 by decide)), h5_10]; omega)
  have hrow : marks (recs E q (j + 1)) = marks (recs E q j) ++ marks (natWord (sl E q jj q).length) ++
      marks ((sl E q jj q).flatMap fun x => natWord x.val) := by
    rw [recs_succ E q j hj, rowRec_eq, NodeEmit.marks_append, NodeEmit.marks_append, List.append_assoc]
  refine ⟨_, WXExec.mono (WXExec.seq e1 (WXExec.seq (WXExec.wm e2) (WXExec.seq e3 (WXExec.seq (WXExec.wm e4)
    (WXExec.seq e5 (WXExec.seq (WXExec.wm e6) (WXExec.wm e7))))))) ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ⟨fun a ha => ?_, ?_⟩, ?_⟩, ?_, ?_⟩
  · unfold rowCostS
    have := fieldCost_mono (v := (sl E q jj q).length) (v' := q) (k := 1) (k' := 3) hsq (by omega)
    omega
  · simp [hc5.out, h4out, hrow, List.append_assoc]
  · simp [hc5.outh]
  · simp [Function.update_of_ne (G_ne G (show (7 : Fin 18) ≠ 10 by decide)),
      Function.update_of_ne (G_ne G (show (7 : Fin 18) ≠ 11 by decide)), hc5.pos, h4pos, hrow]; ring
  · simp
  · simp [Function.update_of_ne (G_ne G (show (11 : Fin 18) ≠ 10 by decide))]
  · simp [Function.update_of_ne (G_ne G (show (9 : Fin 18) ≠ 10 by decide)),
      Function.update_of_ne (G_ne G (show (9 : Fin 18) ≠ 11 by decide)), hc5Q, h4_9]
  · simp [Function.update_of_ne (G_ne G (show (12 : Fin 18) ≠ 10 by decide)),
      Function.update_of_ne (G_ne G (show (12 : Fin 18) ≠ 11 by decide))]
    rw [h5v _ (by simp [G_ne G (show (12 : Fin 18) ≠ 7 by decide), G_ne G (show (12 : Fin 18) ≠ 11 by decide),
      G_ne G (show (12 : Fin 18) ≠ 9 by decide), G_ne G (show (12 : Fin 18) ≠ 15 by decide)])]
    simp [hτ4]
  · simp [Function.update_of_ne (G_ne G (show (15 : Fin 18) ≠ 10 by decide)),
      Function.update_of_ne (G_ne G (show (15 : Fin 18) ≠ 11 by decide)), hc5C, h4_15]
  · simp [hc5.math, h4math, hjj]; ring
  · simp [hc5.mat, h4mat]
  · have h10 : Rw G a ≠ G 10 := Rw_ne G a 10 (by decide)
    have h11 : Rw G a ≠ G 11 := Rw_ne G a 11 (by decide)
    simp [Function.update_of_ne h10, Function.update_of_ne h11, hc5.clean.1 a ha]
  · simp [Function.update_of_ne (G_ne G (show (8 : Fin 18) ≠ 10 by decide)),
      Function.update_of_ne (G_ne G (show (8 : Fin 18) ≠ 11 by decide)), hc5.clean.2]
  · refine h.fr.trans ⟨fun x hx => ?_, fun r hr => ?_, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
      have hxs : x ∉ [SUP, MAT] := by simp [hx.1, hx.2]
      have e5s := hc5.fr.1 x hxs
      simp only [WState.setv_st, WState.setv_sh]
      rw [e5s.1, e5s.2]
      simp [hτ4, hτ2, Function.update_of_ne hx.1, Function.update_of_ne hx.2, (h1s x hx.2).1, (h1s x hx.2).2]
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [WState.setv_val, Function.update_of_ne hr.2.2.1, Function.update_of_ne hr.2.2.2.1]
      rw [h5v _ (by simp [hr.1, hr.2.2.2.1, hr.2.1, hr.2.2.2.2.2.1])]
      simp [hτ4, hτ2, Function.update_of_ne hr.2.2.2.2.1, Function.update_of_ne hr.1]
      exact h1v r (by simp [hr.2.2.1, hr.2.1, hr.2.2.2.2.2.1])
    · simp [hc5.fr.cell, hτ4, hτ2, hc1.fr.cell]
  · simp [Function.update_of_ne (G_ne G (show (16 : Fin 18) ≠ 10 by decide)),
      Function.update_of_ne (G_ne G (show (16 : Fin 18) ≠ 11 by decide))]
    rw [h5v _ (by simp [G_ne G (show (16 : Fin 18) ≠ 7 by decide), G_ne G (show (16 : Fin 18) ≠ 11 by decide),
      G_ne G (show (16 : Fin 18) ≠ 9 by decide), G_ne G (show (16 : Fin 18) ≠ 15 by decide)])]
    simp [hτ4, hτ2, Function.update_of_ne (G_ne G (show (16 : Fin 18) ≠ 12 by decide)),
      Function.update_of_ne (G_ne G (show (16 : Fin 18) ≠ 7 by decide))]
    exact h1v _ (by simp [G_ne G (show (16 : Fin 18) ≠ 10 by decide), G_ne G (show (16 : Fin 18) ≠ 9 by decide),
      G_ne G (show (16 : Fin 18) ≠ 15 by decide)])
  · simp [Function.update_of_ne (G_ne G (show (17 : Fin 18) ≠ 10 by decide)),
      Function.update_of_ne (G_ne G (show (17 : Fin 18) ≠ 11 by decide))]
    rw [h5v _ (by simp [G_ne G (show (17 : Fin 18) ≠ 7 by decide), G_ne G (show (17 : Fin 18) ≠ 11 by decide),
      G_ne G (show (17 : Fin 18) ≠ 9 by decide), G_ne G (show (17 : Fin 18) ≠ 15 by decide)])]
    simp [hτ4, hτ2, Function.update_of_ne (G_ne G (show (17 : Fin 18) ≠ 12 by decide)),
      Function.update_of_ne (G_ne G (show (17 : Fin 18) ≠ 7 by decide))]
    exact h1v _ (by simp [G_ne G (show (17 : Fin 18) ≠ 10 by decide), G_ne G (show (17 : Fin 18) ≠ 9 by decide),
      G_ne G (show (17 : Fin 18) ≠ 15 by decide)])

theorem sRowInv_zero (hSUP : σ0.sh SUP = (σ0.st SUP).length) (hQ : σ0.val (G 9) = q) (h10 : σ0.val (G 10) = 0)
    (h11 : σ0.val (G 11) = 0) (h12 : σ0.val (G 12) = 0) (h15 : σ0.val (G 15) = 0) (hM : σ0.sh MAT = 0)
    (hcl : Clean (Rw G) (G 8) σ0) : SRowInv G SUP MAT E q σ0 0 σ0 := by
  have hm0 : marks ([] : List Bool) = [] := rfl
  exact ⟨by simp [recs, hm0], hSUP, by simp [recs, hm0], h10, h11, hQ, h12, h15, by simp [hM], rfl, hcl,
    SameExcept.refl _ _ _⟩

def supCost (q L : ℕ) : ℕ := L * (rowCostS q + 8) + 7 * L + 3 + 1 + 7

theorem supW_runs (hSM : SUP ≠ MAT) (hmat : ∀ p, readTapeBit (σ0.st MAT) p = matBit E q p)
    (hcap : σ0.val (G 7) + 2 * (E.length q * ((q + 1) * (2 * q + 3))) + 2 * q * (2 * q + 3) + 16 * q + 24 +
      2 * E.length q ≤ cap)
    (h0 : SRowInv G SUP MAT E q σ0 0 σ0) (hLL : σ0.val (G 16) = E.length q) (hCL : σ0.val (G 17) = 0) :
    ∃ τ, WXExec cap (supW G SUP MAT) σ0 τ (supCost q (E.length q)) ∧
      τ.st SUP = σ0.st SUP ++ marks (CheckedPCPP.supportsWord E q) ++ [false] ∧
      τ.st MAT = σ0.st MAT ∧ SameExcept σ0 τ [SUP, MAT] [G 7, G 9, G 10, G 11, G 12, G 15, G 16, G 17] := by
  obtain ⟨τ, e1, hI, _, _⟩ := Runs.rep (cap := cap) (G_ne G (show (16 : Fin 18) ≠ 17 by decide)) (rowCostS q)
    (E.length q) (SRowInv G SUP MAT E q σ0) (by omega)
    (fun k σ v hk => sRowInv_setv G SUP MAT E q σ0 k σ hk 16 (Or.inl rfl) v)
    (fun k σ v hk => sRowInv_setv G SUP MAT E q σ0 k σ hk 17 (Or.inr rfl) v)
    (fun k hk σ hk' => rowS_runs cap G SUP MAT E q σ0 hSM hmat (by omega) k hk σ hk') σ0 h0 hLL hCL
  have hrl := recs_le E q (E.length q) le_rfl
  have e2 := Codec.emitBit_spec cap SUP (G 7) false τ hI.outh (by
    rw [hI.pos, marks_len]; nlinarith)
  refine ⟨_, WXExec.mono (WXExec.seq e1 (WXExec.wm e2)) (by unfold supCost; omega), ?_, ?_, ?_⟩
  · simp [hI.out, recs_full]
  · simp [Function.update_of_ne (Ne.symm hSM), hI.mat]
  · refine hI.fr.trans ⟨fun x hx => ?_, fun r hr => ?_, by simp⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
      simp [Function.update_of_ne hx.1]
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [Function.update_of_ne hr.1]

end Rows

end NearCubicGates.Close.CheckedPCPP.SupW
