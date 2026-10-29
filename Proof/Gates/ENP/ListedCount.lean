import Proof.Gates.ENP.ListedRow
import Proof.Gates.CheckedPCPP.WMXReady

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxHeartbeats 1000000

namespace NearCubicGates.Close.ENP

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms

namespace UCount

/-- Streams and registers (literal numerals, so `simp` decides their distinctness). -/
local notation "sTB" => (0 : Fin 7)
local notation "sTR" => (1 : Fin 7)
local notation "sOQ" => (2 : Fin 7)
local notation "sOC" => (3 : Fin 7)
local notation "sOK" => (4 : Fin 7)
local notation "sOR" => (5 : Fin 7)
local notation "sOM" => (6 : Fin 7)
local notation "rRR" => (0 : Fin 16)
local notation "rI" => (1 : Fin 16)
local notation "rX" => (2 : Fin 16)
local notation "rY" => (3 : Fin 16)
local notation "rB" => (4 : Fin 16)
local notation "rJ" => (5 : Fin 16)
local notation "rV" => (6 : Fin 16)
local notation "rCB" => (7 : Fin 16)
local notation "rCR" => (8 : Fin 16)
local notation "rCQ" => (9 : Fin 16)
local notation "rCC" => (10 : Fin 16)
local notation "rCK" => (11 : Fin 16)
local notation "rCRo" => (12 : Fin 16)
local notation "rCM" => (13 : Fin 16)
local notation "rT" => (14 : Fin 16)
local notation "rZ" => (15 : Fin 16)

abbrev St := WState 6 16

/-- One listed pair `i`: read `vals[i]`, write row `i`, clause `i` and one unary mark. -/
def body : WMX 6 16 :=
  .seq (.wm (WM.fwdC sTB rCB)) <| .seq (.ifs sTB (WMX.inc rV) WMX.skip) <| .seq (.wm (WM.fwdC sTB rCB)) <|
  .seq (copyReg rI rX rT) <| .seq (rowLoop rRR rJ rX rY rB rCQ sOQ) <| .seq (clearReg rX) <|
  .seq (copyReg rI rZ rT) <| .seq (copyReg rI rZ rT) <| .seq (.ifr rV WMX.skip (WMX.inc rZ)) <|
  .seq (copyReg rZ rX rT) <| .seq (emitBits rX rY rB rCC sOC) <|
  .seq (copyReg rZ rX rT) <| .seq (emitBits rX rY rB rCC sOC) <|
  .seq (copyReg rZ rX rT) <| .seq (emitBits rX rY rB rCC sOC) <|
  .seq (clearReg rZ) <| .seq (emitO sOK rCK true) <| .seq (.ifr rV (WMX.dec rV) WMX.skip) (WMX.inc rI)

/-- The count stage (`sec:all-lengths`, stages 1 and 3). -/
def prog : WMX 6 16 :=
  .seq (.wm (WM.readU sTR rCR rRR)) <| .seq (.wm (WM.rewind sTR rCR)) <|
  .seq (copyReg rRR rX rT) <| .seq (emitBits rX rY rB rCRo sOR) <|
  .seq (.whs sTB body) <|
  .seq (copyReg rI rX rT) <| .seq (emitBits rX rY rB rCM sOM) <|
  .seq (.wm (WM.rewind sTB rCB)) <| .seq (.wm (WM.rewind sOQ rCQ)) <| .seq (.wm (WM.rewind sOC rCC)) <|
  .seq (.wm (WM.rewind sOK rCK)) <| .seq (.wm (WM.rewind sOR rCRo)) <| .seq (.wm (WM.rewind sOM rCM)) <|
  .seq (clearReg rRR) (clearReg rI)

/-- The state before pair `i` (`sec:all-lengths`: rows and clauses `< i` written). -/
def cfg (vals post : List Bool) (R i : ℕ) : St where
  sh := ![2 * i, 0, (qStream R i).length, (cStream vals i).length, i, (RepairOrdinary.frame R.bits).length, 0]
  st := ![RepairOrdinary.frame vals ++ post, List.replicate R true, qStream R i, cStream vals i,
    List.replicate i true, RepairOrdinary.frame R.bits, []]
  val := ![R, i, 0, 0, 0, 0, 0, 2 * i, 0, (qStream R i).length, (cStream vals i).length, i,
    (RepairOrdinary.frame R.bits).length, 0, 0, 0]
  cell := false

/-! Access lemmas for `cfg` (by `rfl`). -/
@[simp] theorem cfg_sh_TB (vals post : List Bool) (R i : ℕ) : (cfg vals post R i).sh sTB = 2 * i := rfl
@[simp] theorem cfg_st_TB (vals post : List Bool) (R i : ℕ) : (cfg vals post R i).st sTB = RepairOrdinary.frame vals ++ post := rfl
@[simp] theorem cfg_sh_TR (vals post : List Bool) (R i : ℕ) : (cfg vals post R i).sh sTR = 0 := rfl
@[simp] theorem cfg_st_TR (vals post : List Bool) (R i : ℕ) : (cfg vals post R i).st sTR = List.replicate R true := rfl
@[simp] theorem cfg_sh_OQ (vals post : List Bool) (R i : ℕ) : (cfg vals post R i).sh sOQ = (qStream R i).length := rfl
@[simp] theorem cfg_st_OQ (vals post : List Bool) (R i : ℕ) : (cfg vals post R i).st sOQ = qStream R i := rfl
@[simp] theorem cfg_sh_OC (vals post : List Bool) (R i : ℕ) : (cfg vals post R i).sh sOC = (cStream vals i).length := rfl
@[simp] theorem cfg_st_OC (vals post : List Bool) (R i : ℕ) : (cfg vals post R i).st sOC = cStream vals i := rfl
@[simp] theorem cfg_sh_OK (vals post : List Bool) (R i : ℕ) : (cfg vals post R i).sh sOK = i := rfl
@[simp] theorem cfg_st_OK (vals post : List Bool) (R i : ℕ) : (cfg vals post R i).st sOK = List.replicate i true := rfl
@[simp] theorem cfg_sh_OR (vals post : List Bool) (R i : ℕ) : (cfg vals post R i).sh sOR = (RepairOrdinary.frame R.bits).length := rfl
@[simp] theorem cfg_st_OR (vals post : List Bool) (R i : ℕ) : (cfg vals post R i).st sOR = RepairOrdinary.frame R.bits := rfl
@[simp] theorem cfg_sh_OM (vals post : List Bool) (R i : ℕ) : (cfg vals post R i).sh sOM = 0 := rfl
@[simp] theorem cfg_st_OM (vals post : List Bool) (R i : ℕ) : (cfg vals post R i).st sOM = [] := rfl
@[simp] theorem cfg_val_RR (vals post : List Bool) (R i : ℕ) : (cfg vals post R i).val rRR = R := rfl
@[simp] theorem cfg_val_I (vals post : List Bool) (R i : ℕ) : (cfg vals post R i).val rI = i := rfl
@[simp] theorem cfg_val_X (vals post : List Bool) (R i : ℕ) : (cfg vals post R i).val rX = 0 := rfl
@[simp] theorem cfg_val_Y (vals post : List Bool) (R i : ℕ) : (cfg vals post R i).val rY = 0 := rfl
@[simp] theorem cfg_val_B (vals post : List Bool) (R i : ℕ) : (cfg vals post R i).val rB = 0 := rfl
@[simp] theorem cfg_val_J (vals post : List Bool) (R i : ℕ) : (cfg vals post R i).val rJ = 0 := rfl
@[simp] theorem cfg_val_V (vals post : List Bool) (R i : ℕ) : (cfg vals post R i).val rV = 0 := rfl
@[simp] theorem cfg_val_CB (vals post : List Bool) (R i : ℕ) : (cfg vals post R i).val rCB = 2 * i := rfl
@[simp] theorem cfg_val_CR (vals post : List Bool) (R i : ℕ) : (cfg vals post R i).val rCR = 0 := rfl
@[simp] theorem cfg_val_CQ (vals post : List Bool) (R i : ℕ) : (cfg vals post R i).val rCQ = (qStream R i).length := rfl
@[simp] theorem cfg_val_CC (vals post : List Bool) (R i : ℕ) : (cfg vals post R i).val rCC = (cStream vals i).length := rfl
@[simp] theorem cfg_val_CK (vals post : List Bool) (R i : ℕ) : (cfg vals post R i).val rCK = i := rfl
@[simp] theorem cfg_val_CRo (vals post : List Bool) (R i : ℕ) : (cfg vals post R i).val rCRo = (RepairOrdinary.frame R.bits).length := rfl
@[simp] theorem cfg_val_CM (vals post : List Bool) (R i : ℕ) : (cfg vals post R i).val rCM = 0 := rfl
@[simp] theorem cfg_val_T (vals post : List Bool) (R i : ℕ) : (cfg vals post R i).val rT = 0 := rfl
@[simp] theorem cfg_val_Z (vals post : List Bool) (R i : ℕ) : (cfg vals post R i).val rZ = 0 := rfl
@[simp] theorem cfg_cell (vals post : List Bool) (R i : ℕ) : (cfg vals post R i).cell = false := rfl

/-- The start state: the table and `R` in unary, everything else empty. -/
def start (vals post : List Bool) (R : ℕ) : St where
  sh := fun _ => 0
  st := ![RepairOrdinary.frame vals ++ post, List.replicate R true, [], [], [], [], []]
  val := fun _ => 0
  cell := false

/-- The end state: every head and register at `0`. -/
def finish (vals post : List Bool) (R : ℕ) : St where
  sh := fun _ => 0
  st := ![RepairOrdinary.frame vals ++ post, List.replicate R true, qStream R vals.length,
    cStream vals vals.length, List.replicate vals.length true, RepairOrdinary.frame R.bits,
    RepairOrdinary.frame vals.length.bits]
  val := fun _ => 0
  cell := false

@[simp] theorem start_st_TB (vals post : List Bool) (R : ℕ) : (start vals post R).st sTB = RepairOrdinary.frame vals ++ post := rfl
@[simp] theorem finish_st_TB (vals post : List Bool) (R : ℕ) : (finish vals post R).st sTB = RepairOrdinary.frame vals ++ post := rfl
@[simp] theorem start_st_TR (vals post : List Bool) (R : ℕ) : (start vals post R).st sTR = List.replicate R true := rfl
@[simp] theorem finish_st_TR (vals post : List Bool) (R : ℕ) : (finish vals post R).st sTR = List.replicate R true := rfl
@[simp] theorem start_st_OQ (vals post : List Bool) (R : ℕ) : (start vals post R).st sOQ = [] := rfl
@[simp] theorem finish_st_OQ (vals post : List Bool) (R : ℕ) : (finish vals post R).st sOQ = qStream R vals.length := rfl
@[simp] theorem start_st_OC (vals post : List Bool) (R : ℕ) : (start vals post R).st sOC = [] := rfl
@[simp] theorem finish_st_OC (vals post : List Bool) (R : ℕ) : (finish vals post R).st sOC = cStream vals vals.length := rfl
@[simp] theorem start_st_OK (vals post : List Bool) (R : ℕ) : (start vals post R).st sOK = [] := rfl
@[simp] theorem finish_st_OK (vals post : List Bool) (R : ℕ) : (finish vals post R).st sOK = List.replicate vals.length true := rfl
@[simp] theorem start_st_OR (vals post : List Bool) (R : ℕ) : (start vals post R).st sOR = [] := rfl
@[simp] theorem finish_st_OR (vals post : List Bool) (R : ℕ) : (finish vals post R).st sOR = RepairOrdinary.frame R.bits := rfl
@[simp] theorem start_st_OM (vals post : List Bool) (R : ℕ) : (start vals post R).st sOM = [] := rfl
@[simp] theorem finish_st_OM (vals post : List Bool) (R : ℕ) : (finish vals post R).st sOM = RepairOrdinary.frame vals.length.bits := rfl
@[simp] theorem start_sh (vals post : List Bool) (R : ℕ) (j : Fin 7) : (start vals post R).sh j = 0 := rfl
@[simp] theorem start_val (vals post : List Bool) (R : ℕ) (j : Fin 16) : (start vals post R).val j = 0 := rfl
@[simp] theorem start_cell (vals post : List Bool) (R : ℕ) : (start vals post R).cell = false := rfl
@[simp] theorem finish_sh (vals post : List Bool) (R : ℕ) (j : Fin 7) : (finish vals post R).sh j = 0 := rfl
@[simp] theorem finish_val (vals post : List Bool) (R : ℕ) (j : Fin 16) : (finish vals post R).val j = 0 := rfl
@[simp] theorem finish_cell (vals post : List Bool) (R : ℕ) : (finish vals post R).cell = false := rfl

theorem read_frame_even (vals post : List Bool) (i : ℕ) (hi : i < vals.length) :
    readTapeBit (RepairOrdinary.frame vals ++ post) (2 * i) = true := by
  induction vals generalizing i with
  | nil => simp at hi
  | cons b l ih =>
    cases i with
    | zero => rfl
    | succ i =>
      have := ih i (by simpa using hi)
      simpa [readTapeBit, RepairOrdinary.frame, show 2 * (i + 1) = 2 * i + 2 by ring] using this

theorem read_frame_odd (vals post : List Bool) (i : ℕ) (hi : i < vals.length) :
    readTapeBit (RepairOrdinary.frame vals ++ post) (2 * i + 1) = vals.getD i false := by
  induction vals generalizing i with
  | nil => simp at hi
  | cons b l ih =>
    cases i with
    | zero => rfl
    | succ i =>
      have := ih i (by simpa using hi)
      simpa [readTapeBit, RepairOrdinary.frame, show 2 * (i + 1) + 1 = 2 * i + 1 + 2 by ring] using this

theorem read_frame_end (vals post : List Bool) :
    readTapeBit (RepairOrdinary.frame vals ++ post) (2 * vals.length) = false := by
  rw [frame_eq_pairs, List.append_assoc]
  have hl : (pairs vals).length = 2 * vals.length := by simp [pairs]; ring
  rw [← hl]
  simp [readTapeBit]

theorem unitCode_le (vals : List Bool) (i : ℕ) : unitCode vals i ≤ 2 * i + 1 := by
  unfold unitCode; split <;> omega

theorem frame_length (l : List Bool) : (RepairOrdinary.frame l).length = 2 * l.length + 1 := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [RepairOrdinary.frame, ih]; ring

theorem cRow_length_le (vals : List Bool) (i : ℕ) : (cRow vals i).length ≤ 3 * (4 * i + 3) := by
  have h := bits_length_le (unitCode vals i)
  have h2 := unitCode_le vals i
  simp only [cRow, List.length_append, frame_length]
  omega

theorem cStream_length_le (vals : List Bool) (i M : ℕ) (hi : i ≤ M) :
    (cStream vals i).length ≤ i * (12 * M + 9) := by
  induction i with
  | zero => simp [cStream]
  | succ i ih =>
    rw [cStream_succ, List.length_append]
    have := ih (by omega)
    have := cRow_length_le vals i
    nlinarith

theorem qStream_length (R i : ℕ) : (qStream R i).length = i * (7 * R) := by
  induction i with
  | zero => simp [qStream]
  | succ i ih => rw [qStream_succ, List.length_append, ih, qRow_length]; ring

theorem overlay_nil (l : List Bool) : StablePartition.Workspace.overlay l [] = l := by
  simp [StablePartition.Workspace.overlay]

theorem fin7_cases {P : Fin 7 → Prop} (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3) (h4 : P 4) (h5 : P 5)
    (h6 : P 6) : ∀ j, P j := by
  intro j; fin_cases j <;> assumption

theorem fin16_cases {P : Fin 16 → Prop} (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3) (h4 : P 4) (h5 : P 5)
    (h6 : P 6) (h7 : P 7) (h8 : P 8) (h9 : P 9) (h10 : P 10) (h11 : P 11) (h12 : P 12) (h13 : P 13) (h14 : P 14)
    (h15 : P 15) : ∀ j, P j := by
  intro j; fin_cases j <;> assumption

/-- The capacity used by the count stage. -/
def capOf (R M : ℕ) : ℕ := 100 * (R + 2) * (M + 2) ^ 2

/-- The cost of one pair. -/
def bodyCost (R M : ℕ) : ℕ := 1000 * (R + 1) * (M + 2) ^ 2

theorem capOf_ge (R M : ℕ) : 100 * (R + 2) * (M + 2) ≤ capOf R M ∧ 100 * (M + 2) * (M + 2) ≤ capOf R M := by
  unfold capOf
  have h1 : M + 2 ≤ (M + 2) ^ 2 := by nlinarith
  have h2 : 100 * (M + 2) * (M + 2) = 100 * (M + 2) ^ 2 := by ring
  constructor
  · exact Nat.mul_le_mul_left _ h1
  · rw [h2]
    have : 100 ≤ 100 * (R + 2) := by omega
    exact Nat.mul_le_mul_right _ this

theorem cap_row (R M i : ℕ) (hi : i < M) : i * (7 * R) + 7 * R + 8 < capOf R M := by
  have := (capOf_ge R M).1
  have : i * (7 * R) ≤ M * (7 * R) := Nat.mul_le_mul_right _ hi.le
  nlinarith

theorem cap_clause (R M i : ℕ) (hi : i < M) :
    i * (12 * M + 9) + 2 * (4 * i + 3) + 3 * (2 * i + 1) + 3 < capOf R M := by
  have := (capOf_ge R M).2
  have : i * (12 * M + 9) ≤ M * (12 * M + 9) := Nat.mul_le_mul_right _ hi.le
  nlinarith

theorem cap_lin (R M : ℕ) : 10 * R + 10 * M + 100 ≤ capOf R M := by
  have := (capOf_ge R M).1
  nlinarith

theorem cap_full (R M : ℕ) : M * (7 * R) + 100 ≤ capOf R M ∧ M * (12 * M + 9) + 100 ≤ capOf R M := by
  have h1 := (capOf_ge R M).1
  have h2 := (capOf_ge R M).2
  constructor <;> nlinarith

theorem body_cost_le (R M i c : ℕ) (hi : i < M) (hcle : c ≤ 2 * i + 1) :
    5 + 1 + (4 + 1 + (5 + 1 + ((18 * i + 3) + 1 + (rowCost R i + 1 + ((3 * (i / 2 ^ R) + 1) + 1 +
      ((18 * i + 3) + 1 + ((18 * i + 3) + 1 + (4 + 1 + ((18 * c + 3) + 1 + (emitBitsCost c + 1 +
      ((18 * c + 3) + 1 + (emitBitsCost c + 1 + ((18 * c + 3) + 1 + (emitBitsCost c + 1 +
      ((3 * c + 1) + 1 + (7 + 1 + (2 + 1 + 3))))))))))))))))) ≤ bodyCost R M := by
  have hd : i / 2 ^ R ≤ i := Nat.div_le_self _ _
  have hE : emitBitsCost c ≤ 60 * (M + 2) ^ 2 := by
    unfold emitBitsCost
    have : c + 1 ≤ 2 * (M + 2) := by omega
    have : 13 * c + 52 ≤ 30 * (M + 2) := by omega
    nlinarith
  have hRw : rowCost R i ≤ 200 * ((R + 1) * (M + 2)) := by
    unfold rowCost
    have : i ≤ M := hi.le
    nlinarith
  have hS1 : (M + 2) ^ 2 ≤ (R + 1) * (M + 2) ^ 2 := Nat.le_mul_of_pos_left _ (by omega)
  have hS2 : (R + 1) * (M + 2) ≤ (R + 1) * (M + 2) ^ 2 := Nat.mul_le_mul_left _ (by nlinarith)
  have hS3 : M + 2 ≤ (M + 2) ^ 2 := by nlinarith
  have hB : bodyCost R M = 1000 * ((R + 1) * (M + 2) ^ 2) := by unfold bodyCost; ring
  rw [hB]
  generalize emitBitsCost c = e at hE ⊢
  generalize rowCost R i = rc at hRw ⊢
  generalize (R + 1) * (M + 2) ^ 2 = S at hS1 hS2 ⊢
  generalize (M + 2) ^ 2 = P at hE hS1 hS3 ⊢
  generalize (R + 1) * (M + 2) = Q at hRw hS2 ⊢
  omega

set_option maxRecDepth 20000 in
theorem body_exec (vals post : List Bool) (R i : ℕ) (hi : i < vals.length) :
    WXExec (capOf R vals.length) body (cfg vals post R i) (cfg vals post R (i + 1)) (bodyCost R vals.length) := by
  have hrow := cap_row R vals.length i hi
  have hcl := cap_clause R vals.length i hi
  have hlin := cap_lin R vals.length
  have hcle : unitCode vals i ≤ 2 * i + 1 := unitCode_le vals i
  have hcS := cStream_length_le vals i vals.length hi.le
  have hqS := qStream_length R i
  have hbc := bits_length_le (unitCode vals i)
  have hfc := frame_length (unitCode vals i).bits
  generalize hcap : capOf R vals.length = cap at hrow hcl hlin ⊢
  generalize hc : unitCode vals i = c at hcle hbc hfc
  -- 1. skip the mark
  have h1 := WXExec.wm (wfwdC_spec (cap := cap) sTB rCB (cfg vals post R i) (by simp; omega))
  -- 2. read the listed value
  set σ1 := ((cfg vals post R i).seth sTB (2 * i + 1)).setv rCB (2 * i + 1) with hσ1
  have e1 : ((cfg vals post R i).seth sTB ((cfg vals post R i).sh sTB + 1)).setv rCB
      ((cfg vals post R i).val rCB + 1) = σ1 := by simp [σ1]
  rw [e1] at h1
  have hw1 : wbit σ1 sTB = vals.getD i false := by
    simp only [wbit, σ1, WState.setv_st, WState.seth_st, WState.setv_sh, WState.seth_sh,
      Function.update_self, cfg_st_TB]
    exact read_frame_odd vals post i hi
  have hV1 : σ1.val rV = 0 := by simp [σ1]
  set v := vals.getD i false with hv
  have h2 : WXExec cap (.ifs sTB (WMX.inc rV) WMX.skip) σ1 (σ1.setv rV (if v then 1 else 0)) 4 := by
    by_cases hvt : v = true
    · have := WXExec.ifsT (Q := WMX.skip) (by rw [hw1, hvt]) (WXExec.inc cap rV σ1 (by rw [hV1]; omega))
      refine WXExec.cast cap this ?_ le_rfl
      rw [hV1, hvt]; rfl
    · have hvf : v = false := by simpa using hvt
      have := WXExec.ifsF (P := WMX.inc rV) (by rw [hw1, hvf]) (WXExec.skip cap σ1)
      refine WXExec.mono (WXExec.cast cap this ?_ le_rfl) (by omega)
      rw [hvf]
      conv_lhs => rw [← wsetv_same σ1 rV]
      rw [hV1]; rfl
  set σ2 := σ1.setv rV (if v then 1 else 0) with hσ2
  -- 3. skip the value
  have h3 := WXExec.wm (wfwdC_spec (cap := cap) sTB rCB σ2 (by simp [σ2, σ1]; omega))
  set σ3 := (σ2.seth sTB (σ2.sh sTB + 1)).setv rCB (σ2.val rCB + 1) with hσ3
  -- 4. X := i
  have h4 := copyReg_exec (cap := cap) rI rX rT (by decide) (by decide) (by decide) i σ3
    (by simp [σ3, σ2, σ1]) (by simp [σ3, σ2, σ1]) (by simp [σ3, σ2, σ1]; omega) (by omega)
  set σ4 := σ3.setv rX (σ3.val rX + i) with hσ4
  -- 5. the row
  have h5 := rowLoop_exec (cap := cap) rRR rJ rX rY rB rCQ sOQ ⟨⟨by decide, by decide, by decide, by decide,
      by decide, by decide⟩, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
      by decide⟩
    R i σ4 (qStream R i) [] (by simp [σ4, σ3, σ2, σ1]) (by simp [σ4, σ3, σ2, σ1])
    (by simp [σ4, σ3, σ2, σ1]) (by simp [σ4, σ3, σ2, σ1]) (by simp [σ4, σ3, σ2, σ1])
    ⟨by simp [σ4, σ3, σ2, σ1, overlay_nil], by simp [σ4, σ3, σ2, σ1], by simp [σ4, σ3, σ2, σ1]⟩
    (by omega) (by omega) (by rw [hqS]; omega)
  set σ5 := outSt (σ4.setv rX (i / 2 ^ R)) sOQ rCQ (qStream R i ++ qRow R i) [] with hσ5
  -- 6. X := 0
  have h6 := clearReg_exec (cap := cap) rX (i / 2 ^ R) σ5 (by simp [σ5, outSt])
    ((Nat.div_le_self _ _).trans (by omega))
  set σ6 := σ5.setv rX 0 with hσ6
  -- 7, 8. Z := 2i
  have h7 := copyReg_exec (cap := cap) rI rZ rT (by decide) (by decide) (by decide) i σ6
    (by simp [σ6, σ5, σ4, σ3, σ2, σ1, outSt]) (by simp [σ6, σ5, σ4, σ3, σ2, σ1, outSt])
    (by simp [σ6, σ5, σ4, σ3, σ2, σ1, outSt]; omega) (by omega)
  set σ7 := σ6.setv rZ (σ6.val rZ + i) with hσ7
  have h8 := copyReg_exec (cap := cap) rI rZ rT (by decide) (by decide) (by decide) i σ7
    (by simp [σ7, σ6, σ5, σ4, σ3, σ2, σ1, outSt]) (by simp [σ7, σ6, σ5, σ4, σ3, σ2, σ1, outSt])
    (by simp [σ7, σ6, σ5, σ4, σ3, σ2, σ1, outSt]; omega) (by omega)
  set σ8 := σ7.setv rZ (σ7.val rZ + i) with hσ8
  have hZ8 : σ8.val rZ = 2 * i := by simp [σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, outSt]; ring
  have hV8 : σ8.val rV = if v then 1 else 0 := by simp [σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, outSt]
  -- 9. Z := c
  have h9 : WXExec cap (.ifr rV WMX.skip (WMX.inc rZ)) σ8 (σ8.setv rZ c) 4 := by
    by_cases hvt : v = true
    · have := WXExec.ifrT (Q := WMX.inc rZ) (by rw [hV8, hvt]; decide) (WXExec.skip cap σ8)
      refine WXExec.mono (WXExec.cast cap this ?_ le_rfl) (by omega)
      have hcv : c = 2 * i := by rw [← hc]; unfold unitCode; rw [← hv]; simp [hvt]
      rw [hcv, ← hZ8, wsetv_same]
    · have hvf : v = false := by simpa using hvt
      have := WXExec.ifrF (P := WMX.skip) (by rw [hV8, hvf]; decide)
        (WXExec.inc cap rZ σ8 (by rw [hZ8]; omega))
      refine WXExec.cast cap this ?_ (by omega)
      have hcv : c = 2 * i + 1 := by rw [← hc]; unfold unitCode; rw [← hv]; simp [hvf]
      rw [hcv, hZ8]
  set σ9 := σ8.setv rZ c with hσ9
  -- 10–15. three copies of the clause code
  have hreg : ERegs (nr := 16) rX rY rB rCC := ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
  have h10 := copyReg_exec (cap := cap) rZ rX rT (by decide) (by decide) (by decide) c σ9
    (by simp [σ9]) (by simp [σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, outSt])
    (by simp [σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, outSt]; omega) (by omega)
  set σ10 := σ9.setv rX (σ9.val rX + c) with hσ10
  have hO10 : OutOn σ10 sOC rCC (cStream vals i) [] :=
    ⟨by simp [σ10, σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, outSt, overlay_nil],
      by simp [σ10, σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, outSt],
      by simp [σ10, σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, outSt]⟩
  have h11 := emitBits_exec (cap := cap) rX rY rB rCC sOC hreg c σ10 (cStream vals i) []
    (by simp [σ10, σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, outSt])
    (by simp [σ10, σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, outSt])
    (by simp [σ10, σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, outSt]) hO10 (by omega)
  set fb := RepairOrdinary.frame c.bits with hfb
  set σ11 := outSt (σ10.setv rX 0) sOC rCC (cStream vals i ++ fb) [] with hσ11
  have h12 := copyReg_exec (cap := cap) rZ rX rT (by decide) (by decide) (by decide) c σ11
    (by simp [σ11, σ10, σ9, outSt]) (by simp [σ11, σ10, σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, outSt])
    (by simp [σ11, outSt]; omega) (by omega)
  set σ12 := σ11.setv rX (σ11.val rX + c) with hσ12
  have h13 := emitBits_exec (cap := cap) rX rY rB rCC sOC hreg c σ12 (cStream vals i ++ fb) []
    (by simp [σ12, σ11, outSt])
    (by simp [σ12, σ11, σ10, σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, outSt])
    (by simp [σ12, σ11, σ10, σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, outSt])
    (outOn_setv (outOn_outSt _ _ _ _ _) rX (by decide) _) (by simp [hfb]; omega)
  set σ13 := outSt (σ12.setv rX 0) sOC rCC (cStream vals i ++ fb ++ fb) [] with hσ13
  have h14 := copyReg_exec (cap := cap) rZ rX rT (by decide) (by decide) (by decide) c σ13
    (by simp [σ13, σ12, σ11, σ10, σ9, outSt])
    (by simp [σ13, σ12, σ11, σ10, σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, outSt])
    (by simp [σ13, outSt]; omega) (by omega)
  set σ14 := σ13.setv rX (σ13.val rX + c) with hσ14
  have h15 := emitBits_exec (cap := cap) rX rY rB rCC sOC hreg c σ14 (cStream vals i ++ fb ++ fb) []
    (by simp [σ14, σ13, outSt])
    (by simp [σ14, σ13, σ12, σ11, σ10, σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, outSt])
    (by simp [σ14, σ13, σ12, σ11, σ10, σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, outSt])
    (outOn_setv (outOn_outSt _ _ _ _ _) rX (by decide) _) (by simp [hfb]; omega)
  set σ15 := outSt (σ14.setv rX 0) sOC rCC (cStream vals i ++ fb ++ fb ++ fb) [] with hσ15
  -- 16. Z := 0
  have h16 := clearReg_exec (cap := cap) rZ c σ15
    (by simp [σ15, σ14, σ13, σ12, σ11, σ10, σ9, outSt]) (by omega)
  set σ16 := σ15.setv rZ 0 with hσ16
  -- 17. one unary mark
  have hO16 : OutOn σ16 sOK rCK (List.replicate i true) [] :=
    ⟨by simp [σ16, σ15, σ14, σ13, σ12, σ11, σ10, σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, outSt, overlay_nil],
      by simp [σ16, σ15, σ14, σ13, σ12, σ11, σ10, σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, outSt],
      by simp [σ16, σ15, σ14, σ13, σ12, σ11, σ10, σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, outSt]⟩
  have h17 := emitO_spec cap σ16 (List.replicate i true) [] true hO16 (by simp; omega)
  set σ17 := outSt σ16 sOK rCK (List.replicate i true ++ [true]) [] with hσ17
  -- 18. V := 0
  have hV17 : σ17.val rV = if v then 1 else 0 := by
    simp [σ17, σ16, σ15, σ14, σ13, σ12, σ11, σ10, σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, outSt]
  have h18 : WXExec cap (.ifr rV (WMX.dec rV) WMX.skip) σ17 (σ17.setv rV 0) 2 := by
    by_cases hvt : v = true
    · have := WXExec.ifrT (Q := WMX.skip) (by rw [hV17, hvt]; decide)
        (WXExec.dec cap rV σ17 (by rw [hV17, hvt]; simp; omega))
      refine WXExec.cast cap this ?_ le_rfl
      rw [hV17, hvt]; rfl
    · have hvf : v = false := by simpa using hvt
      have := WXExec.ifrF (P := WMX.dec rV) (by rw [hV17, hvf]; decide) (WXExec.skip cap σ17)
      refine WXExec.mono (WXExec.cast cap this ?_ le_rfl) (by omega)
      conv_lhs => rw [← wsetv_same σ17 rV]
      rw [hV17, hvf]; rfl
  set σ18 := σ17.setv rV 0 with hσ18
  -- 19. I := i + 1
  have hI18 : σ18.val rI = i := by
    simp [σ18, σ17, σ16, σ15, σ14, σ13, σ12, σ11, σ10, σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, outSt]
  have h19 := WXExec.inc cap rI σ18 (by rw [hI18]; omega)
  have hfin : σ18.setv rI (σ18.val rI + 1) = cfg vals post R (i + 1) := by
    have hcr : cRow vals i = fb ++ (fb ++ fb) := by simp [cRow, hfb, hc]
    have hrep : List.replicate i true ++ [true] = List.replicate (i + 1) true := by
      rw [List.replicate_succ']
    apply WState.eq
    · funext j
      revert j
      apply fin7_cases <;>
        simp [σ18, σ17, σ16, σ15, σ14, σ13, σ12, σ11, σ10, σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, outSt,
          qStream_succ, cStream_succ, hcr] <;> ring
    · funext j
      revert j
      apply fin7_cases <;>
        simp [σ18, σ17, σ16, σ15, σ14, σ13, σ12, σ11, σ10, σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, outSt, overlay_nil,
          qStream_succ, cStream_succ, hcr, hrep]
    · funext j
      revert j
      apply fin16_cases <;>
        simp [σ18, σ17, σ16, σ15, σ14, σ13, σ12, σ11, σ10, σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, outSt,
          qStream_succ, cStream_succ, hcr] <;> ring
    · rfl
  rw [hfin] at h19
  have hall := WXExec.seq h1 (WXExec.seq h2 (WXExec.seq h3 (WXExec.seq h4 (WXExec.seq h5 (WXExec.seq h6
    (WXExec.seq h7 (WXExec.seq h8 (WXExec.seq h9 (WXExec.seq h10 (WXExec.seq h11 (WXExec.seq h12
    (WXExec.seq h13 (WXExec.seq h14 (WXExec.seq h15 (WXExec.seq h16 (WXExec.seq h17 (WXExec.seq h18
    h19)))))))))))))))))
  exact WXExec.mono hall (body_cost_le R vals.length i c hi hcle)

/-- The pair loop: from `cfg 0` to `cfg M`. -/
theorem loop_exec (vals post : List Bool) (R : ℕ) :
    WXExec (capOf R vals.length) (.whs sTB body) (cfg vals post R 0) (cfg vals post R vals.length)
      (vals.length * (bodyCost R vals.length + 2) + 1) := by
  have h := Runs.whs (cap := capOf R vals.length) (i := sTB) (P := body)
    (fun k σ => k ≤ vals.length ∧ σ = cfg vals post R (vals.length - k)) (bodyCost R vals.length)
    (fun σ => σ = cfg vals post R vals.length)
    (by
      rintro σ ⟨_, rfl⟩
      refine ⟨?_, by simp⟩
      simp only [wbit, Nat.sub_zero, cfg_st_TB, cfg_sh_TB]
      exact read_frame_end vals post)
    (by
      rintro k σ ⟨hk, rfl⟩
      have hi : vals.length - (k + 1) < vals.length := by omega
      refine ⟨?_, ?_⟩
      · simp only [wbit, cfg_st_TB, cfg_sh_TB]
        exact read_frame_even vals post _ hi
      · refine ⟨_, body_exec vals post R _ hi, by omega, ?_⟩
        congr 1
        omega)
    vals.length (cfg vals post R 0) ⟨le_rfl, by simp⟩
  obtain ⟨τ, e, rfl⟩ := h
  exact e

/-- The whole count stage's cost. -/
def progCost (R M : ℕ) : ℕ := 100000 * ((R + 1) ^ 2 * (M + 2) ^ 3)

theorem prog_cost_le (R M lq lc lfR lfM : ℕ) (hq : lq = M * (7 * R)) (hc : lc ≤ M * (12 * M + 9))
    (hfR : lfR ≤ 2 * R + 1) (hfM : lfM ≤ 2 * M + 1) :
    11 * R + 7 + 1 + (5 * (R + 1) + 1 + 1 + (18 * R + 3 + 1 + (emitBitsCost R + 1 +
      (M * (bodyCost R M + 2) + 1 + 1 + (18 * M + 3 + 1 + (emitBitsCost M + 1 + (5 * (2 * M) + 1 + 1 +
      (5 * lq + 1 + 1 + (5 * lc + 1 + 1 + (5 * M + 1 + 1 + (5 * lfR + 1 + 1 + (5 * lfM + 1 + 1 +
      (3 * R + 1 + 1 + (3 * M + 1)))))))))))))) ≤ progCost R M := by
  have hER : emitBitsCost R ≤ 70 * (R + 1) * (R + 1) := by unfold emitBitsCost; nlinarith
  have hEM : emitBitsCost M ≤ 70 * (M + 2) * (M + 2) := by unfold emitBitsCost; nlinarith
  have hB : M * (bodyCost R M + 2) ≤ 1002 * (R + 1) * (M + 2) ^ 3 := by
    unfold bodyCost
    have : M ≤ M + 2 := by omega
    nlinarith
  unfold progCost
  have hR1 : R + 1 ≤ (R + 1) ^ 2 := by nlinarith
  have hM3 : (M + 2) * (M + 2) ≤ (M + 2) ^ 3 := by nlinarith
  have hM1 : 1 ≤ (M + 2) ^ 3 := Nat.one_le_pow _ _ (by omega)
  have hA1 : 70 * (R + 1) * (R + 1) ≤ 70 * ((R + 1) ^ 2 * (M + 2) ^ 3) := by nlinarith
  have hA2 : 70 * (M + 2) * (M + 2) ≤ 70 * ((R + 1) ^ 2 * (M + 2) ^ 3) := by nlinarith
  have hA3 : 1002 * (R + 1) * (M + 2) ^ 3 ≤ 1002 * ((R + 1) ^ 2 * (M + 2) ^ 3) := by nlinarith
  have hA4 : M * (7 * R) ≤ 7 * ((R + 1) ^ 2 * (M + 2) ^ 3) := by nlinarith
  have hA5 : M * (12 * M + 9) ≤ 21 * ((R + 1) ^ 2 * (M + 2) ^ 3) := by nlinarith
  have hA6 : R + M + 1 ≤ (R + 1) ^ 2 * (M + 2) ^ 3 := by nlinarith
  generalize (R + 1) ^ 2 * (M + 2) ^ 3 = A at hA1 hA2 hA3 hA4 hA5 hA6 ⊢
  generalize emitBitsCost R = e1 at hER ⊢
  generalize emitBitsCost M = e2 at hEM ⊢
  generalize M * (bodyCost R M + 2) = b at hB ⊢
  generalize 70 * (R + 1) * (R + 1) = x1 at hER hA1
  generalize 70 * (M + 2) * (M + 2) = x2 at hEM hA2
  generalize 1002 * (R + 1) * (M + 2) ^ 3 = x3 at hB hA3
  generalize M * (7 * R) = x4 at hq hA4
  generalize M * (12 * M + 9) = x5 at hc hA5
  omega

set_option maxRecDepth 20000 in
/-- **The count stage** (`sec:all-lengths`, stages 1 and 3): from the listed table and `R`, it writes the five source
fields of
`unitPCP` and returns every head and register to `0`. -/
theorem prog_exec (vals post : List Bool) (R : ℕ) :
    WXExec (capOf R vals.length) prog (start vals post R) (finish vals post R) (progCost R vals.length) := by
  have hlin := cap_lin R vals.length
  have hbig := (capOf_ge R vals.length).1
  have hbR := bits_length_le R
  have hbM := bits_length_le vals.length
  have hfR := frame_length R.bits
  have hfM := frame_length vals.length.bits
  have hqS := qStream_length R vals.length
  have hcS := cStream_length_le vals vals.length vals.length le_rfl
  have hfull := cap_full R vals.length
  generalize hcap : capOf R vals.length = cap at hlin hbig hfull ⊢
  set σ0 := start vals post R with hσ0
  -- 1, 2. RR := R
  have h1 := WXExec.wm (wreadU_spec (cap := cap) sTR rCR rRR (by decide) R σ0
    (by intro k hk; simp [σ0, readTapeBit, hk])
    (by simp [σ0, readTapeBit]) (by simp [σ0]; omega) (by simp [σ0]; omega))
  set σ1 := ((σ0.seth sTR (σ0.sh sTR + R + 1)).setv rCR (σ0.val rCR + R + 1)).setv rRR (σ0.val rRR + R)
    with hσ1
  have h2 := WXExec.wm (wrewind_spec (cap := cap) sTR rCR (R + 1) σ1 (by simp [σ1, σ0]) (by simp [σ1, σ0]; omega))
  set σ2 := (σ1.setv rCR 0).seth sTR (σ1.sh sTR - (R + 1)) with hσ2
  -- 3, 4. OR := frame R.bits
  have h3 := copyReg_exec (cap := cap) rRR rX rT (by decide) (by decide) (by decide) R σ2
    (by simp [σ2, σ1, σ0]) (by simp [σ2, σ1, σ0]) (by simp [σ2, σ1, σ0]; omega) (by omega)
  set σ3 := σ2.setv rX (σ2.val rX + R) with hσ3
  have h4 := emitBits_exec (cap := cap) rX rY rB rCRo sOR
    ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩ R σ3 [] []
    (by simp [σ3, σ2, σ1, σ0]) (by simp [σ3, σ2, σ1, σ0]) (by simp [σ3, σ2, σ1, σ0])
    ⟨by simp [σ3, σ2, σ1, σ0, overlay_nil], by simp [σ3, σ2, σ1, σ0], by simp [σ3, σ2, σ1, σ0]⟩
    (by simp; omega)
  have e4 : outSt (σ3.setv rX 0) sOR rCRo ([] ++ RepairOrdinary.frame R.bits) [] = cfg vals post R 0 := by
    apply WState.eq
    · funext j; revert j
      apply fin7_cases <;> simp [σ3, σ2, σ1, σ0, outSt, qStream, cStream]
    · funext j; revert j
      apply fin7_cases <;> simp [σ3, σ2, σ1, σ0, outSt, overlay_nil, qStream, cStream]
    · funext j; revert j
      apply fin16_cases <;> simp [σ3, σ2, σ1, σ0, outSt, qStream, cStream]
    · rfl
  rw [e4] at h4
  -- 5. the pairs
  have h5 := loop_exec vals post R
  rw [hcap] at h5
  -- 6, 7. OM := frame M.bits
  set σ5 := cfg vals post R vals.length with hσ5
  have h6 := copyReg_exec (cap := cap) rI rX rT (by decide) (by decide) (by decide) vals.length σ5
    (by simp [σ5]) (by simp [σ5]) (by simp [σ5]; omega) (by omega)
  set σ6 := σ5.setv rX (σ5.val rX + vals.length) with hσ6
  have h7 := emitBits_exec (cap := cap) rX rY rB rCM sOM
    ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩ vals.length σ6 [] []
    (by simp [σ6, σ5]) (by simp [σ6, σ5]) (by simp [σ6, σ5])
    ⟨by simp [σ6, σ5, overlay_nil], by simp [σ6, σ5], by simp [σ6, σ5]⟩ (by simp; omega)
  set σ7 := outSt (σ6.setv rX 0) sOM rCM ([] ++ RepairOrdinary.frame vals.length.bits) [] with hσ7
  -- 8–13. rewind every stream
  have h8 := WXExec.wm (wrewind_spec (cap := cap) sTB rCB (2 * vals.length) σ7 (by simp [σ7, σ6, σ5, outSt])
    (by simp [σ7, σ6, σ5, outSt]; omega))
  set σ8 := (σ7.setv rCB 0).seth sTB (σ7.sh sTB - 2 * vals.length) with hσ8
  have h9 := WXExec.wm (wrewind_spec (cap := cap) sOQ rCQ (qStream R vals.length).length σ8
    (by simp [σ8, σ7, σ6, σ5, outSt]) (by simp [σ8, σ7, σ6, σ5, outSt]; omega))
  set σ9 := (σ8.setv rCQ 0).seth sOQ (σ8.sh sOQ - (qStream R vals.length).length) with hσ9
  have h10 := WXExec.wm (wrewind_spec (cap := cap) sOC rCC (cStream vals vals.length).length σ9
    (by simp [σ9, σ8, σ7, σ6, σ5, outSt]) (by simp [σ9, σ8, σ7, σ6, σ5, outSt]; omega))
  set σ10 := (σ9.setv rCC 0).seth sOC (σ9.sh sOC - (cStream vals vals.length).length) with hσ10
  have h11 := WXExec.wm (wrewind_spec (cap := cap) sOK rCK vals.length σ10
    (by simp [σ10, σ9, σ8, σ7, σ6, σ5, outSt]) (by simp [σ10, σ9, σ8, σ7, σ6, σ5, outSt]; omega))
  set σ11 := (σ10.setv rCK 0).seth sOK (σ10.sh sOK - vals.length) with hσ11
  have h12 := WXExec.wm (wrewind_spec (cap := cap) sOR rCRo (RepairOrdinary.frame R.bits).length σ11
    (by simp [σ11, σ10, σ9, σ8, σ7, σ6, σ5, outSt]) (by simp [σ11, σ10, σ9, σ8, σ7, σ6, σ5, outSt]; omega))
  set σ12 := (σ11.setv rCRo 0).seth sOR (σ11.sh sOR - (RepairOrdinary.frame R.bits).length) with hσ12
  have h13 := WXExec.wm (wrewind_spec (cap := cap) sOM rCM (RepairOrdinary.frame vals.length.bits).length σ12
    (by simp [σ12, σ11, σ10, σ9, σ8, σ7, σ6, σ5, outSt])
    (by simp [σ12, σ11, σ10, σ9, σ8, σ7, σ6, σ5, outSt]; omega))
  set σ13 := (σ12.setv rCM 0).seth sOM (σ12.sh sOM - (RepairOrdinary.frame vals.length.bits).length) with hσ13
  -- 14, 15. clear the two counters
  have h14 := clearReg_exec (cap := cap) rRR R σ13
    (by simp [σ13, σ12, σ11, σ10, σ9, σ8, σ7, σ6, σ5, outSt]) (by omega)
  set σ14 := σ13.setv rRR 0 with hσ14
  have h15 := clearReg_exec (cap := cap) rI vals.length σ14
    (by simp [σ14, σ13, σ12, σ11, σ10, σ9, σ8, σ7, σ6, σ5, outSt]) (by omega)
  have hfin : σ14.setv rI 0 = finish vals post R := by
    apply WState.eq
    · funext j; revert j
      apply fin7_cases <;> simp [σ14, σ13, σ12, σ11, σ10, σ9, σ8, σ7, σ6, σ5, outSt]
    · funext j; revert j
      apply fin7_cases <;> simp [σ14, σ13, σ12, σ11, σ10, σ9, σ8, σ7, σ6, σ5, outSt, overlay_nil]
    · funext j; revert j
      apply fin16_cases <;> simp [σ14, σ13, σ12, σ11, σ10, σ9, σ8, σ7, σ6, σ5, outSt]
    · rfl
  rw [hfin] at h15
  have hall := WXExec.seq h1 (WXExec.seq h2 (WXExec.seq h3 (WXExec.seq h4 (WXExec.seq h5 (WXExec.seq h6
    (WXExec.seq h7 (WXExec.seq h8 (WXExec.seq h9 (WXExec.seq h10 (WXExec.seq h11 (WXExec.seq h12
    (WXExec.seq h13 (WXExec.seq h14 h15)))))))))))))
  exact WXExec.mono hall (prog_cost_le R vals.length _ _ _ _ hqS hcS (by omega) (by omega))

/-- **The count stage as a ready run** from empty work tapes (`sec:all-lengths`, stages 1 and 3). -/
theorem prog_ready (vals post : List Bool) (R : ℕ) :
    ∃ out, ClockJoin.ReadyRun prog.compile (progCost R vals.length)
      (CheckedPCPP.coldBank (start vals post R)) out ∧
      ∀ i, out (sTape (nr := 16) i) = (finish vals post R).st i :=
  CheckedPCPP.WXExec.ready (prog_exec vals post R) (fun _ => rfl) (fun _ => rfl) rfl (fun _ => rfl) (fun _ => rfl)

end UCount

end NearCubicGates.Close.ENP
