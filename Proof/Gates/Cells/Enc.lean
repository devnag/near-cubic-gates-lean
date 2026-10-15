import Proof.Gates.Cells.Lang
import Proof.Gates.WordPrograms.BinW
import Proof.Gates.WordPrograms.BinWDiv
import Proof.Gates.WordPrograms.RecLoop
import Proof.Gates.CheckedPCPP.EncCols

set_option autoImplicit false

namespace NearCubicGates.Close.Cells

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length binary_value)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (NumOn)
open NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay)

/-! ## Layout -/

/-- Streams minus one. -/
abbrev NS (M t V : ℕ) : ℕ := 7 + 2 * M + t + V
/-- Registers. -/
abbrev NR (M : ℕ) : ℕ := 11 + M

section Layout
variable {V M t : ℕ}

def sIN : Fin (NS M t V + 1) := ⟨0, by unfold NS; omega⟩
def sOUT : Fin (NS M t V + 1) := ⟨1, by unfold NS; omega⟩
def sZ : Fin (NS M t V + 1) := ⟨2, by unfold NS; omega⟩
def sKI : Fin (NS M t V + 1) := ⟨3, by unfold NS; omega⟩
def sKO : Fin (NS M t V + 1) := ⟨4, by unfold NS; omega⟩
def sLG : Fin (NS M t V + 1) := ⟨5, by unfold NS; omega⟩
def sRU : Fin (NS M t V + 1) := ⟨6, by unfold NS; omega⟩
def sTP : Fin (NS M t V + 1) := ⟨7, by unfold NS; omega⟩
def sM (m : Fin M) : Fin (NS M t V + 1) := ⟨8 + m.val, by unfold NS; omega⟩
def sS (m : Fin M) : Fin (NS M t V + 1) := ⟨8 + M + m.val, by unfold NS; omega⟩
def sT (j : Fin t) : Fin (NS M t V + 1) := ⟨8 + 2 * M + j.val, by unfold NS; omega⟩
def vs (x : Fin V) : Fin (NS M t V + 1) := ⟨8 + 2 * M + t + x.val, by unfold NS; omega⟩

def rF : Fin (NR M) := ⟨0, by unfold NR; omega⟩
def rR : Fin (NR M) := ⟨1, by unfold NR; omega⟩
def rG : Fin (NR M) := ⟨2, by unfold NR; omega⟩
def rK : Fin (NR M) := ⟨3, by unfold NR; omega⟩
def rT : Fin (NR M) := ⟨4, by unfold NR; omega⟩
def rIP : Fin (NR M) := ⟨5, by unfold NR; omega⟩
def rOP : Fin (NR M) := ⟨6, by unfold NR; omega⟩
def rKI : Fin (NR M) := ⟨7, by unfold NR; omega⟩
def rKO : Fin (NR M) := ⟨8, by unfold NR; omega⟩
def rC1 : Fin (NR M) := ⟨9, by unfold NR; omega⟩
def rC2 : Fin (NR M) := ⟨10, by unfold NR; omega⟩
def rM (m : Fin M) : Fin (NR M) := ⟨11 + m.val, by unfold NR; omega⟩

@[simp] theorem sIN_val : (sIN : Fin (NS M t V + 1)).val = 0 := rfl
@[simp] theorem sOUT_val : (sOUT : Fin (NS M t V + 1)).val = 1 := rfl
@[simp] theorem sZ_val : (sZ : Fin (NS M t V + 1)).val = 2 := rfl
@[simp] theorem sKI_val : (sKI : Fin (NS M t V + 1)).val = 3 := rfl
@[simp] theorem sKO_val : (sKO : Fin (NS M t V + 1)).val = 4 := rfl
@[simp] theorem sLG_val : (sLG : Fin (NS M t V + 1)).val = 5 := rfl
@[simp] theorem sRU_val : (sRU : Fin (NS M t V + 1)).val = 6 := rfl
@[simp] theorem sTP_val : (sTP : Fin (NS M t V + 1)).val = 7 := rfl
@[simp] theorem sM_val (m : Fin M) : (sM m : Fin (NS M t V + 1)).val = 8 + m.val := rfl
@[simp] theorem sS_val (m : Fin M) : (sS m : Fin (NS M t V + 1)).val = 8 + M + m.val := rfl
@[simp] theorem sT_val (j : Fin t) : (sT j : Fin (NS M t V + 1)).val = 8 + 2 * M + j.val := rfl
@[simp] theorem vs_val (x : Fin V) : (vs x : Fin (NS M t V + 1)).val = 8 + 2 * M + t + x.val := rfl
@[simp] theorem rF_val : (rF : Fin (NR M)).val = 0 := rfl
@[simp] theorem rR_val : (rR : Fin (NR M)).val = 1 := rfl
@[simp] theorem rG_val : (rG : Fin (NR M)).val = 2 := rfl
@[simp] theorem rK_val : (rK : Fin (NR M)).val = 3 := rfl
@[simp] theorem rT_val : (rT : Fin (NR M)).val = 4 := rfl
@[simp] theorem rIP_val : (rIP : Fin (NR M)).val = 5 := rfl
@[simp] theorem rOP_val : (rOP : Fin (NR M)).val = 6 := rfl
@[simp] theorem rKI_val : (rKI : Fin (NR M)).val = 7 := rfl
@[simp] theorem rKO_val : (rKO : Fin (NR M)).val = 8 := rfl
@[simp] theorem rC1_val : (rC1 : Fin (NR M)).val = 9 := rfl
@[simp] theorem rC2_val : (rC2 : Fin (NR M)).val = 10 := rfl
@[simp] theorem rM_val (m : Fin M) : (rM m : Fin (NR M)).val = 11 + m.val := rfl

theorem vs_inj {x y : Fin V} (h : x ≠ y) : (vs x : Fin (NS M t V + 1)) ≠ vs y := by
  intro e; apply h; apply Fin.ext; have := congrArg Fin.val e; simp at this; omega
theorem vs_ne_Z (x : Fin V) : (vs x : Fin (NS M t V + 1)) ≠ sZ := by
  intro e; have := congrArg Fin.val e; simp at this; omega
theorem sM_inj {m m' : Fin M} (h : m ≠ m') : (sM m : Fin (NS M t V + 1)) ≠ sM m' := by
  intro e; apply h; apply Fin.ext; have := congrArg Fin.val e; simp at this; omega
theorem sS_inj {m m' : Fin M} (h : m ≠ m') : (sS m : Fin (NS M t V + 1)) ≠ sS m' := by
  intro e; apply h; apply Fin.ext; have := congrArg Fin.val e; simp at this; omega
theorem rM_inj {m m' : Fin M} (h : m ≠ m') : (rM m : Fin (NR M)) ≠ rM m' := by
  intro e; apply h; apply Fin.ext; have := congrArg Fin.val e; simp at this; omega

end Layout

/-- Distinct layout indices (by their values). -/
macro "lay_ne" : tactic =>
  `(tactic| (intro e; have := congrArg Fin.val e; simp at this; try omega))

/-! ## Record stores -/

open NearCubicGates.Close.WordPrograms (recStream)

/-- A store's stream: its records `frame (binary W v)` back to back. -/
def enc (W : ℕ) (l : List ℕ) : List Bool := l.flatMap fun v => frame (binary W v)

theorem frame_binary_length (W v : ℕ) : (frame (binary W v)).length = 2 * W + 1 := by
  rw [frame_eq_frameP]; simp [frameP, binary_length]; ring

theorem enc_length (W : ℕ) (l : List ℕ) : (enc W l).length = (2 * W + 1) * l.length := by
  induction l with
  | nil => simp [enc]
  | cons v l ih =>
    simp only [enc, List.flatMap_cons, List.length_append, frame_binary_length] at ih ⊢
    rw [ih]; simp; ring

theorem enc_append (W : ℕ) (l l' : List ℕ) : enc W (l ++ l') = enc W l ++ enc W l' := by
  simp [enc, List.flatMap_append]

/-- The store split at record `i < |l|`, as `copyRec` reads it. -/
theorem enc_split (W : ℕ) (l : List ℕ) (i : ℕ) (hi : i < l.length) :
    enc W l = enc W (l.take i) ++ frameP (binary W (l.getD i 0)) ++ false :: enc W (l.drop (i + 1)) := by
  conv_lhs => rw [← List.take_append_drop i l]
  rw [enc_append, List.drop_eq_getElem_cons hi, List.getD_eq_getElem _ _ hi]
  simp only [enc, List.flatMap_cons, frame_eq_frameP, List.append_assoc]
  simp

def encR (W : ℕ) (l : List ℕ) : List Bool := enc W l ++ [false]

theorem encR_eq (W : ℕ) (l : List ℕ) : encR W l = WordPrograms.recStream (l.map (binary W)) := by
  simp [encR, enc, WordPrograms.recStream, List.flatMap_map]

theorem encR_length (W : ℕ) (l : List ℕ) : (encR W l).length = (2 * W + 1) * l.length + 1 := by
  simp [encR, enc_length]

/-- The store split at record `i < |l|`, as `copyRec` reads it. -/
theorem encR_split (W : ℕ) (l : List ℕ) (i : ℕ) (hi : i < l.length) :
    encR W l = enc W (l.take i) ++ frameP (binary W (l.getD i 0)) ++ false :: encR W (l.drop (i + 1)) := by
  rw [encR, enc_split W l i hi]; simp [encR]

theorem overlay_prefix (pre rest : List Bool) : overlay pre (pre ++ rest) = pre ++ rest := by
  simp [overlay]

/-- Writing record `v` at `i ≤ |l|` (`appendRec` over the old stream). -/
theorem enc_putAt (W : ℕ) (l : List ℕ) (i v : ℕ) (hi : i ≤ l.length) :
    overlay (enc W (l.take i) ++ frame (binary W v)) (enc W l) = enc W (putAt l i v) := by
  unfold putAt
  split_ifs with h
  · rw [List.set_eq_take_append_cons_drop, if_pos h]
    have e1 : enc W l = (enc W (l.take i) ++ frame (binary W (l.getD i 0))) ++ enc W (l.drop (i + 1)) := by
      rw [enc_split W l i h, frame_eq_frameP]; simp
    rw [e1, overlay]
    have hl : (enc W (l.take i) ++ frame (binary W v)).length =
        (enc W (l.take i) ++ frame (binary W (l.getD i 0))).length := by
      simp
    rw [hl, List.drop_left]
    simp [enc, List.flatMap_append]
  · have hi' : i = l.length := by omega
    subst hi'
    rw [List.take_of_length_le le_rfl, enc_append, overlay, List.drop_eq_nil_of_le (by simp)]
    simp [enc]

end NearCubicGates.Close.Cells
