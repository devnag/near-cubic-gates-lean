import Proof.Wire_3_5.SeedFixRowsRef
import Proof.Wire_3_5.BlockJoin

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.SeedFix
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.SignedSortKey NearCubicWires.WireExponent3_5.Block NearCubicWires.WireExponent3_5.Cost
open NearCubicWires.WireExponent3_5.GF2
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay)

/-! ## The inner loop (tapes 0 the unary column counter, 1 the current column, 2 the table, 3 the modulus, 4 the flag
cell, 5 the capacity tape) -/

def t6Copy : Fin 3 → Fin 6 := ![1, 2, 5]

theorem install_t6Copy (A : Fin 6 → List Bool) (v : Fin 3 → List Bool) :
    RecoveryRootRound.install t6Copy A v = ![A 0, v 0, v 1, A 3, A 4, v 2] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 1
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 2
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

theorem dockH_t6Copy (H : Fin 6 → ℕ) (v : Fin 3 → ℕ) :
    dockH t6Copy H v = ![H 0, v 0, v 1, H 3, H 4, v 2] := by
  funext i; fin_cases i
  all_goals first
    | exact dockH_slot _ (by decide) _ _ 0
    | exact dockH_slot _ (by decide) _ _ 1
    | exact dockH_slot _ (by decide) _ _ 2
    | exact dockH_other _ _ _ _ (by decide)

def t6Lfsr : Fin 4 → Fin 6 := ![1, 3, 4, 5]

theorem install_t6Lfsr (A : Fin 6 → List Bool) (v : Fin 4 → List Bool) :
    RecoveryRootRound.install t6Lfsr A v = ![A 0, v 0, A 2, v 1, v 2, v 3] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 1
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 2
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 3
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

theorem dockH_t6Lfsr (H : Fin 6 → ℕ) (v : Fin 4 → ℕ) :
    dockH t6Lfsr H v = ![H 0, v 0, H 2, v 1, v 2, v 3] := by
  funext i; fin_cases i
  all_goals first
    | exact dockH_slot _ (by decide) _ _ 0
    | exact dockH_slot _ (by decide) _ _ 1
    | exact dockH_slot _ (by decide) _ _ 2
    | exact dockH_slot _ (by decide) _ _ 3
    | exact dockH_other _ _ _ _ (by decide)

def t6Nudge : Fin 1 → Fin 6 := ![0]

theorem install_t6Nudge (A : Fin 6 → List Bool) (v : Fin 1 → List Bool) :
    RecoveryRootRound.install t6Nudge A v = ![v 0, A 1, A 2, A 3, A 4, A 5] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

theorem dockH_t6Nudge (H : Fin 6 → ℕ) (v : Fin 1 → ℕ) :
    dockH t6Nudge H v = ![v 0, H 1, H 2, H 3, H 4, H 5] := by
  funext i; fin_cases i
  all_goals first
    | exact dockH_slot _ (by decide) _ _ 0
    | exact dockH_other _ _ _ _ (by decide)
def selCopy : Fin 2 → Bool := ![true, false]

noncomputable def tInnerBody :=
  Composition.machine (Composition.machine (RecoveryFocus.machine t6Copy (MaskedReset.machine CopyO.machine selCopy))
    (RecoveryFocus.machine t6Lfsr lfsrM)) (RecoveryFocus.machine t6Nudge nudgeM)

/-- **The inner loop**: one pass per cell of the unary counter. -/
noncomputable def tInnerM := StreamController.machine tInnerBody 0

/-- The framed words the first `b` passes append from `acc`: `acc, x·acc, …`. -/
def colWords (p ℓ acc b : ℕ) : List Bool :=
  ((List.range b).map fun b' => binary ℓ ((lfsr p ℓ)^[b'] acc)).flatMap frame

theorem colWords_succ (p ℓ acc b : ℕ) :
    colWords p ℓ acc (b + 1) = colWords p ℓ acc b ++ frame (binary ℓ ((lfsr p ℓ)^[b] acc)) := by
  unfold colWords
  rw [List.range_succ, List.map_append, List.flatMap_append]
  simp

theorem colWords_length (p ℓ acc : ℕ) : ∀ b, (colWords p ℓ acc b).length = b * (2 * ℓ + 1)
  | 0 => by simp [colWords]
  | b + 1 => by rw [colWords_succ, List.length_append, colWords_length p ℓ acc b, frame_length, binary_length]; ring

/-- The heads before pass `b`. -/
def innerH (ℓ n0 b : ℕ) : Fin 6 → ℕ := ![b, 0, n0 + b * (2 * ℓ + 1), 0, 0, 0]

/-- The tapes before pass `b`. -/
def innerA (p ℓ acc cap : ℕ) (out backing : List Bool) (b : ℕ) : Fin 6 → List Bool :=
  ![List.replicate ℓ true ++ [false], frame (binary ℓ ((lfsr p ℓ)^[b] acc)), overlay (out ++ colWords p ℓ acc b) backing,
    frame (binary ℓ p), [false], List.replicate cap false]

def innerCost (ℓ : ℕ) : ℕ := 2 * (2 * ℓ + 1) + 2 + 1 + lfsrCost ℓ + 1 + 1

theorem tInner_step (p ℓ acc cap : ℕ) (out backing : List Bool) (hℓ : 1 ≤ ℓ) (hcap : 2 * ℓ + 2 ≤ cap) (b : ℕ) :
    Step tInnerBody (innerCost ℓ) (innerH ℓ out.length b) (innerA p ℓ acc cap out backing b)
      (innerH ℓ out.length (b + 1)) (innerA p ℓ acc cap out backing (b + 1)) := by
  set w := binary ℓ ((lfsr p ℓ)^[b] acc) with hw
  set O := out ++ colWords p ℓ acc b with hO
  have hOl : O.length = out.length + b * (2 * ℓ + 1) := by rw [hO, List.length_append, colWords_length]
  -- 1: append the column to the table (the column's head is restored)
  obtain ⟨c, hc, hcf⟩ := CopyO.copy_run [] w [] O backing
  simp only [List.nil_append, List.append_nil, List.length_nil, Nat.zero_add] at hc hcf
  have hcs : Step CopyO.machine (2 * w.length + 1) ![0, O.length] ![frame w, overlay O backing]
      ![2 * w.length, O.length + (2 * w.length + 1)] ![frame w, overlay (O ++ frame w) backing] := by
    refine ⟨c, ?_, ?_, ?_, runFrom_steps_le _ _ _ _ hc⟩
    · exact hc
    · rw [hcf]; funext i; fin_cases i <;> simp [CopyO.config]
    · rw [hcf]; funext i; fin_cases i <;> simp [CopyO.config]
  rw [hw, binary_length] at hcs
  have hm := hcs.mask (cap := cap) selCopy (by intro i hi; fin_cases i <;> first | rfl | simp [selCopy] at hi)
    (by omega)
  have hm' : Step (MaskedReset.machine CopyO.machine selCopy) (2 * (2 * ℓ + 1) + 2)
      ![0, O.length, 0] ![frame w, overlay O backing, List.replicate cap false]
      ![0, O.length + (2 * ℓ + 1), 0] ![frame w, overlay (O ++ frame w) backing, List.replicate cap false] := by
    refine (hm.congr_in ?_ ?_).congr ?_ ?_ <;> funext i <;> fin_cases i <;> rfl
  have h1 := dockRun hm' t6Copy (by decide) (innerH ℓ out.length b) (innerA p ℓ acc cap out backing b)
    (by intro j; fin_cases j <;> simp [innerH, t6Copy, hOl]) (by intro j; fin_cases j <;> rfl)
  rw [dockH_t6Copy, install_t6Copy] at h1
  -- 2: one LFSR step of the column
  have hl := lfsr_run p ℓ ((lfsr p ℓ)^[b] acc) hℓ false cap hcap
  have hl' : Step lfsrM (lfsrCost ℓ) (fun _ => 0)
      ![frame (binary ℓ ((lfsr p ℓ)^[b] acc)), frame (binary ℓ p), [false], List.replicate cap false] (fun _ => 0)
      ![frame (binary ℓ (lfsr p ℓ ((lfsr p ℓ)^[b] acc))), frame (binary ℓ p), [false], List.replicate cap false] :=
    (hl.congr_in (by funext i; fin_cases i <;> rfl) rfl).congr (by funext i; fin_cases i <;> rfl) rfl
  have h2 := dockKeep hl' t6Lfsr (by decide)
    ![b, 0, O.length + (2 * ℓ + 1), 0, 0, 0]
    ![List.replicate ℓ true ++ [false], frame w, overlay (O ++ frame w) backing, frame (binary ℓ p), [false],
      List.replicate cap false]
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  rw [install_t6Lfsr] at h2
  -- 3: the counter
  have h3 := dockRun (nudge_run (List.replicate ℓ true ++ [false]) b) t6Nudge (by decide)
    ![b, 0, O.length + (2 * ℓ + 1), 0, 0, 0]
    ![List.replicate ℓ true ++ [false], frame (binary ℓ (lfsr p ℓ ((lfsr p ℓ)^[b] acc))),
      overlay (O ++ frame w) backing, frame (binary ℓ p), [false], List.replicate cap false]
    (by intro j; fin_cases j; rfl) (by intro j; fin_cases j; rfl)
  rw [dockH_t6Nudge, install_t6Nudge] at h3
  have hall := ((h1.congr (by funext i; fin_cases i <;> rfl) (by funext i; fin_cases i <;> rfl)).seq
    (h2.congr rfl (by funext i; fin_cases i <;> rfl))).seq h3
  have e1 : (lfsr p ℓ)^[b + 1] acc = lfsr p ℓ ((lfsr p ℓ)^[b] acc) := Function.iterate_succ_apply' _ _ _
  have e2 : out ++ colWords p ℓ acc (b + 1) = O ++ frame w := by rw [colWords_succ, hO, hw, List.append_assoc]
  have e3 : out.length + (b + 1) * (2 * ℓ + 1) = O.length + (2 * ℓ + 1) := by rw [hOl]; ring
  unfold innerH innerA
  rw [e1, e2, e3]
  exact hall.congr (by funext i; fin_cases i <;> rfl) (by funext i; fin_cases i <;> rfl)

theorem read_unary (ℓ b : ℕ) : readTapeBit (List.replicate ℓ true ++ [false]) b = decide (b < ℓ) := by
  unfold readTapeBit
  by_cases h : b < ℓ
  · rw [List.getD_append _ _ _ _ (by simpa using h), List.getD_eq_getElem _ _ (by simpa using h),
      List.getElem_replicate, decide_eq_true h]
  · rw [List.getD_append_right _ _ _ _ (by simp; omega), decide_eq_false h]
    simp only [List.length_replicate]
    cases h2 : b - ℓ <;> simp

/-- **The inner loop as one `Step`**: the `ℓ` columns `acc, x·acc, …, x^{ℓ−1}·acc` appended to the table. -/
theorem tInner_run (p ℓ acc cap : ℕ) (out backing : List Bool) (hℓ : 1 ≤ ℓ) (hcap : 2 * ℓ + 2 ≤ cap) :
    Step tInnerM (ℓ * (innerCost ℓ + 2) + 1) (innerH ℓ out.length 0) (innerA p ℓ acc cap out backing 0)
      (innerH ℓ out.length ℓ) (innerA p ℓ acc cap out backing ℓ) := by
  let W : WhileBody 6 _ :=
    { body := tInnerBody
      tape := 0
      bound := ℓ
      H := innerH ℓ out.length
      A := innerA p ℓ acc cap out backing
      cost := fun _ => innerCost ℓ
      step := fun b _ => tInner_step p ℓ acc cap out backing hℓ hcap b
      cont := fun b hb => by
        show readTapeBit (List.replicate ℓ true ++ [false]) b = true
        rw [read_unary, decide_eq_true hb]
      halt := by
        show readTapeBit (List.replicate ℓ true ++ [false]) ℓ = false
        rw [read_unary, decide_eq_false (lt_irrefl ℓ)] }
  have h := W.run
  rw [W.rest_const (innerCost ℓ) (fun _ => rfl)] at h
  exact h

/-! ## The outer loop (tapes 0 the unary power counter, 1 the unary column counter, 2 the power `λ^i`, 3 the current
column, 4 the table, 5 the modulus, 6 the label, 7 and 8 the product's scratch words, 9 the flag cell, 10 the capacity
tape, 11 the rewind log) -/

def t12Cur : Fin 4 → Fin 12 := ![3, 2, 9, 10]

theorem install_t12Cur (A : Fin 12 → List Bool) (v : Fin 4 → List Bool) :
    RecoveryRootRound.install t12Cur A v = ![A 0, A 1, v 1, v 0, A 4, A 5, A 6, A 7, A 8, v 2, v 3, A 11] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 1
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 2
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 3
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

theorem dockH_t12Cur (H : Fin 12 → ℕ) (v : Fin 4 → ℕ) :
    dockH t12Cur H v = ![H 0, H 1, v 1, v 0, H 4, H 5, H 6, H 7, H 8, v 2, v 3, H 11] := by
  funext i; fin_cases i
  all_goals first
    | exact dockH_slot _ (by decide) _ _ 0
    | exact dockH_slot _ (by decide) _ _ 1
    | exact dockH_slot _ (by decide) _ _ 2
    | exact dockH_slot _ (by decide) _ _ 3
    | exact dockH_other _ _ _ _ (by decide)

def t12Inner : Fin 7 → Fin 12 := ![1, 3, 4, 5, 9, 10, 11]

theorem install_t12Inner (A : Fin 12 → List Bool) (v : Fin 7 → List Bool) :
    RecoveryRootRound.install t12Inner A v = ![A 0, v 0, A 2, v 1, v 2, v 3, A 6, A 7, A 8, v 4, v 5, v 6] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 1
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 2
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 3
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 4
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 5
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 6
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

theorem dockH_t12Inner (H : Fin 12 → ℕ) (v : Fin 7 → ℕ) :
    dockH t12Inner H v = ![H 0, v 0, H 2, v 1, v 2, v 3, H 6, H 7, H 8, v 4, v 5, v 6] := by
  funext i; fin_cases i
  all_goals first
    | exact dockH_slot _ (by decide) _ _ 0
    | exact dockH_slot _ (by decide) _ _ 1
    | exact dockH_slot _ (by decide) _ _ 2
    | exact dockH_slot _ (by decide) _ _ 3
    | exact dockH_slot _ (by decide) _ _ 4
    | exact dockH_slot _ (by decide) _ _ 5
    | exact dockH_slot _ (by decide) _ _ 6
    | exact dockH_other _ _ _ _ (by decide)

def t12X : Fin 4 → Fin 12 := ![7, 2, 9, 10]

theorem install_t12X (A : Fin 12 → List Bool) (v : Fin 4 → List Bool) :
    RecoveryRootRound.install t12X A v = ![A 0, A 1, v 1, A 3, A 4, A 5, A 6, v 0, A 8, v 2, v 3, A 11] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 1
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 2
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 3
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

theorem dockH_t12X (H : Fin 12 → ℕ) (v : Fin 4 → ℕ) :
    dockH t12X H v = ![H 0, H 1, v 1, H 3, H 4, H 5, H 6, v 0, H 8, v 2, v 3, H 11] := by
  funext i; fin_cases i
  all_goals first
    | exact dockH_slot _ (by decide) _ _ 0
    | exact dockH_slot _ (by decide) _ _ 1
    | exact dockH_slot _ (by decide) _ _ 2
    | exact dockH_slot _ (by decide) _ _ 3
    | exact dockH_other _ _ _ _ (by decide)

def t12Z : Fin 4 → Fin 12 := ![8, 2, 9, 10]

theorem install_t12Z (A : Fin 12 → List Bool) (v : Fin 4 → List Bool) :
    RecoveryRootRound.install t12Z A v = ![A 0, A 1, v 1, A 3, A 4, A 5, A 6, A 7, v 0, v 2, v 3, A 11] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 1
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 2
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 3
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

theorem dockH_t12Z (H : Fin 12 → ℕ) (v : Fin 4 → ℕ) :
    dockH t12Z H v = ![H 0, H 1, v 1, H 3, H 4, H 5, H 6, H 7, v 0, v 2, v 3, H 11] := by
  funext i; fin_cases i
  all_goals first
    | exact dockH_slot _ (by decide) _ _ 0
    | exact dockH_slot _ (by decide) _ _ 1
    | exact dockH_slot _ (by decide) _ _ 2
    | exact dockH_slot _ (by decide) _ _ 3
    | exact dockH_other _ _ _ _ (by decide)

def t12Fmul : Fin 7 → Fin 12 := ![6, 8, 7, 5, 9, 10, 11]

theorem install_t12Fmul (A : Fin 12 → List Bool) (v : Fin 7 → List Bool) :
    RecoveryRootRound.install t12Fmul A v = ![A 0, A 1, A 2, A 3, A 4, v 3, v 0, v 2, v 1, v 4, v 5, v 6] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 1
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 2
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 3
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 4
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 5
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 6
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

theorem dockH_t12Fmul (H : Fin 12 → ℕ) (v : Fin 7 → ℕ) :
    dockH t12Fmul H v = ![H 0, H 1, H 2, H 3, H 4, v 3, v 0, v 2, v 1, v 4, v 5, v 6] := by
  funext i; fin_cases i
  all_goals first
    | exact dockH_slot _ (by decide) _ _ 0
    | exact dockH_slot _ (by decide) _ _ 1
    | exact dockH_slot _ (by decide) _ _ 2
    | exact dockH_slot _ (by decide) _ _ 3
    | exact dockH_slot _ (by decide) _ _ 4
    | exact dockH_slot _ (by decide) _ _ 5
    | exact dockH_slot _ (by decide) _ _ 6
    | exact dockH_other _ _ _ _ (by decide)

def t12Acc : Fin 4 → Fin 12 := ![2, 8, 9, 10]

theorem install_t12Acc (A : Fin 12 → List Bool) (v : Fin 4 → List Bool) :
    RecoveryRootRound.install t12Acc A v = ![A 0, A 1, v 0, A 3, A 4, A 5, A 6, A 7, v 1, v 2, v 3, A 11] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 1
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 2
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 3
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

theorem dockH_t12Acc (H : Fin 12 → ℕ) (v : Fin 4 → ℕ) :
    dockH t12Acc H v = ![H 0, H 1, v 0, H 3, H 4, H 5, H 6, H 7, v 1, v 2, v 3, H 11] := by
  funext i; fin_cases i
  all_goals first
    | exact dockH_slot _ (by decide) _ _ 0
    | exact dockH_slot _ (by decide) _ _ 1
    | exact dockH_slot _ (by decide) _ _ 2
    | exact dockH_slot _ (by decide) _ _ 3
    | exact dockH_other _ _ _ _ (by decide)

def t12U : Fin 1 → Fin 12 := ![0]

theorem install_t12U (A : Fin 12 → List Bool) (v : Fin 1 → List Bool) :
    RecoveryRootRound.install t12U A v = ![v 0, A 1, A 2, A 3, A 4, A 5, A 6, A 7, A 8, A 9, A 10, A 11] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

theorem dockH_t12U (H : Fin 12 → ℕ) (v : Fin 1 → ℕ) :
    dockH t12U H v = ![v 0, H 1, H 2, H 3, H 4, H 5, H 6, H 7, H 8, H 9, H 10, H 11] := by
  funext i; fin_cases i
  all_goals first
    | exact dockH_slot _ (by decide) _ _ 0
    | exact dockH_other _ _ _ _ (by decide)
def selUB : Fin 6 → Bool := ![true, false, false, false, false, false]
def selY : Fin 6 → Bool := ![true, false, false, false, false, false]

noncomputable def oCur := RecoveryFocus.machine t12Cur (MaskedReset.machine (ZipFlag.machine copyG) sel3)
noncomputable def oInner := RecoveryFocus.machine t12Inner (MaskedReset.machine tInnerM selUB)
noncomputable def oX := RecoveryFocus.machine t12X (MaskedReset.machine (ZipFlag.machine copyG) sel3)
noncomputable def oZ := RecoveryFocus.machine t12Z (MaskedReset.machine (ZipFlag.machine clearG) sel3)
noncomputable def oFmul := RecoveryFocus.machine t12Fmul (MaskedReset.machine fmulM selY)
noncomputable def oAcc := RecoveryFocus.machine t12Acc (MaskedReset.machine (ZipFlag.machine copyG) sel3)
noncomputable def oU := RecoveryFocus.machine t12U nudgeM

noncomputable def tOuterBody :=
  Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine
    (Composition.machine oCur oInner) oX) oZ) oFmul) oAcc) oU

/-- **The table machine**: one pass per power `λ^i`, `i < 2h`. -/
noncomputable def tableM := StreamController.machine tOuterBody 0

/-- A masked in-place zip docked on four tapes of the bank whose heads are at zero. -/
theorem zipStage (g : Bool → Bool → Bool → Bool) (slots : Fin 4 → Fin 12) (hi : Function.Injective slots)
    (H : Fin 12 → ℕ) (A : Fin 12 → List Bool) (u v : List Bool) (f : Bool) (cap : ℕ) (hl : u.length = v.length)
    (hH : ∀ j, H (slots j) = 0) (h0 : A (slots 0) = frame u) (h1 : A (slots 1) = frame v) (h2 : A (slots 2) = [f])
    (h3 : A (slots 3) = List.replicate cap false) (hcap : 2 * u.length + 2 ≤ cap) :
    Step (RecoveryFocus.machine slots (MaskedReset.machine (ZipFlag.machine g) sel3)) (2 * (2 * u.length + 2) + 2)
      H A H (RecoveryRootRound.install slots A
        ![frame (List.zipWith (g f) u v), frame v, [f], List.replicate cap false]) := by
  have hz := ZipFlag.run g u v [f] 0 hl
  rw [read_single] at hz
  have hz' : Step (ZipFlag.machine g) (2 * u.length + 2) (fun _ => 0) ![frame u, frame v, [f]]
      ![2 * u.length, 2 * u.length, 0] ![frame (List.zipWith (g f) u v), frame v, [f]] :=
    hz.congr_in (by funext i; fin_cases i <;> rfl) rfl
  have hm := maskZero hz' sel3 (by intro j hj; fin_cases j <;> first | rfl | simp [sel3] at hj) hcap
  have hm' : Step (MaskedReset.machine (ZipFlag.machine g) sel3) (2 * (2 * u.length + 2) + 2) (fun _ => 0)
      ![frame u, frame v, [f], List.replicate cap false] (fun _ => 0)
      ![frame (List.zipWith (g f) u v), frame v, [f], List.replicate cap false] := by
    refine (hm.congr_in rfl ?_).congr rfl ?_ <;> funext i <;> fin_cases i <;> rfl
  exact dockKeep hm' slots hi H A hH (by intro j; fin_cases j <;> assumption)

/-- The table of the first `i` powers: the columns `x^b·λ^{i'}`, `i' < i`, as framed words. -/
def tabWords (p ℓ lam i : ℕ) : List Bool := ((colTable p ℓ i lam).map (binary ℓ)).flatMap frame

theorem tabWords_succ (p ℓ lam i : ℕ) :
    tabWords p ℓ lam (i + 1) = tabWords p ℓ lam i ++ colWords p ℓ (accPow p ℓ lam i) ℓ := by
  unfold tabWords colWords colTable
  rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.map_append, List.flatMap_append,
    List.map_map]
  rfl

theorem tabWords_length (p ℓ lam i : ℕ) : (tabWords p ℓ lam i).length = i * (ℓ * (2 * ℓ + 1)) := by
  induction i with
  | zero => simp [tabWords, colTable]
  | succ i ih => rw [tabWords_succ, List.length_append, ih, colWords_length]; ring

/-- The scratch contents after pass `i` (the given initial words before the first pass). -/
def curG (p ℓ lam c0 : ℕ) : ℕ → ℕ
  | 0 => c0
  | i + 1 => (lfsr p ℓ)^[ℓ] (accPow p ℓ lam i)

def xG (p ℓ lam x0 : ℕ) : ℕ → ℕ
  | 0 => x0
  | i + 1 => (mulState p ℓ (accPow p ℓ lam i) lam ℓ).2

def zG (p ℓ lam z0 : ℕ) : ℕ → ℕ
  | 0 => z0
  | i + 1 => accPow p ℓ lam (i + 1)

/-- The heads before pass `i`. -/
def outerH (ℓ n0 i : ℕ) : Fin 12 → ℕ := ![i, 0, 0, 0, n0 + i * (ℓ * (2 * ℓ + 1)), 0, 0, 0, 0, 0, 0, 0]

/-- The tapes before pass `i`. -/
def outerA (p ℓ lam twoH c0 x0 z0 cap cap2 : ℕ) (out backing : List Bool) (i : ℕ) : Fin 12 → List Bool :=
  ![List.replicate twoH true ++ [false], List.replicate ℓ true ++ [false], frame (binary ℓ (accPow p ℓ lam i)),
    frame (binary ℓ (curG p ℓ lam c0 i)), overlay (out ++ tabWords p ℓ lam i) backing, frame (binary ℓ p),
    frame (binary ℓ lam), frame (binary ℓ (xG p ℓ lam x0 i)), frame (binary ℓ (zG p ℓ lam z0 i)), [false],
    List.replicate cap false, List.replicate cap2 false]

/-- The cost of one pass of the outer loop. -/
def outerCost (ℓ : ℕ) : ℕ :=
  2 * (2 * ℓ + 2) + 2 + 1 + (2 * (ℓ * (innerCost ℓ + 2) + 1) + 2) + 1 + (2 * (2 * ℓ + 2) + 2) + 1 +
    (2 * (2 * ℓ + 2) + 2) + 1 + (2 * (ℓ * (mulIterCost ℓ + 2) + 1) + 2) + 1 + (2 * (2 * ℓ + 2) + 2) + 1 + 1

/-- **One pass of the outer loop**: the `ℓ` columns of `λ^i` appended, then `λ^{i+1}`. -/
theorem tOuter_step (p ℓ lam twoH c0 x0 z0 cap cap2 : ℕ) (out backing : List Bool) (hℓ : 1 ≤ ℓ)
    (hcap : 2 * ℓ + 2 ≤ cap) (hcap2 : ℓ * (innerCost ℓ + 2) + 1 ≤ cap2)
    (hcap3 : ℓ * (mulIterCost ℓ + 2) + 1 ≤ cap2) (i : ℕ) :
    Step tOuterBody (outerCost ℓ) (outerH ℓ out.length i) (outerA p ℓ lam twoH c0 x0 z0 cap cap2 out backing i)
      (outerH ℓ out.length (i + 1)) (outerA p ℓ lam twoH c0 x0 z0 cap cap2 out backing (i + 1)) := by
  set acc := accPow p ℓ lam i with hacc
  set O := out ++ tabWords p ℓ lam i with hO
  have hOl : O.length = out.length + i * (ℓ * (2 * ℓ + 1)) := by rw [hO, List.length_append, tabWords_length]
  set T0 := List.replicate twoH true ++ [false]
  set T1 := List.replicate ℓ true ++ [false]
  set FP := frame (binary ℓ p)
  set FL := frame (binary ℓ lam)
  set Cp := List.replicate cap false
  set Cp2 := List.replicate cap2 false
  set fX := frame (binary ℓ (xG p ℓ lam x0 i))
  set fZ := frame (binary ℓ (zG p ℓ lam z0 i))
  set H0 : Fin 12 → ℕ := ![i, 0, 0, 0, O.length, 0, 0, 0, 0, 0, 0, 0]
  set H1 : Fin 12 → ℕ := ![i, 0, 0, 0, O.length + ℓ * (2 * ℓ + 1), 0, 0, 0, 0, 0, 0, 0]
  -- 1: the current column := the power
  have s1 := zipStage copyG t12Cur (by decide) H0
    ![T0, T1, frame (binary ℓ acc), frame (binary ℓ (curG p ℓ lam c0 i)), overlay O backing, FP, FL, fX, fZ, [false], Cp, Cp2]
    (binary ℓ (curG p ℓ lam c0 i)) (binary ℓ acc) false cap (by simp) (by intro j; fin_cases j <;> rfl) rfl rfl rfl rfl
    (by simp; omega)
  rw [zipWith_copy _ _ (by simp), binary_length, install_t12Cur] at s1
  have s1' := s1.congr (hout' := H0)
    (tout' := ![T0, T1, frame (binary ℓ acc), frame (binary ℓ acc), overlay O backing, FP, FL, fX, fZ, [false], Cp, Cp2])
    rfl (by funext j; fin_cases j <;> rfl)
  -- 2: the inner loop, its counter rewound
  have hin0 := tInner_run p ℓ acc cap O backing hℓ hcap
  have e0 : innerH ℓ O.length 0 = ![0, 0, O.length, 0, 0, 0] := by
    funext j; fin_cases j <;> simp [innerH]
  have e1 : innerA p ℓ acc cap O backing 0 = ![T1, frame (binary ℓ acc), overlay O backing, FP, [false], Cp] := by
    funext j; fin_cases j <;> simp [innerA, colWords, T1, FP, Cp]
  rw [e0, e1] at hin0
  have hin : Step tInnerM (ℓ * (innerCost ℓ + 2) + 1) ![0, 0, O.length, 0, 0, 0]
      ![T1, frame (binary ℓ acc), overlay O backing, FP, [false], Cp]
      ![ℓ, 0, O.length + ℓ * (2 * ℓ + 1), 0, 0, 0]
      ![T1, frame (binary ℓ ((lfsr p ℓ)^[ℓ] acc)), overlay (O ++ colWords p ℓ acc ℓ) backing, FP, [false], Cp] := hin0
  have hm := hin.mask (cap := cap2) selUB (by intro j hj; fin_cases j <;> first | rfl | simp [selUB] at hj) hcap2
  have hm' : Step (MaskedReset.machine tInnerM selUB) (2 * (ℓ * (innerCost ℓ + 2) + 1) + 2)
      ![0, 0, O.length, 0, 0, 0, 0] ![T1, frame (binary ℓ acc), overlay O backing, FP, [false], Cp, Cp2]
      ![0, 0, O.length + ℓ * (2 * ℓ + 1), 0, 0, 0, 0]
      ![T1, frame (binary ℓ ((lfsr p ℓ)^[ℓ] acc)), overlay (O ++ colWords p ℓ acc ℓ) backing, FP, [false], Cp, Cp2] := by
    refine (hm.congr_in ?_ ?_).congr ?_ ?_ <;> funext j <;> fin_cases j <;> rfl
  have s2 := dockRun hm' t12Inner (by decide) H0
    ![T0, T1, frame (binary ℓ acc), frame (binary ℓ acc), overlay O backing, FP, FL, fX, fZ, [false], Cp, Cp2]
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  rw [dockH_t12Inner, install_t12Inner] at s2
  have s2' := s2.congr (hout' := H1)
    (tout' := ![T0, T1, frame (binary ℓ acc), frame (binary ℓ ((lfsr p ℓ)^[ℓ] acc)),
      overlay (O ++ colWords p ℓ acc ℓ) backing, FP, FL, fX, fZ, [false], Cp, Cp2])
    (by funext j; fin_cases j <;> rfl) (by funext j; fin_cases j <;> rfl)
  set fC := frame (binary ℓ ((lfsr p ℓ)^[ℓ] acc))
  set ovT := overlay (O ++ colWords p ℓ acc ℓ) backing
  -- 3: the multiplicand's scratch := the power
  have s3 := zipStage copyG t12X (by decide) H1
    ![T0, T1, frame (binary ℓ acc), fC, ovT, FP, FL, fX, fZ, [false], Cp, Cp2]
    (binary ℓ (xG p ℓ lam x0 i)) (binary ℓ acc) false cap (by simp) (by intro j; fin_cases j <;> rfl) rfl rfl rfl rfl
    (by simp; omega)
  rw [zipWith_copy _ _ (by simp), binary_length, install_t12X] at s3
  have s3' := s3.congr (hout' := H1)
    (tout' := ![T0, T1, frame (binary ℓ acc), fC, ovT, FP, FL, frame (binary ℓ acc), fZ, [false], Cp, Cp2])
    rfl (by funext j; fin_cases j <;> rfl)
  -- 4: the accumulator := 0
  have s4 := zipStage clearG t12Z (by decide) H1
    ![T0, T1, frame (binary ℓ acc), fC, ovT, FP, FL, frame (binary ℓ acc), fZ, [false], Cp, Cp2]
    (binary ℓ (zG p ℓ lam z0 i)) (binary ℓ acc) false cap (by simp) (by intro j; fin_cases j <;> rfl) rfl rfl rfl rfl
    (by simp; omega)
  rw [zipWith_clear _ _ (by simp), binary_length, show List.replicate ℓ false = binary ℓ 0 from (binary_zero ℓ).symm,
    install_t12Z] at s4
  have s4' := s4.congr (hout' := H1)
    (tout' := ![T0, T1, frame (binary ℓ acc), fC, ovT, FP, FL, frame (binary ℓ acc), frame (binary ℓ 0), [false], Cp,
      Cp2])
    rfl (by funext j; fin_cases j <;> rfl)
  -- 5: the product `λ^{i+1} = λ^i·λ`, the label's head rewound
  have hf := fmul_run p ℓ acc lam cap hℓ hcap
  have hf' : Step fmulM (ℓ * (mulIterCost ℓ + 2) + 1) (fun _ => 0)
      ![FL, frame (binary ℓ 0), frame (binary ℓ acc), FP, [false], Cp] ![2 * ℓ, 0, 0, 0, 0, 0]
      ![FL, frame (binary ℓ (fmulShift p ℓ acc lam)), frame (binary ℓ (mulState p ℓ acc lam ℓ).2), FP, [false], Cp] :=
    hf.congr_in (by funext j; fin_cases j <;> rfl) rfl
  have hfm := maskZero hf' selY (by intro j hj; fin_cases j <;> first | rfl | simp [selY] at hj) hcap3
  have hfm' : Step (MaskedReset.machine fmulM selY) (2 * (ℓ * (mulIterCost ℓ + 2) + 1) + 2) (fun _ => 0)
      ![FL, frame (binary ℓ 0), frame (binary ℓ acc), FP, [false], Cp, Cp2] (fun _ => 0)
      ![FL, frame (binary ℓ (fmulShift p ℓ acc lam)), frame (binary ℓ (mulState p ℓ acc lam ℓ).2), FP, [false], Cp,
        Cp2] := by
    refine (hfm.congr_in rfl ?_).congr rfl ?_ <;> funext j <;> fin_cases j <;> rfl
  have s5 := dockKeep hfm' t12Fmul (by decide) H1
    ![T0, T1, frame (binary ℓ acc), fC, ovT, FP, FL, frame (binary ℓ acc), frame (binary ℓ 0), [false], Cp, Cp2]
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  rw [install_t12Fmul] at s5
  set fN := frame (binary ℓ (fmulShift p ℓ acc lam))
  set fM := frame (binary ℓ (mulState p ℓ acc lam ℓ).2)
  have s5' := s5.congr (hout' := H1)
    (tout' := ![T0, T1, frame (binary ℓ acc), fC, ovT, FP, FL, fM, fN, [false], Cp, Cp2])
    rfl (by funext j; fin_cases j <;> rfl)
  -- 6: the power := the product
  have s6 := zipStage copyG t12Acc (by decide) H1
    ![T0, T1, frame (binary ℓ acc), fC, ovT, FP, FL, fM, fN, [false], Cp, Cp2]
    (binary ℓ acc) (binary ℓ (fmulShift p ℓ acc lam)) false cap (by simp) (by intro j; fin_cases j <;> rfl) rfl rfl
    rfl rfl (by simp; omega)
  rw [zipWith_copy _ _ (by simp), binary_length, install_t12Acc] at s6
  have s6' := s6.congr (hout' := H1)
    (tout' := ![T0, T1, fN, fC, ovT, FP, FL, fM, fN, [false], Cp, Cp2])
    rfl (by funext j; fin_cases j <;> rfl)
  -- 7: the power counter
  have s7 := dockRun (nudge_run T0 i) t12U (by decide) H1 ![T0, T1, fN, fC, ovT, FP, FL, fM, fN, [false], Cp, Cp2]
    (by intro j; fin_cases j; rfl) (by intro j; fin_cases j; rfl)
  rw [dockH_t12U, install_t12U] at s7
  have hall := (((((s1'.seq s2').seq s3').seq s4').seq s5').seq s6').seq s7
  have e2 : out ++ tabWords p ℓ lam (i + 1) = O ++ colWords p ℓ acc ℓ := by rw [tabWords_succ, hO, List.append_assoc]
  have e3 : out.length + (i + 1) * (ℓ * (2 * ℓ + 1)) = O.length + ℓ * (2 * ℓ + 1) := by rw [hOl]; ring
  have eH0 : outerH ℓ out.length i = H0 := by
    funext j; fin_cases j <;> simp [outerH, H0, hOl]
  have eA0 : outerA p ℓ lam twoH c0 x0 z0 cap cap2 out backing i =
      ![T0, T1, frame (binary ℓ acc), frame (binary ℓ (curG p ℓ lam c0 i)), overlay O backing, FP, FL, fX, fZ, [false],
        Cp, Cp2] := by
    funext j; fin_cases j <;> rfl
  have eH1 : outerH ℓ out.length (i + 1) = ![i + 1, 0, 0, 0, O.length + ℓ * (2 * ℓ + 1), 0, 0, 0, 0, 0, 0, 0] := by
    funext j; fin_cases j <;> simp [outerH, e3]
  have eA1 : outerA p ℓ lam twoH c0 x0 z0 cap cap2 out backing (i + 1) =
      ![T0, T1, fN, fC, ovT, FP, FL, fM, fN, [false], Cp, Cp2] := by
    funext j; fin_cases j
    · rfl
    · rfl
    · rfl
    · rfl
    · show overlay (out ++ tabWords p ℓ lam (i + 1)) backing = ovT
      rw [e2]
    all_goals rfl
  rw [eH0, eA0, eH1, eA1]
  exact hall.congr (by funext j; fin_cases j <;> rfl) (by funext j; fin_cases j <;> rfl)

theorem table_run (p ℓ lam twoH c0 x0 z0 cap cap2 : ℕ) (out backing : List Bool) (hℓ : 1 ≤ ℓ)
    (hcap : 2 * ℓ + 2 ≤ cap) (hcap2 : ℓ * (innerCost ℓ + 2) + 1 ≤ cap2)
    (hcap3 : ℓ * (mulIterCost ℓ + 2) + 1 ≤ cap2) :
    Step tableM (twoH * (outerCost ℓ + 2) + 1) (outerH ℓ out.length 0)
      (outerA p ℓ lam twoH c0 x0 z0 cap cap2 out backing 0) (outerH ℓ out.length twoH)
      (outerA p ℓ lam twoH c0 x0 z0 cap cap2 out backing twoH) := by
  let W : WhileBody 12 _ :=
    { body := tOuterBody
      tape := 0
      bound := twoH
      H := outerH ℓ out.length
      A := outerA p ℓ lam twoH c0 x0 z0 cap cap2 out backing
      cost := fun _ => outerCost ℓ
      step := fun i _ => tOuter_step p ℓ lam twoH c0 x0 z0 cap cap2 out backing hℓ hcap hcap2 hcap3 i
      cont := fun i hi => by
        show readTapeBit (List.replicate twoH true ++ [false]) i = true
        rw [read_unary, decide_eq_true hi]
      halt := by
        show readTapeBit (List.replicate twoH true ++ [false]) twoH = false
        rw [read_unary, decide_eq_false (lt_irrefl twoH)] }
  have h := W.run
  rw [W.rest_const (outerCost ℓ) (fun _ => rfl)] at h
  exact h

/-- The table tape at the end is the column table. -/
theorem table_out (p ℓ lam twoH c0 x0 z0 cap cap2 : ℕ) (out backing : List Bool) :
    outerA p ℓ lam twoH c0 x0 z0 cap cap2 out backing twoH 4 =
      overlay (out ++ ((colTable p ℓ twoH lam).map (binary ℓ)).flatMap frame) backing := rfl

end NearCubicWires.WireExponent3_5.SeedFix
