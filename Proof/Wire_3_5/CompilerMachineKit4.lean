import Proof.Wire_3_5.CompilerMachineKit3

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.CompilerMachine.Kit
open NearCubicWires.WireExponent3_5.Block NearCubicWires.WireExponent3_5.GF2
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay overlay_write overlay_length)

/-! ## A loop over an encoded list -/

theorem enc_split {α : Type} (enc : α → List Bool) (xs : List α) (j : ℕ) (hj : j < xs.length) :
    xs.flatMap enc = (xs.take j).flatMap enc ++ enc xs[j] ++ (xs.drop (j + 1)).flatMap enc := by
  have e : xs = xs.take j ++ xs[j] :: xs.drop (j + 1) := by
    rw [← List.drop_eq_getElem_cons hj, List.take_append_drop]
  conv_lhs => rw [e]
  rw [List.flatMap_append, List.flatMap_cons, List.append_assoc]

/-- **A uniform body once per item of an encoded list.** The source tape holds `P ++ xs.flatMap enc ++ false :: post`
in every bank; every code starts with `true`; before item `j` the source head is at the item's first cell. -/
theorem encRun {t s : ℕ} {α : Type} (enc : α → List Bool) (henc : ∀ x, ∃ l, enc x = true :: l)
    (body : Machine t s) (src : Fin t) (P : List Bool) (xs : List α) (post : List Bool)
    {σ : Type} (f : σ → α → σ) (s0 : σ) (bH : σ → ℕ → Fin t → ℕ) (bA : σ → Fin t → List Bool)
    (hsrcA : ∀ st, bA st src = P ++ xs.flatMap enc ++ false :: post) (hsrcH : ∀ st p, bH st p src = p) (c : ℕ)
    (hstep : ∀ j, j < xs.length → Step body c
      (bH ((xs.take j).foldl f s0) (P.length + ((xs.take j).flatMap enc).length)) (bA ((xs.take j).foldl f s0))
      (bH ((xs.take (j + 1)).foldl f s0) (P.length + ((xs.take (j + 1)).flatMap enc).length))
      (bA ((xs.take (j + 1)).foldl f s0))) :
    Step (StreamController.machine body src) (xs.length * (c + 2) + 1) (bH s0 P.length) (bA s0)
      (bH (xs.foldl f s0) (P.length + (xs.flatMap enc).length)) (bA (xs.foldl f s0)) := by
  let W : WhileBody t s :=
    { body := body
      tape := src
      bound := xs.length
      H := fun j => bH ((xs.take j).foldl f s0) (P.length + ((xs.take j).flatMap enc).length)
      A := fun j => bA ((xs.take j).foldl f s0)
      cost := fun _ => c
      step := fun j hj => hstep j hj
      cont := fun j hj => by
        show readTapeBit (bA ((xs.take j).foldl f s0) src)
          (bH ((xs.take j).foldl f s0) (P.length + ((xs.take j).flatMap enc).length) src) = true
        rw [hsrcA, hsrcH, enc_split enc xs j hj]
        obtain ⟨l, hl⟩ := henc xs[j]
        rw [hl]
        have := Streaming.read_append (P ++ (xs.take j).flatMap enc) (l ++ (xs.drop (j + 1)).flatMap enc ++ false :: post)
          true
        simpa [List.append_assoc] using this
      halt := by
        show readTapeBit (bA ((xs.take xs.length).foldl f s0) src)
          (bH ((xs.take xs.length).foldl f s0) (P.length + ((xs.take xs.length).flatMap enc).length) src) = false
        rw [hsrcA, hsrcH, List.take_length]
        have := Streaming.read_append (P ++ xs.flatMap enc) post false
        simpa [List.append_assoc] using this }
  have hW := W.run
  rw [W.rest_const c (fun _ => rfl)] at hW
  have e0 : W.H 0 = bH s0 P.length := by simp [W]
  have e1 : W.A 0 = bA s0 := by simp [W]
  have e2 : W.H W.bound = bH (xs.foldl f s0) (P.length + (xs.flatMap enc).length) := by
    simp only [W, List.take_length]
  have e3 : W.A W.bound = bA (xs.foldl f s0) := by simp only [W, List.take_length]
  rw [e0, e1, e2, e3] at hW
  exact hW

theorem enc_succ_length {α : Type} (enc : α → List Bool) (xs : List α) (j : ℕ) (hj : j < xs.length) :
    ((xs.take (j + 1)).flatMap enc).length = ((xs.take j).flatMap enc).length + (enc xs[j]).length := by
  rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some, List.flatMap_append, List.length_append]
  simp

/-! ## Writing cell 0 of a tape -/

theorem write0Step (b x : Bool) (rest : List Bool) :
    Step (cellM b) 1 ![0] ![x :: rest] ![0] ![b :: rest] := by
  have hs : step (cellM b) ⟨(cellM b).start, ![0], ![x :: rest]⟩ = some ⟨1, ![0], ![b :: rest]⟩ := by
    simp [step, cellM]
    apply configuration_ext
    · rfl
    · funext i; fin_cases i; simp [applyAction, HeadMove.apply]
    · funext i; fin_cases i; simp [applyAction, writeTapeBit]
  obtain ⟨r, hr, hf, hs'⟩ := (RecoveryExecution.Timed.single (p := cellM b) rfl hs).run rfl
  exact ⟨r, hr, by rw [hf], by rw [hf], by omega⟩

/-! ## The subset counter -/

/-- Add the flag cell's bit to a binary register, register head back at cell 0 (log on tape 2). -/
noncomputable def incM := MaskedReset.machine IncFlag.machine ![true, false]

theorem incStep (m j : ℕ) (c : Bool) (cap : ℕ) (hcap : 2 * m + 2 ≤ cap) :
    Step incM (2 * (2 * m + 2) + 2) ![0, 0, 0] ![frame (binary m j), [c], List.replicate cap false]
      ![0, 0, 0] ![frame (binary m (j + c.toNat)), [c], List.replicate cap false] := by
  have h0 := IncFlag.run m j [c] 0
  rw [read_single] at h0
  have hm := h0.mask ![true, false] (by intro i hi; fin_cases i <;> simp_all) hcap
  refine (hm.congr_in ?_ ?_).congr ?_ ?_ <;> funext i <;> refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    (try fin_cases j) <;> rfl

/-- `binary m (2^m)` is the zero word: the counter returns to `0` after `2^m` increments. -/
theorem binary_two_pow (m : ℕ) : binary m (2 ^ m) = binary m 0 := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    rw [binary_getElem, binary_getElem, Nat.testBit_two_pow]
    simp only [binary_length] at h1
    simp [Nat.ne_of_gt h1]

/-- Word inequality of two registers into a cell (both register heads back at cell 0). -/
noncomputable def neqM := MaskedReset.machine (EqCell.machine true) ![true, true, false]

theorem neqStep (u v : List Bool) (e : Bool) (hl : u.length = v.length) (cap : ℕ) (hcap : 2 * u.length + 1 ≤ cap) :
    Step neqM (2 * (2 * u.length + 1) + 2) ![0, 0, 0, 0] ![frame u, frame v, [e], List.replicate cap false]
      ![0, 0, 0, 0] ![frame u, frame v, [!decide (u = v)], List.replicate cap false] := by
  have h0 := EqCell.run true u v e hl
  rw [Bool.true_xor] at h0
  have h1 : Step (EqCell.machine true) (2 * u.length + 1) (fun _ => 0) ![frame u, frame v, [e]]
      ![2 * u.length, 2 * u.length, 0] ![frame u, frame v, [!decide (u = v)]] :=
    h0.congr_in (by funext i; fin_cases i <;> rfl) rfl
  have hm := h1.mask ![true, true, false] (by intro i _; rfl) hcap
  refine (hm.congr_in ?_ ?_).congr ?_ ?_ <;> funext i <;> refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    (try fin_cases j) <;> rfl

end NearCubicWires.WireExponent3_5.CompilerMachine.Kit
