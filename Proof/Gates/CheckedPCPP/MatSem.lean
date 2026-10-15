import Proof.Gates.CheckedPCPP.Emit
import Proof.Gates.CheckedPCPP.FramedWord
import Proof.Gates.Gadget.CheckedNodes

set_option autoImplicit false

namespace NearCubicGates.Close.CheckedPCPP

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicGates.PublishedSources.PCPP NearCubicGates.Close.Gadget NearCubicWires.SourceInterfaces

/-- The unit vector `e_i` (all `false` when `i ≥ n`). -/
def unitVec (n i : ℕ) : BitInput n := fun j => decide (j.val = i)

theorem foldl_xor_unit {n : ℕ} (i : Fin n) : ∀ (l : List (Fin n)) (b : Bool), l.Nodup →
    l.foldl (fun p j => xor p (unitVec n i.val j)) b = xor b (decide (i ∈ l))
  | [], b, _ => by simp
  | j :: l, b, hl => by
    rw [List.foldl_cons, foldl_xor_unit i l _ (List.nodup_cons.1 hl).2]
    have hj := (List.nodup_cons.1 hl).1
    by_cases hji : j = i
    · subst hji
      simp [unitVec, hj]
    · have : unitVec n i.val j = false := by
        simp [unitVec, Fin.val_eq_val, hji]
      simp [this, Ne.symm hji]

/-- **`Enc` on a unit vector.** -/
theorem enc_unit (E : LinearCodeFamily) (n : ℕ) (i : Fin n) (j : Fin (E.length n)) :
    E.enc n (unitVec n i.val) j = decide (i ∈ E.support n j) := by
  simp only [LinearCodeFamily.enc, SourceInterfaces.parityOn]
  rw [foldl_xor_unit i _ false (Finset.nodup_toList _)]
  simp

/-- The support matrix, row-major: cell `j·n + i` is `[i ∈ E.support n j]`. -/
def matBit (E : LinearCodeFamily) (n p : ℕ) : Bool :=
  if h : p / n < E.length n ∧ p % n < n then decide ((⟨p % n, h.2⟩ : Fin n) ∈ E.support n ⟨p / n, h.1⟩) else false

theorem matBit_at (E : LinearCodeFamily) (n : ℕ) (i : Fin n) (j : Fin (E.length n)) :
    matBit E n (j.val * n + i.val) = decide (i ∈ E.support n j) := by
  have hn : 0 < n := Fin.pos i
  have h1 : (j.val * n + i.val) / n = j.val := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt i.isLt, Nat.zero_add]
  have h2 : (j.val * n + i.val) % n = i.val := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt i.isLt]
  unfold matBit
  rw [dif_pos (by rw [h1, h2]; exact ⟨j.isLt, i.isLt⟩)]
  have key : ∀ (a : Fin n) (b : Fin (E.length n)), a = i → b = j →
      decide (a ∈ E.support n b) = decide (i ∈ E.support n j) := by rintro a b rfl rfl; rfl
  exact key _ _ (Fin.ext h2) (Fin.ext h1)

theorem matBit_beyond (E : LinearCodeFamily) (n p : ℕ) (hp : E.length n ≤ p / n) : matBit E n p = false := by
  unfold matBit; rw [dif_neg (by omega)]

/-- The matrix after columns `< i` and, in column `i`, rows `< j`. -/
def matPart (E : LinearCodeFamily) (n i j p : ℕ) : Bool :=
  if p % n < i ∨ (p % n = i ∧ p / n < j) then matBit E n p else false

theorem matPart_next_col (E : LinearCodeFamily) (n i p : ℕ) :
    matPart E n i (E.length n) p = matPart E n (i + 1) 0 p := by
  unfold matPart
  by_cases h1 : p % n < i
  · rw [if_pos (Or.inl h1), if_pos (Or.inl (show p % n < i + 1 by omega))]
  · by_cases h2 : p % n = i
    · by_cases h3 : p / n < E.length n
      · rw [if_pos (Or.inr ⟨h2, h3⟩), if_pos (Or.inl (show p % n < i + 1 by omega))]
      · rw [if_neg (show ¬ (p % n < i ∨ (p % n = i ∧ p / n < E.length n)) by omega),
          if_pos (Or.inl (show p % n < i + 1 by omega)), matBit_beyond E n p (by omega)]
    · rw [if_neg (show ¬ (p % n < i ∨ (p % n = i ∧ p / n < E.length n)) by omega),
        if_neg (show ¬ (p % n < i + 1 ∨ (p % n = i + 1 ∧ p / n < 0)) by
          have := Nat.not_lt_zero (p / n); omega)]

theorem matPart_zero (E : LinearCodeFamily) (n p : ℕ) : matPart E n 0 0 p = false := by
  unfold matPart
  rw [if_neg (show ¬ (p % n < 0 ∨ (p % n = 0 ∧ p / n < 0)) by have := Nat.not_lt_zero (p / n); omega)]

theorem matPart_full (E : LinearCodeFamily) (n p : ℕ) (hn : 0 < n) : matPart E n n 0 p = matBit E n p := by
  unfold matPart; rw [if_pos (Or.inl (Nat.mod_lt _ hn))]

/-- Writing row `j` of column `i`. -/
theorem matPart_step (E : LinearCodeFamily) (n : ℕ) (i : Fin n) (j : Fin (E.length n)) (p : ℕ) :
    matPart E n i.val (j.val + 1) p =
      if p = j.val * n + i.val then decide (i ∈ E.support n j) else matPart E n i.val j.val p := by
  have hn : 0 < n := Fin.pos i
  by_cases hp : p = j.val * n + i.val
  · subst hp
    rw [if_pos rfl, ← matBit_at E n i j]
    have h1 : (j.val * n + i.val) / n = j.val := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt i.isLt, Nat.zero_add]
    have h2 : (j.val * n + i.val) % n = i.val := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt i.isLt]
    unfold matPart; rw [if_pos (Or.inr ⟨h2, by omega⟩)]
  · rw [if_neg hp]
    unfold matPart
    have hpq : p = (p / n) * n + p % n := by rw [Nat.mul_comm]; exact (Nat.div_add_mod p n).symm
    have hc : ¬ (p % n = i.val ∧ p / n = j.val) := fun hc => hp (by rw [hpq, hc.1, hc.2])
    by_cases h1 : p % n < i.val
    · rw [if_pos (Or.inl h1), if_pos (Or.inl h1)]
    · by_cases h2 : p % n = i.val ∧ p / n < j.val
      · rw [if_pos (Or.inr (show p % n = i.val ∧ p / n < j.val + 1 by omega)), if_pos (Or.inr h2)]
      · rw [if_neg (show ¬ (p % n < i.val ∨ (p % n = i.val ∧ p / n < j.val + 1)) by omega),
          if_neg (show ¬ (p % n < i.val ∨ (p % n = i.val ∧ p / n < j.val)) by omega)]

/-! ## The encoder's input and output -/

/-- One message bit under two frames. -/
def quad (b : Bool) : List Bool := [true, true, true, b]

theorem pairs_pairs (w : List Bool) : FramedSim.pairs (FramedSim.pairs w) = w.flatMap quad := by
  induction w with
  | nil => rfl
  | cons b w ih => simp [ih, quad]

/-- The encoder's input tape, cell by cell. -/
theorem frame_frame_append (a c : List Bool) :
    frame (frame a ++ frame c) = a.flatMap quad ++ [true, false] ++ c.flatMap quad ++ [true, false] ++ [false] := by
  rw [FramedSim.frame_eq_pairs (frame a ++ frame c), FramedSim.frame_eq_pairs a, FramedSim.frame_eq_pairs c]
  simp [pairs_pairs, List.append_assoc]

theorem ofFn_unitVec (n i : ℕ) (hi : i < n) :
    List.ofFn (unitVec n i) = List.replicate i false ++ true :: List.replicate (n - i - 1) false := by
  apply List.ext_getElem
  · simp; omega
  · intro k h1 h2
    simp only [List.getElem_ofFn, unitVec]
    rw [List.getElem_append]
    split_ifs with hk
    · simp at hk; simp [Nat.ne_of_lt hk]
    · simp at hk
      by_cases hki : k = i
      · subst hki; simp
      · have : k - i ≠ 0 := by omega
        rw [List.getElem_cons]
        simp [this, hki]

/-- The message `⟨n, e_i⟩` (for `2 ≤ n`). -/
def unitReq (n i : ℕ) (hn : 2 ≤ n) : MessageRequest := ⟨n, ⟨unitVec n i, hn⟩⟩

theorem frame_messageWord_unit (n i : ℕ) (hn : 2 ≤ n) (hi : i < n) :
    frame (messageWord (unitReq n i hn)) =
      n.bits.flatMap quad ++ [true, false] ++ (List.replicate i (quad false) ++ [quad true] ++
        List.replicate (n - i - 1) (quad false)).flatten ++ [true, false] ++ [false] := by
  show frame (frame n.bits ++ frame (List.ofFn (unitVec n i))) = _
  rw [frame_frame_append, ofFn_unitVec n i hi]
  simp [List.flatMap_append, List.flatMap_replicate]

/-- One halving step of `Nat.bits`. -/
theorem bits_step (v : ℕ) (hv : v ≠ 0) : v.bits = decide (v % 2 = 1) :: (v / 2).bits := by
  have hv2 := Nat.div_add_mod v 2
  rcases Nat.mod_two_eq_zero_or_one v with h | h
  · have hne : v / 2 ≠ 0 := by omega
    have : v = 2 * (v / 2) := by omega
    conv_lhs => rw [this]
    rw [Nat.bit0_bits _ hne, h]; rfl
  · have : v = 2 * (v / 2) + 1 := by omega
    conv_lhs => rw [this]
    rw [Nat.bit1_bits, h]; rfl

end NearCubicGates.Close.CheckedPCPP
