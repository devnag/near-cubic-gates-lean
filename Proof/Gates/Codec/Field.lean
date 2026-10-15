import Proof.Gates.Codec.Emit
import Proof.Gates.Worker.Format
import Proof.PCP.VerifierDecodingLookup

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.Codec

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.RepairOrdinary.RadixSemantics
open NearCubicWires.RepairOrdinary.SignedSortKey NearCubicGates.Close.Worker.Format

/-! ## Pure facts -/

theorem headD_drop (w : List Bool) (p : ℕ) : (w.drop p).headD false = w.getD p false := by
  rw [List.getD_eq_getElem?_getD, List.headD_eq_head?_getD, List.head?_drop]

theorem drop_succ_tail (w : List Bool) (p : ℕ) : w.drop (p + 1) = (w.drop p).tail := by
  rw [List.tail_drop]

/-- A unary count read at position `p` ends at `p + k + 1` (also past the end of the word). -/
theorem readCount_drop (w : List Bool) (p : ℕ) :
    (readCount (w.drop p)).2 = w.drop (p + (readCount (w.drop p)).1 + 1) := by
  induction h : (readCount (w.drop p)).1 generalizing p with
  | zero =>
    rcases hw : w.drop p with _ | ⟨b, r⟩
    · have : w.drop (p + 1) = [] := by rw [drop_succ_tail, hw]; rfl
      simp [readCount, this]
    · cases b
      · have : w.drop (p + 1) = r := by rw [drop_succ_tail, hw]; rfl
        simp [readCount, this]
      · rw [hw] at h; simp [readCount] at h
  | succ k ih =>
    rcases hw : w.drop p with _ | ⟨b, r⟩
    · rw [hw] at h; simp [readCount] at h
    · cases b
      · rw [hw] at h; simp [readCount] at h
      · have hr : w.drop (p + 1) = r := by rw [drop_succ_tail, hw]; rfl
        rw [hw] at h
        simp only [readCount, Nat.add_right_cancel_iff] at h
        have := ih (p + 1) (by rw [hr]; exact h)
        rw [hr] at this
        simp only [readCount]
        rw [this]
        congr 1; omega

/-- Trailing `false`s. -/
def tz (l : List Bool) : ℕ := (l.reverse.takeWhile (fun b => b = false)).length

theorem tz_append_true (l : List Bool) : tz (l ++ [true]) = 0 := by simp [tz]
theorem tz_append_false (l : List Bool) : tz (l ++ [false]) = tz l + 1 := by simp [tz]
theorem tz_nil : tz [] = 0 := rfl

theorem tz_le (l : List Bool) : tz l ≤ l.length := by
  unfold tz
  calc _ ≤ l.reverse.length := (List.takeWhile_sublist _).length_le
    _ = l.length := List.length_reverse

/-- The word splits as the part up to its last `1`, then `tz` zeros. -/
theorem split_tz (l : List Bool) : l = l.take (l.length - tz l) ++ List.replicate (tz l) false := by
  induction l using List.reverseRecOn with
  | nil => rfl
  | append_singleton l b ih =>
    cases b
    · rw [tz_append_false]
      have hle := tz_le l
      have h1 : (l ++ [false]).length - (tz l + 1) = l.length - tz l := by simp
      rw [h1, List.take_append_of_le_length (by omega), List.replicate_succ', ← List.append_assoc, ← ih]
    · rw [tz_append_true]; simp

theorem value_replicate_false (k : ℕ) : value (List.replicate k false) = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ, value, ih]

theorem value_take_tz (l : List Bool) : value l = value (l.take (l.length - tz l)) := by
  conv_lhs => rw [split_tz l]
  rw [value_append, value_replicate_false]; ring

theorem getLast_take_tz (l : List Bool) (h : tz l < l.length) :
    (l.take (l.length - tz l)).getLast? = some true := by
  induction l using List.reverseRecOn with
  | nil => simp at h
  | append_singleton l b ih =>
    cases b
    · rw [tz_append_false] at h ⊢
      have h1 : (l ++ [false]).length - (tz l + 1) = l.length - tz l := by simp
      rw [h1, List.take_append_of_le_length (by omega)]
      exact ih (by simp at h; omega)
    · rw [tz_append_true]
      simp only [List.length_append, List.length_singleton, Nat.sub_zero]
      rw [List.take_of_length_le (by simp)]
      simp

theorem value_lt_two_pow (l : List Bool) : value l < 2 ^ l.length := by
  induction l with
  | nil => simp [value]
  | cons b l ih => simp only [value, List.length_cons, pow_succ]; cases b <;> simp <;> omega

theorem two_pow_le_value (l : List Bool) (h : l.getLast? = some true) : 2 ^ (l.length - 1) ≤ value l := by
  induction l with
  | nil => simp at h
  | cons b l ih =>
    rcases l with _ | ⟨c, l'⟩
    · simp at h; subst h; simp [value]
    · have h' : (c :: l').getLast? = some true := by simpa [List.getLast?_cons_cons] using h
      have := ih h'
      simp only [List.length_cons, Nat.add_sub_cancel] at this
      show 2 ^ (l'.length + 1 + 1 - 1) ≤ b.toNat + 2 * value (c :: l')
      rw [Nat.add_sub_cancel, pow_succ]
      omega

theorem fixedWidthNatBits_eq_binary (L v : ℕ) : WilliamsPublishedForm.fixedWidthNatBits L v = binary L v := by
  induction L generalizing v with
  | zero => rfl
  | succ L ih =>
    unfold WilliamsPublishedForm.fixedWidthNatBits at ih ⊢
    rw [List.ofFn_succ, binary, ← ih]
    congr 1
    · simp [Nat.testBit_zero]
      rcases Nat.mod_two_eq_zero_or_one v with h | h <;> simp [h]
    · congr 1; funext i; rw [Fin.val_succ, Nat.testBit_succ]

theorem natWord_value (l : List Bool) (h : tz l < l.length) :
    natWord (value l) = List.replicate (l.length - tz l) true ++ false :: l.take (l.length - tz l) := by
  set L := l.length - tz l with hL
  have hL1 : 1 ≤ L := by omega
  set b := l.take L with hb
  have hbl : b.length = L := by simp [hb]; omega
  have hv : value l = value b := value_take_tz l
  have hlast := getLast_take_tz l h
  have hlo := two_pow_le_value b hlast
  have hhi := value_lt_two_pow b
  rw [hbl] at hlo hhi
  have hlog : natBitLength (value b) = L := by
    unfold natBitLength
    have : Nat.log 2 (value b) = L - 1 := by
      have hpos : 0 < value b := lt_of_lt_of_le Nat.one_le_two_pow hlo
      rw [Nat.log_eq_iff (Or.inr ⟨by norm_num, by omega⟩)]
      exact ⟨hlo, by rwa [show L - 1 + 1 = L by omega]⟩
    omega
  rw [hv]
  unfold natWord WilliamsPublishedForm.framedNatBits
  rw [hlog, fixedWidthNatBits_eq_binary, ← hbl, RepairSource.VerifierDecoding.binary_value_word]

/-- A value with no `1` bit is `0`. -/
theorem value_of_tz (l : List Bool) (h : tz l = l.length) : value l = 0 := by
  rw [value_take_tz l, h, Nat.sub_self, List.take_zero]; rfl

/-! ## Reading a unary count -/

variable {ns nr : ℕ} (cap : ℕ)

/-- Read a unary count `1^k 0` on the raw stream `W` into register `K` (added to it). -/
def countW (W : Fin (ns + 1)) (K : Fin nr) : WM ns nr := .seq (.whs W (.seq (.fwd W) (.inc K))) (.fwd W)

theorem wbit_eq (σ : WState ns nr) (i : Fin (ns + 1)) : wbit σ i = ((σ.st i).drop (σ.sh i)).headD false := by
  rw [headD_drop]; rfl

theorem countLoop_spec (W : Fin (ns + 1)) (K : Fin nr) :
    ∀ (k : ℕ) (σ : WState ns nr), (readCount ((σ.st W).drop (σ.sh W))).1 = k → σ.val K + k ≤ cap →
      WExec cap (.whs W (.seq (.fwd W) (.inc K))) σ ((σ.seth W (σ.sh W + k)).setv K (σ.val K + k)) (7 * k + 1)
  | 0, σ, hk, _ => by
    have hb : wbit σ W = false := by
      rw [wbit_eq]
      rcases hw : (σ.st W).drop (σ.sh W) with _ | ⟨b, r⟩
      · rfl
      · cases b
        · rfl
        · rw [hw] at hk; simp [readCount] at hk
    refine WExec.cast cap (WExec.whsF hb) ?_ (by omega)
    apply WState.eq <;> simp
  | k + 1, σ, hk, hcap => by
    rcases hw : (σ.st W).drop (σ.sh W) with _ | ⟨b, r⟩
    · rw [hw] at hk; simp [readCount] at hk
    · cases b
      · rw [hw] at hk; simp [readCount] at hk
      · have hb : wbit σ W = true := by rw [wbit_eq, hw]; rfl
        rw [hw] at hk
        simp only [readCount, Nat.add_right_cancel_iff] at hk
        have h1 : WExec cap (.seq (.fwd W) (.inc K)) σ ((σ.seth W (σ.sh W + 1)).setv K (σ.val K + 1)) 5 :=
          WExec.seq (WExec.fwd W σ) (WExec.inc K _ (by simp; omega))
        set σ1 := (σ.seth W (σ.sh W + 1)).setv K (σ.val K + 1) with hσ1
        have hr : (σ1.st W).drop (σ1.sh W) = r := by
          simp [hσ1, drop_succ_tail, hw]
        have h2 := countLoop_spec W K k σ1 (by rw [hr]; exact hk) (by simp [hσ1]; omega)
        refine WExec.cast cap (WExec.whsT hb h1 h2) ?_ (by omega)
        apply WState.eq
        · funext j; by_cases hj : j = W
          · subst hj; simp [hσ1]; omega
          · simp [hσ1, Function.update_of_ne hj]
        · simp [hσ1]
        · funext j; by_cases hj : j = K
          · subst hj; simp [hσ1]; omega
          · simp [hσ1, Function.update_of_ne hj]
        · simp [hσ1]

/-- **The count reader**, on every stream: `K` gains the count, the head moves past it (and its closing `0`). -/
theorem countW_spec (W : Fin (ns + 1)) (K : Fin nr) (σ : WState ns nr)
    (hcap : σ.val K + (readCount ((σ.st W).drop (σ.sh W))).1 ≤ cap) :
    WExec cap (countW W K) σ
      ((σ.seth W (σ.sh W + (readCount ((σ.st W).drop (σ.sh W))).1 + 1)).setv K
        (σ.val K + (readCount ((σ.st W).drop (σ.sh W))).1))
      (7 * (readCount ((σ.st W).drop (σ.sh W))).1 + 3) := by
  set k := (readCount ((σ.st W).drop (σ.sh W))).1 with hk
  have h1 := countLoop_spec cap W K k σ hk.symm hcap
  have h2 := WExec.fwd (cap := cap) W ((σ.seth W (σ.sh W + k)).setv K (σ.val K + k))
  refine WExec.cast cap (WExec.seq h1 h2) ?_ (by omega)
  apply WState.eq
  · funext j; by_cases hj : j = W
    · subst hj; simp
    · simp [Function.update_of_ne hj]
  · simp
  · simp
  · simp

end NearCubicGates.Close.Codec
