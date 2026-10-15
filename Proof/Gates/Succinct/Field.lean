import Proof.Wire_3_5.PrimAsmParseNat
import Proof.Wire_3_5.UnionMachineRoundParse

set_option autoImplicit false

namespace NearCubicGates.Close.Succinct

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat

/-! ## Register names of the field reader -/

/-- The field reader's registers: unary-prefix flag and count, value, power, temp, the two guard copies, the guard
flag and the position counter. -/
inductive FReg where
  | flag | cnt | val | pw | tmp | gc | hc | zg | cd
  deriving DecidableEq

/-! ## The pure model -/

/-- The length of the run of `true` cells at the head of a list. -/
def onesL : List Bool → ℕ
  | [] => 0
  | true :: l => onesL l + 1
  | false :: _ => 0

theorem onesL_true : ∀ (l : List Bool) (k : ℕ), k < onesL l → l.getD k false = true
  | [], k, h => by simp [onesL] at h
  | true :: l, 0, _ => rfl
  | true :: l, k + 1, h => by
    simp only [onesL] at h
    simpa using onesL_true l k (by omega)
  | false :: _, k, h => by simp [onesL] at h

theorem onesL_false : ∀ (l : List Bool), l.getD (onesL l) false = false
  | [] => rfl
  | true :: l => by simpa [onesL] using onesL_false l
  | false :: _ => rfl

theorem onesL_le : ∀ (l : List Bool), onesL l ≤ l.length
  | [] => le_rfl
  | true :: l => by simp only [onesL, List.length_cons]; have := onesL_le l; omega
  | false :: _ => by simp [onesL]

/-- The unary prefix length of the field at `pos` of the stream `d` (paper lem:succinct-verifier, stage (2)). -/
def ones (d : List Bool) (pos : ℕ) : ℕ := onesL (d.drop pos)

theorem read_drop (d : List Bool) (pos k : ℕ) : readTapeBit d (pos + k) = (d.drop pos).getD k false := by
  unfold readTapeBit
  simp only [List.getD_eq_getElem?_getD, List.getElem?_drop]

theorem ones_true (d : List Bool) (pos k : ℕ) (hk : k < ones d pos) : readTapeBit d (pos + k) = true := by
  rw [read_drop]; exact onesL_true _ k hk

theorem ones_false (d : List Bool) (pos : ℕ) : readTapeBit d (pos + ones d pos) = false := by
  rw [read_drop]; exact onesL_false _

theorem ones_le (d : List Bool) (pos : ℕ) : ones d pos ≤ d.length := by
  have := onesL_le (d.drop pos)
  simp only [List.length_drop] at this
  unfold ones; omega

/-- The `L` payload cells starting at `start`. -/
def payload (d : List Bool) (start L : ℕ) : List Bool := List.ofFn fun k : Fin L => readTapeBit d (start + k.val)

theorem payload_length (d : List Bool) (start L : ℕ) : (payload d start L).length = L := by simp [payload]

/-- The value of the field at `pos` under the guard `lb` (paper lem:succinct-verifier, stage (2)). -/
def fieldVal (d : List Bool) (pos lb : ℕ) : ℕ :=
  if ones d pos ≤ lb then CanonicalBinary.bitsValue (payload d (pos + ones d pos + 1) (ones d pos)) else 0

/-- The position after the field at `pos`. -/
def fieldEnd (d : List Bool) (pos : ℕ) : ℕ := pos + 2 * ones d pos + 1

theorem ones_le_drop (d : List Bool) (pos : ℕ) : ones d pos ≤ d.length - pos := by
  have := onesL_le (d.drop pos)
  simp only [List.length_drop] at this
  exact this

theorem fieldEnd_le (d : List Bool) (pos : ℕ) : fieldEnd d pos ≤ max pos (2 * d.length) + 1 := by
  have := ones_le_drop d pos
  unfold fieldEnd
  rcases Nat.lt_or_ge pos d.length with h | h
  · omega
  · have : ones d pos = 0 := by omega
    omega

theorem le_fieldEnd (d : List Bool) (pos : ℕ) : pos + 1 ≤ fieldEnd d pos := by unfold fieldEnd; omega

theorem fieldVal_lt (d : List Bool) (pos lb : ℕ) : fieldVal d pos lb < 2 ^ lb := by
  unfold fieldVal
  split_ifs with h
  · have := bitsValue_lt (payload d (pos + ones d pos + 1) (ones d pos))
    rw [payload_length] at this
    exact this.trans_le (Nat.pow_le_pow_right (by norm_num) h)
  · exact Nat.pow_pos (by norm_num)

/-! ## A genuine field -/

theorem onesL_replicate (L : ℕ) (r : List Bool) : onesL (List.replicate L true ++ false :: r) = L := by
  induction L with
  | zero => simp [onesL]
  | succ L ih => simp [List.replicate_succ, onesL, ih]

theorem ones_natWord (pre rest : List Bool) (x : ℕ) :
    ones (pre ++ RepairRepresentation.natWord x ++ rest) pre.length = natBitLength x := by
  unfold ones
  rw [List.append_assoc, List.drop_left, natWord_eq]
  simp only [List.append_assoc, List.cons_append]
  exact onesL_replicate _ _

theorem readTapeBit_natWord_payload (pre rest : List Bool) (x m : ℕ) (hm : m < natBitLength x) :
    readTapeBit (pre ++ RepairRepresentation.natWord x ++ rest) (pre.length + natBitLength x + 1 + m) = x.testBit m := by
  unfold readTapeBit
  rw [List.append_assoc, List.getD_append_right _ _ _ _ (by omega)]
  have hlen := natWord_length x
  rw [show pre.length + natBitLength x + 1 + m - pre.length = natBitLength x + 1 + m by omega,
    List.getD_append _ _ _ _ (by omega)]
  exact natWord_getD_payload x m hm

theorem fieldVal_natWord (pre rest : List Bool) (x lb : ℕ) (h : natBitLength x ≤ lb) :
    fieldVal (pre ++ RepairRepresentation.natWord x ++ rest) pre.length lb = x := by
  unfold fieldVal
  rw [ones_natWord, if_pos h]
  have hxL : x < 2 ^ natBitLength x := Nat.lt_pow_succ_log_self (by norm_num) x
  have e : payload (pre ++ RepairRepresentation.natWord x ++ rest) (pre.length + natBitLength x + 1)
      (natBitLength x) = WilliamsPublishedForm.fixedWidthNatBits (natBitLength x) x := by
    unfold payload WilliamsPublishedForm.fixedWidthNatBits
    congr 1; funext k
    exact readTapeBit_natWord_payload pre rest x k.val k.isLt
  rw [e, Transfer.bitsValue_fixedWidth]
  exact Nat.mod_eq_of_lt hxL

theorem fieldEnd_natWord (pre rest : List Bool) (x : ℕ) :
    fieldEnd (pre ++ RepairRepresentation.natWord x ++ rest) pre.length =
      pre.length + (RepairRepresentation.natWord x).length := by
  unfold fieldEnd; rw [ones_natWord, natWord_length]; ring

end NearCubicGates.Close.Succinct
