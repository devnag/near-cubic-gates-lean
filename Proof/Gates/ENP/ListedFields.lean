import Proof.Gates.ENP.UnitPCP
import Proof.PCP.ProjectionNormalizationDedupBytes

set_option autoImplicit false

namespace NearCubicGates.Close.ENP

open NearCubicWires NearCubicWires.RepairSource NearCubicWires.SourceInterfaces NearCubicWires.RepairOrdinary
open NearCubicWires.RepairSource.ProjectionNormalization

/-- `Nat.bits` peels the low bit (used by every halving emitter). -/
theorem bits_eq_cons (v : ℕ) (h : v ≠ 0) : v.bits = decide (v % 2 = 1) :: (v / 2).bits := by
  have hb : Nat.bit (decide (v % 2 = 1)) (v / 2) = v := by
    rw [Nat.bit_val]
    have := Nat.div_add_mod v 2
    rcases Nat.mod_two_eq_zero_or_one v with h0 | h1
    · simp [h0]; omega
    · simp [h1]; omega
  have hz : v / 2 = 0 → decide (v % 2 = 1) = true := by
    intro h0
    have := Nat.div_add_mod v 2
    simp only [decide_eq_true_eq]
    omega
  conv_lhs => rw [← hb]
  exact Nat.bits_append_bit _ _ hz

/-- The field of one address bit `b` of the listed-pairs PCP: `frame (projectionCode (constant b)).bits`. -/
def qField (b : Bool) : List Bool := RepairOrdinary.frame [b, true, true]

/-- The normalized query row of query `i` on oracle width `R`: its address bits `testBit i j`, `j < R`. -/
def qRow (R i : ℕ) : List Bool := (List.range R).flatMap fun j => qField (i.testBit j)

/-- The normalized query stream of `M` queries (paper §11.6, stage 1/3 formula input). -/
def qStream (R M : ℕ) : List Bool := (List.range M).flatMap fun i => qRow R i

/-- The literal code of the unit clause `y_i = vals[i]`: `2i` for a positive literal, `2i+1` for a negative one. -/
def unitCode (vals : List Bool) (i : ℕ) : ℕ := 2 * i + (if vals.getD i false then 0 else 1)

/-- The three framed literal codes of clause `i`. -/
def cRow (vals : List Bool) (i : ℕ) : List Bool :=
  RepairOrdinary.frame (unitCode vals i).bits ++
    (RepairOrdinary.frame (unitCode vals i).bits ++ RepairOrdinary.frame (unitCode vals i).bits)

/-- The clause field stream of the listed-pairs PCP. -/
def cStream (vals : List Bool) (M : ℕ) : List Bool := (List.range M).flatMap fun i => cRow vals i

theorem qStream_succ (R M : ℕ) : qStream R (M + 1) = qStream R M ++ qRow R M := by
  simp [qStream, List.range_succ, List.flatMap_append]

theorem cStream_succ (vals : List Bool) (M : ℕ) : cStream vals (M + 1) = cStream vals M ++ cRow vals M := by
  simp [cStream, List.range_succ, List.flatMap_append]

theorem projectionCode_constant_bits {w : ℕ} (b : Bool) :
    (projectionCode (.constant b : ProjectedRandomBit w)).bits = [b, true, true] := by
  cases b
  · show (Nat.pair 2 0).bits = _
    decide
  · show (Nat.pair 2 1).bits = _
    decide

theorem framedCodes_ofFn (R : ℕ) (c : ℕ → ℕ) :
    QueryBytes.framedCodes (List.ofFn fun j : Fin R => c j.val) =
      (List.range R).flatMap fun j => RepairOrdinary.frame (c j).bits := by
  induction R with
  | zero => rfl
  | succ R ih =>
    rw [List.ofFn_succ_last, QueryBytes.framed_append, List.range_succ, List.flatMap_append]
    simp only [Fin.val_castSucc, Fin.val_last] at *
    rw [ih]
    simp [QueryBytes.framedCodes, FieldList.stream]

theorem framedCodes_ofFn2 (M R : ℕ) (c : ℕ → ℕ → ℕ) :
    QueryBytes.framedCodes (List.ofFn fun i : Fin M => List.ofFn fun j : Fin R => c i.val j.val).flatten =
      (List.range M).flatMap fun i => (List.range R).flatMap fun j => RepairOrdinary.frame (c i j).bits := by
  induction M with
  | zero => rfl
  | succ M ih =>
    rw [List.ofFn_succ_last, List.flatten_append, QueryBytes.framed_append, List.range_succ, List.flatMap_append]
    simp only [Fin.val_castSucc, Fin.val_last] at *
    rw [ih]
    simp only [List.flatten_cons, List.flatten_nil, List.append_nil, List.flatMap_cons, List.flatMap_nil]
    rw [framedCodes_ofFn R (c M)]

/-- **The normalized query stream of `unitPCP` is `qStream`** (oracle width `R ≥ w`, `2^w` queries). -/
theorem qStream_eq (w R : ℕ) (vals : List Bool) (hlen : vals.length = 2 ^ w) (hw : w ≤ R) :
    QueryBytes.framedCodes (normalizedRows (unitPCP w vals) R vals.length).flatten = qStream R vals.length := by
  have hrows : normalizedRows (unitPCP w vals) R vals.length =
      List.ofFn fun i : Fin vals.length => List.ofFn fun j : Fin R => 6 + (i.val.testBit j.val).toNat := by
    unfold normalizedRows queryRows
    simp only [unitPCP, Nat.sub_self, List.replicate_zero, List.append_nil, List.map_ofFn]
    apply List.ext_getElem
    · simp
    · intro i h1 h2
      simp only [List.getElem_ofFn, Function.comp_apply]
      apply List.ext_getElem
      · simp; omega
      · intro j hj1 hj2
        simp only [List.getElem_ofFn]
        by_cases hjw : j < w
        · rw [List.getElem_append_left (by simpa using hjw)]
          simp only [List.getElem_ofFn]
          cases h : i.testBit j <;> rfl
        · rw [List.getElem_append_right (by simpa using hjw)]
          simp only [List.getElem_replicate, zeroCode]
          have hi : i < 2 ^ j := by
            have := Nat.pow_le_pow_right (by decide : 0 < 2) (show w ≤ j by omega)
            simp only [List.length_ofFn] at h1
            omega
          rw [Nat.testBit_eq_false_of_lt hi]
          rfl
  rw [hrows, framedCodes_ofFn2 vals.length R (fun i j => 6 + (i.testBit j).toNat)]
  unfold qStream qRow qField
  congr 1
  funext i
  congr 1
  funext j
  cases i.testBit j <;> decide

theorem unit_clauses_nodup (w : ℕ) (vals : List Bool) :
    ((unitPCP w vals).decision.clauses.map clauseCodes).Nodup := by
  simp only [unitPCP, List.map_ofFn]
  rw [List.nodup_ofFn]
  intro i j h
  simp only [Function.comp_apply, clauseCodes, unitClause] at h
  have h0 := congrArg (fun l => l.headD 0) h
  simp only [List.ofFn_succ, List.headD_cons] at h0
  apply Fin.ext
  split_ifs at h0 <;> simp [literalCode] at h0 <;> omega

theorem flatMap_ofFn_eq_range {α : Type} (n : ℕ) (f : ℕ → List α) :
    (List.ofFn fun i : Fin n => f i.val).flatten = (List.range n).flatMap f := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ_last, List.flatten_append, List.range_succ, List.flatMap_append]
    simp only [Fin.val_castSucc, Fin.val_last] at *
    rw [ih]
    simp

theorem flatten_ofFn_range {α : Type} (n : ℕ) (f : Fin n → List α) (g : ℕ → List α)
    (h : ∀ i : Fin n, f i = g i.val) : (List.ofFn f).flatten = (List.range n).flatMap g := by
  rw [show f = fun i : Fin n => g i.val from funext h]
  exact flatMap_ofFn_eq_range n g

/-- **The clause fields of `unitPCP` are `cStream`.** -/
theorem cStream_eq (w : ℕ) (vals : List Bool) :
    DedupBytes.fields (unitPCP w vals) = cStream vals vals.length := by
  unfold DedupBytes.fields Codec.clauses
  rw [List.Nodup.dedup (unit_clauses_nodup w vals)]
  simp only [unitPCP, List.map_ofFn]
  unfold cStream
  apply flatten_ofFn_range
  intro i
  have hg : vals.getD i.val false = vals.get i := by
    simp [List.getD_eq_getElem?_getD]
  simp only [Function.comp_apply, clauseCodes, unitClause, cRow, unitCode, hg,
    QueryBytes.framedCodes, FieldList.stream]
  cases vals.get i <;> simp [List.ofFn_succ, literalCode]

end NearCubicGates.Close.ENP
