import Proof.Wire_3_5.TransferUnion
import Proof.Wire_3_5.StarCarrier
import Proof.CaseAnalysis.RowsEstimatorParityThreshold

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.SupplierPipeline
open NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorParity (thresholdParityBottomGate
  thresholdParityBottomGate_eval thresholdParityTopGate normalizedThresholdParityCircuit
  normalizedThresholdParityCircuit_eval parityOn_eq_decide_odd_filter_card)

/-- The constant-true `THR∘THR` circuit: no bottoms, top `0 ≥ 0`. -/
def thrConstCircuit (n : ℕ) : NormalizedThresholdThresholdCircuit n :=
  ⟨0, Fin.elim0, ⟨⟨Fin.elim0, 0⟩, ∅, fun i => i.elim0⟩⟩

/-- The constant-true `SYM∘THR` circuit: no bottoms, top table `true`. -/
def symConstCircuit (n : ℕ) : NormalizedSymmetricThresholdCircuit n := ⟨0, Fin.elim0, fun _ => true⟩

/-- The staircase parity as a `SYM∘THR` circuit: bottoms `[Σ_{i∈S} x_i ≥ j+1]`, top "odd count". -/
def symStaircaseParity {n : ℕ} (S : Finset (Fin n)) : NormalizedSymmetricThresholdCircuit n :=
  ⟨S.card, thresholdParityBottomGate S, fun c => decide (Odd c.val)⟩

/-- **The constant atom** of each class mode. -/
def unionConstAtom : (m : Mode) → (n : ℕ) → m.Circuit n
  | .thr, n => thrConstCircuit n
  | .sym, n => symConstCircuit n

/-- **The encoding-parity atom** of each class mode. -/
def unionParityAtom : (m : Mode) → (n : ℕ) → Finset (Fin n) → m.Circuit n
  | .thr, _, S => normalizedThresholdParityCircuit S
  | .sym, _, S => symStaircaseParity S

theorem unionConstAtom_eval (m : Mode) (n : ℕ) (x : BitInput n) : m.eval (unionConstAtom m n) x = true := by
  cases m
  · show (thrConstCircuit n).eval x = true
    unfold thrConstCircuit NormalizedThresholdThresholdCircuit.eval SupportedNormalizedGate.eval
      NormalizedThresholdGate.eval
    simp
  · rfl

theorem unionConstAtom_gates (m : Mode) (n : ℕ) : m.gates (unionConstAtom m n) = [] := by
  cases m <;> rfl

theorem card_filter_val_lt (m c : ℕ) (h : c ≤ m) : (Finset.univ.filter fun i : Fin m => i.val < c).card = c := by
  rw [← Finset.card_map Fin.valEmbedding]
  have hmap : (Finset.univ.filter fun i : Fin m => i.val < c).map Fin.valEmbedding = Finset.range c := by
    ext j
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply,
      Finset.mem_range]
    constructor
    · rintro ⟨i, hi, rfl⟩; exact hi
    · intro hj; exact ⟨⟨j, by omega⟩, hj, rfl⟩
  rw [hmap, Finset.card_range]

theorem symStaircaseParity_eval {n : ℕ} (S : Finset (Fin n)) (x : BitInput n) :
    (symStaircaseParity S).eval x = parityOn S x := by
  rw [parityOn_eq_decide_odd_filter_card]
  have hc : (S.filter fun i => x i).card ≤ S.card := Finset.card_le_card (Finset.filter_subset _ _)
  have hcount : ((symStaircaseParity S).acceptedBottomCount x).val = (S.filter fun i => x i).card := by
    unfold NormalizedSymmetricThresholdCircuit.acceptedBottomCount
    show (Finset.univ.filter fun i : Fin S.card => (thresholdParityBottomGate S i).eval x).card = _
    simp only [thresholdParityBottomGate_eval, decide_eq_true_eq]
    exact card_filter_val_lt _ _ hc
  show decide (Odd ((symStaircaseParity S).acceptedBottomCount x).val) = _
  rw [hcount]

theorem unionParityAtom_eval (m : Mode) (n : ℕ) (S : Finset (Fin n)) (x : BitInput n) :
    m.eval (unionParityAtom m n S) x = parityOn S x := by
  cases m
  · exact normalizedThresholdParityCircuit_eval S x
  · exact symStaircaseParity_eval S x

/-- The staircase gates, in order. -/
def staircaseGates {n : ℕ} (S : Finset (Fin n)) : Stars.Carrier n :=
  (List.finRange S.card).map fun i => (thresholdParityBottomGate S i).gate

theorem unionParityAtom_gates (m : Mode) (n : ℕ) (S : Finset (Fin n)) :
    m.gates (unionParityAtom m n S) = staircaseGates S := by
  cases m
  · show Stars.thrGates (normalizedThresholdParityCircuit S) = _
    unfold Stars.thrGates staircaseGates
    have hf : ((List.finRange (normalizedThresholdParityCircuit S).bottomCount).filter fun i =>
        decide (i ∈ (normalizedThresholdParityCircuit S).top.support)) = List.finRange S.card :=
      List.filter_eq_self.2 fun i _ => decide_eq_true (Finset.mem_univ i)
    rw [hf]
    rfl
  · rfl

theorem card_le_of_fin {n : ℕ} (S : Finset (Fin n)) : S.card ≤ n := by
  simpa using Finset.card_le_univ S

theorem unionParityAtom_gates_length (m : Mode) (n : ℕ) (S : Finset (Fin n)) :
    (m.gates (unionParityAtom m n S)).length ≤ n := by
  rw [unionParityAtom_gates]
  simp only [staircaseGates, List.length_map, List.length_finRange]
  exact card_le_of_fin S

theorem intBitLength_le (z : ℤ) : intBitLength z ≤ z.natAbs + 1 := by
  unfold intBitLength
  have := Nat.log_le_self 2 z.natAbs
  omega

/-- The encoding bits of one staircase gate: `≤ 2n + 1`. -/
theorem staircase_encodingBits_le {n : ℕ} (S : Finset (Fin n)) (i : Fin S.card) :
    (thresholdParityBottomGate S i).gate.encodingBits ≤ 2 * n + 1 := by
  have hi : i.val < n := lt_of_lt_of_le i.isLt (card_le_of_fin S)
  show intBitLength ((i.val : ℤ) + 1) + ∑ j : Fin n, intBitLength (if j ∈ S then 1 else 0) ≤ 2 * n + 1
  have h1 : intBitLength ((i.val : ℤ) + 1) ≤ n + 1 := by
    refine (intBitLength_le _).trans ?_
    have : ((i.val : ℤ) + 1).natAbs = i.val + 1 := by omega
    omega
  have h2 : ∑ j : Fin n, intBitLength (if j ∈ S then 1 else 0) ≤ n := by
    have hle : ∀ j : Fin n, intBitLength (if j ∈ S then 1 else 0) ≤ 1 := fun j => by
      split_ifs <;> decide
    calc ∑ j : Fin n, intBitLength (if j ∈ S then 1 else 0) ≤ ∑ _j : Fin n, 1 :=
          Finset.sum_le_sum fun j _ => hle j
      _ = n := by simp
  omega

theorem unionParityAtom_encodingBits_le (m : Mode) (n : ℕ) (S : Finset (Fin n)) :
    ∀ g ∈ m.gates (unionParityAtom m n S), g.encodingBits ≤ 2 * n + 1 := by
  rw [unionParityAtom_gates]
  intro g hg
  simp only [staircaseGates, List.mem_map] at hg
  obtain ⟨i, -, rfl⟩ := hg
  exact staircase_encodingBits_le S i

theorem staircase_atomWires {n : ℕ} (S : Finset (Fin n)) (i : Fin S.card) :
    Stars.Carrier.atomWires (thresholdParityBottomGate S i).gate = S.card + 1 := by
  unfold Stars.Carrier.atomWires
  congr 1
  congr 1
  ext j
  show j ∈ Finset.univ.filter (fun j => (if j ∈ S then (1 : ℤ) else 0) ≠ 0) ↔ j ∈ S
  by_cases hj : j ∈ S <;> simp [hj]

/-- The parity's wires: `|S|(|S|+1) ≤ 2n²` (the `C_par = 2` of `tr:B`, every support). -/
theorem unionParityAtom_wires_le (m : Mode) (n : ℕ) (S : Finset (Fin n)) :
    (m.gates (unionParityAtom m n S)).wires ≤ 2 * n ^ 2 := by
  rw [unionParityAtom_gates]
  have hw : (staircaseGates S).wires = S.card * (S.card + 1) := by
    unfold staircaseGates Stars.Carrier.wires
    rw [List.map_map]
    have : ((List.finRange S.card).map (Stars.Carrier.atomWires ∘ fun i => (thresholdParityBottomGate S i).gate)) =
        (List.finRange S.card).map fun _ => S.card + 1 :=
      List.map_congr_left fun i _ => staircase_atomWires S i
    rw [this, List.map_const', List.length_finRange, List.sum_replicate, smul_eq_mul]
  rw [hw]
  have h := card_le_of_fin S
  rcases Nat.eq_zero_or_pos S.card with h0 | h0
  · rw [h0]; omega
  · nlinarith

/-- The parity's description bits: `≤ (n+1)⁴`. -/
theorem unionParityAtom_descriptionBits_le (m : Mode) (n : ℕ) (S : Finset (Fin n)) :
    m.descriptionBits (unionParityAtom m n S) ≤ (n + 1) ^ 4 := by
  have hS := card_le_of_fin S
  have hb : ∑ i : Fin S.card, (thresholdParityBottomGate S i).descriptionBits ≤ S.card * (3 * n + 1) := by
    calc ∑ i : Fin S.card, (thresholdParityBottomGate S i).descriptionBits
        ≤ ∑ _i : Fin S.card, (3 * n + 1) := Finset.sum_le_sum fun i _ => by
          show (thresholdParityBottomGate S i).gate.encodingBits + n ≤ 3 * n + 1
          have := staircase_encodingBits_le S i
          omega
      _ = S.card * (3 * n + 1) := by simp
  have hpow : 3 * n ^ 2 + 3 * n + 1 ≤ (n + 1) ^ 4 := by nlinarith [Nat.zero_le n, Nat.zero_le (n ^ 2)]
  have hmul : S.card * (3 * n + 1) ≤ n * (3 * n + 1) := Nat.mul_le_mul_right _ hS
  cases m
  · show (thresholdParityTopGate S.card).descriptionBits +
        ∑ i : Fin S.card, (thresholdParityBottomGate S i).descriptionBits ≤ (n + 1) ^ 4
    have ht : (thresholdParityTopGate S.card).descriptionBits ≤ 2 * S.card + 1 := by
      show intBitLength 1 + ∑ i : Fin S.card, intBitLength (if Even i.val then 1 else -1) + S.card ≤ 2 * S.card + 1
      have hle : ∀ i : Fin S.card, intBitLength (if Even i.val then 1 else -1) ≤ 1 := fun i => by
        split_ifs <;> decide
      have hsum : ∑ i : Fin S.card, intBitLength (if Even i.val then 1 else -1) ≤ S.card := by
        calc ∑ i : Fin S.card, intBitLength (if Even i.val then 1 else -1) ≤ ∑ _i : Fin S.card, 1 :=
              Finset.sum_le_sum fun i _ => hle i
          _ = S.card := by simp
      have h1 : intBitLength 1 = 1 := by decide
      omega
    nlinarith
  · show S.card + 1 + ∑ i : Fin S.card, (thresholdParityBottomGate S i).descriptionBits ≤ (n + 1) ^ 4
    nlinarith

theorem unionConstAtom_descriptionBits (m : Mode) (n : ℕ) : m.descriptionBits (unionConstAtom m n) = 1 := by
  cases m
  · show (⟨⟨Fin.elim0, 0⟩, ∅, fun i => i.elim0⟩ : SupportedNormalizedGate 0).descriptionBits +
        ∑ i : Fin 0, (Fin.elim0 i : SupportedNormalizedGate n).descriptionBits = 1
    simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero]
    show intBitLength 0 + ∑ i : Fin 0, intBitLength (Fin.elim0 i) + 0 = 1
    simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero]
    decide
  · show 0 + 1 + ∑ i : Fin 0, (Fin.elim0 i : SupportedNormalizedGate n).descriptionBits = 1
    simp

end NearCubicWires.WireExponent3_5.Transfer
