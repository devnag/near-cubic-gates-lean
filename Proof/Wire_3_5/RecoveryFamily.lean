import Proof.Wire_3_5.TransferUnionComplete
import Proof.Wire_3_5.StarCarrier
import Proof.CaseAnalysis.SampledWitness

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.SupplierPipeline NearCubicWires.CanonicalWitnessCodec
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.CloseoutWitness NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.Shared (uMean bitR)
open NearCubicWires.ComponentwiseBranchExtraction (literalIndex)
open scoped BigOperators

/-! ## Circuits of a mode along an arity equation -/

/-- The wire count of a circuit of a class mode (the Theorem 2.5 `wireCount`). -/
def modeWireCount : (m : Mode) → {n : ℕ} → m.Circuit n → ℕ
  | .thr, _, c => NormalizedThresholdThresholdCircuit.wireCount c
  | .sym, _, c => NormalizedSymmetricThresholdCircuit.wireCount c

/-- A circuit of a mode, transported along an arity equation. -/
def castAtom (m : Mode) {a b : ℕ} (h : a = b) (C : m.Circuit a) : m.Circuit b := h ▸ C

theorem castAtom_eval (m : Mode) {a b : ℕ} (h : a = b) (C : m.Circuit a) (x : BitInput b) :
    m.eval (castAtom m h C) x = m.eval C (fun j => x (Fin.cast h j)) := by
  subst h; rfl

theorem castAtom_descriptionBits (m : Mode) {a b : ℕ} (h : a = b) (C : m.Circuit a) :
    m.descriptionBits (castAtom m h C) = m.descriptionBits C := by
  subst h; rfl

theorem castAtom_wireCount (m : Mode) {a b : ℕ} (h : a = b) (C : m.Circuit a) :
    modeWireCount m (castAtom m h C) = modeWireCount m C := by
  subst h; rfl

theorem castAtom_gates_length (m : Mode) {a b : ℕ} (h : a = b) (C : m.Circuit a) :
    (m.gates (castAtom m h C)).length = (m.gates C).length := by
  subst h; rfl

theorem castAtom_gates_wires (m : Mode) {a b : ℕ} (h : a = b) (C : m.Circuit a) :
    (m.gates (castAtom m h C)).wires = (m.gates C).wires := by
  subst h; rfl

theorem castAtom_gates_encodingBits (m : Mode) {a b : ℕ} (h : a = b) (C : m.Circuit a) (E : ℕ)
    (hE : ∀ g ∈ m.gates C, g.encodingBits ≤ E) : ∀ g ∈ m.gates (castAtom m h C), g.encodingBits ≤ E := by
  subst h; exact hE

/-- A mode circuit's charged gates are at most its wire count. -/
theorem gates_length_le_wireCount (m : Mode) {n : ℕ} (C : m.Circuit n) : (m.gates C).length ≤ modeWireCount m C := by
  cases m
  · show (Stars.thrGates C).length ≤ NormalizedThresholdThresholdCircuit.wireCount C
    unfold Stars.thrGates NormalizedThresholdThresholdCircuit.wireCount
    rw [List.length_map]
    calc ((List.finRange C.bottomCount).filter fun i => decide (i ∈ C.top.support)).length
        = (C.top.support).card := by
          rw [← List.toFinset_card_of_nodup ((List.nodup_finRange _).filter _)]
          congr 1; ext i; simp
      _ = ∑ _i ∈ C.top.support, 1 := by simp
      _ ≤ ∑ i ∈ C.top.support, ((C.bottom i).wireCount + 1) := Finset.sum_le_sum fun i _ => by omega
  · show (Stars.symGates C).length ≤ NormalizedSymmetricThresholdCircuit.wireCount C
    unfold Stars.symGates NormalizedSymmetricThresholdCircuit.wireCount
    rw [List.length_map, List.length_finRange]
    calc C.bottomCount = ∑ _i : Fin C.bottomCount, 1 := by simp
      _ ≤ ∑ i, ((C.bottom i).wireCount + 1) := Finset.sum_le_sum fun i _ => by omega

theorem wires_le_wireCount (m : Mode) {n : ℕ} (C : m.Circuit n) : (m.gates C).wires ≤ modeWireCount m C := by
  cases m
  · exact Stars.wires_thrGates_le C
  · exact Stars.wires_symGates_le C

/-- A charged gate's encoding bits are at most the circuit's description bits. -/
theorem gate_encodingBits_le_descriptionBits (m : Mode) {n : ℕ} (C : m.Circuit n) :
    ∀ g ∈ m.gates C, g.encodingBits ≤ m.descriptionBits C := by
  cases m
  · intro g hg
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hg
    show (C.bottom i).gate.encodingBits ≤ C.top.descriptionBits + ∑ j, (C.bottom j).descriptionBits
    have h1 : (C.bottom i).gate.encodingBits ≤ (C.bottom i).descriptionBits := Nat.le_add_right _ _
    have h2 : (C.bottom i).descriptionBits ≤ ∑ j, (C.bottom j).descriptionBits :=
      Finset.single_le_sum (f := fun j => (C.bottom j).descriptionBits) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ i)
    omega
  · intro g hg
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hg
    show (C.bottom i).gate.encodingBits ≤ C.bottomCount + 1 + ∑ j, (C.bottom j).descriptionBits
    have h1 : (C.bottom i).gate.encodingBits ≤ (C.bottom i).descriptionBits := Nat.le_add_right _ _
    have h2 : (C.bottom i).descriptionBits ≤ ∑ j, (C.bottom j).descriptionBits :=
      Finset.single_le_sum (f := fun j => (C.bottom j).descriptionBits) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ i)
    omega

/-! ## The averaged family's atoms -/

theorem foldl_abs_eq {Circ : SupplierPipeline.CircuitFamily} {q : ℕ} (l : List (LegalCircuitTerm Circ q)) (c : ℚ) :
    l.foldl (fun total term => total + |term.coefficient|) c = c + (l.map fun t => |t.coefficient|).sum := by
  induction l generalizing c with
  | nil => simp
  | cons t l ih => rw [List.foldl_cons, ih, List.map_cons, List.sum_cons]; ring

theorem cast_sum_abs {Circ : SupplierPipeline.CircuitFamily} {q : ℕ} (l : List (LegalCircuitTerm Circ q)) :
    (((l.map fun t => |t.coefficient|).sum : ℚ) : ℝ) = (l.map fun t => |(t.coefficient : ℝ)|).sum := by
  induction l with
  | nil => simp
  | cons t l ih => rw [List.map_cons, List.sum_cons, Rat.cast_add, ih, Rat.cast_abs]; rfl

section Family
variable {m : Mode} {limits : LegalSumLimits} {nv : ℕ}
  (family : SumFamily m.Circuit (fun C => modeWireCount m C) (fun C => m.descriptionBits C) limits nv)

/-- The terms of the averaged sum of one variable. -/
def famTerms (X : Fin nv) := (family.getSum X).value.terms

/-- The atom `C_{X,j}` (the `j`-th term's circuit, at the limits' arity). -/
def famAtom (X : Fin nv) (j : Fin (famTerms family X).length) : m.Circuit limits.expectedArity :=
  castAtom m (family.getSum X).arity_eq ((famTerms family X).get j).circuit

/-- The coefficient `α_{X,j}`. -/
noncomputable def famCoeff (X : Fin nv) (j : Fin (famTerms family X).length) : ℝ :=
  (((famTerms family X).get j).coefficient : ℝ)

/-- **`T_X = Σ_j α_{X,j} C_{X,j}`**: the family's value is the atom combination. -/
theorem famValue_eq (u : BitInput limits.expectedArity) (X : Fin nv) :
    family.value (fun C x => m.eval C x) u X = ∑ j, famCoeff family X j * bitR (m.eval (famAtom family X j) u) := by
  unfold SumFamily.value famCoeff famAtom bitR
  simp only [castAtom_eval]
  rw [← Fin.sum_univ_fun_getElem]
  rfl

/-- `T_X ∈ [0,1]` from the family's unit range. -/
theorem famT_mem (hu : ∀ u X, 0 ≤ family.value (fun C x => m.eval C x) u X ∧
      family.value (fun C x => m.eval C x) u X ≤ 1) (X : Fin nv) (u : BitInput limits.expectedArity) :
    0 ≤ ∑ j, famCoeff family X j * bitR (m.eval (famAtom family X j) u) ∧
      ∑ j, famCoeff family X j * bitR (m.eval (famAtom family X j) u) ≤ 1 := by
  rw [← famValue_eq]; exact hu u X

/-- **The coefficient mass** `Σ_j |α_{X,j}|` is at most the limits' mass cap. -/
theorem famMass_le (X : Fin nv) : ∑ j, |famCoeff family X j| ≤ (limits.coefficientMassCap : ℝ) := by
  have hm := (family.getSum X).mass_le
  unfold LegalCircuitSumDescription.coefficientMass at hm
  rw [foldl_abs_eq, zero_add] at hm
  have hr : ((((family.getSum X).value.terms.map fun t => |t.coefficient|).sum : ℚ) : ℝ) ≤
      (limits.coefficientMassCap : ℝ) := by exact_mod_cast hm
  rw [cast_sum_abs] at hr
  have he := Fin.sum_univ_fun_getElem (famTerms family X) (fun t => |(t.coefficient : ℝ)|)
  unfold famCoeff
  calc ∑ j, |(((famTerms family X).get j).coefficient : ℝ)| = _ := he
    _ ≤ _ := hr

/-- The atoms' wire counts are at most the limits' wire cap. -/
theorem famAtom_wireCount_le (X : Fin nv) (j : Fin (famTerms family X).length) :
    modeWireCount m (famAtom family X j) ≤ limits.wireCap := by
  unfold famAtom
  rw [castAtom_wireCount]
  exact (family.getSum X).wires_le _ (List.get_mem _ _)

/-- The atoms' description bits are at most the limits' description cap. -/
theorem famAtom_descriptionBits_le (X : Fin nv) (j : Fin (famTerms family X).length) :
    m.descriptionBits (famAtom family X j) ≤ limits.descriptionCap := by
  unfold famAtom
  rw [castAtom_descriptionBits]
  exact (family.getSum X).description_le _ (List.get_mem _ _)

/-- The atoms' charged gates are at most the wire cap. -/
theorem famAtom_gates_length_le (X : Fin nv) (j : Fin (famTerms family X).length) :
    (m.gates (famAtom family X j)).length ≤ limits.wireCap :=
  (gates_length_le_wireCount m _).trans (famAtom_wireCount_le family X j)

/-- The atoms' gates' encoding bits are at most the description cap. -/
theorem famAtom_gate_encodingBits_le (X : Fin nv) (j : Fin (famTerms family X).length) :
    ∀ g ∈ m.gates (famAtom family X j), g.encodingBits ≤ limits.descriptionCap := fun g hg =>
  (gate_encodingBits_le_descriptionBits m _ g hg).trans (famAtom_descriptionBits_le family X j)

end Family

/-! ## The approximation mean is the honest error -/

section Approx
open NearCubicWires.OccurrenceSliceTransport (occurrenceVariable occurrenceLiteral clauseOccurrenceErrorMean_eq_expect_slot)

theorem occurrenceVariable_eq_posVar {n : ℕ} {c : BooleanCircuit n} (pcpp : PointwisePCPP c)
    (i : Fin (2 ^ pcpp.clauseBits)) (j : Fin 2) :
    occurrenceVariable pcpp (i, decide (j = 1)) = posVar pcpp i j := by
  fin_cases j
  · simp [occurrenceVariable, occurrenceLiteral, posVar, posLiteral]
  · simp [occurrenceVariable, occurrenceLiteral, posVar, posLiteral]

theorem sum_slot_eq {M : ℕ} (g : Fin M × Bool → ℝ) :
    ∑ slot, g slot = ∑ i, ∑ j : Fin 2, g (i, decide (j = 1)) := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fintype.sum_bool, Fin.sum_univ_two]
  simp only [Fin.isValue]
  norm_num
  ring

/-- The approximation mean, over clause occurrences and inputs, as an input average of occurrence means. -/
theorem approx_eq_expect {n : ℕ} {c : BooleanCircuit n} (pcpp : PointwisePCPP c)
    (value : BitInput n → Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → ℝ) :
    uMean (fun p : Fin (2 ^ pcpp.clauseBits) × Fin 2 × BitInput n =>
      |value p.2.2 (posVar pcpp p.1 p.2.1) - honestBit pcpp pcpp.honestAuxiliary (posVar pcpp p.1 p.2.1) p.2.2|) =
    𝔼 x : BitInput n, NearCubicWires.VerifierThresholdSeam.clauseOccurrenceErrorMean pcpp (value x)
      (fun j => bitAsReal (pcpp.assignment x (pcpp.honestAuxiliary x) j)) := by
  simp_rw [clauseOccurrenceErrorMean_eq_expect_slot, Finset.expect_eq_sum_div_card, Finset.card_univ]
  have hR : ∀ x : BitInput n, ∑ slot : Fin (2 ^ pcpp.clauseBits) × Bool,
      |value x (occurrenceVariable pcpp slot) -
        bitAsReal (pcpp.assignment x (pcpp.honestAuxiliary x) (occurrenceVariable pcpp slot))| =
      ∑ i : Fin (2 ^ pcpp.clauseBits), ∑ j : Fin 2,
        |value x (posVar pcpp i j) - honestBit pcpp pcpp.honestAuxiliary (posVar pcpp i j) x| := by
    intro x
    rw [sum_slot_eq]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [occurrenceVariable_eq_posVar]
    rfl
  simp only [hR]
  unfold uMean
  rw [← Finset.sum_div, div_div]
  let e : (BitInput n × Fin (2 ^ pcpp.clauseBits) × Fin 2) ≃ (Fin (2 ^ pcpp.clauseBits) × Fin 2 × BitInput n) :=
    { toFun := fun p => (p.2.1, p.2.2, p.1), invFun := fun p => (p.2.2, p.1, p.2.1),
      left_inv := fun _ => rfl, right_inv := fun _ => rfl }
  rw [← Equiv.sum_comp e]
  congr 1
  · simp only [Fintype.sum_prod_type]
    rfl
  · simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
    push_cast
    ring

/-- **The `happrox` mean of `exists_unionAccepts` is base's `honestError`** (the incidence-weighted `L¹` distance of
the guessed values to the honest proof, over clause occurrences and inputs). -/
theorem approx_eq_honestError (source : PointwisePCPPAlgorithm) (r : PCPPRequest source.minimumArity)
    (value : BitInput r.arity → Fin ((source.output r).systematicBits + (source.output r).auxiliaryBits) → ℝ) :
    uMean (fun p : Fin (2 ^ (source.output r).clauseBits) × Fin 2 × BitInput r.arity =>
      |value p.2.2 (posVar (source.output r) p.1 p.2.1) -
        honestBit (source.output r) (source.output r).honestAuxiliary (posVar (source.output r) p.1 p.2.1) p.2.2|) =
    CompetitorSourceAverage.honestError source r value :=
  approx_eq_expect (source.output r) value

end Approx

end NearCubicWires.WireExponent3_5.Transfer
