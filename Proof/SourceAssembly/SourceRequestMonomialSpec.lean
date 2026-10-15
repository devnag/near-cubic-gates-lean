import Proof.SourceAssembly.SourceRequestFactorLoop

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.SourceRequest.MonomialSpec
open NearCubicWires NearCubicWires.ComponentwisePolynomial

section lists
variable {α β : Type}

/-- The `m`-th element of a lexicographic product list whose inner lists all have length `|R|`. -/
theorem get_flatMap_map (L : List α) (R : List β) {γ : Type} (g : α → β → γ) (m : Nat) :
    (L.flatMap (fun l => R.map (g l)))[m]? =
      if 0 < R.length then (L[m / R.length]?).bind (fun l => (R[m % R.length]?).map (g l)) else none := by
  induction L generalizing m with
  | nil =>
    split
    · simp
    · simp
  | cons l L ih =>
    rw [List.flatMap_cons]
    by_cases hR : 0 < R.length
    · rw [if_pos hR]
      by_cases hm : m < R.length
      · rw [List.getElem?_append_left (by rw [List.length_map]; exact hm)]
        rw [Nat.div_eq_of_lt hm, Nat.mod_eq_of_lt hm]
        simp [List.getElem?_map]
      · have hm' : R.length ≤ m := by omega
        rw [List.getElem?_append_right (by rw [List.length_map]; exact hm'), List.length_map, ih, if_pos hR]
        have hd : m / R.length = (m - R.length) / R.length + 1 := by
          rw [← Nat.sub_add_cancel hm', Nat.add_div_right _ hR, Nat.add_sub_cancel]
        have hmod : m % R.length = (m - R.length) % R.length := by
          conv_lhs => rw [← Nat.sub_add_cancel hm']
          exact Nat.add_mod_right _ _
        rw [hd, hmod]
        simp
    · rw [if_neg hR]
      have h0 : R = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst h0
      simp only [List.map_nil, List.nil_append]
      have := ih m
      rw [if_neg hR] at this
      exact this

theorem length_flatMap_map (L : List α) (R : List β) {γ : Type} (g : α → β → γ) :
    (L.flatMap (fun l => R.map (g l))).length = L.length * R.length := by
  induction L with
  | nil => simp
  | cons l L ih =>
    rw [List.flatMap_cons, List.length_append, List.length_map, ih, List.length_cons, Nat.succ_mul]
    omega

end lists

section poly
variable {Atom : Type}

theorem get_add {d : Nat} (A B : CircuitPolynomial Atom d) (m : Nat) :
    (A.add B).monomials[m]? =
      if m < A.monomials.length then A.monomials[m]? else B.monomials[m - A.monomials.length]? := by
  show (A.monomials ++ B.monomials)[m]? = _
  split
  · rename_i h
    exact List.getElem?_append_left h
  · rename_i h
    exact List.getElem?_append_right (by omega)

theorem len_add {d : Nat} (A B : CircuitPolynomial Atom d) :
    (A.add B).monomials.length = A.monomials.length + B.monomials.length :=
  List.length_append

theorem get_scale {d : Nat} (q : ℚ) (A : CircuitPolynomial Atom d) (m : Nat) :
    (A.scale q).monomials[m]? = (A.monomials[m]?).map (CircuitMonomial.scale q) :=
  List.getElem?_map

theorem len_scale {d : Nat} (q : ℚ) (A : CircuitPolynomial Atom d) :
    (A.scale q).monomials.length = A.monomials.length :=
  List.length_map _

theorem get_weaken {d e : Nat} (h : d ≤ e) (A : CircuitPolynomial Atom d) (m : Nat) :
    (A.weaken h).monomials[m]? = (A.monomials[m]?).map (CircuitMonomial.weaken h) :=
  List.getElem?_map

theorem len_weaken {d e : Nat} (h : d ≤ e) (A : CircuitPolynomial Atom d) :
    (A.weaken h).monomials.length = A.monomials.length :=
  List.length_map _

theorem get_mul {d e : Nat} (A : CircuitPolynomial Atom d) (B : CircuitPolynomial Atom e) (m : Nat) :
    (A.mul B).monomials[m]? =
      if 0 < B.monomials.length then
        (A.monomials[m / B.monomials.length]?).bind
          (fun a => (B.monomials[m % B.monomials.length]?).map (a.mul ·))
      else none :=
  get_flatMap_map A.monomials B.monomials (fun a b => a.mul b) m

theorem len_mul {d e : Nat} (A : CircuitPolynomial Atom d) (B : CircuitPolynomial Atom e) :
    (A.mul B).monomials.length = A.monomials.length * B.monomials.length :=
  length_flatMap_map A.monomials B.monomials (fun a b => a.mul b)

theorem mul_factors {d e : Nat} (a : CircuitMonomial Atom d) (b : CircuitMonomial Atom e) :
    (a.mul b).factors = a.factors ++ b.factors := rfl

theorem mul_coefficient {d e : Nat} (a : CircuitMonomial Atom d) (b : CircuitMonomial Atom e) :
    (a.mul b).coefficient = a.coefficient * b.coefficient := rfl

theorem scale_factors {d : Nat} (q : ℚ) (a : CircuitMonomial Atom d) :
    (a.scale q).factors = a.factors := rfl

theorem scale_coefficient {d : Nat} (q : ℚ) (a : CircuitMonomial Atom d) :
    (a.scale q).coefficient = q * a.coefficient := rfl

theorem weaken_factors {d e : Nat} (h : d ≤ e) (a : CircuitMonomial Atom d) :
    (a.weaken h).factors = a.factors := rfl

theorem weaken_coefficient {d e : Nat} (h : d ≤ e) (a : CircuitMonomial Atom d) :
    (a.weaken h).coefficient = a.coefficient := rfl

end poly

/-! ## The site's monomial count `N` (what `nT` receives), per phase

`N` depends only on the two queried coordinates' term counts `JL`, `JR`, the two literal signs (clause phase) and
whether each literal index is systematic (penalty phase: `coordinatePenalty` is `Fin.addCases`). -/

section site
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.CloseoutFinalC10Exactness
open NearCubicWires.ComponentwiseBranchExtraction NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule
open NearCubicWires.SourceInterfaces NearCubicWires.LocalBitMultitape

/-- One side's validity-block count: systematic `1 + J + J²`, auxiliary `J² + J³ + J⁴`. -/
def penLen (sys : Bool) (J : Nat) : Nat :=
  if sys then 1 + (J + J * J) else J * J + (J * J * J + J * J * (J * J))

/-- One literal polynomial's count: negated `1 + J` (the constant `1`), positive `J`. -/
def litLen (neg : Bool) (J : Nat) : Nat := if neg then 1 + J else J

/-- **The site's monomial count.** -/
def siteLen : Phase → Bool → Bool → Bool → Bool → Nat → Nat → Nat
  | .penalty, sL, sR, _, _, JL, JR => penLen sL JL + penLen sR JR
  | .moment, _, _, _, _, JL, _ => JL * JL
  | .clause, _, _, nL, nR, JL, JR => litLen nL JL + (litLen nR JR + litLen nL JL * litLen nR JR)

variable {Atom : Type} {n : Nat} {circuit : BooleanCircuit n}

theorem len_literal (neg : Bool) (T : CircuitPolynomial Atom 1) :
    (literalPolynomial neg T).monomials.length = litLen neg T.monomials.length := by
  cases neg
  · rfl
  · show (CircuitPolynomial.add (CircuitPolynomial.constant 1 1) (T.scale (-1))).monomials.length = _
    rw [len_add, len_scale]
    rfl

theorem len_systematicValidity (e : Atom) (T : CircuitPolynomial Atom 1) :
    (systematicValidityPolynomial e T).monomials.length = penLen true T.monomials.length := by
  unfold systematicValidityPolynomial penLen
  simp only [len_add, len_weaken, len_scale, if_true]
  rw [len_mul, len_mul]
  simp only [atomPolynomial, List.length_singleton]
  ring

theorem len_auxiliaryValidity (T : CircuitPolynomial Atom 1) :
    (auxiliaryValidityPolynomial T).monomials.length = penLen false T.monomials.length := by
  unfold auxiliaryValidityPolynomial penLen
  simp only [len_add, len_weaken, len_scale, len_mul, Bool.false_eq_true, if_false]
  rw [len_mul, len_mul]

theorem len_secondMoment (T : CircuitPolynomial Atom 1) :
    (secondMomentPolynomial T).monomials.length = T.monomials.length * T.monomials.length :=
  len_mul T T

theorem len_clause (nL nR : Bool) (TL TR : CircuitPolynomial Atom 1) :
    (clausePolynomial nL nR TL TR).monomials.length =
      litLen nL TL.monomials.length + (litLen nR TR.monomials.length +
        litLen nL TL.monomials.length * litLen nR TR.monomials.length) := by
  unfold clausePolynomial
  simp only [len_add, len_weaken, len_scale, len_literal]
  rw [len_mul, len_literal, len_literal]

theorem len_coordinatePenalty (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial Atom 1)
    (sa : Fin pcpp.systematicBits → Atom) (j : Fin (pcpp.systematicBits + pcpp.auxiliaryBits)) :
    (coordinatePenalty pcpp coordinate sa j).monomials.length =
      penLen (decide (j.val < pcpp.systematicBits)) (coordinate j).monomials.length := by
  cases j using Fin.addCases with
  | left i =>
    unfold coordinatePenalty
    rw [Fin.addCases_left, len_weaken, len_systematicValidity]
    simp [Fin.val_castAdd, i.isLt]
  | right i =>
    unfold coordinatePenalty
    rw [Fin.addCases_right, len_auxiliaryValidity]
    simp [Fin.val_natAdd]

/-- **`N` from the two queried coordinates' term counts** (`FactorLoop.monomials` is `siteCalls`' list). -/
theorem monomials_len {pcpp : PointwisePCPP circuit}
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) →
      CircuitPolynomial (RepairSource.CloseoutFinal.C10TotalDecode.Atom pcpp) 1)
    (ph : Phase) (ci : Fin (2 ^ pcpp.clauseBits)) :
    (FactorLoop.monomials coordinate ph ci).length =
      siteLen ph (decide ((literalIndex (pcpp.clauses ci).left).val < pcpp.systematicBits))
        (decide ((literalIndex (pcpp.clauses ci).right).val < pcpp.systematicBits))
        (literalNegated (pcpp.clauses ci).left) (literalNegated (pcpp.clauses ci).right)
        (coordinate (literalIndex (pcpp.clauses ci).left)).monomials.length
        (coordinate (literalIndex (pcpp.clauses ci).right)).monomials.length := by
  unfold FactorLoop.monomials CloseoutFinalC10SupplierCalls.siteCalls
  rw [len_scale]
  cases ph with
  | penalty =>
    show (CircuitPolynomial.scale _ (CircuitPolynomial.add _ _)).monomials.length = _
    rw [len_scale, len_add, len_coordinatePenalty, len_coordinatePenalty]
    rfl
  | moment =>
    show (CircuitPolynomial.weaken _ _).monomials.length = _
    rw [len_weaken, len_secondMoment]
    rfl
  | clause =>
    show (CircuitPolynomial.weaken _ _).monomials.length = _
    rw [len_weaken, len_clause]
    rfl

end site

end NearCubicWires.SourceRequest.MonomialSpec

