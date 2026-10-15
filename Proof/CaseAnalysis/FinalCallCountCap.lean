import Proof.CaseAnalysis.FinalCallCountMajorant

namespace NearCubicWires.RepairOrdinary.CloseoutFinalC10CallCountCap

open Finset
open NearCubicWires
open NearCubicWires.ComponentwisePolynomial
open NearCubicWires.SourceInterfaces
open NearCubicWires.SupplierPipeline
open NearCubicWires.ComponentwiseBranchExtraction
open NearCubicWires.RepairOrdinary.CloseoutFinalC10Exactness
open NearCubicWires.RepairOrdinary.CloseoutFinalC10SupplierCalls
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerDockSeam
open NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorCoefficients.Stream (Entry)

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-! ## §1 The monomial count of the polynomial algebra -/

variable {Atom : Type}

@[simp] theorem weaken_length {d e : ℕ} (p : CircuitPolynomial Atom d) (h : d ≤ e) :
    (p.weaken h).monomials.length = p.monomials.length := by
  simp [CircuitPolynomial.weaken]

@[simp] theorem scale_length {d : ℕ} (p : CircuitPolynomial Atom d) (c : ℚ) :
    (p.scale c).monomials.length = p.monomials.length := by
  simp [CircuitPolynomial.scale]

@[simp] theorem add_length {d : ℕ} (p q : CircuitPolynomial Atom d) :
    (p.add q).monomials.length = p.monomials.length + q.monomials.length := by
  simp [CircuitPolynomial.add]

@[simp] theorem mul_length {d e : ℕ} (p : CircuitPolynomial Atom d)
    (q : CircuitPolynomial Atom e) :
    (p.mul q).monomials.length = p.monomials.length * q.monomials.length := by
  simp [CircuitPolynomial.mul, List.length_flatMap]

@[simp] theorem constant_length (d : ℕ) (c : ℚ) :
    (CircuitPolynomial.constant (Circuit := Atom) d c).monomials.length = 1 := rfl

@[simp] theorem atom_length (a : Atom) : (atomPolynomial a).monomials.length = 1 := rfl

/-! ## §2 The site majorant -/

/-- A majorant for one site's monomial count, from a bound `L` on the coordinate
polynomials.  Built from `L` alone. -/
def siteCap (L : ℕ) : ℕ := 16 * (L + 1) ^ 4

theorem pow_le_cap (L : ℕ) (k : ℕ) (hk : k ≤ 4) : L ^ k ≤ (L + 1) ^ 4 :=
  le_trans (Nat.pow_le_pow_left (Nat.le_succ L) k) (Nat.pow_le_pow_right (Nat.succ_le_succ (Nat.zero_le L)) hk)

theorem succ_le_cap (L : ℕ) : L + 1 ≤ (L + 1) ^ 4 := by
  simpa using Nat.pow_le_pow_right (Nat.succ_le_succ (Nat.zero_le L)) (by omega : 1 ≤ 4)

theorem sq_succ_le_cap (L : ℕ) : (L + 1) ^ 2 ≤ (L + 1) ^ 4 :=
  Nat.pow_le_pow_right (Nat.succ_le_succ (Nat.zero_le L)) (by omega)

theorem literal_length_le (L : ℕ) (negative : Bool) (linear : CircuitPolynomial Atom 1)
    (hL : linear.monomials.length ≤ L) :
    (literalPolynomial negative linear).monomials.length ≤ L + 1 := by
  unfold literalPolynomial
  split
  · simp only [add_length, scale_length, constant_length]
    omega
  · omega

theorem systematic_length_le (L : ℕ) (a : Atom) (linear : CircuitPolynomial Atom 1)
    (hL : linear.monomials.length ≤ L) :
    (systematicValidityPolynomial a linear).monomials.length ≤ 1 + L + L ^ 2 := by
  have hsq : linear.monomials.length * linear.monomials.length ≤ L ^ 2 := by
    have := Nat.mul_le_mul hL hL
    simpa [pow_two] using this
  have hmul : (linear.mul linear).monomials.length ≤ L ^ 2 := by
    simp only [mul_length]; exact hsq
  have hone : ((atomPolynomial a).mul linear).monomials.length ≤ L := by
    simp only [mul_length, atom_length, one_mul]; exact hL
  have hone' : (atomPolynomial a).monomials.length * linear.monomials.length ≤ L := by
    rw [atom_length, one_mul]; exact hL
  unfold systematicValidityPolynomial
  simp only [add_length, scale_length, weaken_length, atom_length]
  omega

theorem auxiliary_length_le (L : ℕ) (linear : CircuitPolynomial Atom 1)
    (hL : linear.monomials.length ≤ L) :
    (auxiliaryValidityPolynomial linear).monomials.length ≤ L ^ 2 + (L ^ 3 + L ^ 4) := by
  have h2 : linear.monomials.length * linear.monomials.length ≤ L ^ 2 := by
    have := Nat.mul_le_mul hL hL
    simpa [pow_two] using this
  have h3 : linear.monomials.length * linear.monomials.length * linear.monomials.length
      ≤ L ^ 3 := by
    have := Nat.mul_le_mul (Nat.mul_le_mul hL hL) hL
    calc linear.monomials.length * linear.monomials.length * linear.monomials.length
        ≤ L * L * L := this
      _ = L ^ 3 := by ring
  have h4 : linear.monomials.length * linear.monomials.length *
      (linear.monomials.length * linear.monomials.length) ≤ L ^ 4 := by
    have := Nat.mul_le_mul (Nat.mul_le_mul hL hL) (Nat.mul_le_mul hL hL)
    calc linear.monomials.length * linear.monomials.length *
          (linear.monomials.length * linear.monomials.length)
        ≤ L * L * (L * L) := this
      _ = L ^ 4 := by ring
  have m2 : (linear.mul linear).monomials.length ≤ L ^ 2 := by
    simp only [mul_length]; exact h2
  have m3 : ((linear.mul linear).mul linear).monomials.length ≤ L ^ 3 := by
    simp only [mul_length]; exact h3
  have m4 : ((linear.mul linear).mul (linear.mul linear)).monomials.length ≤ L ^ 4 := by
    simp only [mul_length]; exact h4
  unfold auxiliaryValidityPolynomial
  simp only [add_length, scale_length, weaken_length]
  omega

theorem penalty_le (L : ℕ) (n : ℕ) {circuit : BooleanCircuit n} (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom)
    (hL : ∀ i, (coordinate i).monomials.length ≤ L)
    (j : Fin (pcpp.systematicBits + pcpp.auxiliaryBits)) :
    (coordinatePenalty pcpp coordinate systematicAtom j).monomials.length ≤
      1 + L + L ^ 2 + L ^ 3 + L ^ 4 := by
  unfold coordinatePenalty
  refine Fin.addCases (fun index => ?_) (fun index => ?_) j
  · rw [Fin.addCases_left]
    have h := systematic_length_le L (systematicAtom index)
      (coordinate (Fin.castAdd pcpp.auxiliaryBits index)) (hL _)
    simp only [weaken_length]
    omega
  · rw [Fin.addCases_right]
    have h := auxiliary_length_le L (coordinate (Fin.natAdd pcpp.systematicBits index)) (hL _)
    omega

theorem site_le (L : ℕ) (n : ℕ) {circuit : BooleanCircuit n} (pcpp : PointwisePCPP circuit)
    (ph : CloseoutRowsOriginalSchedule.Phase)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom)
    (hL : ∀ i, (coordinate i).monomials.length ≤ L)
    (i : Fin (2 ^ pcpp.clauseBits)) :
    (sitePolynomial ph pcpp coordinate systematicAtom i).monomials.length ≤ siteCap L := by
  have c0 : (1 : ℕ) ≤ (L + 1) ^ 4 := le_trans (by omega) (succ_le_cap L)
  have c1 : L ≤ (L + 1) ^ 4 := le_trans (Nat.le_succ L) (succ_le_cap L)
  have c2 : L ^ 2 ≤ (L + 1) ^ 4 := pow_le_cap L 2 (by omega)
  have c3 : L ^ 3 ≤ (L + 1) ^ 4 := pow_le_cap L 3 (by omega)
  have c4 : L ^ 4 ≤ (L + 1) ^ 4 := pow_le_cap L 4 (by omega)
  have csq : (L + 1) * (L + 1) ≤ (L + 1) ^ 4 := by
    have := sq_succ_le_cap L
    simpa [pow_two] using this
  unfold siteCap
  cases ph with
  | penalty =>
    have h1 := penalty_le L n pcpp coordinate systematicAtom hL (literalIndex (pcpp.clauses i).left)
    have h2 := penalty_le L n pcpp coordinate systematicAtom hL (literalIndex (pcpp.clauses i).right)
    unfold sitePolynomial penaltySite
    simp only [scale_length, add_length]
    omega
  | moment =>
    have hm := hL (literalIndex (pcpp.clauses i).left)
    have hsq : (coordinate (literalIndex (pcpp.clauses i).left)).monomials.length *
        (coordinate (literalIndex (pcpp.clauses i).left)).monomials.length ≤ L ^ 2 := by
      have := Nat.mul_le_mul hm hm
      simpa [pow_two] using this
    have hmul : ((coordinate (literalIndex (pcpp.clauses i).left)).mul
        (coordinate (literalIndex (pcpp.clauses i).left))).monomials.length ≤ L ^ 2 := by
      simp only [mul_length]; exact hsq
    unfold sitePolynomial momentSite secondMomentPolynomial
    simp only [weaken_length]
    omega
  | clause =>
    have hl := literal_length_le L (literalNegated (pcpp.clauses i).left)
      (coordinate (literalIndex (pcpp.clauses i).left)) (hL _)
    have hr := literal_length_le L (literalNegated (pcpp.clauses i).right)
      (coordinate (literalIndex (pcpp.clauses i).right)) (hL _)
    have hprod : (literalPolynomial (literalNegated (pcpp.clauses i).left)
          (coordinate (literalIndex (pcpp.clauses i).left))).monomials.length *
        (literalPolynomial (literalNegated (pcpp.clauses i).right)
          (coordinate (literalIndex (pcpp.clauses i).right))).monomials.length ≤
        (L + 1) * (L + 1) := Nat.mul_le_mul hl hr
    have hmul : ((literalPolynomial (literalNegated (pcpp.clauses i).left)
          (coordinate (literalIndex (pcpp.clauses i).left))).mul
        (literalPolynomial (literalNegated (pcpp.clauses i).right)
          (coordinate (literalIndex (pcpp.clauses i).right)))).monomials.length ≤
        (L + 1) * (L + 1) := by
      simp only [mul_length]; exact hprod
    unfold sitePolynomial clauseSite clausePolynomial
    simp only [weaken_length, add_length, scale_length]
    omega

/-! ## §3 The clause-address loop -/

theorem length_flatMap_le {α β : Type} (l : List α) (f : α → List β) (M : ℕ)
    (h : ∀ a ∈ l, (f a).length ≤ M) : (l.flatMap f).length ≤ l.length * M := by
  induction l with
  | nil => simp
  | cons a t ih =>
    have ha : (f a).length ≤ M := h a (by simp)
    have ht : (t.flatMap f).length ≤ t.length * M :=
      ih (fun b hb => h b (by simp [hb]))
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    calc (f a).length + (t.flatMap f).length ≤ M + t.length * M := Nat.add_le_add ha ht
      _ = (t.length + 1) * M := by ring

/-- **The call count is capped by the coordinate degree and P3a's site count.**
`L` bounds the coordinate polynomials' monomial count; the cap is
`2 ^ pcpp.clauseBits * siteCap L`, with no constant beyond those two. -/
theorem phaseRecords_length_le (L : ℕ) (n : ℕ) {circuit : BooleanCircuit n}
    (pcpp : PointwisePCPP circuit) (answer : List Atom → ℕ) (denominator : ℕ)
    (ph : CloseoutRowsOriginalSchedule.Phase)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom)
    (hL : ∀ i, (coordinate i).monomials.length ≤ L) :
    (phaseRecords answer denominator ph pcpp coordinate systematicAtom).length ≤
      2 ^ pcpp.clauseBits * siteCap L := by
  unfold phaseRecords
  have hsite : ∀ address ∈ (univ : Finset (Fin (2 ^ pcpp.clauseBits))).toList,
      (siteRecords answer denominator ph pcpp coordinate systematicAtom address).length ≤
        siteCap L := by
    intro address _
    unfold siteRecords callRecords siteCalls
    simp only [List.length_map, scale_length]
    exact site_le L n pcpp ph coordinate systematicAtom hL address
  have hcard : (univ : Finset (Fin (2 ^ pcpp.clauseBits))).toList.length = 2 ^ pcpp.clauseBits := by
    rw [Finset.length_toList, Finset.card_univ, Fintype.card_fin]
  have := length_flatMap_le (univ : Finset (Fin (2 ^ pcpp.clauseBits))).toList
    (siteRecords answer denominator ph pcpp coordinate systematicAtom) (siteCap L) hsite
  rw [hcard] at this
  exact this

end NearCubicWires.RepairOrdinary.CloseoutFinalC10CallCountCap
