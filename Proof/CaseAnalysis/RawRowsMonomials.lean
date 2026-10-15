import Proof.CaseAnalysis.RawRowsModes

/-! Raw monomial degrees through the actual masked and powered-walk rows.
Every literal substitution has degree at most one; no cancellation is used. -/
namespace NearCubicWires.RepairSource.CloseoutRawRows
open CanonicalFourfoldRowProgram SupplierPipeline SupplierEstimator
open SupplierListPolynomial SupplierListSchedule SupplierWalkBridge SupplierToeplitz SupplierToeplitzCore
open SupplierWalk SupplierRadix SupplierTouching
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem rawDegree_mono {a b : ℕ} {P : StructuralGF2Polynomial}
    (h : RawMonomialDegreeAtMost a P) (hab : a ≤ b) : RawMonomialDegreeAtMost b P :=
  fun m hm => (h m hm).trans hab

theorem rawDegree_add {d : ℕ} {P Q : StructuralGF2Polynomial}
    (hP : RawMonomialDegreeAtMost d P) (hQ : RawMonomialDegreeAtMost d Q) :
    RawMonomialDegreeAtMost d (structuralGF2Add P Q) := by
  intro m hm
  exact (List.mem_append.mp hm).elim (hP m) (hQ m)

theorem rawDegree_one (d : ℕ) : RawMonomialDegreeAtMost d structuralGF2One := by
  intro m hm
  simp only [structuralGF2One,List.mem_singleton] at hm
  subst m
  simp

theorem rawDegree_not {d : ℕ} {P : StructuralGF2Polynomial}
    (h : RawMonomialDegreeAtMost d P) : RawMonomialDegreeAtMost d (structuralGF2Not P) :=
  rawDegree_add (rawDegree_one d) h

theorem rawDegree_variable (code : ℕ) : RawMonomialDegreeAtMost 1 (structuralGF2Variable code) := by
  intro m hm
  simp only [structuralGF2Variable,List.mem_singleton] at hm
  subst m
  rfl

theorem rawDegree_product (a : ℕ) (ps : List StructuralGF2Polynomial)
    (hp : ∀ P ∈ ps, RawMonomialDegreeAtMost a P) :
    RawMonomialDegreeAtMost (a*ps.length) (structuralGF2Product ps) := by
  induction ps with
  | nil => exact rawDegree_one _
  | cons P ps ih =>
    have h := rawDegree_mul (hp P (by simp)) (ih (fun Q hQ => hp Q (by simp [hQ])))
    simpa only [structuralGF2Product,List.foldr_cons,List.length_cons,
      Nat.mul_add,Nat.mul_one,Nat.add_comm] using h

theorem rawDegree_substitute {d : ℕ} (atom : ℕ → StructuralGF2Polynomial)
    (ha : ∀ code, RawMonomialDegreeAtMost 1 (atom code)) (P : StructuralGF2Polynomial)
    (hP : RawMonomialDegreeAtMost d P) :
    RawMonomialDegreeAtMost d (structuralGF2Substitute atom P) := by
  induction P with
  | nil => exact rawDegree_zero _
  | cons m P ih =>
    apply rawDegree_add
    · have hm := rawDegree_product 1 (m.map atom) (by
        intro Q hQ
        obtain ⟨code,_,rfl⟩ := List.mem_map.mp hQ
        exact ha code)
      simp only [List.length_map,Nat.one_mul] at hm
      exact rawDegree_mono hm (hP m (by simp))
    · exact ih (fun n hn => hP n (by simp [hn]))

theorem rawDegree_parity {n d : ℕ} (ps : Fin n → StructuralGF2Polynomial)
    (hp : ∀ i, RawMonomialDegreeAtMost d (ps i)) :
    RawMonomialDegreeAtMost d (structuralGF2FinParity ps) := by
  induction n with
  | zero => exact rawDegree_zero _
  | succ n ih => exact rawDegree_add (hp 0) (ih _ (fun i => hp i.succ))

theorem rawDegree_conjunction {n d : ℕ} (ps : Fin n → StructuralGF2Polynomial)
    (hp : ∀ i, RawMonomialDegreeAtMost d (ps i)) :
    RawMonomialDegreeAtMost (n*d) (structuralGF2FiniteConjunction ps) := by
  have h := rawDegree_product d (List.ofFn ps) (by
    intro P hP
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hP
    exact hp i)
  simpa only [structuralGF2FiniteConjunction,List.length_ofFn,Nat.mul_comm] using h

theorem rawDegree_literal {rank depth population : ℕ}
    (mask : Finset (Fin population)) (label : Fin population → BinaryVector rank)
    (seed : ToeplitzSeed rank) (code : ℕ) :
    RawMonomialDegreeAtMost 1 (structuralListLiteralAtom (depth := depth) mask label seed code) := by
  have hmask (i : Fin population) : RawMonomialDegreeAtMost 1 (structuralMaskedCoordinate mask i) := by
    unfold structuralMaskedCoordinate
    split
    · exact rawDegree_variable _
    · exact rawDegree_zero _
  unfold structuralListLiteralAtom
  split
  · exact rawDegree_zero _
  · split
    · exact hmask _
    · exact rawDegree_zero _
  · split
    · split
      · exact hmask _
      · exact rawDegree_zero _
    · split
      · exact rawDegree_not (hmask _)
      · exact rawDegree_zero _

theorem rawDegree_masked {rank depth population : ℕ}
    (mask : Finset (Fin population)) (label : Fin population → BinaryVector rank)
    (seed : ToeplitzSeed rank) (window : Fin depth → ℕ) (terminal : ℕ)
    (candidate : Fin (population+1)) :
    RawMonomialDegreeAtMost (structuralListCoordinateRawDegree depth window terminal)
      (structuralMaskedListCoordinate mask label seed window terminal candidate) :=
  rawDegree_substitute _ (rawDegree_literal mask label seed) _
    (rawDegree_structuralListPolynomialVector label seed window terminal candidate)

theorem rawDegree_selector {n d : ℕ} (ps : Fin n → StructuralGF2Polynomial)
    (target : BitInput n) (hp : ∀ i, RawMonomialDegreeAtMost d (ps i)) :
    RawMonomialDegreeAtMost (n*d) (structuralGF2BooleanSelector ps target) := by
  have h := rawDegree_product d
    (List.ofFn (fun i => if target i = true then ps i else structuralGF2Not (ps i))) (by
      intro P hP
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hP
      split
      · exact hp i
      · exact rawDegree_not (hp i))
  simpa only [structuralGF2BooleanSelector,List.length_ofFn,Nat.mul_comm] using h

theorem rawDegree_majority {n d : ℕ} (ps : Fin n → StructuralGF2Polynomial)
    (hp : ∀ i, RawMonomialDegreeAtMost d (ps i)) :
    RawMonomialDegreeAtMost (n*d) (structuralGF2BitMajority ps) := by
  unfold structuralGF2BitMajority structuralGF2TruthTable
  apply rawDegree_parity
  intro code
  split
  · exact rawDegree_selector ps _ hp
  · exact rawDegree_zero _

theorem rawDegree_walk {rank depth population t : ℕ}
    (mask : Finset (Fin population)) (label : Fin population → BinaryVector rank)
    (window : Fin depth → ℕ) (terminal : ℕ)
    (seed : MargulisWalkSample (2 ^ toeplitzWalkSideBits rank) t)
    (candidate : Fin (population+1)) :
    RawMonomialDegreeAtMost (t*structuralListCoordinateRawDegree depth window terminal)
      (structuralMaskedWalkListCoordinate mask label window terminal seed candidate) :=
  rawDegree_majority _ (fun _ => rawDegree_masked mask label _ window terminal candidate)

def coordinateDegree {q : ℕ} (gs : List (SupportedNormalizedGate q)) (L den : ℕ) : ℕ :=
  let active := touchingCost (occurrenceSupport gs) (normalizedLiveSet gs L)
  canonicalWalkLength den * structuralListCoordinateRawDegree (canonicalGradedDepth active)
    (executableGradedWindow active) gradedTerminalWindow

theorem rawDegree_coordinate {q : ℕ} (gs : List (SupportedNormalizedGate q)) (L den : ℕ)
    (mask : Finset (Fin gs.length)) (seed : NormalizedOccurrenceListSeed gs L den)
    (candidate : Fin (gs.length+1)) :
    RawMonomialDegreeAtMost (coordinateDegree gs L den)
      (structuralCanonicalOccurrenceListCoordinate gs L den mask seed candidate) :=
  rawDegree_walk mask _ _ _ seed candidate

end
end NearCubicWires.RepairSource.CloseoutRawRows
