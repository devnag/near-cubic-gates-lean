import Proof.Foundations.ComponentwiseTransfer

/-!
# Restriction closure for the two physical wire families

Padding arguments must restrict actual threshold circuits, not merely their
truth tables.  This file fixes the canonical `Fin core ⊕ Fin padding` split,
absorbs the frozen score into each bottom threshold, and proves that neither
semantics nor the retained-support wire charge increases.
-/

open Finset
open scoped BigOperators

namespace NearCubicWires.CircuitRestriction

open NearCubicWires
open NearCubicWires.ComponentwiseTransfer
open NearCubicWires.RecoveryPipeline
open NearCubicWires.SourceInterfaces

def coreIndex {core target : ℕ} (hcore : core ≤ target)
    (index : Fin core) : Fin target :=
  finSplitEquiv hcore (.inl index)

def paddingIndex {core target : ℕ} (hcore : core ≤ target)
    (index : Fin (target - core)) : Fin target :=
  finSplitEquiv hcore (.inr index)

theorem sum_split {core target : ℕ} (hcore : core ≤ target)
    (value : Fin target → ℝ) :
    (∑ index : Fin target, value index) =
      (∑ index : Fin core, value (coreIndex hcore index)) +
      ∑ index : Fin (target - core), value (paddingIndex hcore index) := by
  have hsum := Equiv.sum_comp (finSplitEquiv hcore) value
  simpa [coreIndex, paddingIndex] using hsum.symm

noncomputable def restrictRealThresholdGate {core target : ℕ}
    (gate : RealThresholdGate target) (hcore : core ≤ target)
    (padding : BitInput (target - core)) : RealThresholdGate core where
  weight index := gate.weight (coreIndex hcore index)
  threshold := gate.threshold -
    ∑ index, gate.weight (paddingIndex hcore index) *
      bitAsReal (padding index)
  support := Finset.univ.filter fun index =>
    gate.weight (coreIndex hcore index) ≠ 0
  mem_support_iff := by simp

theorem restrictRealThresholdGate_eval {core target : ℕ}
    (gate : RealThresholdGate target) (hcore : core ≤ target)
    (padding : BitInput (target - core)) (input : BitInput core) :
    (restrictRealThresholdGate gate hcore padding).eval input =
      gate.eval (fun index =>
        Sum.elim input padding ((finSplitEquiv hcore).symm index)) := by
  unfold RealThresholdGate.eval
  apply decide_eq_decide.mpr
  let combined : BitInput target := fun index =>
    Sum.elim input padding ((finSplitEquiv hcore).symm index)
  have hcoreValue (index : Fin core) :
      combined (coreIndex hcore index) = input index := by
    simp [combined, coreIndex]
  have hpaddingValue (index : Fin (target - core)) :
      combined (paddingIndex hcore index) = padding index := by
    simp [combined, paddingIndex]
  have hsum :
      (∑ index : Fin target,
          gate.weight index * bitAsReal (combined index)) =
        (∑ index : Fin core,
          gate.weight (coreIndex hcore index) * bitAsReal (input index)) +
        ∑ index : Fin (target - core),
          gate.weight (paddingIndex hcore index) *
            bitAsReal (padding index) := by
    rw [sum_split hcore]
    congr 1
    · apply Finset.sum_congr rfl
      intro index _
      rw [hcoreValue]
    · apply Finset.sum_congr rfl
      intro index _
      rw [hpaddingValue]
  change
    gate.threshold -
          (∑ index : Fin (target - core),
            gate.weight (paddingIndex hcore index) *
              bitAsReal (padding index)) ≤
        (∑ index : Fin core,
          gate.weight (coreIndex hcore index) * bitAsReal (input index)) ↔
      gate.threshold ≤
        ∑ index : Fin target,
          gate.weight index * bitAsReal (combined index)
  rw [hsum]
  constructor <;> intro hypothesis <;> linarith

theorem restrictRealThresholdGate_support_card_le {core target : ℕ}
    (gate : RealThresholdGate target) (hcore : core ≤ target)
    (padding : BitInput (target - core)) :
    (restrictRealThresholdGate gate hcore padding).support.card ≤
      gate.support.card := by
  classical
  let restricted := restrictRealThresholdGate gate hcore padding
  let embed : Fin core → Fin target := coreIndex hcore
  have hinjective : Function.Injective embed :=
    (finSplitEquiv hcore).injective.comp Sum.inl_injective
  have hsubset : restricted.support.image embed ⊆ gate.support := by
    intro index hindex
    rcases Finset.mem_image.mp hindex with ⟨source, hsource, rfl⟩
    have hnonzero :
        gate.weight (coreIndex hcore source) ≠ 0 := by
      simpa [restricted, restrictRealThresholdGate] using
        (Finset.mem_filter.mp hsource).2
    exact (gate.mem_support_iff _).2 hnonzero
  calc
    restricted.support.card =
        (restricted.support.image embed).card := by
      exact (Finset.card_image_of_injective _ hinjective).symm
    _ ≤ gate.support.card := Finset.card_le_card hsubset

noncomputable def restrictSymmetricCircuit {core target : ℕ}
    (circuit : SymmetricThresholdCircuit target) (hcore : core ≤ target)
    (padding : BitInput (target - core)) :
    SymmetricThresholdCircuit core where
  bottomCount := circuit.bottomCount
  bottom index :=
    restrictRealThresholdGate (circuit.bottom index) hcore padding
  top := circuit.top

theorem restrictSymmetricCircuit_eval {core target : ℕ}
    (circuit : SymmetricThresholdCircuit target) (hcore : core ≤ target)
    (padding : BitInput (target - core)) (input : BitInput core) :
    (restrictSymmetricCircuit circuit hcore padding).eval input =
      restrictTarget circuit.eval hcore padding input := by
  change
    circuit.top
        ((Finset.univ.filter fun index =>
          (restrictRealThresholdGate
            (circuit.bottom index) hcore padding).eval input).card) =
      circuit.top
        ((Finset.univ.filter fun index =>
          (circuit.bottom index).eval
            (fun targetIndex =>
              Sum.elim input padding
                ((finSplitEquiv hcore).symm targetIndex))).card)
  apply congrArg circuit.top
  apply congrArg Finset.card
  ext index
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [restrictRealThresholdGate_eval]

theorem restrictSymmetricCircuit_wireCount_le {core target : ℕ}
    (circuit : SymmetricThresholdCircuit target) (hcore : core ≤ target)
    (padding : BitInput (target - core)) :
    (restrictSymmetricCircuit circuit hcore padding).wireCount ≤
      circuit.wireCount := by
  unfold SymmetricThresholdCircuit.wireCount restrictSymmetricCircuit
  apply Finset.sum_le_sum
  intro index _
  exact Nat.add_le_add_right
    (restrictRealThresholdGate_support_card_le
      (circuit.bottom index) hcore padding) 1

noncomputable def restrictThresholdCircuit {core target : ℕ}
    (circuit : ThresholdThresholdCircuit target) (hcore : core ≤ target)
    (padding : BitInput (target - core)) :
    ThresholdThresholdCircuit core where
  bottomCount := circuit.bottomCount
  bottom index :=
    restrictRealThresholdGate (circuit.bottom index) hcore padding
  topWeight := circuit.topWeight
  topThreshold := circuit.topThreshold

theorem restrictThresholdCircuit_eval {core target : ℕ}
    (circuit : ThresholdThresholdCircuit target) (hcore : core ≤ target)
    (padding : BitInput (target - core)) (input : BitInput core) :
    (restrictThresholdCircuit circuit hcore padding).eval input =
      restrictTarget circuit.eval hcore padding input := by
  change decide (circuit.topThreshold ≤
      ∑ index, circuit.topWeight index *
        bitAsReal
          ((restrictRealThresholdGate
            (circuit.bottom index) hcore padding).eval input)) =
    decide (circuit.topThreshold ≤
      ∑ index, circuit.topWeight index *
        bitAsReal ((circuit.bottom index).eval
          (fun targetIndex =>
            Sum.elim input padding
              ((finSplitEquiv hcore).symm targetIndex))))
  apply decide_eq_decide.mpr
  have hsum :
      (∑ index, circuit.topWeight index *
        bitAsReal
          ((restrictRealThresholdGate
            (circuit.bottom index) hcore padding).eval input)) =
      ∑ index, circuit.topWeight index *
        bitAsReal ((circuit.bottom index).eval
          (fun targetIndex =>
            Sum.elim input padding
              ((finSplitEquiv hcore).symm targetIndex))) := by
    apply Finset.sum_congr rfl
    intro index _
    rw [restrictRealThresholdGate_eval]
  rw [hsum]

theorem restrictThresholdCircuit_wireCount_le {core target : ℕ}
    (circuit : ThresholdThresholdCircuit target) (hcore : core ≤ target)
    (padding : BitInput (target - core)) :
    (restrictThresholdCircuit circuit hcore padding).wireCount ≤
      circuit.wireCount := by
  unfold ThresholdThresholdCircuit.wireCount restrictThresholdCircuit
  simp only
  exact Finset.sum_le_sum
    (s := Finset.univ.filter fun index => circuit.topWeight index ≠ 0)
    fun index _ =>
      Nat.add_le_add_right
        (restrictRealThresholdGate_support_card_le
          (circuit.bottom index) hcore padding) 1

def symmetricWireFamily : SizedFunctionFamily :=
  fun n function size =>
    ∃ circuit : SymmetricThresholdCircuit n,
      circuit.wireCount ≤ size ∧ circuit.eval = function

def thresholdWireFamily : SizedFunctionFamily :=
  fun n function size =>
    ∃ circuit : ThresholdThresholdCircuit n,
      circuit.wireCount ≤ size ∧ circuit.eval = function

theorem symmetricWireFamily_restrictionClosed :
    RestrictionClosed symmetricWireFamily := by
  intro core target size candidate hcore hcandidate padding
  rcases hcandidate with ⟨circuit, hwires, heval⟩
  refine ⟨restrictSymmetricCircuit circuit hcore padding,
    le_trans (restrictSymmetricCircuit_wireCount_le circuit hcore padding)
      hwires, ?_⟩
  funext input
  rw [restrictSymmetricCircuit_eval, heval]

theorem thresholdWireFamily_restrictionClosed :
    RestrictionClosed thresholdWireFamily := by
  intro core target size candidate hcore hcandidate padding
  rcases hcandidate with ⟨circuit, hwires, heval⟩
  refine ⟨restrictThresholdCircuit circuit hcore padding,
    le_trans (restrictThresholdCircuit_wireCount_le circuit hcore padding)
      hwires, ?_⟩
  funext input
  rw [restrictThresholdCircuit_eval, heval]

/-! ## Negation closure

`paper.tex:617`: "Output negation changes only the symmetric lookup, or replaces
a top inequality `L ≥ θ` by `-L ≥ -θ+1`, so it also preserves the class and wire
count."  Both families are closed under output negation **at the same wire
budget**, which is the second half of the licence `paper.tex:4364-4366` gives
for the CLW XOR import. -/

/-- Negating a symmetric top is a lookup-table flip.  The bottom layer, and
hence the entire wire charge, is untouched. -/
def negateSymmetricCircuit {n : ℕ} (circuit : SymmetricThresholdCircuit n) :
    SymmetricThresholdCircuit n where
  bottomCount := circuit.bottomCount
  bottom := circuit.bottom
  top := fun count => !circuit.top count

@[simp] theorem negateSymmetricCircuit_wireCount {n : ℕ}
    (circuit : SymmetricThresholdCircuit n) :
    (negateSymmetricCircuit circuit).wireCount = circuit.wireCount := rfl

@[simp] theorem negateSymmetricCircuit_eval {n : ℕ}
    (circuit : SymmetricThresholdCircuit n) (input : BitInput n) :
    (negateSymmetricCircuit circuit).eval input = !circuit.eval input := rfl

theorem symmetricWireFamily_negationClosed :
    SourceInterfaces.NegationClosedFamily symmetricWireFamily := by
  intro n size candidate hcandidate
  rcases hcandidate with ⟨circuit, hwires, heval⟩
  refine ⟨negateSymmetricCircuit circuit, ?_, ?_⟩
  · rwa [negateSymmetricCircuit_wireCount]
  · funext input
    rw [negateSymmetricCircuit_eval, heval]

/-- The weighted top score of a threshold-of-threshold circuit. -/
noncomputable def topScore {n : ℕ} (circuit : ThresholdThresholdCircuit n)
    (input : BitInput n) : ℝ :=
  ∑ i, circuit.topWeight i * bitAsReal ((circuit.bottom i).eval input)

theorem thresholdCircuit_eval_eq_decide {n : ℕ}
    (circuit : ThresholdThresholdCircuit n) (input : BitInput n) :
    circuit.eval input = decide (circuit.topThreshold ≤ topScore circuit input) :=
  rfl

/-- Flip the top inequality by negating every top weight and retargeting the
threshold.  Only the sign of each `topWeight` changes, so the retained-incidence
wire charge is literally the same sum. -/
noncomputable def negateThresholdCircuit {n : ℕ}
    (circuit : ThresholdThresholdCircuit n) (target : ℝ) :
    ThresholdThresholdCircuit n where
  bottomCount := circuit.bottomCount
  bottom := circuit.bottom
  topWeight := fun i => -circuit.topWeight i
  topThreshold := -target

@[simp] theorem negateThresholdCircuit_wireCount {n : ℕ}
    (circuit : ThresholdThresholdCircuit n) (target : ℝ) :
    (negateThresholdCircuit circuit target).wireCount = circuit.wireCount := by
  unfold ThresholdThresholdCircuit.wireCount negateThresholdCircuit
  simp only [neg_ne_zero]

theorem negateThresholdCircuit_eval {n : ℕ}
    (circuit : ThresholdThresholdCircuit n) (target : ℝ) (input : BitInput n) :
    (negateThresholdCircuit circuit target).eval input =
      decide (topScore circuit input ≤ target) := by
  unfold ThresholdThresholdCircuit.eval negateThresholdCircuit topScore
  simp only [neg_mul, Finset.sum_neg_distrib, neg_le_neg_iff]

/-- The constant-`false` threshold circuit over the same bottom layer.  Every
top weight is zero, so no bottom incidence is retained and the wire charge is
`0`; it is used only when the original gate accepts everything. -/
noncomputable def constantFalseThresholdCircuit {n : ℕ}
    (circuit : ThresholdThresholdCircuit n) : ThresholdThresholdCircuit n where
  bottomCount := circuit.bottomCount
  bottom := circuit.bottom
  topWeight := fun _ => 0
  topThreshold := 1

@[simp] theorem constantFalseThresholdCircuit_wireCount {n : ℕ}
    (circuit : ThresholdThresholdCircuit n) :
    (constantFalseThresholdCircuit circuit).wireCount = 0 := by
  unfold ThresholdThresholdCircuit.wireCount constantFalseThresholdCircuit
  simp

@[simp] theorem constantFalseThresholdCircuit_eval {n : ℕ}
    (circuit : ThresholdThresholdCircuit n) (input : BitInput n) :
    (constantFalseThresholdCircuit circuit).eval input = false := by
  unfold ThresholdThresholdCircuit.eval constantFalseThresholdCircuit
  norm_num

/-- **Negation closure for the threshold family.**  On the Boolean cube the top
score takes finitely many values, so the strict complement `score < θ` of a
non-strict test is itself a non-strict test at the largest attained value below
`θ`.  Real top weights are therefore no obstruction, and no wire is added. -/
theorem thresholdWireFamily_negationClosed :
    SourceInterfaces.NegationClosedFamily thresholdWireFamily := by
  classical
  intro n size candidate hcandidate
  rcases hcandidate with ⟨circuit, hwires, heval⟩
  by_cases hbelow :
      (Finset.univ.image (topScore circuit)).filter
        (fun value => value < circuit.topThreshold) = ∅
  · -- The gate is constantly true, so its negation is the constant `false`.
    refine ⟨constantFalseThresholdCircuit circuit, ?_, ?_⟩
    · simp
    · funext input
      have hnot : ¬ topScore circuit input < circuit.topThreshold := by
        intro hlt
        have hmem :
            topScore circuit input ∈
              (Finset.univ.image (topScore circuit)).filter
                (fun value => value < circuit.topThreshold) := by
          simp only [Finset.mem_filter, Finset.mem_image]
          exact ⟨⟨input, Finset.mem_univ input, rfl⟩, hlt⟩
        rw [hbelow] at hmem
        exact absurd hmem (Finset.notMem_empty _)
      have hcandidateTrue : candidate input = true := by
        rw [← heval, thresholdCircuit_eval_eq_decide]
        exact decide_eq_true (le_of_not_gt hnot)
      simp [hcandidateTrue]
  · obtain ⟨largest, hlargest⟩ :=
      Finset.max_of_nonempty (Finset.nonempty_iff_ne_empty.mpr hbelow)
    have hmemLargest :
        largest ∈
          (Finset.univ.image (topScore circuit)).filter
            (fun value => value < circuit.topThreshold) :=
      Finset.mem_of_max hlargest
    have hlargestBelow : largest < circuit.topThreshold :=
      (Finset.mem_filter.mp hmemLargest).2
    refine ⟨negateThresholdCircuit circuit largest, ?_, ?_⟩
    · rwa [negateThresholdCircuit_wireCount]
    · funext input
      rw [negateThresholdCircuit_eval, ← heval,
        thresholdCircuit_eval_eq_decide]
      by_cases hlt : topScore circuit input < circuit.topThreshold
      · have hmem :
            topScore circuit input ∈
              (Finset.univ.image (topScore circuit)).filter
                (fun value => value < circuit.topThreshold) := by
          simp only [Finset.mem_filter, Finset.mem_image]
          exact ⟨⟨input, Finset.mem_univ input, rfl⟩, hlt⟩
        have hle : topScore circuit input ≤ largest :=
          Finset.le_max_of_eq hmem hlargest
        simp [hle, not_le.mpr hlt]
      · have hge : circuit.topThreshold ≤ topScore circuit input :=
          le_of_not_gt hlt
        have hnotle : ¬ topScore circuit input ≤ largest := by
          exact not_le.mpr (lt_of_lt_of_le hlargestBelow hge)
        simp [hnotle, hge]

/-- **Anti-vacuity.**  The two closure hypotheses the XOR contract now carries
are simultaneously satisfiable, and satisfiable at exactly the two classes the
source is ever instantiated at.  Neither premise is a disguised `False`, so the
weakened contract is not vacuously weaker. -/
theorem wireFamilies_closureHypotheses_satisfiable :
    (SourceInterfaces.RestrictionClosedFamily symmetricWireFamily ∧
        SourceInterfaces.NegationClosedFamily symmetricWireFamily) ∧
      (SourceInterfaces.RestrictionClosedFamily thresholdWireFamily ∧
        SourceInterfaces.NegationClosedFamily thresholdWireFamily) :=
  ⟨⟨symmetricWireFamily_restrictionClosed.toSourceFamily,
      symmetricWireFamily_negationClosed⟩,
    ⟨thresholdWireFamily_restrictionClosed.toSourceFamily,
      thresholdWireFamily_negationClosed⟩⟩

end NearCubicWires.CircuitRestriction
