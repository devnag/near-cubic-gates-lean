import Proof.Hierarchy.HierarchyStreamLayout
import Proof.PCP.ProjectionNormalizationStreamBounds

/-! The actual selected-source and normalization prefix keeps its input
power fixed before the hierarchy degree is chosen. Hierarchy-only dependence
is confined to the coefficient, including the source-code padding constant. -/
namespace NearCubicWires.RepairSource.ProjectionNormalization.HierarchyStreamCost
open RepairOrdinary HierarchySourceScales
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
def inputExponent := 3*HierarchySourceCost.inputExponent source
def logBase := HierarchySourceCost.logExponent source+source.degrees.queries+1
def logExponent := 3*logBase source
noncomputable def sizeCoefficient {k : ℕ} (H : OrdinaryHierarchy (fun n => n^(k+2))) (Cpad : ℕ) :=
  HierarchySourceCost.coefficient source H Cpad+HierarchySourceCost.widthCoefficient source H Cpad+
    source.coefficient*(HierarchySourceCost.widthCoefficient source H Cpad+1)^source.degrees.queries+1
noncomputable def coefficient {k : ℕ} (H : OrdinaryHierarchy (fun n => n^(k+2))) (Cpad : ℕ) :=
  HierarchySourceCost.coefficient source H Cpad+1+1024*(sizeCoefficient source H Cpad)^3

noncomputable def framedBudget {k : ℕ} (H : OrdinaryHierarchy (fun n => n^(k+2))) (Cpad : ℕ) (r : InputRequest) :=
  HierarchySourceInput.constructorBudget source H Cpad r+1+
    Streams.budget (source.output (HierarchyEncode.encode H Cpad r))
      (HierarchyProjection.width source H Cpad r.1) (HierarchyProjection.queries source H Cpad r.1)

theorem size_bound {k : ℕ} (H : OrdinaryHierarchy (fun n => n^(k+2))) (Cpad : ℕ)
    (hcoeff : H.coefficient ≤ Cpad) (hpad : k+3 ≤ Cpad) (r : InputRequest) :
    (source.output (HierarchyEncode.encode H Cpad r)).word.length+
      HierarchyProjection.width source H Cpad r.1+HierarchyProjection.queries source H Cpad r.1+1 ≤
      sizeCoefficient source H Cpad*(r.1+1)^HierarchySourceCost.inputExponent source*
        (natBitLength (H.time r.1)+1)^logBase source := by
  let X := r.1+1
  let Z := natBitLength (H.time r.1)+1
  let a := HierarchySourceCost.inputExponent source
  let g := logBase source
  let M := X^a*Z^g
  have hX : 1 ≤ X := by dsimp [X]; omega
  have hZ : 1 ≤ Z := by dsimp [Z]; omega
  have hsource := HierarchySourceCost.source_word_bound source H Cpad hcoeff r
  have hwidth := HierarchySourceCost.width_bound source H Cpad hcoeff hpad r.1
  have hqueries := HierarchySourceCost.queries_bound source H Cpad hcoeff hpad r.1
  have hmSource : X^a*Z^HierarchySourceCost.logExponent source ≤ M :=
    monomial_le X Z a g a _ hX hZ le_rfl (by dsimp [g,logBase]; omega)
  have hmWidth : Z ≤ M := by
    simpa only [pow_zero,one_mul,pow_one] using
      monomial_le X Z a g 0 1 hX hZ (by omega) (by dsimp [g,logBase]; omega)
  have hmQueries : Z^source.degrees.queries ≤ M := by
    simpa only [pow_zero,one_mul] using monomial_le X Z a g 0 source.degrees.queries hX hZ
      (by omega) (by dsimp [g,logBase]; omega)
  have hmOne : 1 ≤ M := by
    simpa only [pow_zero,one_mul] using monomial_le X Z a g 0 0 hX hZ (by omega) (by omega)
  have hs : (source.output (HierarchyEncode.encode H Cpad r)).word.length ≤
      HierarchySourceCost.coefficient source H Cpad*M := by
    exact hsource.trans (by simpa only [Nat.mul_assoc] using
        (Nat.mul_le_mul_left (HierarchySourceCost.coefficient source H Cpad) hmSource))
  have hw := hwidth.trans (Nat.mul_le_mul_left (HierarchySourceCost.widthCoefficient source H Cpad) hmWidth)
  have hq := hqueries.trans (Nat.mul_le_mul_left
    (source.coefficient*(HierarchySourceCost.widthCoefficient source H Cpad+1)^source.degrees.queries) hmQueries)
  change _ ≤ sizeCoefficient source H Cpad*X^a*Z^g
  rw [Nat.mul_assoc]
  dsimp only [sizeCoefficient]
  change _ ≤ (HierarchySourceCost.coefficient source H Cpad+HierarchySourceCost.widthCoefficient source H Cpad+
    source.coefficient*(HierarchySourceCost.widthCoefficient source H Cpad+1)^source.degrees.queries+1)*M
  nlinarith

theorem budget_bound {k : ℕ} (H : OrdinaryHierarchy (fun n => n^(k+2))) (Cpad : ℕ)
    (hcoeff : H.coefficient ≤ Cpad) (hpad : k+3 ≤ Cpad) (r : InputRequest) :
    framedBudget source H Cpad r ≤ coefficient source H Cpad*(r.1+1)^inputExponent source*
      (natBitLength (H.time r.1)+1)^logExponent source := by
  let X := r.1+1
  let Z := natBitLength (H.time r.1)+1
  let a := HierarchySourceCost.inputExponent source
  let g := logBase source
  let M := X^(3*a)*Z^(3*g)
  have hX : 1 ≤ X := by dsimp [X]; omega
  have hZ : 1 ≤ Z := by dsimp [Z]; omega
  have hprefix := HierarchySourceCost.constructor_bound source H Cpad hcoeff hpad r
  have hm : X^a*Z^HierarchySourceCost.logExponent source ≤ M :=
    monomial_le X Z (3*a) (3*g) a _ hX hZ (by omega) (by dsimp [g,logBase]; omega)
  have hp : HierarchySourceInput.constructorBudget source H Cpad r ≤
      HierarchySourceCost.coefficient source H Cpad*M :=
    hprefix.trans (by simpa only [Nat.mul_assoc] using
        (Nat.mul_le_mul_left (HierarchySourceCost.coefficient source H Cpad) hm))
  have hOne : 1 ≤ M := by
    simpa only [pow_zero,one_mul] using monomial_le X Z (3*a) (3*g) 0 0 hX hZ (by omega) (by omega)
  have hb := Streams.budget_bound (source.output (HierarchyEncode.encode H Cpad r))
    (HierarchyProjection.width source H Cpad r.1) (HierarchyProjection.queries source H Cpad r.1)
    (HierarchyProjection.width_fits source H Cpad hpad r) (HierarchyProjection.queries_fit source H Cpad hpad r)
  have hz := size_bound source H Cpad hcoeff hpad r
  have hcube := Nat.mul_le_mul_left 1024 (Nat.pow_le_pow_left hz 3)
  have hc : Streams.budget (source.output (HierarchyEncode.encode H Cpad r))
      (HierarchyProjection.width source H Cpad r.1) (HierarchyProjection.queries source H Cpad r.1) ≤
      (1024*(sizeCoefficient source H Cpad)^3)*M := by
    refine (hb.trans hcube).trans_eq ?_
    dsimp only [M,X,Z,a,g]
    simp only [mul_pow,←pow_mul]
    ring
  change _ ≤ coefficient source H Cpad*X^(3*a)*Z^(3*g)
  rw [Nat.mul_assoc]
  dsimp only [coefficient,framedBudget]
  change _ ≤ (HierarchySourceCost.coefficient source H Cpad+1+1024*(sizeCoefficient source H Cpad)^3)*M
  nlinarith

end NearCubicWires.RepairSource.ProjectionNormalization.HierarchyStreamCost
