import Proof.Hierarchy.HierarchySourceCost

/-! Fixed source exponents separate the input power from the logarithmic
hierarchy-clock power. The hierarchy enters coefficients only. -/
namespace NearCubicWires.RepairSource.ProjectionNormalization.HierarchySourceCost
open RepairOrdinary HierarchySourceScales
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def ledger (n N u b C V d S s : ℕ) :=
  C*(n+1)*PCPResourceLedger.q n^2+11658*(N+1)*PCPResourceLedger.q N^2+
  V*(u+1)^d+2*S*(N+u+1)^s+64*(n+N+u+b+1)
def aggregateCoefficient (C A K J V d S s : ℕ) :=
  4*C+11658*A*J^2+V*K^d+2*S*(A+K)^s+64*(A+K+3)

theorem separate (n N u b C A K J V d S s : ℕ)
    (hN : N+1 ≤ A*(n+1)) (hq : PCPResourceLedger.q n ≤ 2*(b+1))
    (hQ : PCPResourceLedger.q N ≤ J*(b+1)) (hu : u+1 ≤ K*(b+1)) :
    ledger n N u b C V d S s ≤ aggregateCoefficient C A K J V d S s*
      (n+1)^(s+1)*(b+1)^(d+s+2) := by
  let X := n+1
  let Z := b+1
  let M := X^(s+1)*Z^(d+s+2)
  have hX : 1 ≤ X := by dsimp [X]; omega
  have hZ : 1 ≤ Z := by dsimp [Z]; omega
  have h2 : X*Z^2 ≤ M := by
    simpa only [pow_one] using monomial_le X Z (s+1) (d+s+2) 1 2 hX hZ (by omega) (by omega)
  have hd : Z^d ≤ M := by
    simpa only [pow_zero,one_mul] using monomial_le X Z (s+1) (d+s+2) 0 d hX hZ (by omega) (by omega)
  have hs : X^s*Z^s ≤ M := monomial_le X Z (s+1) (d+s+2) s s hX hZ (by omega) (by omega)
  have h1 : X*Z ≤ M := by
    simpa only [pow_one] using monomial_le X Z (s+1) (d+s+2) 1 1 hX hZ (by omega) (by omega)
  have hXZ : X ≤ X*Z := by have h := Nat.mul_le_mul_left X hZ; simpa using h
  have hZX : Z ≤ X*Z := by have h := Nat.mul_le_mul_right Z hX; simpa using h
  have hAX : A*X ≤ A*(X*Z) := Nat.mul_le_mul_left A hXZ
  have hKZ : K*Z ≤ K*(X*Z) := Nat.mul_le_mul_left K hZX
  have harg : N+u+1 ≤ (A+K)*(X*Z) := by
    change N+1 ≤ A*X at hN
    change u+1 ≤ K*Z at hu
    nlinarith
  have hlinear : n+N+u+b+1 ≤ (A+K+3)*(X*Z) := by
    change N+1 ≤ A*X at hN
    change u+1 ≤ K*Z at hu
    have hn : n+1=X := rfl
    have hb : b+1=Z := rfl
    nlinarith
  have hc : C*(n+1)*PCPResourceLedger.q n^2 ≤ (4*C)*M := by
    calc
      _ ≤ C*X*(2*Z)^2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hq 2)
      _ = (4*C)*(X*Z^2) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ h2
  have hclock : 11658*(N+1)*PCPResourceLedger.q N^2 ≤ (11658*A*J^2)*M := by
    calc
      _ ≤ 11658*(A*X)*(J*Z)^2 :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ hN) (Nat.pow_le_pow_left hQ 2)
      _ = (11658*A*J^2)*(X*Z^2) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ h2
  have hdim : V*(u+1)^d ≤ (V*K^d)*M := by
    calc
      _ ≤ V*(K*Z)^d := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hu d)
      _ = (V*K^d)*Z^d := by rw [mul_pow]; ring
      _ ≤ _ := Nat.mul_le_mul_left _ hd
  have hsource : 2*S*(N+u+1)^s ≤ (2*S*(A+K)^s)*M := by
    calc
      _ ≤ 2*S*((A+K)*(X*Z))^s := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left harg s)
      _ = (2*S*(A+K)^s)*(X^s*Z^s) := by simp only [mul_pow]; ring
      _ ≤ _ := Nat.mul_le_mul_left _ hs
  have hrest : 64*(n+N+u+b+1) ≤ (64*(A+K+3))*M := by
    calc
      _ ≤ 64*((A+K+3)*(X*Z)) := Nat.mul_le_mul_left _ hlinear
      _ = (64*(A+K+3))*(X*Z) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ h1
  have hsum := Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hc hclock) hdim) hsource) hrest
  change ledger n N u b C V d S s ≤ _ at hsum
  calc
    _ ≤ _ := hsum
    _ = aggregateCoefficient C A K J V d S s*(n+1)^(s+1)*(b+1)^(d+s+2) := by
      dsimp [aggregateCoefficient,M,X,Z]
      ring

def inputExponent (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time) :=
  source.degrees.construction+1
def logExponent (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time) :=
  dimDegree source+source.degrees.construction+2
def coefficient (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
    {k : ℕ} (H : OrdinaryHierarchy (fun n => n^(k+2))) (Cpad : ℕ) :=
  aggregateCoefficient (runtime H Cpad) (Ncoefficient H Cpad) (Tcoefficient H Cpad)
    (HierarchyEncode.qCoefficient H Cpad) (dimCoefficient source) (dimDegree source)
    source.coefficient source.degrees.construction

theorem coefficient_positive (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
    {k : ℕ} (H : OrdinaryHierarchy (fun n => n^(k+2))) (Cpad : ℕ) : 0<coefficient source H Cpad := by
  dsimp [coefficient,aggregateCoefficient]
  omega

theorem constructor_bound (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
    {k : ℕ} (H : OrdinaryHierarchy (fun n => n^(k+2))) (Cpad : ℕ)
    (hcoeff : H.coefficient ≤ Cpad) (hpad : k+3 ≤ Cpad) (r : InputRequest) :
    HierarchySourceInput.constructorBudget source H Cpad r ≤
      coefficient source H Cpad*(r.1+1)^inputExponent source*
        (natBitLength (H.time r.1)+1)^logExponent source :=
  (budget_bound source H Cpad hpad r).trans (separate r.1 (HierarchyEncode.length H Cpad r.1)
    (natBitLength (UWhole.time (HierarchyEncode.length H Cpad r.1))) (natBitLength (H.time r.1))
    (runtime H Cpad) (Ncoefficient H Cpad) (Tcoefficient H Cpad) (HierarchyEncode.qCoefficient H Cpad)
    (dimCoefficient source) (dimDegree source) source.coefficient source.degrees.construction
    (length_bound H Cpad r.1) (input_q_bound H r.1) (padded_q_bound H Cpad r.1)
    (time_short_bound H Cpad hcoeff r.1))

noncomputable def constructor (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
    {k : ℕ} (H : OrdinaryHierarchy (fun n => n^(k+2))) (Cpad : ℕ)
    (hcoeff : H.coefficient ≤ Cpad) (hpad : k+3 ≤ Cpad) :
    OrdinaryWordFunction InputRequest (HierarchySourceInput.hierarchyInput H)
      (fun r => (source.output (HierarchyEncode.encode H Cpad r)).word)
      (fun r => coefficient source H Cpad*(r.1+1)^inputExponent source*
        (natBitLength (H.time r.1)+1)^logExponent source) :=
  (HierarchySourceInput.constructor source H Cpad hpad).enlargeBudget (constructor_bound source H Cpad hcoeff hpad)

end NearCubicWires.RepairSource.ProjectionNormalization.HierarchySourceCost
