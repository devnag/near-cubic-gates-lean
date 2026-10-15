import Proof.CaseAnalysis.NativeWidthStep

namespace NearCubicWires.RepairSource.CloseoutWeakRuntime
open RepairOrdinary ProjectionNormalization CloseoutNativeWidth
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem native_grows {v : OrdinaryVerifier} (source : ProjectionSourceAlgorithm v UAggregateClock.time)
    {k : Nat} (H : OrdinaryHierarchy (fun n => n^(k+2))) (Cpad : Nat) :
    ∀ m, ∃ onset, ∀ n, onset ≤ n → m ≤ HierarchyProjection.width source H Cpad n := by
  intro m
  refine ⟨2^m,?_⟩
  intro n hn
  have hp : 2^m ≤ Dimensions.envelope source (HierarchyEncode.length H Cpad n) :=
    hn.trans ((Nat.le_succ n).trans (input_le_envelope source H Cpad n))
  have hl := Nat.le_log_of_pow_le (by decide : 1 < 2) hp
  change m ≤ Nat.log 2 _+1
  omega

theorem split_bound (n q k a d sigma A B C hot multiplier : Nat)
    (hn1 : 1 ≤ n) (hq1 : 1 ≤ q) (ha : a ≤ k+1) (hs : d+1 ≤ sigma)
    (hn : 2*multiplier*A*2^a ≤ n) (hq : 2*multiplier*B*C ≤ q)
    (hh : hot*q^sigma ≤ B*2^q) (ht : 2^q ≤ C*n^(k+2)*q^d) :
    multiplier*(A*(n+1)^a+hot) ≤ n^(k+2) := by
  have hpre : 2*multiplier*(A*(n+1)^a) ≤ n^(k+2) := calc
    _ ≤ 2*multiplier*(A*(2*n)^a) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _))
    _ = (2*multiplier*A*2^a)*n^a := by rw [mul_pow]; ring
    _ ≤ n*n^a := Nat.mul_le_mul_right _ hn
    _ ≤ n*n^(k+1) := Nat.mul_le_mul_left _ (pow_le_pow_right₀ hn1 ha)
    _ = n^(k+2) := by ring
  have hp : q^(d+1) ≤ q^sigma := pow_le_pow_right₀ hq1 hs
  have hscaled : (2*multiplier*hot)*q^sigma ≤ n^(k+2)*q^sigma := calc
    _ = 2*multiplier*(hot*q^sigma) := by ring
    _ ≤ 2*multiplier*(B*2^q) := Nat.mul_le_mul_left _ hh
    _ ≤ 2*multiplier*(B*(C*n^(k+2)*q^d)) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ ht)
    _ = n^(k+2)*((2*multiplier*B*C)*q^d) := by ring
    _ ≤ n^(k+2)*(q*q^d) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hq)
    _ = n^(k+2)*q^(d+1) := by ring
    _ ≤ n^(k+2)*q^sigma := Nat.mul_le_mul_left _ hp
  have hpower : 0 < q^sigma := pow_pos (by omega) _
  have hhot : 2*multiplier*hot ≤ n^(k+2) := (mul_le_mul_iff_of_pos_right hpower).mp hscaled
  nlinarith

theorem littleO_of_split (M : OrdinaryWeakMachine) (k A B C a d sigma : Nat)
    (q hot : Nat → Nat) (ha : a ≤ k+1) (hs : d+1 ≤ sigma)
    (growth : ∀ m, ∃ onset, ∀ n, onset ≤ n → m ≤ q n)
    (bound : ∃ onset, ∀ n, onset ≤ n →
      M.runtime n ≤ A*(n+1)^a+hot n ∧
      hot n*(q n)^sigma ≤ B*2^(q n) ∧
      2^(q n) ≤ C*n^(k+2)*(q n)^d) :
    OrdinaryLittleO M (fun n => n^(k+2)) := by
  intro multiplier _hm
  obtain ⟨base,hbase⟩ := bound
  obtain ⟨qOnset,hq⟩ := growth (2*multiplier*B*C+1)
  refine ⟨max (max base qOnset) (2*multiplier*A*2^a+1),?_⟩
  intro n hn
  have hb : base ≤ n := (Nat.le_max_left _ _).trans ((Nat.le_max_left _ _).trans hn)
  have hqn : qOnset ≤ n := (Nat.le_max_right _ _).trans ((Nat.le_max_left _ _).trans hn)
  have hnn : 2*multiplier*A*2^a+1 ≤ n := (Nat.le_max_right _ _).trans hn
  obtain ⟨hrt,hhot,ht⟩ := hbase n hb
  have hq' := hq n hqn
  exact (Nat.mul_le_mul_left multiplier hrt).trans
    (split_bound n (q n) k a d sigma A B C (hot n) multiplier
      (by omega) (by omega) ha hs (by omega) (by omega) hhot ht)

end NearCubicWires.RepairSource.CloseoutWeakRuntime
