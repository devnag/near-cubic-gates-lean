import Proof.Hierarchy.HierarchySourceSeparation

/-! Full native output and length-only normalization dimensions are bounded
in the same separated currency as the actual constructor prefix. -/
namespace NearCubicWires.RepairSource.ProjectionNormalization.HierarchySourceCost
open RepairOrdinary HierarchySourceScales
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem source_word_bound (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
    {k : ℕ} (H : OrdinaryHierarchy (fun n => n^(k+2))) (Cpad : ℕ)
    (hcoeff : H.coefficient ≤ Cpad) (r : InputRequest) :
    (source.output (HierarchyEncode.encode H Cpad r)).word.length ≤
      coefficient source H Cpad*(r.1+1)^inputExponent source*
        (natBitLength (H.time r.1)+1)^logExponent source := by
  let N := HierarchyEncode.length H Cpad r.1
  let u := natBitLength (UWhole.time N)
  have ho := SourceCall.output_length source (HierarchyEncode.encode H Cpad r)
  change (source.output (HierarchyEncode.encode H Cpad r)).word.length ≤
    max (4*(N+(UWhole.time N).bits.length)+5) (source.coefficient*(N+u+1)^source.degrees.construction+1) at ho
  have hb := bits_length_le (UWhole.time N)
  change (UWhole.time N).bits.length ≤ u at hb
  have hledger : (source.output (HierarchyEncode.encode H Cpad r)).word.length ≤
      ledger r.1 N u (natBitLength (H.time r.1)) (runtime H Cpad) (dimCoefficient source)
        (dimDegree source) source.coefficient source.degrees.construction := by
    unfold ledger
    simp only [Nat.mul_assoc] at ho ⊢
    omega
  exact hledger.trans (separate r.1 N u (natBitLength (H.time r.1))
    (runtime H Cpad) (Ncoefficient H Cpad) (Tcoefficient H Cpad) (HierarchyEncode.qCoefficient H Cpad)
    (dimCoefficient source) (dimDegree source) source.coefficient source.degrees.construction
    (length_bound H Cpad r.1) (input_q_bound H r.1) (padded_q_bound H Cpad r.1)
    (time_short_bound H Cpad hcoeff r.1))

noncomputable def widthCoefficient (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
    {k : ℕ} (H : OrdinaryHierarchy (fun n => n^(k+2))) (Cpad : ℕ) :=
  logScale (HierarchyProjection.proofCoefficient source H Cpad)+source.degrees.proofLog+6

theorem width_bound (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
    {k : ℕ} (H : OrdinaryHierarchy (fun n => n^(k+2))) (Cpad : ℕ)
    (hcoeff : H.coefficient ≤ Cpad) (hpad : k+3 ≤ Cpad) (n : ℕ) :
    HierarchyProjection.width source H Cpad n ≤
      widthCoefficient source H Cpad*(natBitLength (H.time n)+1) := by
  let R := HierarchyProjection.width source H Cpad n
  let C := HierarchyProjection.proofCoefficient source H Cpad
  let B := H.time n
  let d := 5+source.degrees.proofLog
  have hp := HierarchyProjection.proof_bound source H Cpad hcoeff hpad n
  have hl : Nat.clog 2 (2^R) ≤ logScale (C*B*logScale B^d) :=
    Nat.clog_mono_right 2 (hp.trans (Nat.le_add_right _ 2))
  rw [Nat.clog_pow 2 R (by decide)] at hl
  have hm := HierarchyEncode.logScale_monomial_bound C B d (C*B*logScale B^d) (Nat.le_refl _)
  have he : logScale C+d+1=widthCoefficient source H Cpad := by dsimp [C,d,widthCoefficient]; omega
  rw [he] at hm
  exact (hl.trans hm).trans (Nat.mul_le_mul_left _ (logScale_le_short B))

theorem queries_bound (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
    {k : ℕ} (H : OrdinaryHierarchy (fun n => n^(k+2))) (Cpad : ℕ)
    (hcoeff : H.coefficient ≤ Cpad) (hpad : k+3 ≤ Cpad) (n : ℕ) :
    HierarchyProjection.queries source H Cpad n ≤
      (source.coefficient*(widthCoefficient source H Cpad+1)^source.degrees.queries)*
        (natBitLength (H.time n)+1)^source.degrees.queries := by
  have hr := width_bound source H Cpad hcoeff hpad n
  have hb : 1 ≤ natBitLength (H.time n)+1 := by omega
  have hr' : HierarchyProjection.width source H Cpad n+1 ≤
      (widthCoefficient source H Cpad+1)*(natBitLength (H.time n)+1) := by nlinarith
  calc
    _ = source.coefficient*(HierarchyProjection.width source H Cpad n+1)^source.degrees.queries := rfl
    _ ≤ source.coefficient*((widthCoefficient source H Cpad+1)*(natBitLength (H.time n)+1))^source.degrees.queries :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hr' _)
    _ = _ := by rw [mul_pow]; ring

end NearCubicWires.RepairSource.ProjectionNormalization.HierarchySourceCost
