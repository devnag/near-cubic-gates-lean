import Proof.PCP.PCPPSubstitutionRequest
import Proof.Supplier.SupplierEstimator

/-! The same faithful pointwise source is averaged over the actual padded
substituted outer circuit. Outer soundness contributes its acceptance mass;
pointwise PCPP soundness applies only outside that exceptional set. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSourceAverage
open RepairSource RepairRepresentation SourceInterfaces PCPPRequestBoundary
open ProjectionPCPPadding SupplierEstimator
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def acceptanceMean {n : ℕ} (c : BooleanCircuit n) : ℝ :=
  𝔼 x : BitInput n,if c.eval x then 1 else 0
noncomputable def satisfiedMean (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (auxiliary : BitInput r.arity → BitInput (a.output r).auxiliaryBits) : ℝ :=
  𝔼 x : BitInput r.arity,(a.output r).satisfiedFraction x (auxiliary x)

theorem source_sound_average (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (auxiliary : BitInput r.arity → BitInput (a.output r).auxiliaryBits) :
    satisfiedMean a r auxiliary≤a.soundness+acceptanceMean r.circuit := by
  have bound (x : BitInput r.arity) : (a.output r).satisfiedFraction x (auxiliary x)≤1 := by
    unfold PointwisePCPP.satisfiedFraction
    apply (div_le_one (by positivity)).2
    have hcard := Finset.card_filter_le (Finset.univ : Finset (Fin (2^(a.output r).clauseBits)))
      (fun i => ((a.output r).clauses i).eval ((a.output r).assignment x (auxiliary x)))
    simp only [Finset.card_univ,Fintype.card_fin] at hcard
    exact_mod_cast hcard
  have hpoint (x : BitInput r.arity) : (a.output r).satisfiedFraction x (auxiliary x)≤
      a.soundness+(if r.circuit.eval x then 1 else 0) := by
    cases hx : r.circuit.eval x
    · simpa only [hx,Bool.false_eq_true,ite_false,add_zero] using a.sound r x hx (auxiliary x)
    · simp only [ite_true]
      linarith [bound x,a.soundnessPositive]
  have h := Finset.expect_le_expect (fun x (_ : x∈(Finset.univ : Finset (BitInput r.arity))) => hpoint x)
  simpa only [satisfiedMean,acceptanceMean,Finset.expect_add_distrib,Fintype.expect_const] using h

theorem prefix_mean {native padded : ℕ} (hwidth : native≤padded) (f : BitInput native→ℝ) :
    (𝔼 x : BitInput padded,f (prefixBits hwidth x))=𝔼 x : BitInput native,f x := by
  have h := Fintype.expect_equiv (bitInputSplitEquiv hwidth)
    (fun x => f (prefixBits hwidth x)) (fun x => f x.1) (fun _ => rfl)
  rw [h,←Finset.univ_product_univ,Finset.expect_product]
  simp

theorem request_acceptance (a : PointwisePCPPAlgorithm) {n : ℕ} (c : BooleanCircuit n) :
    acceptanceMean (request a c).circuit=acceptanceMean c := by
  unfold acceptanceMean
  simp only [request_eval]
  exact prefix_mean (Nat.le_max_left n a.minimumArity) (fun x => if c.eval x then (1 : ℝ) else 0)

def oracleProof {n : ℕ} (oracle : BooleanCircuit n) : BitInput (2^n) :=
  fun i => oracle.eval (bitInputIndexEquiv n i)

theorem oracleProof_address {n : ℕ} (oracle : BooleanCircuit n) (bits : BitInput n) :
    oracleProof oracle (binaryAddress bits)=oracle.eval bits :=
  congrArg oracle.eval ((bitInputIndexEquiv n).apply_symm_apply bits)

theorem outer_eval {M : TimedDecisionMachine} {T : ℕ→ℕ} (pcp : ProjectionPCP M T)
    {n : ℕ} (x : BitInput n) (oracle : BooleanCircuit (pcp.nativeWidth n))
    (hind : ∀ u v,pcp.decision x u=pcp.decision x v) (u : BitInput (pcp.nativeWidth n)) :
    (PCPPSubstitution.compactSubstituted oracle (pcp.queryAddressBits x) (pcp.decision x (fun _=>false))).eval u=
      pcp.accepts x (oracleProof oracle) u := by
  rw [PCPPSubstitution.compactSubstituted_eval,hind (fun _=>false) u]
  unfold ProjectionPCP.accepts ProjectionPCP.queryAddress
  congr 1
  funext j
  exact (oracleProof_address oracle _).symm

theorem outer_acceptance {M : TimedDecisionMachine} {T : ℕ→ℕ} (pcp : ProjectionPCP M T)
    {n : ℕ} (x : BitInput n) (oracle : BooleanCircuit (pcp.nativeWidth n))
    (hind : ∀ u v,pcp.decision x u=pcp.decision x v) :
    acceptanceMean (PCPPSubstitution.compactSubstituted oracle (pcp.queryAddressBits x)
      (pcp.decision x (fun _=>false)))=pcp.acceptanceFraction x (oracleProof oracle) := by
  unfold acceptanceMean ProjectionPCP.acceptanceFraction
  simp only [outer_eval pcp x oracle hind,Finset.expect_eq_sum_div_card]
  congr 1
  simp

theorem ordinary_no_average {T : ℕ→ℕ} {H : OrdinaryHierarchy T} {degrees : PCPDegrees}
    (P : OrdinaryPCPResult H degrees) (a : PointwisePCPPAlgorithm) {n : ℕ}
    (x : BitInput n) (oracle : BooleanCircuit (P.pcp.nativeWidth n)) (hn : 1≤n)
    (hno : H.timedView.accepts n x=false)
    (auxiliary : BitInput (domain a (P.pcp.nativeWidth n)) →
      BitInput (a.output (PCPPSubstitution.sourceRequest a oracle (P.pcp.queryAddressBits x)
        (P.pcp.decision x (fun _=>false)))).auxiliaryBits) :
    satisfiedMean a (PCPPSubstitution.sourceRequest a oracle (P.pcp.queryAddressBits x)
      (P.pcp.decision x (fun _=>false))) auxiliary≤a.soundness+1/(n : ℝ)^10 := by
  have hs := source_sound_average a (PCPPSubstitution.sourceRequest a oracle
    (P.pcp.queryAddressBits x) (P.pcp.decision x (fun _=>false))) auxiliary
  have hacc : acceptanceMean (PCPPSubstitution.sourceRequest a oracle (P.pcp.queryAddressBits x)
      (P.pcp.decision x (fun _=>false))).circuit=P.pcp.acceptanceFraction x (oracleProof oracle) :=
    (request_acceptance a _).trans (outer_acceptance P.pcp x oracle (P.decisionIndependent n x))
  rw [hacc] at hs
  exact hs.trans (add_le_add_right (P.sound n hn x hno (oracleProof oracle)) a.soundness)

theorem source_complete_average (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (hyes : ∀ x,r.circuit.eval x=true) :
    a.completeness ≤ satisfiedMean a r (a.output r).honestAuxiliary := by
  have h := Finset.expect_le_expect (fun x (_ : x∈(Finset.univ : Finset (BitInput r.arity))) =>
    a.complete r x (hyes x))
  simpa only [satisfiedMean,Fintype.expect_const] using h

end NearCubicWires.RepairOrdinary.CompetitorSourceAverage
