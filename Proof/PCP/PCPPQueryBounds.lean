import Proof.PCP.PCPPQueryCost
import Proof.Amplification.RecoveryWitnessPolicy

/-! One polynomial majorant for both same-source accessors. Its coefficient
and degree depend only on the fixed source algorithm. The circuit-code width
is bounded by the accepted structural codec theorem, separately from the
source constructor's running time and explicit PCPP dimensions. -/
namespace NearCubicWires.RepairOrdinary.PCPPQueryBounds
open RepairRepresentation SourceInterfaces PCPPQueryCost RecoveryWitnessPolicy PolynomialSchedule ExecutableInterfaces
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def scalar (a : PointwisePCPPAlgorithm) (n : ℕ) :=
  a.coefficient*(n+1)^a.degree+(n+1)+canonicalBooleanCircuitCodeBitBound (n+1)+10
def majorant (a : PointwisePCPPAlgorithm) (n : ℕ) := 10000*(scalar a n+1)^2

theorem circuit_polynomial : PolynomiallyBounded canonicalBooleanCircuitCodeBitBound := by
  have hone := polynomiallyBounded_constant 1
  have htwo := polynomiallyBounded_constant 2
  have hsucc := polynomiallyBounded_add polynomiallyBounded_id hone
  have hnat : PolynomiallyBounded canonicalNatCodeBitBound :=
    polynomiallyBounded_add hone (polynomiallyBounded_mul
      (polynomiallyBounded_mul htwo (polynomiallyBounded_pow hsucc 4))
      (polynomiallyBounded_add hsucc hone))
  have tag {left right : ℕ→ℕ} (hl : PolynomiallyBounded left) (hr : PolynomiallyBounded right) :
      PolynomiallyBounded (fun n => 4*(left n+right n)) :=
    polynomiallyBounded_mul (polynomiallyBounded_constant 4) (polynomiallyBounded_add hl hr)
  have hnode : PolynomiallyBounded canonicalBooleanNodeCodeBitBound := tag hnat (tag hnat (tag hnat hone))
  have hbalanced : PolynomiallyBounded (fun n => canonicalBalancedCodeBitBound n (canonicalBooleanNodeCodeBitBound n)) :=
    polynomiallyBounded_add hone (polynomiallyBounded_mul
      (polynomiallyBounded_mul htwo (polynomiallyBounded_pow polynomiallyBounded_id 4))
      (polynomiallyBounded_add (polynomiallyBounded_mul polynomiallyBounded_id hnode) hone))
  exact tag hbalanced (tag hnat hone)

theorem majorant_polynomial (a : PointwisePCPPAlgorithm) : PolynomiallyBounded (majorant a) := by
  have hsucc := polynomiallyBounded_add polynomiallyBounded_id (polynomiallyBounded_constant 1)
  have hcode := polynomiallyBounded_comp circuit_polynomial hsucc
  have hsource := polynomiallyBounded_mul (polynomiallyBounded_constant a.coefficient)
    (polynomiallyBounded_pow hsucc a.degree)
  have hscalar := polynomiallyBounded_add (polynomiallyBounded_add
    (polynomiallyBounded_add hsource hsucc) hcode) (polynomiallyBounded_constant 10)
  exact polynomiallyBounded_mul (polynomiallyBounded_constant 10000)
    (polynomiallyBounded_pow (polynomiallyBounded_add hscalar (polynomiallyBounded_constant 1)) 2)

theorem bits_le (n : ℕ) : n.bits.length≤natBitLength n := by
  rw [Nat.size_eq_bits_len]
  apply Nat.size_le.mpr
  simpa [natBitLength,Nat.succ_eq_add_one] using Nat.lt_pow_succ_log_self (b:=2) (by omega) n

theorem components (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity) :
    let M := scalar a (r.circuit.size+r.arity)
    1≤M ∧ PCPPQuerySourceCall.sourceBudget a r≤M ∧ r.arity≤M ∧
      (encodeBooleanCircuit r.circuit).bits.length≤M ∧ (a.output r).systematicBits≤M ∧
      (a.output r).auxiliaryBits≤M ∧ 2^(a.output r).clauseBits≤M ∧ (a.output r).clauseBits≤M := by
  dsimp only
  have hsource : PCPPQuerySourceCall.sourceBudget a r ≤ scalar a (r.circuit.size+r.arity) := by
    unfold scalar PCPPQuerySourceCall.sourceBudget
    omega
  have harity : r.arity ≤ scalar a (r.circuit.size+r.arity) := by unfold scalar; omega
  have hcode := (bits_le (encodeBooleanCircuit r.circuit)).trans
    (encodeBooleanCircuit_bits_le_parameter r.circuit
      (by have hmin := a.minimumArityBound; have hr := r.large; have hs := r.sizeLarge; omega)
      (show r.arity≤r.circuit.size+r.arity+1 by omega)
      (show r.circuit.size≤r.circuit.size+r.arity+1 by omega))
  have hsys := (a.systematicBound r).trans
    (Nat.mul_le_mul_left a.coefficient (Nat.pow_le_pow_left
      (show r.arity+1≤r.circuit.size+r.arity+1 by omega) a.degree))
  have haux := (a.auxiliaryBound r).trans
    (Nat.mul_le_mul_left a.coefficient (Nat.pow_le_pow_left
      (show r.circuit.size+1≤r.circuit.size+r.arity+1 by omega) a.degree))
  have hcount := (a.clauseCountBound r).trans
    (Nat.mul_le_mul_left a.coefficient (Nat.pow_le_pow_left
      (show r.circuit.size+1≤r.circuit.size+r.arity+1 by omega) a.degree))
  have hclause : (a.output r).clauseBits<2^(a.output r).clauseBits := Nat.lt_two_pow_self
  unfold PCPPQuerySourceCall.sourceBudget at hsource
  refine ⟨by unfold scalar; omega,hsource,harity,?_,by omega,by omega,by omega,by omega⟩
  unfold scalar
  omega

theorem literal_le {n : ℕ} (l : Literal n) : literalIndex l≤2*n := by
  cases l with
  | positive i => dsimp [literalIndex]; omega
  | negative i => dsimp [literalIndex]; omega

theorem support_bound (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (i : Fin (a.output r).systematicBits) :
    PCPPQuerySourceCall.budget a r i.val+1+
      PCPPQuerySupport.budget (a.output r).systematicBits (a.output r).auxiliaryBits
        (a.output r).clauseBits r.arity i.val ≤ majorant a (r.circuit.size+r.arity) := by
  let M := scalar a (r.circuit.size+r.arity)
  obtain ⟨hpos,hsource,harity,hcode,hsys,haux,_,hclause⟩ := components a r
  have hi : i.val≤M := i.isLt.le.trans hsys
  have hprepare := prepare_le r.arity i.val (encodeBooleanCircuit r.circuit).bits M harity hi hcode
  have hlocal := support_le (a.output r).systematicBits (a.output r).auxiliaryBits
    (a.output r).clauseBits r.arity i.val M hsys haux hclause harity hi
  change _≤10000*(M+1)^2
  unfold PCPPQuerySourceCall.budget
  nlinarith

theorem clause_bound (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (i : Fin (2^(a.output r).clauseBits)) :
    PCPPQuerySourceCall.budget a r i.val+1+PCPPQueryClause.queryBudget r (a.output r) i≤
      majorant a (r.circuit.size+r.arity) := by
  let M := scalar a (r.circuit.size+r.arity)
  obtain ⟨hpos,hsource,harity,hcode,hsys,haux,hcount,hclause⟩ := components a r
  have hi : i.val≤M := i.isLt.le.trans hcount
  have hprepare := prepare_le r.arity i.val (encodeBooleanCircuit r.circuit).bits M harity hi hcode
  have hlit (l : Literal ((a.output r).systematicBits+(a.output r).auxiliaryBits)) : literalIndex l≤4*M := by
    have h := literal_le l
    omega
  have hrows : ∀ p∈(PCPPQueryClause.clausePairs r (a.output r)).take i.val,p.1≤4*M ∧ p.2≤4*M := by
    intro p hp
    have hm := List.mem_of_mem_take hp
    obtain ⟨j,hj⟩ := List.mem_ofFn.mp hm
    rw [← hj]
    exact ⟨hlit _,hlit _⟩
  have hlen : ((PCPPQueryClause.clausePairs r (a.output r)).take i.val).length≤M :=
    (List.length_take_le _ _).trans hi
  have hlocal := clause_le (a.output r).systematicBits (a.output r).auxiliaryBits
    (a.output r).clauseBits r.arity (2*2^(a.output r).clauseBits)
    ((PCPPQueryClause.clausePairs r (a.output r)).take i.val)
    (literalIndex ((a.output r).clauses i).left) (literalIndex ((a.output r).clauses i).right)
    M hsys haux hclause harity (by omega) hlen hrows (hlit _) (hlit _)
  change PCPPQueryClause.queryBudget r (a.output r) i≤1000*(M+1)^2 at hlocal
  change _≤10000*(M+1)^2
  unfold PCPPQuerySourceCall.budget
  nlinarith

end NearCubicWires.RepairOrdinary.PCPPQueryBounds
