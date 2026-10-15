import Proof.CaseAnalysis.FinalRetainedConsumer
import Proof.CaseAnalysis.FinalExactFraction
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 120000
set_option warningAsError true
namespace OrderedCallPhases
open NearCubicWires ComponentwisePolynomial RepairOrdinary
open CloseoutRowsEstimatorCoefficients.Stream (Entry contributions)
open CloseoutFinalC10WorkerChain CloseoutFinalC10Exactness CloseoutFinalC10SupplierCalls

/-- Semantic matching may reorder monomials; the physical record stream is unchanged. -/
def OrderedCalls {Atom : Type} (supplier : List Atom → Rat)
 (monomials : List (CircuitMonomial Atom 4)) (entries : List Entry) : Prop :=
 ∃ order, monomials.Perm order ∧ List.Forall₂ (Calls supplier) order entries

theorem OrderedCalls.exact {Atom : Type} {supplier : List Atom → Rat}
 {monomials : List (CircuitMonomial Atom 4)} {entries : List Entry}
 (h : List.Forall₂ (Calls supplier) monomials entries) : OrderedCalls supplier monomials entries :=
 ⟨monomials,List.Perm.refl _,h⟩

theorem folded_value_of_orderedCalls {Atom : Type} (supplier : List Atom → Rat)
 (width : Nat) (polynomial : CircuitPolynomial Atom 4) (entries : List Entry)
 (hcalls : OrderedCalls supplier polynomial.monomials entries)
 (hvalid : ∀ estimate ∈ contributions entries, CompetitorValidity.Estimate.Valid estimate width) :
 (((CompetitorSumFold.folded CompetitorSumWidth.zero (contributions entries)).value : Rat) : Real)=
 polynomial.estimatedMean supplier := by
 obtain ⟨order,hperm,hcalls⟩ := hcalls
 let ordered : CircuitPolynomial Atom 4 := ⟨order⟩
 have h := folded_value_eq_estimatedMean supplier width ordered entries hcalls hvalid
 refine h.trans ?_
 exact (hperm.map (fun m => (m.coefficient : Real)*(supplier m.factors : Real))).sum_eq.symm

theorem natural_phase_calls {Atom : Type} {arity : Nat} {circuit : BooleanCircuit arity}
 (phase : CloseoutRowsOriginalSchedule.Phase) (pcpp : SourceInterfaces.PointwisePCPP circuit)
 (coordinate : Fin (pcpp.systematicBits+pcpp.auxiliaryBits) → CircuitPolynomial Atom 1)
 (systematicAtom : Fin pcpp.systematicBits → Atom) (supplier : List Atom → Rat)
 (records : Fin (2^pcpp.clauseBits) → List Entry)
 (hrecords : ∀ i,List.Forall₂ (Calls supplier)
   (siteCalls phase pcpp coordinate systematicAtom i).monomials (records i)) :
 OrderedCalls supplier (phasePolynomial phase pcpp coordinate systematicAtom).monomials
  ((List.finRange (2^pcpp.clauseBits)).flatMap records) := by
 classical
 have hp : (Finset.univ : Finset (Fin (2^pcpp.clauseBits))).toList.Perm
     (List.finRange (2^pcpp.clauseBits)) := by
   apply (List.perm_ext_iff_of_nodup (Finset.nodup_toList _) (List.nodup_finRange _)).mpr
   intro i
   simp
 refine ⟨(List.finRange (2^pcpp.clauseBits)).flatMap
   (fun i => (siteCalls phase pcpp coordinate systematicAtom i).monomials),?_,?_⟩
 · rw [phasePolynomial_monomials]
   exact hp.flatMap (fun _ _ => List.Perm.refl _)
 · exact forall2_flatMap (Calls supplier) _ _ _ hrecords

end OrderedCallPhases
