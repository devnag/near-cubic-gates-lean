import Proof.CaseAnalysis.WitnessAverage
import Proof.CaseAnalysis.WitnessAliases

/-! Exactly one sum per actual PCPP variable.  Occurrence aliases share that
sum; the only term-count multiplier is the actual fibre size. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.Fibers
open SourceInterfaces CanonicalWitnessCodec ExecutableInterfaces
open ComponentwiseTransfer OccurrenceSliceTransport
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

variable {Circuit : CanonicalWitnessCodec.CircuitFamily} {n : ℕ}
  {c : BooleanCircuit n} (pcpp : PointwisePCPP c)

abbrev Slot := Fin (2^pcpp.clauseBits) × Bool
abbrev Variable := Fin (pcpp.systematicBits+pcpp.auxiliaryBits)

noncomputable def slices (atSlot : Slot pcpp→List (LegalCircuitTerm Circuit n))
    (i : Variable pcpp) := (occurrenceFiber (occurrenceVariable pcpp) i).toList.map atSlot

theorem length_le (atSlot : Slot pcpp→List (LegalCircuitTerm Circuit n)) (i : Variable pcpp) :
    (slices pcpp atSlot i).length ≤ 2*2^pcpp.clauseBits := by
  classical
  simp only [slices,List.length_map,Finset.length_toList]
  have h:=Finset.card_le_card (Finset.subset_univ (occurrenceFiber (occurrenceVariable pcpp) i))
  simpa [Fintype.card_prod,Nat.mul_comm] using h

theorem mem_slices (atSlot : Slot pcpp→List (LegalCircuitTerm Circuit n))
    (i : Variable pcpp) (ts : List (LegalCircuitTerm Circuit n))
    (h : ts∈slices pcpp atSlot i) : ∃ slot,ts=atSlot slot := by
  obtain ⟨slot,_,he⟩:=List.mem_map.mp h
  exact ⟨slot,he.symm⟩

theorem getSum_ofFn {wires description : {n : ℕ}→Circuit n→ℕ}
    {limits : LegalSumLimits} {V : ℕ}
    (f : Fin V→CheckedLegalCircuitSum Circuit wires description limits) (i : Fin V) :
    (SumFamily.mk (List.ofFn f) List.length_ofFn).getSum i=f i := by
  unfold SumFamily.getSum
  rw [List.get_ofFn]
  rfl

noncomputable def family (wires description : {n : ℕ}→Circuit n→ℕ)
    (atSlot : Slot pcpp→List (LegalCircuitTerm Circuit n)) (J B : ℕ) (A : ℚ) (W L : ℕ)
    (hA : 0 ≤ A) (hj : ∀ slot,(atSlot slot).length ≤ J)
    (hm : ∀ slot,Average.mass (atSlot slot) ≤ A)
    (hc : ∀ slot,∀ t∈atSlot slot,t.coefficient.num.natAbs ≤ B ∧ t.coefficient.den ≤ B)
    (hw : ∀ slot,∀ t∈atSlot slot,wires t.circuit ≤ W)
    (hl : ∀ slot,∀ t∈atSlot slot,description t.circuit ≤ L) :
    SumFamily Circuit wires description
      (Average.limits n J B (2*2^pcpp.clauseBits) A W L)
      (pcpp.systematicBits+pcpp.auxiliaryBits) where
  sums:=List.ofFn fun i=>Average.checked wires description (slices pcpp atSlot i)
    J B (2*2^pcpp.clauseBits) A W L (length_le pcpp atSlot i) hA
    (by intro ts ht;obtain ⟨slot,rfl⟩:=mem_slices pcpp atSlot i ts ht;exact hj slot)
    (by intro ts ht;obtain ⟨slot,rfl⟩:=mem_slices pcpp atSlot i ts ht;exact hm slot)
    (by intro ts ht;obtain ⟨slot,rfl⟩:=mem_slices pcpp atSlot i ts ht;exact hc slot)
    (by intro ts ht;obtain ⟨slot,rfl⟩:=mem_slices pcpp atSlot i ts ht;exact hw slot)
    (by intro ts ht;obtain ⟨slot,rfl⟩:=mem_slices pcpp atSlot i ts ht;exact hl slot)
  length_eq:=List.length_ofFn

theorem family_value (wires description : {n : ℕ}→Circuit n→ℕ)
    (evaluate : {n : ℕ}→Circuit n→BitInput n→Bool)
    (atSlot : Slot pcpp→List (LegalCircuitTerm Circuit n)) (J B : ℕ) (A : ℚ) (W L : ℕ)
    (hA : 0 ≤ A) (hj : ∀ slot,(atSlot slot).length ≤ J)
    (hm : ∀ slot,Average.mass (atSlot slot) ≤ A)
    (hc : ∀ slot,∀ t∈atSlot slot,t.coefficient.num.natAbs ≤ B ∧ t.coefficient.den ≤ B)
    (hw : ∀ slot,∀ t∈atSlot slot,wires t.circuit ≤ W)
    (hl : ∀ slot,∀ t∈atSlot slot,description t.circuit ≤ L)
    (u : BitInput n) (i : Variable pcpp) :
    (family pcpp wires description atSlot J B A W L hA hj hm hc hw hl).value evaluate u i=
      occurrenceAverage (occurrenceVariable pcpp)
        (fun slot=>Average.value evaluate (atSlot slot) u) i := by
  classical
  let read (sum : CheckedLegalCircuitSum Circuit wires description
      (Average.limits n J B (2*2^pcpp.clauseBits) A W L)) : ℝ :=
    (sum.value.terms.map fun term=>(term.coefficient:ℝ)*
      (if evaluate term.circuit (fun j=>u (Fin.cast sum.arity_eq j)) then 1 else 0)).sum
  change read ((family pcpp wires description atSlot J B A W L hA hj hm hc hw hl).getSum i)=_
  unfold family
  rw [getSum_ofFn]
  change Average.value evaluate (Average.terms (slices pcpp atSlot i)) u=_
  rw [Average.terms_value]
  simp only [slices,List.length_map,Finset.length_toList,List.map_map,Function.comp_def,
    Finset.sum_map_toList,occurrenceAverage,meanOn]

end NearCubicWires.RepairOrdinary.CloseoutWitness.Fibers
