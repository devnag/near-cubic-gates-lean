import Proof.CaseAnalysis.RowsCircuitTermSupplier
import Proof.CaseAnalysis.CloseoutWitnessFamilyRun

/-! The two actual circuit workers instantiate the whole family ABI.
The predicate is the same public circuit decoder and original wire and
description guards; no worker certificate is an external premise. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.FamilyMode
open LocalBitMultitape CloseoutRowsCircuitTermSupplier
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def program (sym : Bool) : Σ s,Machine 1703 s:=
  if sym then ⟨CloseoutRowsCircuitSymmetricRun.program.1,CloseoutRowsCircuitSymmetricRun.machine⟩
  else ⟨CloseoutRowsCircuitThresholdRun.program.1,CloseoutRowsCircuitThresholdRun.machine⟩
def machine (sym : Bool) : Machine 1703 (program sym).1:=(program sym).2
def flag (sym : Bool) (core W L : ℕ):=
  if sym then symmetricFlag core W L else thresholdFlag core W L
def native (sym : Bool) (core : ℕ):=
  if sym then symmetricNative core else thresholdNative core
def fuel (P N : ℕ):=CloseoutRowsCircuitWholeBudget.budget P N

private theorem select {α β γ : Type} (sym : Bool) (p : α → β → γ → Prop)
    (a0 a1 : α) (b0 b1 : β) (c0 c1 : γ) (h0 : p a0 b0 c0) (h1 : p a1 b1 c1) :
    p (if sym then a1 else a0) (if sym then b1 else b0) (if sym then c1 else c0):=by
  cases sym
  · exact h0
  · exact h1

theorem supplier (sym : Bool) (P H core W L N : ℕ) (words : List (List Bool))
    (hH : P+1 ≤ H) (hcap : CloseoutRowsCircuitCapacity.capacity N ≤ P)
    (hwords : ∀ bits∈words,bits.length ≤ N) :
    TermLoop.CircuitSupplier (machine sym) P H core W L (fuel P N) words (flag sym core W L) (native sym core):=by
  exact select sym
    (fun (p : Σ s,Machine 1703 s) (f : List Bool → Bool) (g : List Bool → List Bool)=>
      TermLoop.CircuitSupplier p.2 P H core W L (fuel P N) words f g)
    ⟨CloseoutRowsCircuitThresholdRun.program.1,CloseoutRowsCircuitThresholdRun.machine⟩
    ⟨CloseoutRowsCircuitSymmetricRun.program.1,CloseoutRowsCircuitSymmetricRun.machine⟩
    (thresholdFlag core W L) (symmetricFlag core W L) (thresholdNative core) (symmetricNative core)
    (threshold_bounded P H core W L N words hH hcap hwords)
    (symmetric_bounded P H core W L N words hH hcap hwords)

theorem field_width (bits field : List Bool) (hfield : field∈FamilyFields.words bits) : field.length=bits.length:=by
  obtain ⟨_,_,rfl⟩:=List.mem_map.mp hfield
  exact SignedSortKey.binary_length _ _

theorem term_width (field term : List Bool) (hterm : term∈SumHeader.words field) : term.length=field.length:=by
  obtain ⟨_,_,rfl⟩:=List.mem_map.mp hterm
  rw [SignedSortKey.binary_length]
  exact (RecoveryFixedUnpair.word_lengths _).1.trans (CompetitorWitnessTriple.word_length field _)

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.FamilyMode
