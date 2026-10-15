import Proof.CaseAnalysis.RowsSupportTermSupplier
import Proof.CaseAnalysis.WitnessFamilyMode

/-! The literal two circuit modes supply the same original verdict/native
semantics together with each kept gate's declared support frame. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.FamilyMode
open LocalBitMultitape CloseoutWitness CloseoutRowsCircuitTermSupplier
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def program (sym : Bool):Σ s,Machine 1704 s:=
  if sym then ⟨Symmetric.program.1,Symmetric.machine⟩ else ⟨Threshold.program.1,Threshold.machine⟩
def machine (sym : Bool):Machine 1704 (program sym).1:=(program sym).2
def support (sym : Bool) (core : ℕ):=
  if sym then fun bits=>Symmetric.support core (TermCoefficient.circuitCode bits)
  else fun bits=>Threshold.support core (TermCoefficient.circuitCode bits)
def fuel (P core N : ℕ):=circuitBudget P core N

theorem symmetric_bounded (P H core W L N : ℕ) (words : List (List Bool))
    (hH:P+1 ≤ H) (hcap:CloseoutRowsCircuitCapacity.capacity N ≤ P) (hwords:∀ bits∈words,bits.length ≤ N) :
    Term.CircuitSupplier Symmetric.machine P H core W L (fuel P core N) words
      (symmetricFlag core W L) (symmetricNative core)
      (fun bits=>Symmetric.support core (TermCoefficient.circuitCode bits)):=by
  apply Term.symmetric P H core W L _ words hH
  · intro bits hb
    rw [raw_width]
    exact (CloseoutRowsCircuitCapacity.monotone (hwords bits hb)).trans hcap
  · intro bits hb
    rw [raw_width]
    exact Term.budget_mono P core (hwords bits hb)

theorem threshold_bounded (P H core W L N : ℕ) (words : List (List Bool))
    (hH:P+1 ≤ H) (hcap:CloseoutRowsCircuitCapacity.capacity N ≤ P) (hwords:∀ bits∈words,bits.length ≤ N) :
    Term.CircuitSupplier Threshold.machine P H core W L (fuel P core N) words
      (thresholdFlag core W L) (thresholdNative core)
      (fun bits=>Threshold.support core (TermCoefficient.circuitCode bits)):=by
  apply Term.threshold P H core W L _ words hH
  · intro bits hb
    rw [raw_width]
    exact (CloseoutRowsCircuitCapacity.monotone (hwords bits hb)).trans hcap
  · intro bits hb
    rw [raw_width]
    exact Term.budget_mono P core (hwords bits hb)

private theorem select4 {α β γ δ : Type} (sym : Bool) (p : α→β→γ→δ→Prop)
    (a0 a1 : α) (b0 b1 : β) (c0 c1 : γ) (d0 d1 : δ)
    (h0:p a0 b0 c0 d0) (h1:p a1 b1 c1 d1) :
    p (if sym then a1 else a0) (if sym then b1 else b0)
      (if sym then c1 else c0) (if sym then d1 else d0):=by
  cases sym
  · exact h0
  · exact h1

theorem supplier (sym : Bool) (P H core W L N : ℕ) (words : List (List Bool))
    (hH:P+1 ≤ H) (hcap:CloseoutRowsCircuitCapacity.capacity N ≤ P) (hwords:∀ bits∈words,bits.length ≤ N) :
    Term.CircuitSupplier (machine sym) P H core W L (fuel P core N) words
      (CloseoutWitness.FamilyMode.flag sym core W L) (CloseoutWitness.FamilyMode.native sym core) (support sym core):=by
  exact select4 sym
    (fun (p:Σ s,Machine 1704 s) (f:List Bool→Bool) (g h:List Bool→List Bool)=>
      Term.CircuitSupplier p.2 P H core W L (fuel P core N) words f g h)
    ⟨Threshold.program.1,Threshold.machine⟩ ⟨Symmetric.program.1,Symmetric.machine⟩
    (thresholdFlag core W L) (symmetricFlag core W L)
    (thresholdNative core) (symmetricNative core)
    (fun bits=>Threshold.support core (TermCoefficient.circuitCode bits))
    (fun bits=>Symmetric.support core (TermCoefficient.circuitCode bits))
    (threshold_bounded P H core W L N words hH hcap hwords)
    (symmetric_bounded P H core W L N words hH hcap hwords)

end
end NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.FamilyMode
