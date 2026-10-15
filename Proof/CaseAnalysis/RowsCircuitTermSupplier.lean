import Proof.CaseAnalysis.RowsCircuitTermDock
import Proof.CaseAnalysis.RowsCircuitSymmetricRun
import Proof.CaseAnalysis.RowsCircuitThresholdRun

/-! Both actual circuit programs supply the existing counted term/family
consumer, with original decoder guards and no circuit serialization. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsCircuitTermSupplier
open LocalBitMultitape CloseoutWitness CanonicalWitnessCodec RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def symmetricFlag (core W L : ℕ) (bits : List Bool) : Bool:=
  match decodeNormalizedSymmetricThresholdCircuit core (value (TermCoefficient.circuitCode bits)) with
  | none=>false
  | some c=>decide (c.wireCount ≤ W ∧ c.descriptionBits ≤ L)
noncomputable def thresholdFlag (core W L : ℕ) (bits : List Bool) : Bool:=
  match decodeNormalizedThresholdThresholdCircuit core (value (TermCoefficient.circuitCode bits)) with
  | none=>false
  | some c=>decide (c.wireCount ≤ W ∧ c.descriptionBits ≤ L)
noncomputable def symmetricNative (core : ℕ) (bits : List Bool):=
  CloseoutRowsCircuitSymmetricRun.native core (TermCoefficient.circuitCode bits)
noncomputable def thresholdNative (core : ℕ) (bits : List Bool):=
  CloseoutRowsCircuitThresholdRun.native core (TermCoefficient.circuitCode bits)

theorem symmetricFlag_iff (core W L : ℕ) (bits : List Bool) : symmetricFlag core W L bits=true ↔
    CloseoutRowsCircuitSymmetricRun.passed core W L (TermCoefficient.circuitCode bits):=by
  rw [CloseoutRowsCircuitMeaning.symmetric_exact]
  cases hd:decodeNormalizedSymmetricThresholdCircuit core (value (TermCoefficient.circuitCode bits)) <;>
    simp [symmetricFlag,hd]

theorem thresholdFlag_iff (core W L : ℕ) (bits : List Bool) : thresholdFlag core W L bits=true ↔
    CloseoutRowsCircuitThresholdRun.passed core W L (TermCoefficient.circuitCode bits):=by
  rw [CloseoutRowsCircuitMeaning.threshold_exact]
  cases hd:decodeNormalizedThresholdThresholdCircuit core (value (TermCoefficient.circuitCode bits)) <;>
    simp [thresholdFlag,hd]

theorem symmetric (P H core W L fuel : ℕ) (words : List (List Bool))
    (hH : P+1 ≤ H)
    (hcap : ∀ bits∈words,CloseoutRowsCircuitCapacity.capacity (TermCoefficient.circuitCode bits).length ≤ P)
    (hcost : ∀ bits∈words,CloseoutRowsCircuitWholeBudget.budget P (TermCoefficient.circuitCode bits).length ≤ fuel) :
    TermLoop.CircuitSupplier CloseoutRowsCircuitSymmetricRun.machine P H core W L fuel words
      (symmetricFlag core W L) (symmetricNative core):=by
  intro bits hb pos out native ambient terms hraw hdriver
  obtain ⟨base,br,bs,bfh,bflag,brh,braw,bdh,bd,bgood⟩:=
    CloseoutRowsCircuitSymmetricRun.cold_run P core W L (TermCoefficient.circuitCode bits) native (hcap bits hb)
  obtain ⟨padded,pr,ps,pfh,pflag,prh,praw,pdh,pd,pgood⟩:=
    CloseoutRowsCircuitPadding.run CloseoutRowsCircuitSymmetricRun.machine P H core W L _
      (TermCoefficient.circuitCode bits) native (symmetricNative core bits) _ base br bs bfh bflag
      brh braw bdh bd bgood hH
  have more:=runFrom_moreFuel CloseoutRowsCircuitSymmetricRun.machine _
    (fuel-CloseoutRowsCircuitWholeBudget.budget P (TermCoefficient.circuitCode bits).length) _ padded pr
  rw [Nat.add_sub_of_le (hcost bits hb)] at more
  have flag:readTapeBit (padded.final.tapes 1700) 0=symmetricFlag core W L bits:=
    Bool.eq_iff_iff.mpr (pflag.trans (symmetricFlag_iff core W L bits).symm)
  exact CloseoutRowsCircuitTermDock.dock CloseoutRowsCircuitSymmetricRun.machine P H core W L fuel pos
    (TermCoefficient.circuitCode bits) out native (symmetricNative core bits) (symmetricFlag core W L bits)
    terms ambient hraw hdriver padded more pfh flag prh praw pdh pd
    (fun hp=>pgood ((symmetricFlag_iff core W L bits).mp hp))

theorem threshold (P H core W L fuel : ℕ) (words : List (List Bool))
    (hH : P+1 ≤ H)
    (hcap : ∀ bits∈words,CloseoutRowsCircuitCapacity.capacity (TermCoefficient.circuitCode bits).length ≤ P)
    (hcost : ∀ bits∈words,CloseoutRowsCircuitWholeBudget.budget P (TermCoefficient.circuitCode bits).length ≤ fuel) :
    TermLoop.CircuitSupplier CloseoutRowsCircuitThresholdRun.machine P H core W L fuel words
      (thresholdFlag core W L) (thresholdNative core):=by
  intro bits hb pos out native ambient terms hraw hdriver
  obtain ⟨base,br,bs,bfh,bflag,brh,braw,bdh,bd,bgood⟩:=
    CloseoutRowsCircuitThresholdRun.cold_run P core W L (TermCoefficient.circuitCode bits) native (hcap bits hb)
  obtain ⟨padded,pr,ps,pfh,pflag,prh,praw,pdh,pd,pgood⟩:=
    CloseoutRowsCircuitPadding.run CloseoutRowsCircuitThresholdRun.machine P H core W L _
      (TermCoefficient.circuitCode bits) native (thresholdNative core bits) _ base br bs bfh bflag
      brh braw bdh bd bgood hH
  have more:=runFrom_moreFuel CloseoutRowsCircuitThresholdRun.machine _
    (fuel-CloseoutRowsCircuitWholeBudget.budget P (TermCoefficient.circuitCode bits).length) _ padded pr
  rw [Nat.add_sub_of_le (hcost bits hb)] at more
  have flag:readTapeBit (padded.final.tapes 1700) 0=thresholdFlag core W L bits:=
    Bool.eq_iff_iff.mpr (pflag.trans (thresholdFlag_iff core W L bits).symm)
  exact CloseoutRowsCircuitTermDock.dock CloseoutRowsCircuitThresholdRun.machine P H core W L fuel pos
    (TermCoefficient.circuitCode bits) out native (thresholdNative core bits) (thresholdFlag core W L bits)
    terms ambient hraw hdriver padded more pfh flag prh praw pdh pd
    (fun hp=>pgood ((thresholdFlag_iff core W L bits).mp hp))

theorem raw_width (bits : List Bool) : (TermCoefficient.circuitCode bits).length=bits.length:=
  (RecoveryFixedUnpair.word_lengths _).1.trans (CompetitorWitnessTriple.word_length bits _)

theorem budget_mono (P : ℕ) {n N : ℕ} (h : n ≤ N) :
    CloseoutRowsCircuitWholeBudget.budget P n ≤ CloseoutRowsCircuitWholeBudget.budget P N:=
  Nat.mul_le_mul_right (P+1) (Nat.mul_le_mul_left 1000 (by omega))

theorem symmetric_bounded (P H core W L N : ℕ) (words : List (List Bool))
    (hH : P+1 ≤ H) (hcap : CloseoutRowsCircuitCapacity.capacity N ≤ P)
    (hwords : ∀ bits∈words,bits.length ≤ N) :
    TermLoop.CircuitSupplier CloseoutRowsCircuitSymmetricRun.machine P H core W L
      (CloseoutRowsCircuitWholeBudget.budget P N) words (symmetricFlag core W L) (symmetricNative core):=by
  apply symmetric P H core W L _ words hH
  · intro bits hb
    rw [raw_width]
    exact (CloseoutRowsCircuitCapacity.monotone (hwords bits hb)).trans hcap
  · intro bits hb
    rw [raw_width]
    exact budget_mono P (hwords bits hb)

theorem threshold_bounded (P H core W L N : ℕ) (words : List (List Bool))
    (hH : P+1 ≤ H) (hcap : CloseoutRowsCircuitCapacity.capacity N ≤ P)
    (hwords : ∀ bits∈words,bits.length ≤ N) :
    TermLoop.CircuitSupplier CloseoutRowsCircuitThresholdRun.machine P H core W L
      (CloseoutRowsCircuitWholeBudget.budget P N) words (thresholdFlag core W L) (thresholdNative core):=by
  apply threshold P H core W L _ words hH
  · intro bits hb
    rw [raw_width]
    exact (CloseoutRowsCircuitCapacity.monotone (hwords bits hb)).trans hcap
  · intro bits hb
    rw [raw_width]
    exact budget_mono P (hwords bits hb)

end NearCubicWires.RepairOrdinary.CloseoutRowsCircuitTermSupplier
