import Proof.CaseAnalysis.RowsSupportTermDock
import Proof.CaseAnalysis.RowsSupportThresholdCircuit
import Proof.CaseAnalysis.RowsCircuitTermSupplier

/-! The actual extended cold programs supply the support-retaining term
call, with the original decoder guards, policy fields, and native records. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.Term
open LocalBitMultitape CloseoutWitness CanonicalWitnessCodec RadixSemantics
open CloseoutRowsCircuitTermSupplier
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def CircuitSupplier {s : ℕ} (circuit : Machine 1704 s) (P H core W L fuel : ℕ)
    (words : List (List Bool)) (passed : List Bool → Bool) (nativeWord supportWord : List Bool → List Bool) : Prop :=
  ∀ bits∈words,∀ pos out native supports (ambient : Fin 94 → List Bool) (terms : Fin 725 → List Bool),
    terms 78=ZeroPadding.pad P (frame (TermCoefficient.circuitCode bits)) →
    terms 720=List.replicate P true →
    ∃ eh et sh st result,runFrom (programs circuit 1) fuel
      (RecoveryCalls.restarted (programs circuit 1) (lift (TermRound.heads pos out (TermEnvironment.heads native)) supports.length)
        (lift (TermRound.data P terms ambient out (TermEnvironment.tapes H core W L native)) supports))=some result ∧
      result.final.heads=lift (TermRound.heads pos out eh) sh ∧ result.final.tapes=lift (TermRound.data P terms ambient out et) st ∧
      TermRound.heads pos out eh 2527=0 ∧ readTapeBit (TermRound.data P terms ambient out et 2527) 0=passed bits ∧
      (passed bits=true → eh=TermEnvironment.heads (native++nativeWord bits) ∧
        (∀ i : Fin 1703,TermCircuitReset.retained i →
          et (i.castAdd 2)=TermEnvironment.tapes H core W L (native++nativeWord bits) (i.castAdd 2)) ∧
        et 1703=List.replicate H true ∧ et 1704=List.replicate (H+1) false ∧
        sh=(supports++supportWord bits).length ∧ st=supports++supportWord bits ∧
        (∀ i,(et ((TermCircuitReset.privateSlot i).castAdd 2)).length ≤ H))

theorem symmetric (P H core W L fuel : ℕ) (words : List (List Bool))
    (hH : P+1 ≤ H)
    (hcap : ∀ bits∈words,CloseoutRowsCircuitCapacity.capacity (TermCoefficient.circuitCode bits).length ≤ P)
    (hcost : ∀ bits∈words,circuitBudget P core (TermCoefficient.circuitCode bits).length ≤ fuel) :
    CircuitSupplier Symmetric.machine P H core W L fuel words
      (symmetricFlag core W L) (symmetricNative core)
      (fun bits=>Symmetric.support core (TermCoefficient.circuitCode bits)):=by
  intro bits hb pos out native supports ambient terms hraw hdriver
  obtain ⟨base,br,bs,bfh,bflag,brh,braw,bdh,bd,bgood⟩:=
    Symmetric.cold_run P core W L (TermCoefficient.circuitCode bits) native supports (hcap bits hb)
  obtain ⟨padded,pr,ps,pfh,pflag,prh,praw,pdh,pd,pgood⟩:=
    Padding.run Symmetric.machine P H core W L _
      (TermCoefficient.circuitCode bits) native (symmetricNative core bits) supports
      (Symmetric.support core (TermCoefficient.circuitCode bits)) _ base br bs bfh bflag
      brh braw bdh bd bgood hH
  have more:=runFrom_moreFuel Symmetric.machine _
    (fuel-circuitBudget P core (TermCoefficient.circuitCode bits).length) _ padded pr
  rw [Nat.add_sub_of_le (hcost bits hb)] at more
  have flag:readTapeBit (padded.final.tapes 1700) 0=symmetricFlag core W L bits:=
    Bool.eq_iff_iff.mpr (pflag.trans (symmetricFlag_iff core W L bits).symm)
  exact dock Symmetric.machine P H core W L fuel pos
    (TermCoefficient.circuitCode bits) out native (symmetricNative core bits) supports
    (Symmetric.support core (TermCoefficient.circuitCode bits)) (symmetricFlag core W L bits)
    terms ambient hraw hdriver padded more pfh flag prh praw pdh pd
    (fun hp=>pgood ((symmetricFlag_iff core W L bits).mp hp))

theorem threshold (P H core W L fuel : ℕ) (words : List (List Bool))
    (hH : P+1 ≤ H)
    (hcap : ∀ bits∈words,CloseoutRowsCircuitCapacity.capacity (TermCoefficient.circuitCode bits).length ≤ P)
    (hcost : ∀ bits∈words,circuitBudget P core (TermCoefficient.circuitCode bits).length ≤ fuel) :
    CircuitSupplier Threshold.machine P H core W L fuel words
      (thresholdFlag core W L) (thresholdNative core)
      (fun bits=>Threshold.support core (TermCoefficient.circuitCode bits)):=by
  intro bits hb pos out native supports ambient terms hraw hdriver
  obtain ⟨base,br,bs,bfh,bflag,brh,braw,bdh,bd,bgood⟩:=
    Threshold.cold_run P core W L (TermCoefficient.circuitCode bits) native supports (hcap bits hb)
  obtain ⟨padded,pr,ps,pfh,pflag,prh,praw,pdh,pd,pgood⟩:=
    Padding.run Threshold.machine P H core W L _
      (TermCoefficient.circuitCode bits) native (thresholdNative core bits) supports
      (Threshold.support core (TermCoefficient.circuitCode bits)) _ base br bs bfh bflag
      brh braw bdh bd bgood hH
  have more:=runFrom_moreFuel Threshold.machine _
    (fuel-circuitBudget P core (TermCoefficient.circuitCode bits).length) _ padded pr
  rw [Nat.add_sub_of_le (hcost bits hb)] at more
  have flag:readTapeBit (padded.final.tapes 1700) 0=thresholdFlag core W L bits:=
    Bool.eq_iff_iff.mpr (pflag.trans (thresholdFlag_iff core W L bits).symm)
  exact dock Threshold.machine P H core W L fuel pos
    (TermCoefficient.circuitCode bits) out native (thresholdNative core bits) supports
    (Threshold.support core (TermCoefficient.circuitCode bits)) (thresholdFlag core W L bits)
    terms ambient hraw hdriver padded more pfh flag prh praw pdh pd
    (fun hp=>pgood ((thresholdFlag_iff core W L bits).mp hp))

theorem budget_mono (P core : ℕ) {n N : ℕ} (h : n ≤ N) :
    circuitBudget P core n ≤ circuitBudget P core N:=
  Nat.mul_le_mul_right (P+core+1) (Nat.mul_le_mul_left 2000 (by omega))

end NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.Term
