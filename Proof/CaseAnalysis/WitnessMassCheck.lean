import Proof.CaseAnalysis.WitnessMassStep
import Proof.Hierarchy.CompetitorThresholdTail

/-! The unchanged fixed absolute-mass cap is checked by the existing paid
constant printer, native-bank clear, and exact rational comparator. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.MassCheck
open LocalBitMultitape RecoveryRootRound RecoveryExecution
open CompetitorSumFold
open CompetitorValidity (Estimate)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def input (ambient : Fin 94→List Bool) : Fin 110→List Bool:=
  Fin.addCases (m := 94) (n := 16) (motive := fun _=>List Bool) ambient (fun _=>[])
def machine (k : ℕ) (q : ℚ):=CompetitorThresholdAmbient.machine false k q
def budget:=CompetitorThresholdAmbient.budget

theorem check_run (B k : ℕ) (q : ℚ) (a : Estimate) (source : List Bool)
    (ambient : Fin 94→List Bool) (h : Store B a source ambient)
    (ha : a.Valid B) (hq : 0≤q) (hk : k≤B)
    (hp : CompetitorThresholdDecision.numerator q<2^k) (hd : q.den<2^k) : ∃ output,
    ClockJoin.ReadyRun (machine k q) (budget B k) (input ambient) output ∧
      (readTapeBit (output 65) 0=true ↔ a.value≤q):=by
  have he:CompetitorThresholdAmbient.project (input ambient)=ambient:=by
    funext i;simp [CompetitorThresholdAmbient.project,CompetitorThresholdAmbient.native,input]
  have hh:∀ i,(fun _ : Fin 110=>0) (CompetitorThresholdAmbient.native i)=heads 0 i:=by
    intro i;simp only [heads,ite_self]
  have hs:Store B a source (CompetitorThresholdAmbient.project (input ambient)):=by rw [he];exact h
  obtain ⟨r,hr,rt,rh,rf⟩:=CompetitorThresholdAmbient.tail_run false B k 0 q a source
    (fun _=>0) (input ambient) hs hh (by intros;rfl)
    (by intro i hi;simp [input,Fin.addCases,show ¬i.val<94 by omega]) ha hq hk hp hd
  refine ⟨r.final.tapes,⟨r,hr,rfl,?_,rt⟩,?_⟩
  · intro i;rw [rh]
  · simpa only [CompetitorThresholdDecision.passes,Bool.false_eq_true,if_false,
      CompetitorThresholdDecision.estimate,Estimate.value] using rf

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.MassCheck
