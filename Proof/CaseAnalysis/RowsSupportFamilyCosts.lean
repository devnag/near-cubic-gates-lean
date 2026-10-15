import Proof.CaseAnalysis.RowsSupportFamilyMode
import Proof.CaseAnalysis.RowsSupportTermAll
import Proof.CaseAnalysis.WitnessFamilyResourcesCosts
import Proof.Circuits.PaddedRunnerBudgetClosure

/-! Coarse costs of the actual term, sum and outer-family loops, including
their already-checked loads, mask returns, clears and reinitialization. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.FamilyCosts
open LocalBitMultitape CompetitorSumFold CompetitorSumWidth PaddedRunnerBudgetClosure
open CloseoutWitness
open CloseoutWitness.FamilyResources (Fits sum_count)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def termCost (S P : ℕ) := 10000*(S+2)*(P+S+1)
def sumCost (S P : ℕ) := 1000*(S+2)*(termCost S P+P+1)
def totalCost (S P : ℕ) := 100*(S+2)*(sumCost S P+P+1)

theorem term_cost (S P V C T k core : ℕ) (bits arity : List Bool)
    (hf : Fits P V C T k bits arity) (hlen : bits.length ≤ S) (hcore:core ≤ S) :
    ∀ field∈FamilyFields.words bits,∀ term∈SumHeader.words field,
      TermAll.budget P (P+1) C (width T (natBitLength C))
        (FamilyMode.fuel P core bits.length) term ≤ termCost S P := by
  intro field hfield term hterm
  have hr:=hf.read field hfield term hterm
  have hm:=hf.mass
  have hb:=hf.coefficientWidth
  have hw:term.length ≤ S := by
    rw [CloseoutWitness.FamilyMode.term_width field term hterm,CloseoutWitness.FamilyMode.field_width bits field hfield]
    exact hlen
  have fuel:FamilyMode.fuel P core bits.length ≤ 2000*(S+2)*(P+S+1) := by
    unfold FamilyMode.fuel circuitBudget
    gcongr
  unfold TermAll.budget TermRead.budget TermCommit.budget MassReusableStep.budget termCost
  nlinarith

theorem sum_cost (S P V C T k : ℕ) (bits arity : List Bool)
    (hf : Fits P V C T k bits arity) (hlen : bits.length ≤ S) :
    ∀ field∈FamilyFields.words bits,
      FamilyRound.budget P (P+1) (width T (natBitLength C)) T k (termCost S P)
        field arity ≤ sumCost S P := by
  intro field hfield
  have hlen':field.length ≤ S := (CloseoutWitness.FamilyMode.field_width bits field hfield).le.trans hlen
  have hg:=hf.guard field hfield
  have ha:=hf.append field hfield
  have hm:=hf.check
  have hb:=hf.bootstrap
  have hn: (SumHeader.words field).length ≤ S+1 := by
    rw [SumHeader.words_count]
    exact (sum_count field).trans (by omega)
  have hi:=Nat.mul_le_mul_right (termCost S P+3) hn
  unfold FamilyRound.budget FamilyLoad.budget SumRound.budget SumPrefix.budget
    CloseoutRowsCircuitCountHeader.budget SumTail.budget SumBody.budget TermLoop.budget
    SumFinish.budget SumCleanup.budget sumCost
  nlinarith

theorem total_cost (S P V C T k : ℕ) (bits arity : List Bool)
    (hf : Fits P V C T k bits arity) (hv : V ≤ S) :
    FamilyCold.budget P (P+1) V (sumCost S P) bits ≤ totalCost S P := by
  have hh:=hf.header
  have hm:=Nat.mul_le_mul_right (sumCost S P+3) hv
  unfold FamilyCold.budget FamilyPrepare.budget FamilyRun.budget FamilyWork.budget totalCost
  nlinarith

theorem costs_polynomial {S P : ℕ→ℕ} (hs : SourcePoly S) (hp : SourcePoly P) :
    SourcePoly (fun n=>termCost (S n) (P n)) ∧
      SourcePoly (fun n=>sumCost (S n) (P n)) ∧
      SourcePoly (fun n=>totalCost (S n) (P n)) := by
  have hc (v : ℕ) : SourcePoly (fun _=>v) := polyDominated_const v
  have ht:=((hs.add (hc 2)).const_mul 10000).mul ((hp.add hs).add (hc 1))
  have hu:=((hs.add (hc 2)).const_mul 1000).mul ((ht.add hp).add (hc 1))
  exact ⟨ht,hu,((hs.add (hc 2)).const_mul 100).mul ((hu.add hp).add (hc 1))⟩

end
end NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.FamilyCosts
