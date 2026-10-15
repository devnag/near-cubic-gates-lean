import Proof.CaseAnalysis.RowsSupportFamily
import Proof.CaseAnalysis.RowsSupportFamilyCosts
import Proof.CaseAnalysis.WitnessFamilyMeaning

/-! The actual strengthened cold family consumes the original Fits ledger.
Its old streams retain their existing semantic predicate, and the one new
support tape carries the actual ordered family/term/gate accumulation. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.FamilySupport
open LocalBitMultitape CompetitorSumFold CompetitorSumWidth
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

abbrev Actual:=CloseoutRowsSupportStream.FamilyCold.machine
abbrev cost:=CloseoutRowsSupportStream.FamilyCosts.totalCost
abbrev support:=CloseoutRowsSupportStream.FamilyCold.support

def retained (sym : Bool) (P V C T core W L k : ℕ) (q : ℚ) (bits supports : List Bool)
    (cursor : Fin 3244→ℕ) (data : Fin 3244→List Bool) : Prop:=
  ColdFamily.retained sym P V C T core W L k q bits
    (fun i=>cursor (i.castAdd 1)) (fun i=>data (i.castAdd 1)) ∧
    cursor 3243=(support sym core bits supports).length ∧ data 3243=support sym core bits supports

theorem family_run (sym : Bool) (S P V C T core W L k : ℕ) (q : ℚ)
    (bits supports : List Bool) (ambient : Fin 94→List Bool)
    (hf:FamilyResources.Fits P V C T k bits (SignedSortKey.binary (natBitLength core) core))
    (hlen:bits.length≤S) (hv:V≤S) (hcore:core≤S) (hC:0<C)
    (hstore:Store (width T (natBitLength C)) zero [] ambient)
    (hq:0≤q) (hk:k≤width T (natBitLength C))
    (hp:CompetitorThresholdDecision.numerator q<2^k) (hd:q.den<2^k) :
    ∃ actual,runFrom (Actual sym k q)
      (FamilyCold.budget P (P+1) V (CloseoutRowsSupportStream.FamilyCosts.sumCost S P) bits)
      ⟨(Actual sym k q).start,CloseoutRowsSupportStream.FamilyCold.heads supports,
        CloseoutRowsSupportStream.FamilyCold.input P (P+1) V C T core W L bits
          (SignedSortKey.binary (natBitLength core) core) ambient supports⟩=some actual ∧
      actual.steps≤cost S P ∧ actual.final.heads 724=0 ∧
      actual.final.tapes 724=[FamilyCold.passed sym V C T core W L q bits (SignedSortKey.binary (natBitLength core) core)] ∧
      (FamilyCold.passed sym V C T core W L q bits (SignedSortKey.binary (natBitLength core) core)=true→
        retained sym P V C T core W L k q bits supports actual.final.heads actual.final.tapes) := by
  obtain ⟨extra,actual,run,steps,head,flag,count,good⟩:=CloseoutRowsSupportStream.FamilyCold.family_run
    sym P (P+1) V C T core W L (CloseoutRowsSupportStream.FamilyCosts.termCost S P)
    (CloseoutRowsSupportStream.FamilyCosts.sumCost S P) k q bits
    (SignedSortKey.binary (natBitLength core) core) ambient supports hC le_rfl hf.circuit
    (hf.raw.trans (Nat.le_succ _)) hf.raw (hf.header.trans (Nat.le_succ _))
    (fun field hi=>(hf.guard field hi).trans (Nat.le_succ _))
    (fun field hi _=>(hf.append field hi).trans (Nat.le_succ _)) hf.read hf.coefficientWidth
    hf.mass hf.bits hf.native (CloseoutRowsSupportStream.FamilyCosts.term_cost S P V C T k core _ _ hf hlen hcore)
    hstore hq hk hp hd hf.check (CloseoutRowsSupportStream.FamilyCosts.sum_cost S P V C T k _ _ hf hlen)
  refine ⟨actual,run,steps.trans (CloseoutRowsSupportStream.FamilyCosts.total_cost S P V C T k _ _ hf hv),head,flag,?_⟩
  intro accepted
  obtain ⟨after,hh,ht,hs⟩:=good accepted
  refine ⟨⟨extra,after,count,?_,?_,hs⟩,?_,?_⟩
  · funext i
    rw [hh]
    exact Fin.addCases_left i
  · funext i
    rw [ht]
    exact Fin.addCases_left i
  · rw [hh]
    exact Fin.addCases_right (0 : Fin 1)
  · rw [ht]
    exact Fin.addCases_right (0 : Fin 1)

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.FamilySupport
