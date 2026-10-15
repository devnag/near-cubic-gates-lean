import Proof.CaseAnalysis.CommonProgramSelected
import Proof.CaseAnalysis.CommonProgramSourceBounds

/-! Exact remaining suppliers of the fixed common program. These local
interfaces are discharged from the selected prefix, capacities and Case2
theorem; they are not additional source assumptions. -/
namespace NearCubicWires.RepairSource.CloseoutCommonProgram
open LocalBitMultitape RepairOrdinary SourceInterfaces CloseoutLanguage OrdinaryOracleCompose
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def selectedRequest (p : Parameters) (M : OrdinaryWeakMachine) (n : ℕ) : InputRequest:=
  ⟨2^index p n,selectedWord p M n⟩
def prefixFlagPort (p : Parameters):=CloseoutCommonPrefix.firstSlots (work p) p.refuter p.k
  (CloseoutRetainedRefuter.old p.refuter (CloseoutSchedule.RefuterPrefix.flagPort (work p)))

def PrefixRuns (p : Parameters) (M : OrdinaryWeakMachine) (C E : ℕ) : Prop:=
  ∀ bits : List Bool,∃ fuel ≤ C*(2^bits.length+1)^E,∃ out,
    Ready RecoveryOracle.correctedSat (prefixProgram p) fuel
      (CloseoutCommonPrefix.input (work p) p.refuter p.k bits) out ∧
    out ⟨0,(prefixProgram p).base.twoTapes.trans_lt' (by decide)⟩=frame bits ∧
    readTapeBit (out (prefixFlagPort p)) 0=decide (p.onset ≤ length p bits.length) ∧
    (p.onset ≤ length p bits.length → ∃ padding ≤ C*(2^bits.length+1)^E,
      ∀ j,out (prefixRecoveryFields p j)=RecoveryBoundedCold.sharedWords
        (hierarchyWord p (selectedRequest p M bits.length))
        (CloseoutCapacity.capacity p.Aw p.Bw bits.length) padding j)

def TwoRuns (p : Parameters) (C E : ℕ) : Prop:=
  ∀ n (point : BitInput n) (x : BitInput (2^index p n)),p.onset ≤ 2^index p n →
    RecoveryChoice.SmallOracle (globalPCP p) p.degree x →
    let r : InputRequest:=⟨2^index p n,x⟩
    ∃ out,ClockJoin.ReadyRun (two p) (C*(2^n+1)^E)
      (twoInput p (hierarchyWord p r) (recoveryDescription p r) (frame (List.ofFn point)) (R p r) (B p r)) out ∧
      out (twoLocal p 5)=frame
        (core (globalPCP p) (selectedPCPP p.sources) (selectedAmplifier p.sources.amplification p.degree)
          x p.copies (clauseWidth p.D (R p r)) n point).toNat.bits

structure Constants where
  prefixC : ℕ
  prefixE : ℕ
  recoveryC : ℕ
  recoveryE : ℕ
  twoC : ℕ
  twoE : ℕ

structure Suppliers (p : Parameters) (M : OrdinaryWeakMachine) (c : Constants) : Prop where
  onset : 1 ≤ p.onset
  copies : (selectedAmplifier p.sources.amplification p.degree).arityCoefficient ≤ p.copies
  prefixRuns : PrefixRuns p M c.prefixC c.prefixE
  two : TwoRuns p c.twoC c.twoE
  fits : ∀ n (r : InputRequest),r.1 ≤ 2^n → R p r ≤ n →
    Fits p r (CloseoutCapacity.capacity p.Aw p.Bw n)
  budget : ∀ (r : InputRequest) (W : ℕ),Fits p r W →
    recoveryBudget p r W ≤ c.recoveryC*(W+1)^c.recoveryE
  query : ∀ n,max (c.prefixC*(2^n+1)^c.prefixE)
    (c.recoveryC*(CloseoutCapacity.capacity p.Aw p.Bw n+1)^c.recoveryE) ≤
      CloseoutCapacity.capacity p.Aq p.Bq n

def oneCoefficient (p : Parameters):=CloseoutCaseOne.directCoefficient (source p) (hierarchy p) (pad p)
def oneExponent (p : Parameters):=CloseoutCaseOne.directExponent (source p) p.k
  (selectedAmplifier p.sources.amplification p.degree).constructionExponent
def runBudget (p : Parameters) (c : Constants) (bits : List Bool):=
  c.prefixC*(2^bits.length+1)^c.prefixE+
  c.recoveryC*(CloseoutCapacity.capacity p.Aw p.Bw bits.length+1)^c.recoveryE+
  CloseoutCommonQueryClear.budget p.Aq p.Bq bits+
  oneCoefficient p*(2^bits.length+1)^oneExponent p+c.twoC*(2^bits.length+1)^c.twoE+10

end
end NearCubicWires.RepairSource.CloseoutCommonProgram
