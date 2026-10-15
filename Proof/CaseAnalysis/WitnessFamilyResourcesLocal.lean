import Proof.CaseAnalysis.CloseoutWitnessFamilyColdRun
import Proof.PCP.PCPPQueryCost

/-! Uniform numerical bounds for the unchanged all-raw family parser.
The scalar S includes the actual source quantities; its eventual polynomial
degree is fixed before the hierarchy clock. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.FamilyResources
open LocalBitMultitape CompetitorSumFold CompetitorSumWidth
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def capacity (S : ℕ) := 100000000000000000000000000000000*(S+2)^26
def parser (S : ℕ) := 1000000000000000000000*(S+2)^24

theorem code_length (bits : List Bool) (i : Fin 2) :
    (PairHeader.codeWord bits i).length=bits.length := RationalCold.code_length bits i

theorem sum_count (bits : List Bool) : SumFields.count bits ≤ bits.length+1 := by
  have h:=Reencode.count_bound (SumFields.listCode bits)
  simpa only [SumFields.count,SumFields.atoms,TraversalCounted.count,
    SumFields.listCode,code_length] using h

theorem payload_length (bits : List Bool) : (SumFields.payload bits).length ≤ bits.length+1 := by
  have h:=Reencode.count_bound (SumFields.arityCode bits)
  simpa only [SumFields.payload,BitFields.payload,Reencode.fields,List.length_map,
    TraversalCounted.count,SumFields.arityCode,code_length] using h

theorem rational_cold (S : ℕ) (bits : List Bool) (h : bits.length ≤ S) :
    RationalCold.budget bits ≤ parser S := by
  have h2:(bits.length+1)^2 ≤ (S+2)^24 :=
    (Nat.pow_le_pow_left (by omega : bits.length+1 ≤ S+2) 2).trans
      (Nat.pow_le_pow_right (by omega) (by decide))
  have h24:=Nat.pow_le_pow_left (by omega : bits.length+1 ≤ S+2) 24
  have h1:bits.length ≤ (S+2)^24 := h.trans ((Nat.le_add_right S 2).trans
    (Nat.le_self_pow (by decide) _))
  have hp:1 ≤ (S+2)^24 := Nat.one_le_pow _ _ (by omega)
  unfold RationalCold.budget PairHeader.budget CloseoutRowsIntegerGuard.budget
    CloseoutRowsIntegerFields.budget NatCold.budget RationalCold.numeratorWord
    RationalCold.denominatorWord parser
  rw [code_length,code_length]
  omega

theorem coefficient (S C : ℕ) (bits : List Bool) (h : bits.length ≤ S) (hc : C ≤ S) :
    TermCoefficient.budget C bits+1 ≤ 2*parser S := by
  have hw:=PCPPQueryCost.width_le C
  have hcode:(TermCoefficient.coefficientCode bits).length ≤ S := by
    simpa only [TermCoefficient.coefficientCode,code_length] using h
  have hr:=rational_cold S (TermCoefficient.coefficientCode bits) hcode
  have hd: (RationalCold.denominator (TermCoefficient.coefficientCode bits)).length ≤ S+1 :=
    (RationalCold.payload_lengths _).2.trans (by omega)
  have h2:(bits.length+1)^2 ≤ (S+2)^24 :=
    (Nat.pow_le_pow_left (by omega : bits.length+1 ≤ S+2) 2).trans
      (Nat.pow_le_pow_right (by omega) (by decide))
  have hsmall:(S+2)^2 ≤ (S+2)^24 := Nat.pow_le_pow_right (by omega) (by decide)
  have hlin:S+2 ≤ (S+2)^24 := Nat.le_self_pow (by decide) _
  have hp:1 ≤ (S+2)^24 := Nat.one_le_pow _ _ (by omega)
  have hm:(4*C+1)*(32*natBitLength C+40) ≤ 200*(S+2)^2 := by
    have ha:4*C+1 ≤ 4*(S+2) := by omega
    have hb:32*natBitLength C+40 ≤ 50*(S+2) := by omega
    have hmul:=Nat.mul_le_mul ha hb
    nlinarith
  unfold TermCoefficient.budget RationalDecision.budget RationalNormalize.budget
    RationalDecision.tailBudget PairHeader.budget
  unfold parser at hr ⊢
  omega

theorem guard (S T : ℕ) (bits arity : List Bool)
    (h : bits.length ≤ S) (ha : arity.length ≤ S) :
    SumGuard.budget bits arity T+1 ≤ parser S := by
  have hc:=sum_count bits
  have hp:=payload_length bits
  have hm: max (SumFields.payload bits).length arity.length ≤ S+1 := by omega
  have hn:=Nat.min_le_left (SumFields.count bits) T
  have h2:(bits.length+1)^2 ≤ (S+2)^24 :=
    (Nat.pow_le_pow_left (by omega : bits.length+1 ≤ S+2) 2).trans
      (Nat.pow_le_pow_right (by omega) (by decide))
  have h24:=Nat.pow_le_pow_left (by omega : bits.length+1 ≤ S+2) 24
  have h1:S+2 ≤ (S+2)^24 := Nat.le_self_pow (by decide) _
  have hpos:1 ≤ (S+2)^24 := Nat.one_le_pow _ _ (by omega)
  unfold SumGuard.budget SumFields.budget PairHeader.budget NatCold.budget
    CanonicalTest.budget Reencode.polynomialBudget CountBound.budget
    RepairSource.CloseoutSchedule.RawCompare.budget parser
  rw [show (SumFields.arityCode bits).length=bits.length by exact code_length bits 0,
    show (SumFields.listCode bits).length=bits.length by exact code_length bits 1]
  omega

theorem header (S V : ℕ) (bits : List Bool) (h : bits.length ≤ S) :
    FamilyCount.budget bits V+1 ≤ parser S := by
  have hc:=Reencode.count_bound bits
  change FamilyCount.count bits ≤ bits.length+1 at hc
  have hm:=Nat.min_le_left (FamilyCount.count bits) V
  have h24:=Nat.pow_le_pow_left (by omega : bits.length+1 ≤ S+2) 24
  have h1:S+2 ≤ (S+2)^24 := Nat.le_self_pow (by decide) _
  have hp:1 ≤ (S+2)^24 := Nat.one_le_pow _ _ (by omega)
  unfold FamilyCount.budget CanonicalTest.budget Reencode.polynomialBudget parser
  omega

theorem append (S : ℕ) (bits : List Bool) (h : bits.length ≤ S) :
    EquationHeaderAppend.budget (SumFields.count bits)+1 ≤ 200*(S+2)^2 := by
  have hc:=sum_count bits
  have hw:=PCPPQueryCost.width_le (SumFields.count bits)
  have h2:=Nat.pow_le_pow_left (by omega : SumFields.count bits ≤ S+2) 2
  unfold EquationHeaderAppend.budget
  nlinarith [sq_nonneg (S : ℤ)]

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.FamilyResources
