import Proof.Assembly.ColdSource
import Proof.SourceAssembly.SourceRefill
import Proof.MachineModel.CacheRewind
import Proof.MachineModel.FrameSkip
import Proof.MachineModel.OccurrenceRun
import Proof.Hierarchy.HierarchyFixedWord
import Proof.PCP.PCPPQueryNatural
import Proof.PCP.ProjectionDimensionPolynomialBounds

section

/-! One loose source-fixed preprocessing polynomial includes the capacity
factory, every source occurrence, allocation and all finalizer returns. -/
namespace NearCubicWires.ExtDecompositionBatch.Cold
open LocalBitMultitape RepairOrdinary RepairRepresentation ExecutableInterfaces
open RepairOrdinary.DecompositionSource RepairOrdinary.RecoveryRootRound SupplierPipeline
open RepairOrdinary.CloseoutRowsCircuitBottom
open RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
variable (a:DecompositionAlgorithm)

theorem round_sum_bound {q:ℕ} (C:ℕ) (occ:List (SupportedNormalizedGate q))
    (hb:∀g∈occ,bodyCost a q g<C):roundSum a C occ≤occ.length*(4*C+9):=by
  induction occ with
  | nil=>simp [roundSum]
  | cons g occ ih=>
    have head:=hb g (by simp)
    have tail:=ih (fun k hk=>hb k (by simp [hk]))
    simp only [roundSum,List.map_cons,List.sum_cons,List.length_cons,roundCost]
    change 2*bodyCost a q g+2+1+(2*C+4)+2+roundSum a C occ≤_
    nlinarith

theorem batch_bound {q:ℕ} (P:ℕ) (occ:List (SupportedNormalizedGate q)) (top:List Bool)
    (hq:q≤P) (hi:(segment occ top).length≤1000*(P+2)^2):
    batchBudget a (SourceEnvelope.capacity a P) occ top≤64*(SourceEnvelope.capacity a P+1)^2:=by
  let C:=SourceEnvelope.capacity a P
  obtain ⟨body,hn,hh,hb,_hc,header⟩:=SourceEnvelope.actual_capacity a occ top P hq hi
  obtain ⟨qU,nU,bU,_,_⟩:=SourceEnvelope.actual_bounds a occ top P hq hi
  have cover:=SourceEnvelope.capacity_covers a P
  have uc:SourceEnvelope.aggregate a P≤C:=by dsimp [C];nlinarith
  have qc:q≤C:=qU.trans uc
  have nc:occ.length≤C:=nU.trans uc
  have bc:B a occ≤C:=bU.trans uc
  have topc:top.length≤C:=by
    have h:=SourceEnvelope.source_position a occ top P hi
    rw [segment_length] at h
    have f:=word_le_frame top
    dsimp only [C]
    omega
  have sum:roundSum a C occ≤C*(4*C+9):=
    (round_sum_bound a C occ body).trans (Nat.mul_le_mul_right _ nc)
  have prod:=Nat.mul_le_mul qc bc
  change batchBudget a C occ top≤64*(C+1)^2
  unfold batchBudget Prelude.occurrenceBudget Prelude.budget PreludeHeader.budget loopCost FinalLayout.finalCost
  change (2*PCPPQueryNatural.budget occ.length+2*C+7+1+(2*top.length+3))+1+
    (roundSum a C occ+occ.length+3)+1+
    ((bodyWord a occ).length+(6*q+15)*B a occ+2*PCPPNativeNaturalAppend.budget (B a occ)+4*C+28)≤_
  change PCPPNativeNaturalAppend.budget (B a occ)≤C at hh
  change (bodyWord a occ).length≤C at hb
  change PCPPQueryNatural.budget occ.length<C at header
  nlinarith

theorem capacity_square (P:ℕ):
    (SourceEnvelope.capacity a P+1)^2≤(SourceEnvelope.coefficient a+1)^2*
      (P+2)^(2*SourceEnvelope.degree a+2):=by
  have one:1≤(P+1)^SourceEnvelope.degree a:=Nat.one_le_pow _ _ (by omega)
  have le:SourceEnvelope.capacity a P+1≤
      (SourceEnvelope.coefficient a+1)*(P+1)^SourceEnvelope.degree a:=by
    unfold SourceEnvelope.capacity
    nlinarith
  have sq:=Nat.pow_le_pow_left le 2
  have powers:((P+1)^SourceEnvelope.degree a)^2≤(P+2)^(2*SourceEnvelope.degree a+2):=by
    rw [←pow_mul]
    exact (Nat.pow_le_pow_left (by omega : P+1≤P+2) _).trans
      (Nat.pow_le_pow_right (by omega) (by omega))
  rw [mul_pow] at sq
  exact sq.trans (Nat.mul_le_mul_left _ powers)

def runtimeCoefficient:=DimensionPolynomial.coefficient (SourceEnvelope.degree a)
  (SourceEnvelope.coefficient a)+128*(SourceEnvelope.coefficient a+1)^2
def runtimeDegree:=2*SourceEnvelope.degree a+2

theorem budget_bound {q:ℕ} (P:ℕ) (occ:List (SupportedNormalizedGate q)) (top:List Bool)
    (hq:q≤P) (hi:(segment occ top).length≤1000*(P+2)^2):
    budget a P occ top≤runtimeCoefficient a*(P+2)^runtimeDegree a:=by
  have b:=batch_bound a P occ top hq hi
  have factory:=DimensionPolynomial.budget_bound (SourceEnvelope.degree a) (SourceEnvelope.coefficient a) P
  have square:=capacity_square a P
  have scaled:=Nat.mul_le_mul_left 128 square
  unfold budget entryBudget runtimeCoefficient runtimeDegree
  nlinarith

end NearCubicWires.ExtDecompositionBatch.Cold

end
