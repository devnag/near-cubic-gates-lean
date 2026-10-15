import Proof.MachineModel.CapacityBounds

/-! One source-fixed polynomial covers every occurrence, actual aggregate
output and cache finalization. Its degree is selected before the guard clock. -/
namespace NearCubicWires.ExtDecompositionBatch.SourceEnvelope
open LocalBitMultitape RepairOrdinary RepairRepresentation ExecutableInterfaces
open RepairOrdinary.DecompositionSource RepairOrdinary.RecoveryRootRound SupplierPipeline
open RepairOrdinary.CloseoutRowsCircuitBottom
open RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def inputBound (P:ℕ):=4000*(P+1)^2
def aggregateCoefficient (a:DecompositionAlgorithm):=4000*(a.coefficient*4000^a.degree+1)
def aggregateDegree (a:DecompositionAlgorithm):=2*a.degree+2
def aggregate (a:DecompositionAlgorithm) (P:ℕ):=aggregateCoefficient a*(P+1)^aggregateDegree a
def coefficient (a:DecompositionAlgorithm):=16384*(aggregateCoefficient a)^2
def degree (a:DecompositionAlgorithm):=4*a.degree+4
def capacity (a:DecompositionAlgorithm) (P:ℕ):=coefficient a*(P+1)^degree a

theorem coefficient_pos (a:DecompositionAlgorithm):0<coefficient a:=by
  unfold coefficient aggregateCoefficient
  positivity

theorem input_le (a:DecompositionAlgorithm) (P:ℕ):inputBound P≤aggregate a P:=by
  have hp:(P+1)^2≤(P+1)^aggregateDegree a:=Nat.pow_le_pow_right (by omega) (by unfold aggregateDegree;omega)
  have hc:4000≤aggregateCoefficient a:=by unfold aggregateCoefficient;omega
  exact Nat.mul_le_mul hc hp

theorem aggregate_pos (a:DecompositionAlgorithm) (P:ℕ):0<aggregate a P:=by
  unfold aggregate aggregateCoefficient
  positivity

theorem capacity_covers (a:DecompositionAlgorithm) (P:ℕ):
    4096*(aggregate a P+1)^2≤capacity a P:=by
  have he:capacity a P=16384*(aggregate a P)^2:=by
    unfold capacity coefficient aggregate
    rw [mul_pow,←pow_mul]
    have hd:degree a=aggregateDegree a*2:=by unfold degree aggregateDegree;omega
    rw [hd]
    ring
  have hp:=aggregate_pos a P
  rw [he]
  nlinarith

theorem source_product (a:DecompositionAlgorithm) (P:ℕ):
    inputBound P*(a.coefficient*(inputBound P)^a.degree)≤aggregate a P:=by
  calc
    inputBound P*(a.coefficient*(inputBound P)^a.degree)=
        (4000*(a.coefficient*4000^a.degree))*(P+1)^aggregateDegree a:=by
      unfold inputBound aggregateDegree
      simp only [mul_pow,pow_add,pow_mul]
      ring
    _≤aggregate a P:=by
      apply Nat.mul_le_mul_right
      unfold aggregateCoefficient
      omega

theorem source_le (a:DecompositionAlgorithm) (P:ℕ):
    a.coefficient*(inputBound P)^a.degree≤aggregate a P:=by
  have hi:0 < inputBound P:=by unfold inputBound;positivity
  exact (Nat.le_mul_of_pos_left _ hi).trans (source_product a P)

theorem totals_le (a:DecompositionAlgorithm) {q:ℕ} (occ:List (SupportedNormalizedGate q))
    (X:ℕ) (hx:∀g∈occ,sourceBudget a (request g)≤X):
    B a occ≤occ.length*X ∧ (bodyWord a occ).length≤occ.length*X:=by
  induction occ with
  | nil => simp [B,GS,bodyWord]
  | cons g occ ih =>
    have hg:=hx g (by simp)
    obtain ⟨hn,hb⟩:=ih (fun k hk=>hx k (by simp [hk]))
    have gcount:=(children_le_budget a g).trans hg
    have gbody:=(body_le_budget a g).trans hg
    constructor
    · rw [B_cons,List.length_cons]
      nlinarith
    · simp only [bodyWord,GS_cons,List.flatMap_append,List.length_append,List.length_cons]
      change ((children a g).flatMap exactWord).length+(bodyWord a occ).length≤_
      nlinarith

theorem actual_bounds (a:DecompositionAlgorithm) {q:ℕ} (occ:List (SupportedNormalizedGate q))
    (top:List Bool) (P:ℕ) (hq:q≤P) (hi:(segment occ top).length≤1000*(P+2)^2):
    q≤aggregate a P ∧ occ.length≤aggregate a P ∧ B a occ≤aggregate a P ∧
      (bodyWord a occ).length≤aggregate a P ∧
      ∀g∈occ,(frame (nativeWord g)).length≤aggregate a P ∧ sourceBudget a (request g)≤aggregate a P:=by
  have size:(segment occ top).length≤ inputBound P:=by unfold inputBound;nlinarith
  have region:(occ.flatMap (fun g=>frame (nativeWord g))).length≤ inputBound P:=by
    rw [segment_length] at size
    omega
  have count:occ.length≤ inputBound P:=(length_le_region occ).trans region
  have fields:∀g∈occ,(frame (nativeWord g)).length≤ inputBound P:=
    fun g hg=>(frame_le_region occ g hg).trans region
  have sources:∀g∈occ,sourceBudget a (request g)≤a.coefficient*(inputBound P)^a.degree:=by
    intro g hg
    exact (sourceBudget_le_frame a g).trans
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (fields g hg) a.degree))
  have large:=input_le a P
  have product:=source_product a P
  obtain ⟨total,body⟩:=totals_le a occ _ sources
  have scaled:=Nat.mul_le_mul_right (a.coefficient*(inputBound P)^a.degree) count
  have qinput:q≤ inputBound P:=by unfold inputBound;nlinarith
  refine ⟨qinput.trans large,count.trans large,total.trans (scaled.trans product),
    body.trans (scaled.trans product),?_⟩
  intro g hg
  exact ⟨(fields g hg).trans large,(sources g hg).trans (source_le a P)⟩

theorem actual_capacity (a:DecompositionAlgorithm) {q:ℕ} (occ:List (SupportedNormalizedGate q))
    (top:List Bool) (P:ℕ) (hq:q≤P) (hi:(segment occ top).length≤1000*(P+2)^2):
    (∀g∈occ,bodyCost a q g<capacity a P) ∧
      B a occ+2≤capacity a P ∧ PCPPNativeNaturalAppend.budget (B a occ)≤capacity a P ∧
      (bodyWord a occ).length≤capacity a P ∧ (exactListWord (GS a occ)).length≤capacity a P ∧
      PCPPQueryNatural.budget occ.length<capacity a P:=by
  obtain ⟨qbound,nbound,bound,body,fields⟩:=actual_bounds a occ top P hq hi
  have cap:=capacity_covers a P
  obtain ⟨template,header,bodyFit,cache⟩:=CapacityBounds.cache_fits (GS a occ) (aggregate a P) bound body
  refine ⟨?_,template.trans cap,header.trans cap,bodyFit.trans cap,cache.trans cap,?_⟩
  · intro g hg
    have r:=CapacityBounds.round_bound a g (aggregate a P) qbound (fields g hg).1 (fields g hg).2
    nlinarith
  · have hn:=Count.budget_bound occ.length
    have sq:(occ.length+1)^2≤(aggregate a P+1)^2:=Nat.pow_le_pow_left (by omega) 2
    have scaled:=Nat.mul_le_mul_left 128 sq
    unfold Count.budget at hn
    nlinarith

theorem capacity_produced (a:DecompositionAlgorithm) (P:ℕ):∃out,
    ClockJoin.ReadyRun (DimensionPolynomial.machine (degree a) (coefficient a))
      (DimensionPolynomial.budget (degree a) (coefficient a) P)
      (DimensionPolynomial.input (degree a) P) out ∧
    out (DimensionPolynomial.rawSlot (degree a))=List.replicate (capacity a P) true:=by
  obtain ⟨out,run,_input,raw,_bits,_width⟩:=DimensionPolynomial.polynomial_run
    (degree a) (coefficient a) P (coefficient_pos a)
  exact ⟨out,run,raw⟩

end NearCubicWires.ExtDecompositionBatch.SourceEnvelope
