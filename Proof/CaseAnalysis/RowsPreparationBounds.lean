import Proof.CaseAnalysis.RowsSharedInput

/-! Coarse preparation bounds for the actual positional enumerator and
cut consumer. Only the digit exponent contains the monomial population;
native cache and matrix widths occur polynomially outside that exponent. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsPreparationBounds
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def scale (n p F w N Q : ℕ) := n+p+F+w+N+Q+1
def capacity (n p F w N Q : ℕ) :=
  4096*(scale n p F w N Q)^4*2^(w*(Q+1))
def tupleEnvelope (n N p F w M k : ℕ) :=
  2*RowTupleCursorReady.capacity N w M k+N*k+
    RowCommonFixedCapacity.budget n F+2*F+4*p+30

theorem tuple_budget {n : ℕ} (gs : List (ExactThresholdGate n))
    (p F w M : ℕ) (rows : List (List Bool)) (ds : List ℕ)
    (hl : ∀ row∈rows,row.length=gs.length) (hd : ∀ d∈ds,d<rows.length) :
    RowTupleCutBody.budget gs p F w M rows ds+2 ≤ tupleEnvelope n gs.length p F w M ds.length := by
  have hc := RowTupleEquationBounds.count_le gs.length rows ds hl hd
  unfold RowTupleCutBody.budget RowTupleFramedBody.budget RowTupleCursorBody.budget
    RowTupleCursorEquation.budget RowTupleMaskReady.budget RowTupleMaskReady.capacity tupleEnvelope
    RowTupleCursorReady.capacity
  omega

theorem tuple_envelope_le (n N p F w M k U S : ℕ)
    (hn : n ≤ S) (hN : N ≤ S) (hp : p ≤ S) (hF : F ≤ S)
    (hw : w ≤ S) (hk : k ≤ S) (hM : M ≤ U) (hU : 1 ≤ U) (hS : 1 ≤ S) :
    tupleEnvelope n N p F w M k ≤ 1024*U*S^3 := by
  unfold tupleEnvelope RowTupleCursorReady.capacity RowTupleMaskLoop.budget RowTupleMaskBody.budget
    RowMaskLookupReusable.capacity RowMaskLookup.budget RowCommonFixedCapacity.budget
  calc
    _ ≤ 2*(S*(2*(U*(2*S+8*S+15)+8*S+14+S*(4*S+21)+2*S+4*S+8)+4*S+5+3)+3)+
        S*S+((S+1)*(4*S+2*S+20)+3)+2*S+4*S+30 := by gcongr
    _ ≤ 1024*U*S^3 := by
      have h12 : S ≤ S^2 := by nlinarith
      have h23 : S^2 ≤ S^3 := by nlinarith [Nat.mul_le_mul_left S h12]
      have hu0 : U ≤ U*S^3 := by nlinarith [Nat.mul_le_mul_left U (hS.trans (h12.trans h23))]
      have hu1 : U*S ≤ U*S^3 := Nat.mul_le_mul_left U (h12.trans h23)
      have hu2 : U*S^2 ≤ U*S^3 := Nat.mul_le_mul_left U h23
      have h3u : S^3 ≤ U*S^3 := by nlinarith [Nat.mul_le_mul_right (S^3) hU]
      nlinarith

theorem enumeration_le (w k Q S : ℕ) (hw : w ≤ S) (hk : k ≤ S)
    (hQ : k ≤ Q) (hS : 1 ≤ S) :
    RowTupleEnumerationReady.budget w k ≤ 1024*2^(w*Q)*S^2 := by
  have he : 2^(w*k) ≤ 2^(w*Q) := Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left w hQ)
  have hE : 1 ≤ 2^(w*Q) := Nat.one_le_two_pow
  unfold RowTupleEnumerationReady.budget RowTupleDerivedEnumeration.budget
    RowTupleDerivedEnumeration.metadataTime RowTupleDerivedEnumeration.productTime RowTupleLimit.budget
    RowTupleColdEnumeration.budget RowTupleColdFields.time RowTupleEnumeration.time
  calc
    _ ≤ 2*(2*(S*(2*S+3)+2)+2+1+(10*(S*S)+45)+1+
        ((8*S+4*(S*S)+18)+1+(2^(w*Q)*(S*(52*S+68)+40)+1+2)))+2 := by gcongr
    _ ≤ 1024*2^(w*Q)*S^2 := by
      have h12 : S ≤ S^2 := by nlinarith
      have hu0 : 2^(w*Q) ≤ 2^(w*Q)*S^2 := by
        nlinarith [Nat.mul_le_mul_left (2^(w*Q)) (hS.trans h12)]
      have hu1 : 2^(w*Q)*S ≤ 2^(w*Q)*S^2 := Nat.mul_le_mul_left _ h12
      have h2u : S^2 ≤ 2^(w*Q)*S^2 := by nlinarith [Nat.mul_le_mul_right (S^2) hE]
      nlinarith

end NearCubicWires.RepairOrdinary.CloseoutRowsPreparationBounds
