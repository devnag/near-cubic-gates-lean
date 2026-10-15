import Proof.CaseAnalysis.NativeWidth

/-! Fixed additive native-width increments and growth along N=2^s,
for the literal selected-source envelope used by the common language. -/
namespace NearCubicWires.RepairSource.CloseoutNativeWidth
open RepairOrdinary ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem bits_mul_bound (x C y : Nat) (h : x ≤ C*y) :
    natBitLength x ≤ natBitLength C+natBitLength y := by
  have hy : y < 2^natBitLength y := Nat.lt_pow_succ_log_self (by decide) _
  have hC : C < 2^natBitLength C := Nat.lt_pow_succ_log_self (by decide) _
  have hp : x < 2^(natBitLength C+natBitLength y) := by
    calc
      _ ≤ C*y := h
      _ ≤ 2^natBitLength C*y := Nat.mul_le_mul_right _ hC.le
      _ < 2^natBitLength C*2^natBitLength y := Nat.mul_lt_mul_of_pos_left hy (by positivity)
      _ = _ := (pow_add _ _ _).symm
  have hl:=Nat.log_lt_of_lt_pow' (by simp [natBitLength]) hp
  change Nat.log 2 x+1 ≤ _
  omega

def envelopeFactor (k degree : Nat) := 2^clockJump k*(logScale (2^clockJump k)+1)^degree
def nativeJump (k degree : Nat) := natBitLength (envelopeFactor k degree)

theorem native_step {v : OrdinaryVerifier} (source : ProjectionSourceAlgorithm v UAggregateClock.time)
    {k : Nat} (H : OrdinaryHierarchy (fun n=>n^(k+2))) (Cpad n : Nat) :
    HierarchyProjection.width source H Cpad (2*n) ≤
      HierarchyProjection.width source H Cpad n+nativeJump k source.degrees.proofLog := by
  have ht:=time_step H Cpad n
  have hlog:=HierarchyEncode.logScale_monomial_bound (2^clockJump k)
    (UAggregateClock.time (HierarchyEncode.length H Cpad n)) 0
    (UAggregateClock.time (HierarchyEncode.length H Cpad (2*n))) (by simpa using ht)
  have he : Dimensions.envelope source (HierarchyEncode.length H Cpad (2*n)) ≤
      envelopeFactor k source.degrees.proofLog*Dimensions.envelope source (HierarchyEncode.length H Cpad n) := by
    dsimp only [Dimensions.envelope]
    calc
      _ ≤ source.coefficient*(2^clockJump k*UAggregateClock.time (HierarchyEncode.length H Cpad n))*
          ((logScale (2^clockJump k)+1)*logScale (UAggregateClock.time (HierarchyEncode.length H Cpad n)))^
            source.degrees.proofLog := by gcongr
      _ = _ := by simp only [envelopeFactor,mul_pow]; ring
  have hb:=bits_mul_bound _ _ _ he
  simpa only [HierarchyProjection.width,Dimensions.width,nativeJump,Nat.add_comm] using hb

theorem input_le_envelope {v : OrdinaryVerifier} (source : ProjectionSourceAlgorithm v UAggregateClock.time)
    {k : Nat} (H : OrdinaryHierarchy (fun n=>n^(k+2))) (Cpad n : Nat) :
    n+1 ≤ Dimensions.envelope source (HierarchyEncode.length H Cpad n) := by
  have hl:=(PowerSlice.linear_length k (2*Cpad)
    (HierarchyBinary.header (VerifierEncoding.code H.verifier).length H.coefficient) n).1
  have ht:=UAggregateClock.input_le_time (HierarchyEncode.length H Cpad n)
  have hC : 1 ≤ source.coefficient := source.coefficientPositive
  have hlog : 1 ≤ logScale (UAggregateClock.time (HierarchyEncode.length H Cpad n)) :=
    Nat.clog_pos (by decide) (by omega)
  have hp:=Nat.one_le_pow source.degrees.proofLog _ hlog
  apply (hl.trans ht).trans
  dsimp only [Dimensions.envelope]
  calc
    _ = 1*UAggregateClock.time (HierarchyEncode.length H Cpad n)*1 := by ring
    _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul_right _ hC) hp

theorem native_dyadic_lower {v : OrdinaryVerifier} (source : ProjectionSourceAlgorithm v UAggregateClock.time)
    {k : Nat} (H : OrdinaryHierarchy (fun n=>n^(k+2))) (Cpad s : Nat) :
    s+1 ≤ HierarchyProjection.width source H Cpad (2^s) := by
  have hp:=(Nat.le_succ (2^s)).trans (input_le_envelope source H Cpad (2^s))
  have hl:=Nat.le_log_of_pow_le (by decide : 1 < 2) hp
  change s+1 ≤ Nat.log 2 _+1
  omega

end NearCubicWires.RepairSource.CloseoutNativeWidth
