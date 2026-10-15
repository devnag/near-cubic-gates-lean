import Proof.CaseAnalysis.CaseOneConstructionBound
import Proof.CaseAnalysis.CaseOneDirect
import Proof.Hierarchy.HierarchyStreamReady

/-! The complete direct original-input Case1 worker fits C.12 at the actual
final address. The same source, clock, original formula and amplifier remain
fixed; every source call, frame, search, reset and evaluation is included. -/
namespace NearCubicWires.RepairSource.CloseoutCaseOne
open RepairOrdinary ProjectionNormalization SourceInterfaces
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)

def hierarchyCoefficient {k : Nat} (H : OrdinaryHierarchy (fun n=>n^(k+2))) (Cpad : Nat) :=
  HierarchyStreamCost.coefficient source H Cpad*
    (2*H.coefficient+2)^HierarchyStreamCost.logExponent source
def hierarchyExponent (k : Nat) :=
  HierarchyStreamCost.inputExponent source+(k+2)*HierarchyStreamCost.logExponent source

theorem hierarchy_source_bound {k : Nat} (H : OrdinaryHierarchy (fun n=>n^(k+2)))
    (Cpad : Nat) (hc : H.coefficient ≤ Cpad) (hpad : k+3 ≤ Cpad)
    (r : InputRequest) (target : Nat) (hn : r.1 ≤ 2^target) :
    HierarchyStreams.budget source k H.coefficient Cpad (VerifierEncoding.code H.verifier)
      (List.ofFn r.2) ≤ hierarchyCoefficient source H Cpad*(2^target+1)^hierarchyExponent source k := by
  let V : Nat := 2^target+1
  have hV : 1 ≤ V := Nat.le_add_left 1 _
  have hN : r.1+1 ≤ V := Nat.add_le_add_right hn 1
  have hpow : 1 ≤ V^(k+2) := Nat.one_le_pow _ _ hV
  have htime : H.time r.1 ≤ 2*H.coefficient*V^(k+2) := by
    have hnV : r.1 ≤ V := by omega
    have hp := Nat.pow_le_pow_left hnV (k+2)
    unfold OrdinaryHierarchy.time
    nlinarith
  have hz : natBitLength (H.time r.1)+1 ≤ (2*H.coefficient+2)*V^(k+2) := by
    have hl := Nat.log_le_self 2 (H.time r.1)
    unfold natBitLength
    nlinarith
  have hb := HierarchyStreamCost.budget_bound source H Cpad hc hpad r
  have he := HierarchyStreams.framed_budget_eq source H Cpad hpad r
  have hs : HierarchyStreams.budget source k H.coefficient Cpad (VerifierEncoding.code H.verifier)
      (List.ofFn r.2) ≤ HierarchyStreamCost.coefficient source H Cpad*
        (r.1+1)^HierarchyStreamCost.inputExponent source*
        (natBitLength (H.time r.1)+1)^HierarchyStreamCost.logExponent source := by omega
  calc
    _ ≤ HierarchyStreamCost.coefficient source H Cpad*
        V^HierarchyStreamCost.inputExponent source*
        ((2*H.coefficient+2)*V^(k+2))^HierarchyStreamCost.logExponent source := hs.trans (by gcongr)
    _ = _ := by
      simp only [hierarchyCoefficient,hierarchyExponent,mul_pow,pow_add,pow_mul]
      ring

def directCoefficient {k : Nat} (H : OrdinaryHierarchy (fun n=>n^(k+2))) (Cpad : Nat) :=
  CloseoutHierarchyRequest.coefficient k H.coefficient+2*hierarchyCoefficient source H Cpad+
    constructorCoefficient source.coefficient+4104
def directExponent (k amplifierExponent : Nat) :=
  3+hierarchyExponent source k+constructorExponent source.degrees.queries amplifierExponent+2

theorem direct_budget_bound {c d k target : Nat} (amplifier : OrdinaryScheduleAmplifier c d)
    (H : OrdinaryHierarchy (fun n=>n^(k+2))) (Cpad : Nat)
    (hc : H.coefficient ≤ Cpad) (hpad : k+3 ≤ Cpad) (r : InputRequest)
    (hpos : 1 ≤ target) (hN : r.1 ≤ 2^target)
    (hR : HierarchyProjection.width source H Cpad r.1 ≤ target)
    (hn : (RecoveryCaseOnePaddedBit.generated source amplifier H Cpad hpad r).arity ≤ target)
    (address : BitInput target) :
    CloseoutCaseOneDirect.budget source amplifier H Cpad hpad r hn address ≤
      directCoefficient source H Cpad*(2^target+1)^directExponent source k amplifier.constructionExponent := by
  let V : Nat := 2^target+1
  let E := directExponent source k amplifier.constructionExponent
  have hv : 1 ≤ V := Nat.le_add_left 1 _
  have h1 : 1 ≤ V^E := Nat.one_le_pow _ _ hv
  have hrq := RecoveryCaseOneRequest.source_request source H (HierarchyEncode.encode H Cpad)
    (HierarchyProjection.width source H Cpad) (HierarchyProjection.queries source H Cpad)
    (HierarchyProjection.width_fits source H Cpad hpad) (HierarchyProjection.queries_fit source H Cpad hpad) r
  have hout : (amplifier.output (HierarchyProjection.width source H Cpad r.1)
      (RecoveryCaseOneRequest.request (compactProjectionPCP
        (RecoveryPCPFormulaResumeHierarchy.hierarchyNormalized source H Cpad hpad r)) r.2).function).arity ≤ target := by
    change (amplifier.output _ (RecoveryCaseOneRequest.request
      (RecoveryCaseOnePaddedBit.pcp source H Cpad hpad) r.2).function).arity ≤ target at hn
    rw [show RecoveryCaseOnePaddedBit.pcp source H Cpad hpad=
      normalizedSourcePCP source H (HierarchyEncode.encode H Cpad)
        (HierarchyProjection.width source H Cpad) (HierarchyProjection.queries source H Cpad)
        (HierarchyProjection.width_fits source H Cpad hpad) (HierarchyProjection.queries_fit source H Cpad hpad)
      from rfl,hrq] at hn
    exact hn
  have hconstruct := original_constructor_bound amplifier (source.output (HierarchyEncode.encode H Cpad r))
    (HierarchyProjection.width source H Cpad r.1) (HierarchyProjection.queries source H Cpad r.1)
    (HierarchyProjection.width_fits source H Cpad hpad r) (HierarchyProjection.queries_fit source H Cpad hpad r)
    r.2 source.coefficient source.degrees.queries target hpos hR (HierarchyProjection.query_bound source H Cpad r.1) hout
  obtain ⟨he,hwidth,hqueries⟩ := HierarchyStreams.hierarchy_dimensions source H Cpad hpad r
  have hs := hierarchy_source_bound source H Cpad hc hpad r target hN
  have hsE := hs.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega : 0 < V)
    (by dsimp [E,directExponent]; omega : hierarchyExponent source k ≤ E)))
  have hcE := hconstruct.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega : 0 < V)
    (by dsimp [E,directExponent]; omega : constructorExponent source.degrees.queries amplifier.constructionExponent ≤ E)))
  have hb := CloseoutHierarchyRequest.budget_bound k H.coefficient (List.ofFn r.2)
  simp only [List.length_ofFn] at hb
  have hbV := hb.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right hN 1) 3))
  have hbE := hbV.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega : 0 < V)
    (by dsimp [E,directExponent]; omega : 3 ≤ E)))
  have hev := padded_evaluation_bound (RecoveryCaseOnePaddedBit.generated source amplifier H Cpad hpad r).function hn address
  have heV := hev.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left
    (Nat.add_le_add_right (Nat.pow_le_pow_right (by decide) hn) 1) 2))
  have heE := heV.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega : 0 < V)
    (by dsimp [E,directExponent]; omega : 2 ≤ E)))
  change _ ≤ directCoefficient source H Cpad*V^E
  unfold CloseoutCaseOneDirect.budget RecoveryCaseOnePaddedBit.budget RecoveryCaseOneHierarchy.budget
    RecoveryPCPFormulaResumeProofSource.budget
  simp only [he,hwidth,hqueries]
  unfold directCoefficient
  nlinarith

end
end NearCubicWires.RepairSource.CloseoutCaseOne
