import Proof.Amplification.RecoveryCompactCertificatePayload
import Proof.Amplification.RecoveryRawSyntaxSize

/-! Exact all-code existential certificate gate for correctedSat. Invalid raw
Boolean tags retain the existing decoder's accepted empty-formula default;
valid raw formulas retain raw-first dispatch. No prefix clauses are expanded. -/
namespace NearCubicWires.RepairSource.RecoveryOracle.CompactCertificate
open CanonicalBinary BalancedCNFSATEncoding BalancedCertificate
open private decodeClauseCodes from StatementSupport
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def markerCheck (formula : EncodedCNF) (table : FiniteValuation.Table)
    (inner outer : List Row) : Bool :=
  match formula with
  | [[],[(true,payload)]] => rootCheck (clausePredicate 0 0 table) outer payload
  | [[],[(true,payload)],[(false,committed),(true,count)]] =>
      rootCheck (clausePredicate committed count table) outer payload
  | [[],[(false,payload)]] => nestedCheck (clausePredicate 0 0 table) inner outer payload
  | [[],[(false,payload)],[(false,committed),(true,count)]] =>
      nestedCheck (clausePredicate committed count table) inner outer payload
  | _ => false

theorem mapped_meaning (decoded : Option (List Nat)) (committed count : Nat) :
    (∃ codes,decoded=some codes ∧ compactMeaning ⟨decodeClauseCodes codes,committed,count⟩) ↔
      ∃ request,decoded.map (fun codes => (⟨decodeClauseCodes codes,committed,count⟩ : CompactRequest))=
        some request ∧ compactMeaning request := by
  cases decoded <;> simp

theorem markerCheck_iff (code : Nat) :
    (∃ table inner outer,markerCheck (decodeCNF code) table inner outer=true) ↔
      (∃ request,decodeFlatCompact code=some request ∧ compactMeaning request) ∨
      (∃ request,decodeNestedCompact code=some request ∧ compactMeaning request) := by
  unfold markerCheck
  split
  next payload hmarker =>
    simp only [exists_const]
    rw [flat_payload_iff,mapped_meaning]
    simp [decodeFlatCompact,decodeNestedCompact,hmarker]
  next payload committed count hmarker =>
    simp only [exists_const]
    rw [flat_payload_iff,mapped_meaning]
    simp [decodeFlatCompact,decodeNestedCompact,hmarker]
  next payload hmarker =>
    rw [nested_payload_iff,mapped_meaning]
    simp [decodeFlatCompact,decodeNestedCompact,hmarker]
  next payload committed count hmarker =>
    rw [nested_payload_iff,mapped_meaning]
    simp [decodeFlatCompact,decodeNestedCompact,hmarker]
  next hother =>
    simp only [Bool.false_eq_true,exists_false,false_iff]
    simp only [decodeFlatCompact,decodeNestedCompact]
    simp_all

def formulaCheck (code : Nat) (formula : EncodedCNF) (table : FiniteValuation.Table)
    (inner outer : List Row) : Bool :=
  if wellSizedCNFEncoding code formula then FiniteValuation.check ⟨formula,0,0⟩ table
  else markerCheck formula table inner outer

theorem formulaCheck_iff (code : Nat) :
    (∃ table inner outer,formulaCheck code (decodeCNF code) table inner outer=true) ↔
      correctedSat code=true := by
  rw [← correctedWitnessVerifier_iff]
  by_cases hraw : wellSizedCNFEncoding code (decodeCNF code)=true
  · simp only [formulaCheck,correctedWitnessVerifier,if_pos hraw,exists_const]
    rw [FiniteValuation.check_iff,compactVerifier_iff]
  · simp only [formulaCheck,correctedWitnessVerifier,if_neg hraw]
    rw [markerCheck_iff]
    cases hf : decodeFlatCompact code with
    | some request =>
      have hn : decodeNestedCompact code=none := by
        unfold decodeFlatCompact at hf
        split at hf <;> simp_all [decodeNestedCompact]
      simpa [hn] using (compactVerifier_iff request).symm
    | none =>
      cases hn : decodeNestedCompact code with
      | some request =>
        simpa using (compactVerifier_iff request).symm
      | none => simp

structure Certificate where
  view : RawSyntaxCertificate.View
  table : FiniteValuation.Table
  inner : List Row
  outer : List Row

def check (code : Nat) (certificate : Certificate) : Bool :=
  RawSyntaxCertificate.check code certificate.view &&
    if RawSyntaxCertificate.tagsValid certificate.view then
      formulaCheck code (RawSyntaxCertificate.project certificate.view)
        certificate.table certificate.inner certificate.outer
    else true

theorem check_sound (code : Nat) (certificate : Certificate) (hc : check code certificate=true) :
    correctedSat code=true := by
  simp only [check,Bool.and_eq_true] at hc
  cases ht : RawSyntaxCertificate.tagsValid certificate.view with
  | false => exact RawSyntaxCertificate.invalid_raw_accepted code certificate.view hc.1 ht
  | true =>
    have hd : decodeCNF code=RawSyntaxCertificate.project certificate.view := by
      rw [RawSyntaxCertificate.certified_default code certificate.view hc.1,ht]
      rfl
    apply (formulaCheck_iff code).mp
    refine ⟨certificate.table,certificate.inner,certificate.outer,?_⟩
    rw [hd]
    simpa only [ht,ite_true] using hc.2

theorem check_iff (code : Nat) :
    (∃ certificate,check code certificate=true) ↔ correctedSat code=true := by
  constructor
  · rintro ⟨certificate,hc⟩; exact check_sound code certificate hc
  · intro hs
    obtain ⟨view,hv⟩ := RawSyntaxCertificate.exists_view code
    cases ht : RawSyntaxCertificate.tagsValid view with
    | false => exact ⟨⟨view,[],[],[]⟩,by simp [check,hv,ht]⟩
    | true =>
      have hd : decodeCNF code=RawSyntaxCertificate.project view := by
        rw [RawSyntaxCertificate.certified_default code view hv,ht]
        rfl
      obtain ⟨table,inner,outer,hc⟩ := (formulaCheck_iff code).mpr hs
      exact ⟨⟨view,table,inner,outer⟩,by simpa [check,hv,ht,← hd] using hc⟩

end NearCubicWires.RepairSource.RecoveryOracle.CompactCertificate
