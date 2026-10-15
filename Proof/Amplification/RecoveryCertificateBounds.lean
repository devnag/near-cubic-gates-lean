import Proof.Amplification.RecoveryCertificateValuationBounds

/-! One bounded all-code certificate, with every bound charged to the input
query length. The certificate itself is flat data, never a paired natural. -/
namespace NearCubicWires.RepairSource.RecoveryOracle.CompactCertificate
open CanonicalBinary BalancedCNFSATEncoding BalancedCertificate
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem raw_variables_le (code : Nat) (index : Nat)
    (hi : index∈(⟨decodeCNF code,0,0⟩ : CompactRequest).variables) : index≤code := by
  simp only [CompactRequest.variables,List.mem_eraseDups,List.mem_map] at hi
  obtain ⟨literal,hl,rfl⟩ := hi
  obtain ⟨clause,hc,hl⟩ := List.mem_flatten.mp hl
  exact raw_literal_le_code hc hl

theorem bounded_markerCheck (code : Nat)
    (hs : ∃ table inner outer,markerCheck (decodeCNF code) table inner outer=true) :
    ∃ table inner outer,markerCheck (decodeCNF code) table inner outer=true ∧
      DataFits code table inner outer := by
  unfold markerCheck at hs ⊢
  split at hs
  next payload hmarker =>
    simp only [exists_const] at hs
    obtain ⟨table,outer,ho,hf⟩ := bounded_flat_payload payload 0 0 hs
    exact ⟨table,[],outer,ho,hf.mono (raw_literal_le_code (literal := (true,payload))
      (clause := [(true,payload)]) (by rw [hmarker]; simp) (by simp))⟩
  next payload committed count hmarker =>
    simp only [exists_const] at hs
    obtain ⟨table,outer,ho,hf⟩ := bounded_flat_payload payload committed count hs
    exact ⟨table,[],outer,ho,hf.mono (raw_literal_le_code (literal := (true,payload))
      (clause := [(true,payload)]) (by rw [hmarker]; simp) (by simp))⟩
  next payload hmarker =>
    obtain ⟨table,inner,outer,ho,hf⟩ := bounded_nested_payload payload 0 0 hs
    exact ⟨table,inner,outer,ho,hf.mono (raw_literal_le_code (literal := (false,payload))
      (clause := [(false,payload)]) (by rw [hmarker]; simp) (by simp))⟩
  next payload committed count hmarker =>
    obtain ⟨table,inner,outer,ho,hf⟩ := bounded_nested_payload payload committed count hs
    exact ⟨table,inner,outer,ho,hf.mono (raw_literal_le_code (literal := (false,payload))
      (clause := [(false,payload)]) (by rw [hmarker]; simp) (by simp))⟩
  next => simp at hs

theorem bounded_formulaCheck (code : Nat) (hs : correctedSat code=true) :
    ∃ table inner outer,formulaCheck code (decodeCNF code) table inner outer=true ∧
      DataFits code table inner outer := by
  obtain ⟨old,oi,oo,ho⟩ := (formulaCheck_iff code).mpr hs
  unfold formulaCheck at ho ⊢
  split at ho
  next hraw =>
    simp only [if_pos hraw]
    obtain ⟨table,ht,hlen,hindices⟩ := FiniteValuation.bounded_table _ (FiniteValuation.check_sound _ old ho)
    have hbase : (decodeCNF code).length≤natBitLength code := by
      simp only [wellSizedCNFEncoding,Bool.and_eq_true,decide_eq_true_eq] at hraw
      exact hraw.1
    refine ⟨table,[],[],ht,hlen.trans (Nat.mul_le_mul_left 3 hbase),?_,by simp,by simp,by simp⟩
    intro entry he
    exact raw_variables_le code entry.1 (hindices entry he)
  next hraw =>
    simp only [if_neg hraw]
    exact bounded_markerCheck code ⟨old,oi,oo,ho⟩

def Fits (code : Nat) (certificate : Certificate) : Prop :=
  RawSyntaxCertificate.check code certificate.view=true ∧
    DataFits code certificate.table certificate.inner certificate.outer

theorem bounded_certificate (code : Nat) :
    correctedSat code=true ↔ ∃ certificate,check code certificate=true ∧ Fits code certificate := by
  constructor
  · intro hs
    obtain ⟨view,hv⟩ := RawSyntaxCertificate.exists_view code
    cases ht : RawSyntaxCertificate.tagsValid view with
    | false =>
      exact ⟨⟨view,[],[],[]⟩,by simp [check,hv,ht],hv,by simp [DataFits]⟩
    | true =>
      have hd : decodeCNF code=RawSyntaxCertificate.project view := by
        rw [RawSyntaxCertificate.certified_default code view hv,ht]
        rfl
      obtain ⟨table,inner,outer,hc,hf⟩ := bounded_formulaCheck code hs
      exact ⟨⟨view,table,inner,outer⟩,by simpa [check,hv,ht,← hd] using hc,hv,hf⟩
  · rintro ⟨certificate,hc,_⟩
    exact check_sound code certificate hc

end NearCubicWires.RepairSource.RecoveryOracle.CompactCertificate
