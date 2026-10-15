import Proof.Amplification.RecoveryRawSATCodes

/-! Soundness and canonical completeness of the actual raw-SAT replay.
The accepting list has one shared finite valuation; the empty formula is
accepted without requiring an unused valuation parse. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRawSATTable
open RecoveryRawSAT
open RepairSource.RecoveryOracle
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
open private decodeClauseCodes from StatementSupport
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem decode_codes (codes : List Nat)
    (hthree : (decodeClauseCodes codes).all (fun clause=>clause.length=3)=true) :
    Encodable.decode (α:=EncodedCNF) (Encodable.encode codes)=some (decodeClauseCodes codes) := by
  induction codes with
  | nil=>simp [decodeClauseCodes]
  | cons code codes ih=>
    have hc : decide (((Encodable.decode (α:=List (Bool×Nat)) code).getD []).length=3)=true ∧
        (decodeClauseCodes codes).all (fun clause=>clause.length=3)=true := by
      simpa only [decodeClauseCodes,List.map_cons,List.all_cons,Bool.and_eq_true] using hthree
    have ht := ih hc.2
    cases hd : Encodable.decode (α:=List (Bool×Nat)) code with
    | none=>simp [hd] at hc
    | some clause=>
      rw [Encodable.encode_list_cons,Encodable.decode_list_succ,Nat.unpair_pair]
      change (List.cons <$> Encodable.decode (α:=List (Bool×Nat)) code <*>
        Encodable.decode (α:=EncodedCNF) (Encodable.encode codes))=_
      rw [hd,ht]
      simp only [decodeClauseCodes,List.map_cons,hd,Option.getD_some]
      rfl

theorem accepted_meaning (width cap committed count total : Nat) (word : List Bool) (code : Nat)
    (ha : answer width cap committed count total word code=true) :
    compactMeaning ⟨decodeCNF code,committed,count⟩ := by
  obtain ⟨codes,hcodes,table,hcheck⟩ := accepted_codes width cap committed count total word code ha
  have hthree : (decodeClauseCodes codes).all (fun clause=>clause.length=3)=true := by
    have h := hcheck
    simp only [FiniteValuation.check,Bool.and_eq_true] at h
    exact h.1
  have hd : decodeCNF code=decodeClauseCodes codes := by
    unfold decodeCNF
    rw [←RawShape.codes_sound total code codes hcodes,decode_codes codes hthree]
  rw [hd]
  exact FiniteValuation.check_sound _ table hcheck

theorem encode_clause_map (formula : EncodedCNF) :
    Encodable.encode (formula.map Encodable.encode)=Encodable.encode formula := by
  induction formula with
  | nil=>rfl
  | cons clause rest ih=>
    simp only [List.map_cons,Encodable.encode_list_cons,ih]
    rfl

theorem decode_clause_map (formula : EncodedCNF) :
    decodeClauseCodes (formula.map Encodable.encode)=formula := by
  induction formula with
  | nil=>rfl
  | cons clause rest ih=>
    simp only [List.map_cons,decodeClauseCodes,Encodable.encodek,Option.getD_some] at ih ⊢
    exact congrArg (clause::·) ih

theorem canonical_answer (width cap committed count : Nat) (word : List Bool)
    (formula : EncodedCNF) (table : FiniteValuation.Table) (rest : List Bool)
    (hp : readList cap (readEntry width) word=some (table,rest))
    (hc : FiniteValuation.check ⟨formula,committed,count⟩ table=true) :
    answer width cap committed count formula.length word (Encodable.encode formula)=true := by
  have hcodes := RawShape.codes_complete (formula.map Encodable.encode)
  rw [List.length_map,encode_clause_map] at hcodes
  rw [answer_codes,hcodes,Option.any_some,
    parsed_clauses width cap committed count word _ table rest hp,decode_clause_map]
  exact hc

end NearCubicWires.RepairOrdinary.RecoveryRawSATTable
