import Proof.Amplification.RecoveryRawSATTableWhole

/-! Exact list-code meaning of the executed outer loop and empty-tail
test. Empty formulas need no valuation parse; nonempty formulas use one
uniquely determined parser result for every clause. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRawSATTable
open RecoveryRawSAT
open RepairSource.RecoveryOracle
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
open private decodeClauseCodes from StatementSupport
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem prefix_tail_codes (P : Nat→Bool) (n code : Nat) :
    (prefixCheck P n code && decide (tailCode n code=0))=
      (RawShape.codes n code).any (fun values=>values.all P) := by
  induction n generalizing code with
  | zero=>cases code <;> simp [prefixCheck,tailCode,RawShape.codes]
  | succ n ih=>
    cases code with
    | zero=>simp [prefixCheck,RawShape.codes]
    | succ code=>
      simp only [prefixCheck,tailCode,Nat.succ_ne_zero,ne_eq,not_false_eq_true,decide_true,
        Bool.true_and,Nat.succ_sub_one,RawShape.codes,Bool.and_assoc]
      change (P (Nat.unpair code).1 &&
        (prefixCheck P n (Nat.unpair code).2 && decide (tailCode n (Nat.unpair code).2=0)))=_
      rw [ih]
      cases RawShape.codes n (Nat.unpair code).2 <;> simp

theorem answer_codes (width cap committed count total : Nat) (word : List Bool) (code : Nat) :
    answer width cap committed count total word code=
      (RawShape.codes total code).any (fun codes=>
        codes.all (clauseCheck width cap committed count word)) :=
  prefix_tail_codes _ total code

theorem parsed_clauses (width cap committed count : Nat) (word : List Bool)
    (codes : List Nat) (table : FiniteValuation.Table) (rest : List Bool)
    (hp : readList cap (readEntry width) word=some (table,rest)) :
    codes.all (clauseCheck width cap committed count word)=
      FiniteValuation.check ⟨decodeClauseCodes codes,committed,count⟩ table := by
  rw [←CompactCertificate.clause_codes_check]
  apply congrArg (fun P : Nat→Bool=>codes.all P)
  funext code
  simp only [clauseCheck,hp,Option.any_some]

theorem shared_table (width cap committed count : Nat) (word : List Bool) (codes : List Nat)
    (ha : codes.all (clauseCheck width cap committed count word)=true) :
    ∃ table,FiniteValuation.check ⟨decodeClauseCodes codes,committed,count⟩ table=true := by
  cases codes with
  | nil=>exact ⟨[],rfl⟩
  | cons code codes=>
    cases hp : readList cap (readEntry width) word with
    | none=>simp [List.all_cons,clauseCheck,hp] at ha
    | some pair=>
      exact ⟨pair.1,(parsed_clauses width cap committed count word (code::codes) pair.1 pair.2 hp).symm ▸ ha⟩

theorem accepted_codes (width cap committed count total : Nat) (word : List Bool) (code : Nat)
    (ha : answer width cap committed count total word code=true) :
    ∃ codes,RawShape.codes total code=some codes ∧
      ∃ table,FiniteValuation.check ⟨decodeClauseCodes codes,committed,count⟩ table=true := by
  rw [answer_codes] at ha
  cases hp : RawShape.codes total code with
  | none=>simp [hp] at ha
  | some codes=>
    have hc : codes.all (clauseCheck width cap committed count word)=true := by simpa [hp] using ha
    exact ⟨codes,rfl,shared_table width cap committed count word codes hc⟩

end NearCubicWires.RepairOrdinary.RecoveryRawSATTable
