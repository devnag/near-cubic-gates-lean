import Proof.Amplification.RecoveryCertificateRow

namespace NearCubicWires.RepairSource.RecoveryOracle.CompactCertificate
open TseitinCNF
open private faithful_list faithful_prod faithful_bool faithful_nat from Proof.Amplification.RecoveryCompactSize
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def cell (code : Nat) := Nat.unpair (code-1)
def rawThree (code : Nat) : List (Nat×Nat) :=
  [Nat.unpair (cell code).1,Nat.unpair (cell (cell code).2).1,
    Nat.unpair (cell (cell (cell code).2).2).1]
def shapeThree (code : Nat) : Bool :=
  code != 0 && (cell code).2 != 0 && (cell (cell code).2).2 != 0 &&
    (cell (cell (cell code).2).2).2==0
def checkThree (committed count : Nat) (table : FiniteValuation.Table) (code : Nat) : Bool :=
  shapeThree code && (rawThree code).all (fun literal => literal.1≤1) &&
    clauseEval (FiniteValuation.assignment committed count table)
      (RawSyntaxCertificate.projectClause (rawThree code))

theorem shape_three_check (code : Nat) (hs : shapeThree code=true) :
    RawSyntaxCertificate.clauseCheck code (rawThree code)=true := by
  simpa [RawSyntaxCertificate.clauseCheck,RawSyntaxCertificate.listCheck,
    RawSyntaxCertificate.literalCheck,rawThree,shapeThree,cell,and_assoc] using hs

theorem checkThree_sound (committed count : Nat) (table : FiniteValuation.Table) (code : Nat)
    (hc : checkThree committed count table code=true) : clausePredicate committed count table code=true := by
  simp only [checkThree,Bool.and_eq_true] at hc
  have hraw := shape_three_check code hc.1.1
  have he : Encodable.encode (rawThree code)=code :=
    (RawSyntaxCertificate.listCheck_iff RawSyntaxCertificate.literalCheck
      RawSyntaxCertificate.literalCheck_iff (rawThree code) code).mp hraw
  have hd : Encodable.decode (α := List (Bool×Nat)) code=
      some (RawSyntaxCertificate.projectClause (rawThree code)) := by
    calc
      _ = Encodable.decode (α := List (Bool×Nat)) (Encodable.encode (rawThree code)) := congrArg _ he.symm
      _ = _ := by rw [RawSyntaxCertificate.decode_clause,hc.1.2]; rfl
  simp only [clausePredicate,hd,Option.getD_some]
  have hn : (RawSyntaxCertificate.projectClause (rawThree code)).length=3 := by
    simp [RawSyntaxCertificate.projectClause,rawThree]
  rw [hn]
  exact hc.2

theorem checkThree_encoded (committed count : Nat) (table : FiniteValuation.Table)
    (a b c : Bool×Nat) :
    checkThree committed count table (Encodable.encode [a,b,c])=
      clauseEval (FiniteValuation.assignment committed count table) [a,b,c] := by
  rcases a with ⟨atag,ai⟩
  rcases b with ⟨bt,bi⟩
  rcases c with ⟨ct,ci⟩
  cases atag <;> cases bt <;> cases ct <;>
    simp [checkThree,shapeThree,rawThree,cell,Encodable.encode_list_cons,
      Encodable.encode_prod_val,Encodable.encode_true,Encodable.encode_false,
      RawSyntaxCertificate.projectClause,RawSyntaxCertificate.projectLiteral]

theorem clausePredicate_eq_checkThree (committed count : Nat) (table : FiniteValuation.Table) (code : Nat) :
    clausePredicate committed count table code=checkThree committed count table code := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hc
    unfold clausePredicate at hc
    cases hd : Encodable.decode (α := List (Bool×Nat)) code with
    | none => simp [hd] at hc
    | some clause =>
      simp only [hd,Option.getD_some,Bool.and_eq_true,decide_eq_true_eq] at hc
      have he := faithful_list (faithful_prod faithful_bool faithful_nat) code clause hd
      cases clause with
      | nil => simp at hc
      | cons a rest =>
        cases rest with
        | nil => simp at hc
        | cons b rest =>
          cases rest with
          | nil => simp at hc
          | cons c rest =>
            have hr : rest=[] := List.eq_nil_of_length_eq_zero (by simpa using hc.1)
            subst rest
            rw [← he,checkThree_encoded]
            exact hc.2
  · exact checkThree_sound committed count table code

end NearCubicWires.RepairSource.RecoveryOracle.CompactCertificate
