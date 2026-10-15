import Proof.Amplification.RecoveryNestedTableMeaning

/-! Specification for the raw inspector on the existing TableFirst codec.
Only the witness list lengths guide traversal. Literal values come from
actual predecessor/unpair calls on the input code; witness scalar fields
are physically skipped. This does not assert a raw execution theorem. -/
namespace NearCubicWires.RepairSource.RecoveryOracle.RawShape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def codes : Nat → Nat → Option (List Nat)
  | 0,0 => some []
  | 0,_+1 => none
  | _+1,0 => none
  | n+1,c+1 => (codes n (Nat.unpair c).2).map ((Nat.unpair c).1 :: ·)

def clause (count code : Nat) : Option (List (Nat×Nat)) :=
  (codes count code).map (List.map Nat.unpair)

def view : List Nat → Nat → Option RawSyntaxCertificate.View
  | [],0 => some []
  | [],_+1 => none
  | _::_,0 => none
  | n::rest,c+1 => do
    let head ← clause n (Nat.unpair c).1
    let tail ← view rest (Nat.unpair c).2
    some (head::tail)

theorem codes_sound (count code : Nat) (values : List Nat) (h : codes count code=some values) :
    Encodable.encode values=code := by
  induction count generalizing code values with
  | zero =>
    cases code with
    | zero => cases h; rfl
    | succ code => simp [codes] at h
  | succ count ih =>
    cases code with
    | zero => simp [codes] at h
    | succ code =>
      cases ht : codes count (Nat.unpair code).2 with
      | none => simp [codes,ht] at h
      | some tail =>
        have he : (Nat.unpair code).1::tail=values := by simpa only [codes,ht,Option.map_some,Option.some.injEq] using h
        subst values
        rw [Encodable.encode_list_cons,ih _ _ ht]
        change Nat.pair (Nat.unpair code).1 (Nat.unpair code).2+1=code+1
        rw [Nat.pair_unpair]

theorem codes_complete (values : List Nat) : codes values.length (Encodable.encode values)=some values := by
  induction values with
  | nil => rfl
  | cons head tail ih =>
    rw [List.length_cons,Encodable.encode_list_cons,codes,Nat.unpair_pair]
    change (codes tail.length (Encodable.encode tail)).map (head::·)=_
    rw [ih]; rfl

theorem encode_unpair_map (values : List Nat) :
    Encodable.encode (values.map Nat.unpair)=Encodable.encode values := by
  induction values with
  | nil => rfl
  | cons head tail ih =>
    simp only [List.map_cons,Encodable.encode_list_cons,ih]
    change Nat.pair (Nat.pair (Nat.unpair head).1 (Nat.unpair head).2) (Encodable.encode tail)+1=_
    rw [Nat.pair_unpair]
    rfl

theorem clause_sound (count code : Nat) (values : List (Nat×Nat)) (h : clause count code=some values) :
    Encodable.encode values=code := by
  cases hc : codes count code with
  | none => simp [clause,hc] at h
  | some raw =>
    have he : raw.map Nat.unpair=values := by simpa only [clause,hc,Option.map_some,Option.some.injEq] using h
    rw [←he,encode_unpair_map]
    exact codes_sound count code raw hc

theorem view_sound (shape : List Nat) (code : Nat) (values : RawSyntaxCertificate.View)
    (h : view shape code=some values) : RawSyntaxCertificate.check code values=true := by
  apply (RawSyntaxCertificate.check_iff code values).mpr
  induction shape generalizing code values with
  | nil =>
    cases code with
    | zero => cases h; rfl
    | succ code => simp [view] at h
  | cons n shape ih =>
    cases code with
    | zero => simp [view] at h
    | succ code =>
      cases hh : clause n (Nat.unpair code).1 with
      | none => simp [view,hh] at h
      | some head =>
        cases ht : view shape (Nat.unpair code).2 with
        | none => simp [view,hh,ht] at h
        | some tail =>
          have he : head::tail=values := by simpa [view,hh,ht] using h
          subst values
          rw [Encodable.encode_list_cons,clause_sound n _ head hh,ih _ _ ht,Nat.pair_unpair]

theorem encode_literal_map (values : List (Nat×Nat)) :
    Encodable.encode (values.map Encodable.encode)=Encodable.encode values := by
  induction values with
  | nil => rfl
  | cons head tail ih =>
    simp only [List.map_cons,Encodable.encode_list_cons,ih]
    rfl

theorem unpair_literal_map (values : List (Nat×Nat)) :
    (values.map Encodable.encode).map Nat.unpair=values := by
  induction values with
  | nil => rfl
  | cons head tail ih =>
    simp only [List.map_cons,ih]
    change Nat.unpair (Nat.pair head.1 head.2)::tail=head::tail
    rw [Nat.unpair_pair]

theorem clause_complete (values : List (Nat×Nat)) : clause values.length (Encodable.encode values)=some values := by
  have hc := codes_complete (values.map Encodable.encode)
  rw [List.length_map,encode_literal_map] at hc
  rw [clause,hc,Option.map_some,unpair_literal_map]

theorem view_complete (values : RawSyntaxCertificate.View) :
    view (values.map List.length) (Encodable.encode values)=some values := by
  induction values with
  | nil => rfl
  | cons head tail ih =>
    simp [List.map_cons,Encodable.encode_list_cons,view,Nat.unpair_pair,clause_complete,ih]

theorem certified_complete (code : Nat) (values : RawSyntaxCertificate.View)
    (h : RawSyntaxCertificate.check code values=true) :
    view (values.map List.length) code=some values := by
  rw [←(RawSyntaxCertificate.check_iff code values).mp h]
  exact view_complete values

end NearCubicWires.RepairSource.RecoveryOracle.RawShape
