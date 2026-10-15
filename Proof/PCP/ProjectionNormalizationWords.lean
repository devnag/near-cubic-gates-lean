import Proof.PCP.ProjectionRealization

/-! Literal byte contract for normalizing the selected raw projection
description. Native projection and literal codes are unchanged by widening;
only constant-zero slots and stable duplicate deletion alter its lists. -/
namespace NearCubicWires.RepairSource.ProjectionNormalization
open SourceInterfaces ExecutableInterfaces ProjectionPCPPadding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def zeroCode : ℕ := projectionCode (.constant false : ProjectedRandomBit 0)
def queryRows (p : RawProjectionPCP) : List (List ℕ) :=
  List.ofFn fun j => List.ofFn fun i => projectionCode (p.queryBits j i)
def clauseCodes {q : ℕ} (c : Fin 3 → Literal q) : List ℕ := List.ofFn fun i => literalCode (c i)
def normalizedRows (p : RawProjectionPCP) (R Q : ℕ) : List (List ℕ) :=
  (queryRows p).map (fun row => row ++ List.replicate (R-p.width) zeroCode) ++
    List.replicate (Q-p.queries) (List.replicate R zeroCode)

@[simp] theorem projection_lift {r R : ℕ} (h : r ≤ R) (p : ProjectedRandomBit r) :
    projectionCode (liftProjectedRandomBit h p)=projectionCode p := by
  cases p <;> rfl

@[simp] theorem literal_lift {q Q : ℕ} (h : q ≤ Q) (l : Literal q) :
    literalCode (liftQueryLiteral h l)=literalCode l := by
  cases l <;> rfl

theorem ofFn_padding {α : Type} {n N : ℕ} (h : n ≤ N) (f : Fin n → α) (a : α) :
    (List.ofFn fun i : Fin N => if hi : i.val<n then f ⟨i.val,hi⟩ else a) =
      List.ofFn f ++ List.replicate (N-n) a := by
  obtain ⟨extra,rfl⟩ := Nat.exists_eq_add_of_le h
  rw [List.ofFn_add]
  simp only [Fin.val_castLE,Fin.is_lt,↓reduceDIte,Nat.add_sub_cancel_left]
  congr 1
  have he : (fun i : Fin extra => if hi : (i.natAdd n).val<n then f ⟨(i.natAdd n).val,hi⟩ else a)=
        fun _ : Fin extra => a := by
    funext i
    simp only [Fin.val_natAdd]
    rw [dif_neg (by omega)]
  rw [he,List.ofFn_const]

theorem normalized_bit_code (p : RawProjectionPCP) (R Q : ℕ) (hr : p.width ≤ R) (hq : p.queries ≤ Q)
    {n : ℕ} (x : BitInput n) (j : Fin Q) (i : Fin R) :
    projectionCode ((p.normalized R Q hr hq).queryAddressBits x j i)=
      if hi : i.val<p.width then
        if hj : j.val<p.queries then projectionCode (p.queryBits ⟨j.val,hj⟩ ⟨i.val,hi⟩) else zeroCode
      else zeroCode := by
  by_cases hi : i.val<p.width <;> by_cases hj : j.val<p.queries <;>
    simp [RawProjectionPCP.normalized,padProjectionPCP,RawProjectionPCP.constant,
      RawProjectionPCP.raiseQueries,hi,hj,zeroCode] <;> rfl

theorem normalized_rows (p : RawProjectionPCP) (R Q : ℕ) (hr : p.width ≤ R) (hq : p.queries ≤ Q)
    {n : ℕ} (x : BitInput n) :
    (List.ofFn fun j : Fin Q => List.ofFn fun i : Fin R =>
      projectionCode ((p.normalized R Q hr hq).queryAddressBits x j i)) = normalizedRows p R Q := by
  have hrow (j : Fin Q) :
      (List.ofFn fun i : Fin R => projectionCode ((p.normalized R Q hr hq).queryAddressBits x j i)) =
        if hj : j.val<p.queries then
          (List.ofFn fun i : Fin p.width => projectionCode (p.queryBits ⟨j.val,hj⟩ i)) ++
            List.replicate (R-p.width) zeroCode
        else List.replicate R zeroCode := by
    by_cases hj : j.val<p.queries
    · simp only [dif_pos hj]
      simp only [normalized_bit_code,dif_pos hj]
      exact ofFn_padding hr (fun i => projectionCode (p.queryBits ⟨j.val,hj⟩ i)) zeroCode
    · simp [normalized_bit_code,hj]
  simp only [hrow]
  have houter := ofFn_padding hq
    (fun j => (List.ofFn fun i => projectionCode (p.queryBits j i)) ++ List.replicate (R-p.width) zeroCode)
    (List.replicate R zeroCode)
  simpa only [normalizedRows,queryRows,List.map_ofFn,Function.comp_def] using houter

theorem literal_injective {q : ℕ} : Function.Injective (literalCode (t := q)) := by
  intro a b h
  cases a with
  | positive a =>
    cases b with
    | positive b => congr 1; apply Fin.ext; simp only [literalCode] at h; omega
    | negative b => simp only [literalCode] at h; omega
  | negative a =>
    cases b with
    | positive b => simp only [literalCode] at h; omega
    | negative b => congr 1; apply Fin.ext; simp only [literalCode] at h; omega

theorem clauseCodes_injective {q : ℕ} : Function.Injective (clauseCodes (q := q)) := by
  intro a b h
  funext i
  apply literal_injective
  have he := congrArg (fun xs : List ℕ => xs.getD i.val 0) h
  simpa only [clauseCodes,List.getD,List.getElem?_ofFn,i.isLt,↓reduceDIte,Option.getD_some] using he

theorem compact_clause_codes {q Q : ℕ} (h : q ≤ Q) (formula : ThreeCNF q) :
    ((compactThreeCNF ⟨formula.clauses.map (fun c j => liftQueryLiteral h (c j))⟩).clauses.map clauseCodes) =
      (formula.clauses.map clauseCodes).dedup := by
  rw [compactThreeCNF,← List.dedup_map_of_injective clauseCodes_injective,List.map_map]
  congr 1
  apply List.map_congr_left
  intro c _
  simp only [Function.comp_def,clauseCodes,literal_lift]

end NearCubicWires.RepairSource.ProjectionNormalization
