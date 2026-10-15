import Proof.Wire_3_5.JoinEliminationRefs

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Gauss
open NearCubicWires.WireExponent3_5.JoinElimination

/-- A row as the machine stores it: the `nvars` mask bits, low first, then the right-hand side. -/
def rowBits (nvars : ℕ) (r : Row) : List Bool := (List.range nvars).map r.1.testBit ++ [r.2]

/-- One column as one streaming pass. The state is the pivot's tail once found. -/
def pass : Option (List Bool) → List (List Bool) → List (List Bool)
  | _, [] => []
  | none, r :: rs => if r.headD false then pass (some r.tail) rs else r.tail :: pass none rs
  | some p, r :: rs => (if r.headD false then List.zipWith xor r.tail p else r.tail) :: pass (some p) rs

/-- Whether the pass found a pivot. -/
def found (reps : List (List Bool)) : Bool := reps.any (fun r => r.headD false)

/-- The streaming elimination: `c` passes from the given rows and rank. -/
def passes : ℕ → List (List Bool) × ℕ → List (List Bool) × ℕ
  | 0, st => st
  | c + 1, st => (pass none (passes c st).1, (passes c st).2 + if found (passes c st).1 then 1 else 0)

/-- **The streaming elimination.** `nvars` passes, then the consistency check on the remaining
right-hand sides. -/
def gaussDrop (nvars : ℕ) (rows : List Row) : Bool × ℕ :=
  let st := passes nvars (rows.map (rowBits nvars), 0)
  (st.1.all (fun r => !(r.headD false)), st.2)

/-! ## Correctness: `gaussDrop = gauss` -/

/-- The row at stage `c`: its bits from column `c` on. -/
def rep (nvars c : ℕ) (r : Row) : List Bool := (rowBits nvars r).drop c

/-- The pivot XOR of one elimination step. -/
def xorIf (col : ℕ) (piv r : Row) : Row :=
  if r.1.testBit col then (r.1 ^^^ piv.1, xor r.2 piv.2) else r

theorem rep_cons (nvars c : ℕ) (r : Row) (hc : c < nvars) :
    rep nvars c r = r.1.testBit c :: rep nvars (c + 1) r := by
  unfold rep
  rw [List.drop_eq_getElem_cons (by simp [rowBits]; omega)]
  congr 1
  simp [rowBits, List.getElem_append_left, hc]

theorem rep_headD (nvars c : ℕ) (r : Row) (hc : c < nvars) : (rep nvars c r).headD false = r.1.testBit c := by
  rw [rep_cons nvars c r hc]
  rfl

theorem rep_tail (nvars c : ℕ) (r : Row) : (rep nvars c r).tail = rep nvars (c + 1) r := by
  unfold rep
  rw [List.tail_drop]

theorem rep_xor (nvars c : ℕ) (r piv : Row) :
    rep nvars c (r.1 ^^^ piv.1, xor r.2 piv.2) = List.zipWith xor (rep nvars c r) (rep nvars c piv) := by
  unfold rep rowBits
  rw [← List.drop_zipWith]
  congr 1
  rw [List.zipWith_append (by simp)]
  simp [List.zipWith_map, Nat.testBit_xor]

theorem rep_bound (nvars : ℕ) (r : Row) : rep nvars nvars r = [r.2] := by
  simp [rep, rowBits]

/-- The stage invariant: bits below `c` are clear, and masks fit in `nvars` bits. -/
def Low (nvars c : ℕ) (r : Row) : Prop := r.1 < 2 ^ nvars ∧ ∀ j, j < c → r.1.testBit j = false

theorem low_xorIf (nvars c : ℕ) {piv r : Row} (hp : Low nvars c piv) (hpc : piv.1.testBit c = true)
    (hr : Low nvars c r) : Low nvars (c + 1) (xorIf c piv r) := by
  unfold xorIf
  split
  · next hb =>
    refine ⟨Nat.xor_lt_two_pow hr.1 hp.1, fun j hj => ?_⟩
    rw [Nat.testBit_xor]
    by_cases hjc : j < c
    · rw [hr.2 j hjc, hp.2 j hjc]; rfl
    · have : j = c := by omega
      subst this
      rw [hb, hpc]; rfl
  · next hb =>
    refine ⟨hr.1, fun j hj => ?_⟩
    by_cases hjc : j < c
    · exact hr.2 j hjc
    · have : j = c := by omega
      subst this
      simpa using hb

/-- The pass after the pivot: every row is XORed if its column bit is set, then drops that bit. -/
theorem pass_some (nvars c : ℕ) (hc : c < nvars) (piv : Row) (rs : List Row) :
    pass (some (rep nvars (c + 1) piv)) (rs.map (rep nvars c)) = (rs.map (xorIf c piv)).map (rep nvars (c + 1)) := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    rw [List.map_cons, List.map_cons, List.map_cons, pass, ih, rep_headD nvars c r hc]
    congr 1
    unfold xorIf
    by_cases hb : r.1.testBit c = true
    · rw [if_pos hb, if_pos hb, rep_tail, rep_xor]
    · rw [if_neg hb, if_neg hb, rep_tail]

/-- **One column.** The streaming pass computes the elimination step on the stage representations. -/
theorem pass_none (nvars c : ℕ) (hc : c < nvars) (rs : List Row) :
    pass none (rs.map (rep nvars c)) =
      (match rs.find? (fun (r : Row) => r.1.testBit c) with
        | none => rs
        | some piv => (rs.erase piv).map (xorIf c piv)).map (rep nvars (c + 1)) := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    rw [List.map_cons, pass, rep_headD nvars c r hc, List.find?_cons]
    by_cases hb : r.1.testBit c = true
    · rw [if_pos hb, rep_tail, pass_some nvars c hc r rs]
      simp only [hb, List.erase_cons_head]
    · have hb' : r.1.testBit c = false := by simpa using hb
      rw [if_neg hb, ih, rep_tail]
      simp only [hb']
      cases hf : rs.find? (fun (r : Row) => r.1.testBit c) with
      | none => rfl
      | some piv =>
        have hpiv : piv.1.testBit c = true := by
          have := List.find?_some hf
          simpa using this
        have hne : ¬ (r == piv) = true := by
          intro h
          have := beq_iff_eq.mp h
          rw [this, hpiv] at hb'
          contradiction
        simp only [List.erase_cons_tail hne, List.map_cons]
        congr 1
        unfold xorIf
        rw [if_neg hb]

theorem found_iff (nvars c : ℕ) (hc : c < nvars) (rs : List Row) :
    found (rs.map (rep nvars c)) = (rs.find? (fun (r : Row) => r.1.testBit c)).isSome := by
  unfold found
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    rw [List.map_cons, List.any_cons, List.find?_cons, rep_headD nvars c r hc, ih]
    cases r.1.testBit c <;> rfl

/-- The reference step, restated. -/
def refStep (st : List Row × ℕ) (col : ℕ) : List Row × ℕ :=
  match st.1.find? (fun r => r.1.testBit col) with
  | none => (st.1, st.2)
  | some piv => ((st.1.erase piv).map (fun r => if r.1.testBit col then (r.1 ^^^ piv.1, xor r.2 piv.2) else r),
      st.2 + 1)

theorem gauss_eq_fold (nvars : ℕ) (rows : List Row) :
    gauss nvars rows = (((List.range nvars).foldl refStep (rows, 0)).1.all (fun r => !(r.1 == 0 && r.2)),
      ((List.range nvars).foldl refStep (rows, 0)).2) := by
  show (match (List.range nvars).foldl refStep (rows, 0) with
    | (rest, rank) => (rest.all (fun r => !(r.1 == 0 && r.2)), rank)) = _
  rcases (List.range nvars).foldl refStep (rows, 0) with ⟨rs, rank⟩
  rfl

theorem refStep_eq (st : List Row × ℕ) (col : ℕ) :
    refStep st col = ((match st.1.find? (fun (r : Row) => r.1.testBit col) with
        | none => st.1 | some piv => (st.1.erase piv).map (xorIf col piv)),
      st.2 + if (st.1.find? (fun (r : Row) => r.1.testBit col)).isSome then 1 else 0) := by
  unfold refStep
  cases st.1.find? (fun (r : Row) => r.1.testBit col) with
  | none => rfl
  | some piv => rfl

theorem refStep_low (nvars c : ℕ) (st : List Row × ℕ) (hlow : ∀ r ∈ st.1, Low nvars c r) :
    ∀ r ∈ (refStep st c).1, Low nvars (c + 1) r := by
  unfold refStep
  cases hf : st.1.find? (fun r => r.1.testBit c) with
  | none =>
    intro r hr
    have hb : r.1.testBit c = false := by
      have := List.find?_eq_none.mp hf r hr
      simpa using this
    refine ⟨(hlow r hr).1, fun j hj => ?_⟩
    by_cases hjc : j < c
    · exact (hlow r hr).2 j hjc
    · have : j = c := by omega
      subst this; exact hb
  | some piv =>
    intro r hr
    have hpm := List.mem_of_find?_eq_some hf
    have hpc : piv.1.testBit c = true := by simpa using List.find?_some hf
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hr
    exact low_xorIf nvars c (hlow piv hpm) hpc (hlow s (List.mem_of_mem_erase hs))

/-- The stage invariant along the columns. -/
theorem stages (nvars : ℕ) (rows : List Row) (hlow : ∀ r ∈ rows, Low nvars 0 r) (c : ℕ) (hc : c ≤ nvars) :
    (∀ r ∈ ((List.range c).foldl refStep (rows, 0)).1, Low nvars c r) ∧
      passes c (rows.map (rep nvars 0), 0) =
        ((((List.range c).foldl refStep (rows, 0)).1.map (rep nvars c)), ((List.range c).foldl refStep (rows, 0)).2) := by
  induction c with
  | zero => exact ⟨hlow, rfl⟩
  | succ c ih =>
    obtain ⟨hl, hp⟩ := ih (by omega)
    have hcn : c < nvars := by omega
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    refine ⟨refStep_low nvars c _ hl, ?_⟩
    rw [passes, hp, refStep_eq]
    simp only
    rw [pass_none nvars c hcn _, found_iff nvars c hcn]

theorem rep_zero (nvars : ℕ) : rep nvars 0 = rowBits nvars := by
  funext r
  simp [rep]

/-- **The streaming elimination is `gauss`** (for masks below `2^nvars`). -/
theorem gaussDrop_eq (nvars : ℕ) (rows : List Row) (hrows : ∀ r ∈ rows, r.1 < 2 ^ nvars) :
    gaussDrop nvars rows = gauss nvars rows := by
  have hlow : ∀ r ∈ rows, Low nvars 0 r := fun r hr => ⟨hrows r hr, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  obtain ⟨hl, hp⟩ := stages nvars rows hlow nvars (le_refl _)
  have key : ∀ (rs : List Row), (∀ r ∈ rs, Low nvars nvars r) →
      (rs.map (rep nvars nvars)).all (fun r => !(r.headD false)) = rs.all (fun r => !(r.1 == 0 && r.2)) := by
    intro rs hrs
    induction rs with
    | nil => rfl
    | cons r rs ih =>
      have hz : r.1 = 0 := Nat.eq_of_testBit_eq (fun j => by
        by_cases hj : j < nvars
        · rw [(hrs r (List.mem_cons_self)).2 j hj]; simp
        · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (hrs r (List.mem_cons_self)).1
            (Nat.pow_le_pow_right (by norm_num) (by omega)))]
          simp)
      rw [List.map_cons, List.all_cons, List.all_cons, rep_bound, hz,
        ih (fun s hs => hrs s (List.mem_cons_of_mem r hs))]
      rfl
  rw [gauss_eq_fold, gaussDrop, ← rep_zero, hp]
  simp only
  rw [key _ hl]

/-! ## Twins: the pilot systems -/

theorem gaussDrop_twin :
    gaussDrop 8 (system 19 4 2 2 0 0 [(1, 1), (2, 2)]) = gauss 8 (system 19 4 2 2 0 0 [(1, 1), (2, 2)]) ∧
      gaussDrop 5 (system 19 4 2 2 3 5 [(1, 3), (3, 1)]) = gauss 5 (system 19 4 2 2 3 5 [(1, 3), (3, 1)]) ∧
      gaussDrop 5 (system 19 4 2 2 3 5 [(1, 1), (2, 2), (3, 0)]) =
        gauss 5 (system 19 4 2 2 3 5 [(1, 1), (2, 2), (3, 0)]) := by decide

end NearCubicWires.WireExponent3_5.Gauss
