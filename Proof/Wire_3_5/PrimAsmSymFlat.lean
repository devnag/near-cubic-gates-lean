import Proof.Wire_3_5.PrimAsmWriterIface

/-! # PA (d)-SYM, part 11: the SYM tape as one flat stream of units (the writer loop's emissions)

The SYM writer is one bounded loop (base `Cells.ofScrub`) over a flat index `j`; unit `j` appends `symEmit j` to the
output. This module proves that the units' concatenation, closed by `false`, is C4's `BAT` word of the call
(**`symTape_flat`**): the entries in C4's order (state-major, then cell), each `entryRec` of its `R` printed rows
(`rowRec (groupExpr g)`), a printed row being the concatenation of its requests' bodies (`unitBody`: the terms of the
C2 reference expression, i.e. `exprWord` without its closing `false`, which is what C2's row machine prints before
that `false`).

The units of one entry: `[true]` (entry open), for each printed row `r`: `[true]` (row open), `M + 1` request units
(`symReqUnit`: the FILTER row's body at `s = 0`; the POP body of target `s` when `s` is in the clamp preimage), `[false]`
(row close); then `[false]` (entry close). `EU = R·(M+3) + 2` units per entry.

Paper quantity of the main type: C4's `BAT` word `symTape` (`SeedFix.blockWord` of the call's entries). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.PrimAsm.SymFlat
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Filters NearCubicWires.WireExponent3_5.Lists
open NearCubicWires.WireExponent3_5.FinalPass NearCubicWires.WireExponent3_5.FinalPass.Corner
open NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5.PrimAsm.Records NearCubicWires.WireExponent3_5.PrimAsm.Batch
open NearCubicWires.WireExponent3_5.PrimAsm.Enum NearCubicWires.WireExponent3_5.PrimAsm.WriterIface

/-- A request's printed body: the terms of its C2 reference expression. -/
def unitBody (r : RowReq) : List Bool := (refOf r).flatMap fun t => true :: ListMachine.Rec.termWord t

theorem flatMap_flatten' {α β : Type} (l : List (List α)) (f : α → List β) :
    l.flatten.flatMap f = l.flatMap fun x => x.flatMap f := by
  induction l with
  | nil => rfl
  | cons x l ih => rw [List.flatten_cons, List.flatMap_append, ih, List.flatMap_cons]

theorem exprWord_groupExpr (g : List RowReq) :
    ListMachine.Rec.exprWord (groupExpr g) = g.flatMap unitBody ++ [false] := by
  unfold ListMachine.Rec.exprWord groupExpr unitBody
  rw [flatMap_flatten', List.flatMap_map]

theorem range_mul_flatMap {α : Type} (b : ℕ) (f : ℕ → List α) :
    ∀ a, (List.range (a * b)).flatMap f = (List.range a).flatMap fun e => (List.range b).flatMap fun w => f (e * b + w)
  | 0 => by simp
  | a + 1 => by
    rw [Nat.succ_mul, List.range_add, List.flatMap_append, range_mul_flatMap b f a, List.range_succ,
      List.flatMap_append, List.flatMap_singleton, List.flatMap_map]

/-- A printed row's units: its marker, the `M + 1` request units, the close. -/
def rowEmit (M : ℕ) (req : ℕ → List Bool) (v : ℕ) : List Bool :=
  if v = 0 then [true] else if v = M + 2 then [false] else req (v - 1)

/-- An entry's units: its marker, its `R` rows' units, the close. -/
def entryEmit (R M : ℕ) (reqE : ℕ → ℕ → List Bool) (w : ℕ) : List Bool :=
  if w = 0 then [true] else if w = R * (M + 3) + 1 then [false]
  else rowEmit M (reqE ((w - 1) / (M + 3))) ((w - 1) % (M + 3))

/-- **Unit `j`'s emission** (`R` printed rows, targets `0 … M`, request units `reqUnit e r s`). -/
def symEmit (R M : ℕ) (reqUnit : ℕ → ℕ → ℕ → List Bool) (j : ℕ) : List Bool :=
  entryEmit R M (reqUnit (j / (R * (M + 3) + 2))) (j % (R * (M + 3) + 2))

theorem rowEmit_units (M : ℕ) (req : ℕ → List Bool) :
    (List.range (M + 3)).flatMap (rowEmit M req) = true :: ((List.range (M + 1)).flatMap req ++ [false]) := by
  rw [show M + 3 = M + 2 + 1 by rfl, List.range_succ, List.flatMap_append, List.flatMap_singleton,
    List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
  have h0 : rowEmit M req 0 = [true] := by unfold rowEmit; rfl
  have hl : rowEmit M req (M + 2) = [false] := by unfold rowEmit; rw [if_neg (by omega), if_pos rfl]
  have hm : ∀ s ∈ List.range (M + 1), rowEmit M req (Nat.succ s) = req s := by
    intro s hs
    have := List.mem_range.mp hs
    unfold rowEmit
    rw [if_neg (by omega), if_neg (by omega)]
    rfl
  rw [h0, hl, List.flatMap_congr hm]
  rfl

theorem entryEmit_units (R M : ℕ) (reqE : ℕ → ℕ → List Bool) :
    (List.range (R * (M + 3) + 2)).flatMap (entryEmit R M reqE) =
      true :: ((List.range R).flatMap (fun r => (List.range (M + 3)).flatMap (rowEmit M (reqE r))) ++ [false]) := by
  rw [show R * (M + 3) + 2 = R * (M + 3) + 1 + 1 by rfl, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map,
    List.range_succ, List.flatMap_append, List.flatMap_singleton]
  have h0 : entryEmit R M reqE 0 = [true] := by unfold entryEmit; rfl
  have hl : entryEmit R M reqE (Nat.succ (R * (M + 3))) = [false] := by
    unfold entryEmit; rw [if_neg (by omega), if_pos rfl]
  have hm : ∀ x ∈ List.range (R * (M + 3)),
      entryEmit R M reqE (Nat.succ x) = rowEmit M (reqE (x / (M + 3))) (x % (M + 3)) := by
    intro x hx
    have := List.mem_range.mp hx
    unfold entryEmit
    rw [if_neg (by omega), if_neg (by omega)]
    rfl
  rw [h0, hl, List.flatMap_congr hm, range_mul_flatMap (M + 3) _ R]
  have hr : ∀ r ∈ List.range R, ((List.range (M + 3)).flatMap fun w =>
      rowEmit M (reqE ((r * (M + 3) + w) / (M + 3))) ((r * (M + 3) + w) % (M + 3))) =
      (List.range (M + 3)).flatMap (rowEmit M (reqE r)) := by
    intro r _
    refine List.flatMap_congr fun w hw => ?_
    have hw' := List.mem_range.mp hw
    rw [Nat.mul_comm r, Nat.mul_add_div (by omega), Nat.div_eq_of_lt hw', Nat.add_zero, Nat.mul_add_mod,
      Nat.mod_eq_of_lt hw']
  rw [List.flatMap_congr hr]
  simp only [List.cons_append, List.nil_append]

theorem symEmit_at (R M : ℕ) (reqUnit : ℕ → ℕ → ℕ → List Bool) (e w : ℕ) (hw : w < R * (M + 3) + 2) :
    symEmit R M reqUnit (e * (R * (M + 3) + 2) + w) = entryEmit R M (reqUnit e) w := by
  unfold symEmit
  rw [Nat.mul_comm e, Nat.mul_add_div (by omega), Nat.div_eq_of_lt hw, Nat.add_zero, Nat.mul_add_mod,
    Nat.mod_eq_of_lt hw]

/-- **The flat stream of units, closed, is the block word** of the entries (generic form: `nE` entries of `R` printed
rows each, row `r` of entry `e` the group `(grpE e)[r]`, whose requests' bodies are the request units of `(e, r)`). -/
theorem units_blockWord (R M nE : ℕ) (reqUnit : ℕ → ℕ → ℕ → List Bool) (grpE : ℕ → List (List RowReq))
    (hlen : ∀ e < nE, (grpE e).length = R)
    (hunit : ∀ e < nE, ∀ r < R, ((grpE e).getD r []).flatMap unitBody = (List.range (M + 1)).flatMap (reqUnit e r)) :
    (List.range (nE * (R * (M + 3) + 2))).flatMap (symEmit R M reqUnit) ++ [false] =
      SeedFix.blockWord ((List.range nE).map fun e => (grpE e).map groupExpr) := by
  unfold SeedFix.blockWord
  rw [range_mul_flatMap _ _ nE, List.flatMap_map]
  congr 1
  refine List.flatMap_congr fun e he => ?_
  have he' := List.mem_range.mp he
  rw [List.flatMap_congr fun w hw => symEmit_at R M reqUnit e w (List.mem_range.mp hw), entryEmit_units]
  unfold SeedFix.entryRec
  congr 2
  rw [← Records.range_map_getD (grpE e) [] groupExpr, hlen e he', List.flatMap_map]
  refine List.flatMap_congr fun r hr => ?_
  have hr' := List.mem_range.mp hr
  rw [rowEmit_units]
  unfold SeedFix.rowRec
  rw [exprWord_groupExpr, hunit e he' r hr']

/-! ## The SYM call's units -/

section Sym

/-- **A SYM request unit** of printed row `r`, target `s`: the FILTER row `r`'s body at `s = 0` (rows `r < nc`), else
circuit `i = (r − nc)/2`'s POP body of target `s` in sign `+` (even) or `−` (odd), if `s` clamps to the state. -/
def symReqUnit {n a : ℕ} (sl : List (List (NormalizedThresholdGate n))) (nc : ℕ) (FP : GapParams) (e : GapSeed FP)
    (Pl : FlatListParams) (e' : Pl.FlatSeed) (m : Fin a → ℕ) (τ : Rows.SymState m) (G row nw r s : ℕ) : List Bool :=
  if r < nc then (if s = 0 then unitBody (filtRow sl FP e G row nw r) else [])
  else if hi : (r - nc) / 2 < a then
    (if hs : s < Pl.M + 1 then
      (if (Rows.clampState (m ⟨(r - nc) / 2, hi⟩) s : ℕ) =
          (if (r - nc) % 2 = 0 then ((τ ⟨(r - nc) / 2, hi⟩).1 : ℕ) else ((τ ⟨(r - nc) / 2, hi⟩).2 : ℕ))
        then unitBody (popRow sl Pl e' G row nw (nc + (r - nc) / 2) (decide ((r - nc) % 2 = 0)) ⟨s, hs⟩) else [])
     else [])
  else []

theorem flatMap_range_single (M : ℕ) (b : List Bool) :
    (List.range (M + 1)).flatMap (fun s => if s = 0 then b else []) = b := by
  rw [List.range_succ_eq_map, List.flatMap_cons, if_pos rfl, List.flatMap_map]
  have : ∀ s ∈ List.range M, (if Nat.succ s = 0 then b else []) = ([] : List Bool) := fun s _ => by simp
  rw [List.flatMap_congr this]
  simp

theorem flatMap_clampPre (M m τ : ℕ) (f : Fin (M + 1) → List Bool) (g : ℕ → List Bool)
    (hfg : ∀ s : Fin (M + 1), g s.val = if (Rows.clampState m s.val : ℕ) = τ then f s else []) :
    (clampPre M m τ).flatMap f = (List.range (M + 1)).flatMap g := by
  unfold clampPre
  have hm : (List.finRange (M + 1)).map Fin.val = List.range (M + 1) :=
    List.ext_getElem (by simp) (fun i _ _ => by simp)
  rw [← hm, List.flatMap_map]
  induction (List.finRange (M + 1)) with
  | nil => rfl
  | cons x l ih =>
    rw [List.filter_cons, List.flatMap_cons, hfg x]
    by_cases hx : (Rows.clampState m x.val : ℕ) = τ
    · rw [if_pos (by simpa using hx), if_pos hx, List.flatMap_cons, ih]
    · rw [if_neg (by simpa using hx), if_neg hx, List.nil_append, ih]

/-- **The SYM entry's rows, as request units.** -/
theorem symGroups_unit {n a : ℕ} (Cs : Fin a → NormalizedSymmetricThresholdCircuit n) (carriers : List (Carrier n))
    (FP : GapParams) (e : GapSeed FP) (Pl : FlatListParams) (e' : Pl.FlatSeed) (m : Fin a → ℕ) (τ : Rows.SymState m)
    (G row nw r : ℕ) (hr : r < carriers.length + 2 * a) :
    ((symGroups Cs carriers FP e Pl e' m τ G row nw).getD r []).flatMap unitBody =
      (List.range (Pl.M + 1)).flatMap
        (symReqUnit (symSlices Cs carriers) carriers.length FP e Pl e' m τ G row nw r) := by
  unfold symGroups
  by_cases hrc : r < carriers.length
  · rw [List.getD_append _ _ _ _ (by simpa using hrc), List.getD_eq_getElem _ _ (by simpa using hrc),
      List.getElem_map, List.getElem_range, List.flatMap_singleton]
    unfold symReqUnit
    simp only [if_pos hrc]
    rw [flatMap_range_single]
  · rw [List.getD_append_right _ _ _ _ (by simp; omega), List.length_map, List.length_range]
    have hi : (r - carriers.length) / 2 < a := by omega
    have hsplit : r - carriers.length = (r - carriers.length) / 2 * 2 + (r - carriers.length) % 2 := by omega
    rw [hsplit, getD_flatMap_uniform (List.finRange a) _ 2 (fun _ _ => rfl) [] ⟨(r - carriers.length) / 2, hi⟩
      ((r - carriers.length) / 2) ((r - carriers.length) % 2) (by simpa using hi) (Nat.mod_lt _ (by norm_num))
      ⟨(r - carriers.length) / 2, hi⟩ (by rw [List.getD_eq_getElem _ _ (by simpa using hi)]; simp)]
    unfold symReqUnit
    simp only [if_neg hrc, dif_pos hi]
    rcases Nat.mod_two_eq_zero_or_one (r - carriers.length) with h2 | h2
    · rw [h2]
      simp only [List.getD_cons_zero]
      unfold popFactor
      rw [List.flatMap_map]
      refine flatMap_clampPre Pl.M _ _ _ _ fun s => ?_
      rw [dif_pos s.isLt]
      simp only [if_pos rfl, decide_true]
      rfl
    · rw [h2]
      simp only [List.getD_cons_succ, List.getD_cons_zero]
      unfold popFactor
      rw [List.flatMap_map]
      refine flatMap_clampPre Pl.M _ _ _ _ fun s => ?_
      rw [dif_pos s.isLt]
      simp only [if_neg (by norm_num : ¬ (1 : ℕ) = 0), decide_false]
      rfl

end Sym

theorem getD_map_groupExpr (l : List (List RowReq)) (i : ℕ) :
    (l.map groupExpr).getD i [] = groupExpr (l.getD i []) := by
  rcases Nat.lt_or_ge i l.length with hi | hi
  · rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getD_eq_getElem _ _ hi, List.getElem_map]
  · rw [List.getD_eq_default _ _ (by simpa using hi), List.getD_eq_default _ _ hi]; rfl

/-- **C4's chunking of a uniform batch** is the entries' groups (`R` rows per entry). -/
theorem chunk_batchOf (N nT R : ℕ) (grp : ℕ → ℕ → List (List RowReq)) (hR : ∀ t row, (grp t row).length = R) :
    SeedFix.JLink.chunk N nT R ((batchOf nT N grp).map groupExpr) =
      (List.range (nT * N ^ 2)).map fun e => (grp (e / N ^ 2) (e % N ^ 2)).map groupExpr := by
  unfold SeedFix.JLink.chunk
  refine List.map_congr_left fun e he => ?_
  have he' := List.mem_range.mp he
  have hN : 0 < N ^ 2 := by
    rcases Nat.eq_zero_or_pos (N ^ 2) with h | h
    · rw [h, Nat.mul_zero] at he'; omega
    · exact h
  have ht : e / N ^ 2 < nT := by rw [Nat.div_lt_iff_lt_mul hN]; exact he'
  have hrow : e % N ^ 2 < N ^ 2 := Nat.mod_lt _ hN
  have hsplit : e = e / N ^ 2 * N ^ 2 + e % N ^ 2 := by rw [Nat.div_add_mod' e (N ^ 2)]
  rw [← Records.range_map_getD (grp (e / N ^ 2) (e % N ^ 2)) [] groupExpr, hR]
  refine List.map_congr_left fun r hr => ?_
  have hr' := List.mem_range.mp hr
  rw [getD_map_groupExpr]
  congr 1
  conv_lhs => rw [hsplit]
  exact batchOf_getD nT N R grp hR _ _ r ht hrow hr'

section SymCall
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E}
variable (I : PrimitiveInputs B) {n : ℕ} (hs : I.StarAt n) {a : ℕ} (Cs : Fin a → NormalizedSymmetricThresholdCircuit n)
  (carriers : List (Carrier n))

/-- The SYM call's request units (entry `e`: state `e / N²`, cell row `e % N²`). -/
def symCallUnit (e r s : ℕ) : List Bool :=
  symReqUnit (symSlices Cs carriers) carriers.length (I.filterParams .sym n)
    (symEnum I hs Cs carriers (e / (2 ^ SeedFix.callKh (I.starParams n hs)) ^ 2)).1.1 (symListParams I n a Cs carriers)
    (symEnum I hs Cs carriers (e / (2 ^ SeedFix.callKh (I.starParams n hs)) ^ 2)).1.2 (symM (I.starParams n hs) Cs)
    (symEnum I hs Cs carriers (e / (2 ^ SeedFix.callKh (I.starParams n hs)) ^ 2)).2 (symPool Cs carriers).length
    (e % (2 ^ SeedFix.callKh (I.starParams n hs)) ^ 2) n r s

theorem symTape_flat :
    (List.range (symNT I hs Cs carriers * (2 ^ SeedFix.callKh (I.starParams n hs)) ^ 2 *
      ((carriers.length + 2 * a) * ((symListParams I n a Cs carriers).M + 3) + 2))).flatMap
      (symEmit (carriers.length + 2 * a) (symListParams I n a Cs carriers).M (symCallUnit I hs Cs carriers)) ++
      [false] = symTape I hs Cs carriers := by
  unfold symTape symEnts symExprs batchExprs symBatchE symBatch
  rw [chunk_batchOf _ _ _ _ (fun t row => symGroups_length _ _ _ _ _ _ _ _ _ _ _)]
  refine units_blockWord _ _ _ _ _ (fun e _ => symGroups_length _ _ _ _ _ _ _ _ _ _ _) fun e _ r hr => ?_
  exact symGroups_unit Cs carriers _ _ _ _ _ _ _ _ _ r hr

end SymCall

end NearCubicWires.WireExponent3_5.PrimAsm.SymFlat
