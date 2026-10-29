import Proof.Gates.TabMachine.Mono4

/-! # All monomials at one inner point

Proof of lem:print: at the inner point `c`, every monomial of `Q` in order. The occurrence stream holds the code
of the monomials, `codeRecs ts` (per monomial its occurrence count, then its occurrence blocks); the coefficient
stream `Z 56` holds the coefficients, one record each. **`pointBody_spec`**: a record loop over the coefficients runs
`monoStep` per monomial, so the cut stream gains `cutsOf Wd s c ts`, the fields of `Code.pointCutsL c`; the read
index is reset to `0` for the next point. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicGates.Close.TabMachine
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length binary_value)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (NumOn)
open NearCubicGates.Close.WordPrograms.SInt (encS sval SNumOn)
open NearCubicGates.Close.Tabulator
open StablePartition.Workspace (overlay)

variable {ns nr : ℕ}

/-! ## The code of the monomials (value level) -/

/-- One monomial's block: its occurrence count, then its occurrences. -/
def blkRecs (t : List Occ × ℤ) : List ℕ := t.1.length :: t.1.flatMap occRecs

def blkLen (t : List Occ × ℤ) : ℕ := 1 + (t.1.map occLen).sum

/-- The occurrence stream's numbers. -/
def codeRecs (ts : List (List Occ × ℤ)) : List ℕ := ts.flatMap blkRecs

def termStart (ts : List (List Occ × ℤ)) (i : ℕ) : ℕ := ((ts.take i).map blkLen).sum

theorem flatMap_occRecs_length (os : List Occ) : (os.flatMap occRecs).length = (os.map occLen).sum := by
  induction os with
  | nil => simp
  | cons o os ih => simp [List.flatMap_cons, occRecs_length, ih]

theorem blkRecs_length (t : List Occ × ℤ) : (blkRecs t).length = blkLen t := by
  unfold blkRecs blkLen; rw [List.length_cons, flatMap_occRecs_length]; ring

theorem flatMap_drop_sum {α β : Type} (f : α → List β) (len : α → ℕ) (hlen : ∀ a, (f a).length = len a) :
    ∀ (L : List α) (j : ℕ) (hj : j < L.length) (rest : List β),
      (L.flatMap f ++ rest).drop ((L.take j).map len).sum = f L[j] ++ ((L.drop (j + 1)).flatMap f ++ rest)
  | [], j, hj, _ => by simp at hj
  | a :: L, 0, _, rest => by simp [List.append_assoc]
  | a :: L, j + 1, hj, rest => by
    simp only [List.take_succ_cons, List.map_cons, List.sum_cons, List.flatMap_cons, List.append_assoc,
      List.getElem_cons_succ, List.drop_succ_cons]
    rw [← hlen a, ← List.drop_drop, List.drop_left]
    exact flatMap_drop_sum f len hlen L j (by simp at hj; omega) rest

theorem code_drop (ts : List (List Occ × ℤ)) (i : ℕ) (hi : i < ts.length) :
    (codeRecs ts).drop (termStart ts i) = blkRecs ts[i] ++ (ts.drop (i + 1)).flatMap blkRecs := by
  have := flatMap_drop_sum blkRecs blkLen blkRecs_length ts i hi []
  simpa [codeRecs, termStart] using this

theorem code_count (ts : List (List Occ × ℤ)) (i : ℕ) (hi : i < ts.length) :
    termStart ts i < (codeRecs ts).length ∧ ∀ h : termStart ts i < (codeRecs ts).length,
      (codeRecs ts)[termStart ts i] = ts[i].1.length := by
  have e := code_drop ts i hi
  have hlen : 0 < ((codeRecs ts).drop (termStart ts i)).length := by rw [e]; simp [blkRecs]
  rw [List.length_drop] at hlen
  refine ⟨by omega, fun h => ?_⟩
  have := congrArg (fun l => l[0]?) e
  simp only [List.getElem?_drop, Nat.add_zero, List.getElem?_eq_getElem h, blkRecs, List.cons_append,
    List.getElem?_cons_zero, Option.some.injEq] at this
  exact this

theorem code_occ (ts : List (List Occ × ℤ)) (i : ℕ) (hi : i < ts.length) (j : ℕ) (hj : j < ts[i].1.length) :
    ((codeRecs ts).drop (posOf (termStart ts i + 1) ts[i].1 j)).take (occLen ts[i].1[j]) = occRecs ts[i].1[j] := by
  unfold posOf
  rw [← List.drop_drop, ← List.drop_drop, code_drop ts i hi]
  simp only [blkRecs, List.cons_append, List.drop_succ_cons, List.drop_zero]
  rw [flatMap_drop_sum occRecs occLen occRecs_length ts[i].1 j hj, ← occRecs_length, List.take_left]

theorem termStart_succ (ts : List (List Occ × ℤ)) (i : ℕ) (hi : i < ts.length) :
    termStart ts (i + 1) = termStart ts i + blkLen ts[i] := by
  unfold termStart
  rw [List.take_add_one, List.getElem?_eq_getElem hi]
  simp only [Option.toList_some, List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons,
    List.sum_nil, Nat.add_zero]

theorem posOf_end (ts : List (List Occ × ℤ)) (i : ℕ) (hi : i < ts.length) :
    posOf (termStart ts i + 1) ts[i].1 ts[i].1.length = termStart ts (i + 1) := by
  rw [termStart_succ ts i hi]
  unfold posOf blkLen
  rw [List.take_of_length_le le_rfl]; ring

theorem termStart_length (ts : List (List Occ × ℤ)) : termStart ts ts.length = (codeRecs ts).length := by
  unfold termStart codeRecs
  rw [List.take_of_length_le le_rfl, List.length_flatMap]
  congr 1; apply List.map_congr_left; intro t _; exact (blkRecs_length t).symm

/-- The cut records of the monomials `ts` at the inner point `c` (stacking width `Wd`). -/
def cutsOf (Wd s c : ℕ) (ts : List (List Occ × ℤ)) : List Bool :=
  ts.flatMap fun t => (monoTuples c t.1).flatMap (cutRecs Wd s t.2)

def cutCount (c : ℕ) (ts : List (List Occ × ℤ)) : ℕ := (ts.map fun t => (monoTuples c t.1).length).sum

theorem cutsOf_take_succ (Wd s c : ℕ) (ts : List (List Occ × ℤ)) (i : ℕ) (hi : i < ts.length) :
    cutsOf Wd s c (ts.take (i + 1)) = cutsOf Wd s c (ts.take i) ++ (monoTuples c ts[i].1).flatMap (cutRecs Wd s ts[i].2) := by
  unfold cutsOf; rw [List.take_add_one, List.getElem?_eq_getElem hi]
  simp only [Option.toList_some, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]

theorem cutCount_take_succ (c : ℕ) (ts : List (List Occ × ℤ)) (i : ℕ) (hi : i < ts.length) :
    cutCount c (ts.take (i + 1)) = cutCount c (ts.take i) + (monoTuples c ts[i].1).length := by
  unfold cutCount; rw [List.take_add_one, List.getElem?_eq_getElem hi]
  simp only [Option.toList_some, List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons,
    List.sum_nil, Nat.add_zero]

/-! ## The cut machine between points -/

section CutRest
variable (Z : Fin 64 ↪ Fin (ns + 1)) (Y : Fin 112 ↪ Fin nr)

/-- `MonoRest` without the point and the coefficient (their work streams only rewound and short). -/
structure CutRest (cap W s k : ℕ) (xs : List ℕ) (out L0 : List Bool) (g p : ℕ) (σ : WState ns nr) : Prop where
  rest : GRest Z Y cap W s k σ
  r98 : σ.val (Y 98) = 0
  r99 : σ.val (Y 99) = 0
  r44 : σ.val (Y 44) = 0
  r47 : σ.val (Y 47) = 0
  pg : ∃ junk, σ.st (Z 46) = recStream (xs.map (binary (W + 1))) ++ junk
  pgh : σ.sh (Z 46) = 0
  w43h : σ.sh (Z 43) = 0
  w43l : (σ.st (Z 43)).length ≤ 2 * ((s + 1) * (W + 1)) + 1
  w54h : σ.sh (Z 54) = 0
  w54l : (σ.st (Z 54)).length ≤ 2 * (W + 1) + 1
  cut : OutOn σ (Z 34) (Y 56) out L0
  gc : σ.val (Y 74) = g
  idx : σ.val (Y 77) = p

theorem cutRest_of_mono {cap W s k : ℕ} {xs : List ℕ} {c : ℕ} {coef : ℤ} {out L0 : List Bool} {g p : ℕ}
    {σ : WState ns nr} (h : MonoRest Z Y cap W s k xs c coef out L0 g p σ) :
    CutRest Z Y cap W s k xs out L0 g p σ where
  rest := h.rest
  r98 := h.r98
  r99 := h.r99
  r44 := h.r44
  r47 := h.r47
  pg := h.pg
  pgh := h.pgh
  w43h := h.coef.2
  w43l := by rw [h.coef.1, frame_length, binary_length]
  w54h := h.cx.2
  w54l := by rw [h.cx.1, frame_length, binary_length]
  cut := h.cut
  gc := h.gc
  idx := h.idx

/-- Every index `GRest` constrains. -/
def restIdx : List (Fin 64) :=
  w1List ++ wcList ++ [20, 21, 53, 26, 44, 45, 55] ++ [3, 47] ++ [24, 33] ++ [0, 2, 30, 31, 32]

theorem grest_out {cap W s k : ℕ} {σ τ : WState ns nr} (h : GRest Z Y cap W s k σ) (l : List (Fin 64))
    (lr : List (Fin 112)) (hfr : SameExcept σ τ (l.map Z) (lr.map Y)) (hl : ∀ i ∈ l, i ∉ restIdx)
    (hlr : ∀ r ∈ lr, r ∉ zList ∧ r ∉ [(13 : Fin 112), 32, 41, 66, 84, 89]) : GRest Z Y cap W s k τ := by
  refine grest_frame Z Y h hfr ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro i hi hm; rw [mem_map_emb] at hm; exact absurd (by unfold restIdx; simp [hi]) (hl i hm)
  · intro i hi hm; rw [mem_map_emb] at hm; exact absurd (by unfold restIdx; simp [hi]) (hl i hm)
  · intro i hi hm; rw [mem_map_emb] at hm
    exact hl i hm (by unfold restIdx; simp only [List.mem_append]; simp only [List.mem_cons, List.not_mem_nil,
      or_false] at hi ⊢; tauto)
  · intro i hi hm; rw [mem_map_emb] at hm
    exact absurd (by unfold restIdx; simp only [List.mem_append]; simp only [List.mem_cons, List.not_mem_nil,
      or_false] at hi ⊢; tauto) (hl i hm)
  · intro i hi hm; rw [mem_map_emb] at hm
    exact absurd (by unfold restIdx; simp only [List.mem_append]; simp only [List.mem_cons, List.not_mem_nil,
      or_false] at hi ⊢; tauto) (hl i hm)
  · intro i hi hm; rw [mem_map_emb] at hm
    exact absurd (by unfold restIdx; simp only [List.mem_append]; simp only [List.mem_cons, List.not_mem_nil,
      or_false] at hi ⊢; tauto) (hl i hm)
  · intro r hr hm; rw [mem_map_emb] at hm; exact absurd hr (hlr r hm).1
  · intro r hr hm; rw [mem_map_emb] at hm; exact (hlr r hm).2 hr

end CutRest

end NearCubicGates.Close.TabMachine
