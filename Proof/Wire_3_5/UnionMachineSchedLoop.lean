import Proof.Wire_3_5.UnionMachineSchedStage

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.UnionMachine.Sched
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.UnionMachine NearCubicWires.WireExponent3_5.UnionMachine.Round
open NearCubicWires.WireExponent3_5.UnionMachine.Entry NearCubicWires.BlockPlatform

section Loop
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B} (P : FusedPrimitive I)

/-- **The printed answer is short**: the rewound estimator writes `ratWord v` within `2·callBudget + 2` steps from
a blank output tape, so its denominator has at most `2·callBudget + 3` bits. -/
theorem lb_value_le (req : {req : PrimRequest // I.Call req}) : lb (P.value req.1) ≤ 2 * B.callBudget req.1.n + 3 := by
  obtain ⟨tout, hout, hstep⟩ := C10WordFunctionDock.step_of_rewound (estRW P) req
  have hfit := P1Closure.LocalSupport.step_fits hstep (estRW P).program.outputTape (2 * B.callBudget req.1.n + 3)
    (by simp [Program.inputTapes, (estRW P).program.outputFresh]) (by simp)
  rw [hout] at hfit
  have hlen : lb (P.value req.1) ≤ (ratWord (P.value req.1)).length := by
    simp only [lb, ratWord, List.length_append]
    rw [natWord_eq]; simp; omega
  exact hlen.trans hfit

/-! ## The call table of admissible entries -/

/-- A call-table entry with its admissible request. -/
structure TEntry (I : PrimitiveInputs B) where
  e : CallEntry
  req : {req : PrimRequest // I.Call req}
  hw : e.word = req.1.word

/-- The table's word. -/
def tblOf (Ls : List (TEntry I)) : List Bool := tableWord (Ls.map TEntry.e)

/-- The head position of entry `j`. -/
def posOf (Ls : List (TEntry I)) (j : ℕ) : ℕ := (((Ls.take j).map TEntry.e).flatMap entryWord).length

/-- One entry's term on accumulator `i`. -/
def termOf (p : ℕ) (t : TEntry I) (i : Fin 6) : ℕ :=
  accStep t.e (mpOf (P.value t.req.1) p) (mnOf (P.value t.req.1) p) i

/-- The accumulators after `j` entries. -/
def accOf (p : ℕ) (acc0 : Fin 6 → ℕ) (Ls : List (TEntry I)) (j : ℕ) : Fin 6 → ℕ :=
  fun i => acc0 i + ((Ls.take j).map fun t => termOf P p t i).sum

/-- The kept data after `j` entries. -/
def KOf (p : ℕ) (acc0 : Fin 6 → ℕ) (Ls : List (TEntry I)) (j : ℕ) : Kept :=
  ⟨tblOf Ls, posOf Ls j, p, accOf P p acc0 Ls j⟩

theorem tbl_split (Ls : List (TEntry I)) (j : ℕ) (hj : j < Ls.length) :
    tblOf Ls = ((Ls.take j).map TEntry.e).flatMap entryWord ++ entryWord (Ls[j]).e ++
      (((Ls.drop (j + 1)).map TEntry.e).flatMap entryWord ++ [false]) := by
  unfold tblOf tableWord
  have hM : j < (Ls.map TEntry.e).length := by simpa using hj
  conv_lhs => rw [← List.take_append_drop j (Ls.map TEntry.e), List.drop_eq_getElem_cons hM]
  simp [List.flatMap_append, List.append_assoc, List.map_take, List.map_drop]

theorem posOf_succ (Ls : List (TEntry I)) (j : ℕ) (hj : j < Ls.length) :
    posOf Ls (j + 1) = posOf Ls j + (entryWord (Ls[j]).e).length := by
  unfold posOf
  rw [List.take_succ_eq_append_getElem hj]
  simp only [List.map_append, List.flatMap_append, List.length_append, List.map_cons, List.map_nil,
    List.flatMap_cons, List.flatMap_nil, List.append_nil]

theorem accOf_succ (p : ℕ) (acc0 : Fin 6 → ℕ) (Ls : List (TEntry I)) (j : ℕ) (hj : j < Ls.length) (i : Fin 6) :
    accOf P p acc0 Ls (j + 1) i = accOf P p acc0 Ls j i + termOf P p (Ls[j]) i := by
  unfold accOf
  rw [List.take_succ_eq_append_getElem hj]
  simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  omega

theorem KOf_succ (p : ℕ) (acc0 : Fin 6 → ℕ) (Ls : List (TEntry I)) (j : ℕ) (hj : j < Ls.length) :
    nextKept (KOf P p acc0 Ls j) (Ls[j]).e (mpOf (P.value (Ls[j]).req.1) p) (mnOf (P.value (Ls[j]).req.1) p) =
      KOf P p acc0 Ls (j + 1) := by
  simp only [nextKept, KOf, posOf_succ Ls j hj]
  congr 1
  funext i
  rw [accOf_succ P p acc0 Ls j hj]; rfl

theorem tbl_cond (Ls : List (TEntry I)) (j : ℕ) (hj : j < Ls.length) :
    readTapeBit (tblOf Ls) (posOf Ls j) = true := by
  rw [tbl_split Ls j hj, posOf, List.append_assoc, readTapeBit_append, if_neg (lt_irrefl _), Nat.sub_self]
  simp [entryWord, readTapeBit]

theorem tbl_end (Ls : List (TEntry I)) : readTapeBit (tblOf Ls) (posOf Ls Ls.length) = false := by
  unfold tblOf tableWord posOf
  rw [List.take_length, show (List.map TEntry.e Ls).flatMap entryWord ++ [false] =
    (List.map TEntry.e Ls).flatMap entryWord ++ [false] from rfl, ← Nat.add_zero (List.length _), readTapeBit_app]
  rfl

theorem termOf_le (p : ℕ) (t : TEntry I) (i : Fin 6) : termOf P p t i ≤ t.e.mag * (4 * 2 ^ p) := by
  have hvs := value_small I P t.req.1 t.req.2
  have h1 := mpOf_le (P.value t.req.1) p hvs
  have h2 := mnOf_le (P.value t.req.1) p hvs
  unfold termOf accStep accAdd
  split_ifs <;> first | exact Nat.zero_le _ | (apply Nat.mul_le_mul_left; omega)

theorem accOf_le (p : ℕ) (acc0 : Fin 6 → ℕ) (Ls : List (TEntry I)) (Mmax : ℕ) (hM : ∀ t ∈ Ls, t.e.mag ≤ Mmax)
    (j : ℕ) (i : Fin 6) : accOf P p acc0 Ls j i ≤ acc0 i + j * (Mmax * (4 * 2 ^ p)) := by
  unfold accOf
  have : ((Ls.take j).map fun t => termOf P p t i).sum ≤ ((Ls.take j).map fun _ => Mmax * (4 * 2 ^ p)).sum :=
    List.sum_le_sum (fun t ht => (termOf_le P p t i).trans
      (Nat.mul_le_mul_right _ (hM t (List.mem_of_mem_take ht))))
  have h2 : ((Ls.take j).map fun _ => Mmax * (4 * 2 ^ p)).sum ≤ j * (Mmax * (4 * 2 ^ p)) := by
    rw [List.map_const', List.sum_replicate, smul_eq_mul]
    exact Nat.mul_le_mul_right _ (by simp)
  omega

/-! ## The scrubbed loop body -/

/-- The kept tapes: the table, the cell, `PC`, the accumulators. -/
def keptV (v : ℕ) : Bool := v == 0 || v == 1 || v == 13 || (decide (24 ≤ v) && decide (v ≤ 29))

/-- **The scratch selector**: every other tape, the estimator's included. -/
noncomputable def scr : Fin (NA P) → Bool := fun i => !keptV i.val

theorem scr_false (i : Fin (NA P)) (h : scr P i = false) : ∃ m : Fin 31, i = fx P m ∧ keptFx m := by
  simp only [scr, keptV, Bool.not_eq_false', Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at h
  have hi : i.val < 31 := by omega
  refine ⟨⟨i.val, hi⟩, Fin.ext (by simp [fx_val]), ?_⟩
  unfold keptFx; simp only; omega

theorem iterA_scr (cap R : ℕ) (K : Kept) (hR : cap + 1 ≤ R) (i : Fin (NA P)) (h : scr P i = true) :
    ∃ k, k ≤ R ∧ iterA P cap K i = List.replicate k false := by
  simp only [scr, keptV, Bool.not_eq_true', Bool.or_eq_false_iff, beq_eq_false_iff_ne, Bool.and_eq_false_iff,
    decide_eq_false_iff_not] at h
  unfold iterA
  split_ifs with hi
  · unfold fixedA
    simp only
    rw [if_neg (by omega), if_neg (by omega)]
    split_ifs with h3 h13 h24
    · exact ⟨0, Nat.zero_le _, rfl⟩
    · omega
    · omega
    · exact ⟨cap + 1, hR, regTape_zero cap⟩
  · exact ⟨0, Nat.zero_le _, rfl⟩

theorem iterH_scr (K : Kept) (i : Fin (NA P)) (h : scr P i = true) : iterH P K i = 0 := by
  simp only [scr, keptV, Bool.not_eq_true', Bool.or_eq_false_iff, beq_eq_false_iff_ne, Bool.and_eq_false_iff,
    decide_eq_false_iff_not] at h
  unfold iterH
  split_ifs with hi
  · unfold fixedH; simp only; rw [if_neg (by omega), if_neg (by omega), dif_neg (by omega)]
  · rfl

/-- The loop body: the stage, then the scrub of the scratch tapes. -/
noncomputable def loopBody := Scrub.machine (stageM P) (scr P) (scr P)

/-- **One scrubbed round**: the iteration's cleared bank to the next iteration's cleared bank. -/
theorem body_step (cap R Lg : ℕ) (K : Kept) (e : CallEntry) (pre rest : List Bool)
    (hK : K.tbl = pre ++ entryWord e ++ rest) (hpos : K.pos = pre.length)
    (req : {req : PrimRequest // I.Call req}) (hw : e.word = req.1.word)
    (hcapR : 2 * e.word.length + e.mag + 2 ≤ cap)
    (hcapD : 4 * lb (P.value req.1) + 8 * 2 ^ K.p + 20 ≤ cap)
    (hcapA : ∀ i : Fin 6, K.acc i + e.mag * (8 * 2 ^ K.p) ≤ cap) (hR1 : cap + 1 ≤ R)
    (hR2 : stageCost e.mag e.word.length (B.callBudget req.1.n) (lb (P.value req.1)) K.p + 1 ≤ R)
    (hL : R + 1 ≤ Lg) :
    Step (loopBody P)
      (2 * stageCost e.mag e.word.length (B.callBudget req.1.n) (lb (P.value req.1)) K.p + 2 + 1 + (2 * R + 4))
      (Scrub.heads (iterH P K)) (Scrub.bank (Scrub.blank (scr P) (iterA P cap K) R) R Lg)
      (Scrub.heads (iterH P (nextKept K e (mpOf (P.value req.1) K.p) (mnOf (P.value req.1) K.p))))
      (Scrub.bank (Scrub.blank (scr P)
        (iterA P cap (nextKept K e (mpOf (P.value req.1) K.p) (mnOf (P.value req.1) K.p))) R) R Lg) := by
  obtain ⟨H', A', hst, hkept⟩ := stage_step P cap K e pre rest hK hpos req hw hcapR hcapD hcapA
  have hc := Scrub.cleared_entry hst (scr P) R (fun i hi => iterA_scr P cap R K hR1 i hi)
  refine Scrub.step_into hc (scr P) (scr P) R Lg (fun i hi => iterH_scr P K i hi) (fun _ h => h)
    (fun i hi => by simp [Scrub.blank, hi]) hR2 hL ?_ ?_ ?_ ?_
  · intro i hi
    obtain ⟨m, rfl, hm⟩ := scr_false P i hi
    simp only [hi, Bool.false_eq_true, ↓reduceIte, ZeroPadding.pad, Nat.zero_sub, List.replicate_zero,
      List.append_nil, Scrub.blank]
    exact (hkept m hm).2
  · intro i hi; simp [Scrub.blank, hi]
  · intro i hi
    obtain ⟨m, rfl, hm⟩ := scr_false P i hi
    exact (hkept m hm).1
  · intro i hi; exact iterH_scr P _ i hi

/-! ## The loop -/

/-- **The schedule loop machine**: scrubbed stages while the table's head reads an entry marker. -/
noncomputable def loopM := StreamController.machine (loopBody P) (Scrub.inner (fx P 0))

theorem stageCost_mono {mag wl b lbv p Mm Wm lbm : ℕ} (h1 : mag ≤ Mm) (h2 : wl ≤ Wm) (h3 : lbv ≤ lbm) :
    stageCost mag wl b lbv p ≤ stageCost Mm Wm b lbm p := by
  unfold stageCost roundCost
  have a1 : (p + 4) * (400 * (lbv + 2) + 100 * 2 ^ p + 200) ≤ (p + 4) * (400 * (lbm + 2) + 100 * 2 ^ p + 200) :=
    Nat.mul_le_mul_left _ (by omega)
  have a2 : mag * (20 * (8 * 2 ^ p) + 7 + 4) ≤ Mm * (20 * (8 * 2 ^ p) + 7 + 4) := Nat.mul_le_mul_right _ h1
  omega

/-- The loop's per-round bound. -/
def loopCost (Mm Wm b p R : ℕ) : ℕ := 2 * stageCost Mm Wm b (2 * b + 3) p + 2 + 1 + (2 * R + 4)

/-- **The schedule loop** over a table of admissible entries (all at one length `n₀`, magnitudes `≤ Mm`, words
`≤ Wm`): from the cleared bank of entry `0` to the cleared bank after the last entry, whose accumulators are the
start plus every entry's term. -/
theorem sched_loop (cap R Lg p n0 Mm Wm : ℕ) (acc0 : Fin 6 → ℕ) (Ls : List (TEntry I))
    (hn : ∀ t ∈ Ls, t.req.1.n = n0) (hM : ∀ t ∈ Ls, t.e.mag ≤ Mm) (hW : ∀ t ∈ Ls, t.e.word.length ≤ Wm)
    (hcapR : 2 * Wm + Mm + 2 ≤ cap) (hcapD : 4 * (2 * B.callBudget n0 + 3) + 8 * 2 ^ p + 20 ≤ cap)
    (hcapA : ∀ i, acc0 i + (Ls.length + 2) * (Mm * (8 * 2 ^ p)) ≤ cap)
    (hR1 : cap + 1 ≤ R) (hR2 : stageCost Mm Wm (B.callBudget n0) (2 * B.callBudget n0 + 3) p + 1 ≤ R)
    (hL : R + 1 ≤ Lg) :
    Step (loopM P) (Ls.length * (loopCost Mm Wm (B.callBudget n0) p R + 2) + 1)
      (Scrub.heads (iterH P (KOf P p acc0 Ls 0)))
      (Scrub.bank (Scrub.blank (scr P) (iterA P cap (KOf P p acc0 Ls 0)) R) R Lg)
      (Scrub.heads (iterH P (KOf P p acc0 Ls Ls.length)))
      (Scrub.bank (Scrub.blank (scr P) (iterA P cap (KOf P p acc0 Ls Ls.length)) R) R Lg) := by
  have hs0 : scr P (fx P 0) = false := by simp [scr, keptV, fx_val]
  refine whileRun (loopBody P) (Scrub.inner (fx P 0)) Ls.length (loopCost Mm Wm (B.callBudget n0) p R)
    (fun j => Scrub.heads (iterH P (KOf P p acc0 Ls j)))
    (fun j => Scrub.bank (Scrub.blank (scr P) (iterA P cap (KOf P p acc0 Ls j)) R) R Lg) ?_ ?_ ?_
  · intro j hj
    simp only [Scrub.bank_inner, Scrub.heads_inner, Scrub.blank, hs0, Bool.false_eq_true, ↓reduceIte,
      iterA_fx, iterH_fx, fixedA, fixedH, KOf, if_true]
    exact tbl_cond Ls j hj
  · simp only [Scrub.bank_inner, Scrub.heads_inner, Scrub.blank, hs0, Bool.false_eq_true, ↓reduceIte,
      iterA_fx, iterH_fx, fixedA, fixedH, KOf, if_true]
    exact tbl_end Ls
  · intro j hj
    have hmem : Ls[j] ∈ Ls := List.getElem_mem hj
    have hlb := lb_value_le P (Ls[j]).req
    rw [hn _ hmem] at hlb
    have hacc := fun i => accOf_le P p acc0 Ls Mm hM j i
    have hmag := hM _ hmem
    have h8 : (Ls[j]).e.mag * (8 * 2 ^ p) ≤ Mm * (8 * 2 ^ p) := Nat.mul_le_mul_right _ hmag
    have hst := body_step P cap R Lg (KOf P p acc0 Ls j) (Ls[j]).e _ _ (tbl_split Ls j hj) rfl (Ls[j]).req (Ls[j]).hw
      (by have := hW _ hmem; omega) (by simp only [KOf]; omega)
      (fun i => by
        simp only [KOf]
        have := hacc i; have := hcapA i
        have e1 : j * (Mm * (4 * 2 ^ p)) ≤ Ls.length * (Mm * (8 * 2 ^ p)) := by
          have := Nat.mul_le_mul (le_of_lt hj) (Nat.mul_le_mul_left Mm (show 4 * 2 ^ p ≤ 8 * 2 ^ p by omega))
          simpa using this
        nlinarith)
      hR1 (by
        have := stageCost_mono (b := B.callBudget (Ls[j]).req.1.n) (p := p) hmag (hW _ hmem) hlb
        rw [hn _ hmem] at this ⊢; simp only [KOf]; omega) hL
    have hKp : (KOf P p acc0 Ls j).p = p := rfl
    rw [hKp, KOf_succ P p acc0 Ls j hj] at hst
    refine hst.enlarge ?_
    unfold loopCost
    have := stageCost_mono (b := B.callBudget (Ls[j]).req.1.n) (p := p) hmag (hW _ hmem) hlb
    rw [hn _ hmem] at this ⊢; omega

/-- The rounded answer's registers differ by `⌊v·2^p⌋`. -/
theorem mpOf_sub (v : ℚ) (p : ℕ) (hv : v.num.natAbs < 4 * v.den) :
    (mpOf v p : ℤ) - mnOf v p = ⌊v * 2 ^ p⌋ := by
  rw [← floorVal_eq v p hv]
  unfold mpOf mnOf floorVal
  by_cases h : sgn v = true
  · rw [if_pos h, if_pos h, if_pos h]; push_cast; ring
  · rw [if_neg h, if_neg h, if_neg h]; simp

/-- An entry's signed term: `(−1)^neg·|c|·⌊v·2^p⌋` on its test. -/
noncomputable def signedTerm (p : ℕ) (k : Fin 3) (t : TEntry I) : ℤ :=
  if t.e.kind = k then (if t.e.neg then -1 else 1) * (t.e.mag : ℤ) * ⌊P.value t.req.1 * 2 ^ p⌋ else 0

theorem accAdd_pos (k : Fin 3) (neg : Bool) (c mp mn : ℕ) :
    accAdd k neg c mp mn (accPos k) = c * (if neg then mn else mp) := by simp [accAdd]

theorem accAdd_neg (k : Fin 3) (neg : Bool) (c mp mn : ℕ) :
    accAdd k neg c mp mn (accNeg k) = c * (if neg then mp else mn) := by
  unfold accAdd
  rw [if_neg (by intro h; have := congrArg Fin.val h; simp [accPos, accNeg] at this), if_pos rfl]

theorem accAdd_other (k : Fin 3) (neg : Bool) (c mp mn : ℕ) (r : Fin 15) (h1 : r ≠ accPos k) (h2 : r ≠ accNeg k) :
    accAdd k neg c mp mn r = 0 := by
  unfold accAdd; rw [if_neg h1, if_neg h2]

theorem termOf_pos (p : ℕ) (k : Fin 3) (t : TEntry I) :
    termOf P p t ⟨2 * k.val, by omega⟩ =
      accAdd t.e.kind t.e.neg t.e.mag (mpOf (P.value t.req.1) p) (mnOf (P.value t.req.1) p) (accPos k) := by
  unfold termOf accStep; congr 1

theorem termOf_neg (p : ℕ) (k : Fin 3) (t : TEntry I) :
    termOf P p t ⟨2 * k.val + 1, by omega⟩ =
      accAdd t.e.kind t.e.neg t.e.mag (mpOf (P.value t.req.1) p) (mnOf (P.value t.req.1) p) (accNeg k) := by
  unfold termOf accStep; congr 1; apply Fin.ext; simp [accNeg]; omega

theorem termOf_diff (p : ℕ) (k : Fin 3) (t : TEntry I) :
    (termOf P p t ⟨2 * k.val, by omega⟩ : ℤ) - termOf P p t ⟨2 * k.val + 1, by omega⟩ = signedTerm P p k t := by
  have hs := mpOf_sub (P.value t.req.1) p (value_small I P t.req.1 t.req.2)
  rw [termOf_pos, termOf_neg]
  unfold signedTerm
  by_cases hk : t.e.kind = k
  · rw [if_pos hk, ← hk, accAdd_pos, accAdd_neg]
    cases t.e.neg <;> simp <;> push_cast <;> rw [← hs] <;> ring
  · rw [if_neg hk]
    have a1 : accPos k ≠ accPos t.e.kind := by
      intro h; have := congrArg Fin.val h; simp [accPos] at this; exact hk (Fin.ext (by omega))
    have a2 : accPos k ≠ accNeg t.e.kind := by
      intro h; have := congrArg Fin.val h; simp [accPos, accNeg] at this; omega
    have a3 : accNeg k ≠ accPos t.e.kind := by
      intro h; have := congrArg Fin.val h; simp [accPos, accNeg] at this; omega
    have a4 : accNeg k ≠ accNeg t.e.kind := by
      intro h; have := congrArg Fin.val h; simp [accNeg] at this; exact hk (Fin.ext (by omega))
    rw [accAdd_other _ _ _ _ _ _ a1 a2, accAdd_other _ _ _ _ _ _ a3 a4]; simp

/-- **The loop's result per test**: the accumulator pair's difference is the start's plus the sum of the entries'
signed terms `(−1)^neg·|c|·⌊v·2^p⌋` of that test. -/
theorem accOf_diff (p : ℕ) (acc0 : Fin 6 → ℕ) (Ls : List (TEntry I)) (k : Fin 3) :
    (accOf P p acc0 Ls Ls.length ⟨2 * k.val, by omega⟩ : ℤ) - accOf P p acc0 Ls Ls.length ⟨2 * k.val + 1, by omega⟩ =
      ((acc0 ⟨2 * k.val, by omega⟩ : ℤ) - acc0 ⟨2 * k.val + 1, by omega⟩) + (Ls.map (signedTerm P p k)).sum := by
  unfold accOf
  rw [List.take_length]
  induction Ls with
  | nil => simp
  | cons t Ls ih =>
    simp only [List.map_cons, List.sum_cons] at ih ⊢
    push_cast at ih ⊢
    rw [← termOf_diff P p k t]
    linarith

end Loop

end NearCubicWires.WireExponent3_5.UnionMachine.Sched
