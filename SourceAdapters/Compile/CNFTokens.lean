import SourceAdapters.Compile.CNFRpn

/-!
# The token stream in the shape of the printing loops

proof of `lem:multitape-refuter` (the tableau circuit: initial configuration, `T` transition rounds read off the finite transition
table, the acceptance test) and proof of `lem:multitape-refuter` (the half-open rank comparator). `CNFRpn.requestToks r` is defined
through the semantic expressions; this module restates each part as nested `range` loops over plain table lookups
(`TD`), the exact shape the printing program runs:

* `anyT k f`/`allT k f`: `f 0 ++ … ++ f (k-1)`, a constant, then `k` binary operations (`postW_anyOfFn`);
* `transT`/`tmplT`: one transition round (`tmplT_eq`: equal to `roundToks` for any table `D` representing the
  machine, `TD.Rep`);
* `initT` (`initT_eq`), `accT` (`accT_eq`), `rankT` (`rankT_eq`).

-/

namespace NearCubicGates.Adapters.Compile
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
  NearCubicWires.FinitePredicateCircuit NearCubicWires.RepairSource
set_option autoImplicit false

/-- `f 0 ++ … ++ f (k-1)`, then `false`, then `k` disjunctions. -/
def anyT (k : ℕ) (f : ℕ → List RTok) : List RTok :=
  (List.range k).flatMap f ++ [.cst false] ++ List.replicate k .disj

/-- `f 0 ++ … ++ f (k-1)`, then `true`, then `k` conjunctions. -/
def allT (k : ℕ) (f : ℕ → List RTok) : List RTok :=
  (List.range k).flatMap f ++ [.cst true] ++ List.replicate k .conj

theorem ofFn_flatten_range {α : Type} (k : ℕ) :
    ∀ (g : Fin k → List α) (f : ℕ → List α), (∀ i : Fin k, g i = f i.val) →
      (List.ofFn g).flatten = (List.range k).flatMap f := by
  induction k with
  | zero => intro g f _; rfl
  | succ k ih =>
      intro g f h
      rw [List.ofFn_succ, List.flatten_cons, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map, h 0]
      congr 1
      exact ih _ _ (fun i => h i.succ)

theorem postW_any {w : ℕ} (l : List (BoolExpr w)) :
    postW (anyExpression l) = (l.map postW).flatten ++ [.cst false] ++ List.replicate l.length .disj := by
  induction l with
  | nil => rfl
  | cons e rest ih =>
      simp only [anyExpression, postW, ih, List.map_cons, List.flatten_cons, List.length_cons,
        List.replicate_succ', List.append_assoc]

theorem postW_all {w : ℕ} (l : List (BoolExpr w)) :
    postW (allExpression l) = (l.map postW).flatten ++ [.cst true] ++ List.replicate l.length .conj := by
  induction l with
  | nil => rfl
  | cons e rest ih =>
      simp only [allExpression, postW, ih, List.map_cons, List.flatten_cons, List.length_cons,
        List.replicate_succ', List.append_assoc]

theorem postW_anyOfFn {w k : ℕ} (g : Fin k → BoolExpr w) (f : ℕ → List RTok)
    (h : ∀ i : Fin k, postW (g i) = f i.val) : postW (anyExpression (List.ofFn g)) = anyT k f := by
  rw [postW_any, List.map_ofFn, List.length_ofFn, anyT, ofFn_flatten_range k (postW ∘ g) f (fun i => h i)]

theorem postW_allOfFn {w k : ℕ} (g : Fin k → BoolExpr w) (f : ℕ → List RTok)
    (h : ∀ i : Fin k, postW (g i) = f i.val) : postW (allExpression (List.ofFn g)) = allT k f := by
  rw [postW_all, List.map_ofFn, List.length_ofFn, allT, ofFn_flatten_range k (postW ∘ g) f (fun i => h i)]

/-! ## Window indices -/

def headI (s width tape pos : ℕ) : ℕ := s + (pos + width * tape)
def cellI (t s width tape pos : ℕ) : ℕ := s + (t * width + (pos + width * tape))

theorem headIndex_val {t s width : ℕ} (tape : Fin t) (pos : Fin width) :
    (headIndex (s := s) tape pos).val = headI s width tape pos := by
  simp [headIndex, headI, finProdFinEquiv]

theorem cellIndex_val {t s width : ℕ} (tape : Fin t) (pos : Fin width) :
    (cellIndex (s := s) tape pos).val = cellI t s width tape pos := by
  simp [cellIndex, cellI, finProdFinEquiv]
  omega

theorem addCases_wl {t s width : ℕ} {α : Type} (f : Fin s → α) (g : Fin (t * width + t * width) → α) (j : ℕ)
    (hj : j < windowBits t s width) (h : j < s) :
    Fin.addCases (motive := fun _ => α) f g (⟨j, hj⟩ : Fin (windowBits t s width)) = f ⟨j, h⟩ := by
  simp [Fin.addCases, h, Fin.castLT]

theorem addCases_wr {t s width : ℕ} {α : Type} (f : Fin s → α) (g : Fin (t * width + t * width) → α) (j : ℕ)
    (hj : j < windowBits t s width) (h : s ≤ j) :
    Fin.addCases (motive := fun _ => α) f g (⟨j, hj⟩ : Fin (windowBits t s width)) =
      g ⟨j - s, by unfold windowBits at hj; omega⟩ := by
  have : ¬ j < s := by omega
  simp [Fin.addCases, this, Fin.subNat]

theorem addCases_ml {t width : ℕ} {α : Type} (f g : Fin (t * width) → α) (j : ℕ) (hj : j < t * width + t * width)
    (h : j < t * width) : Fin.addCases (motive := fun _ => α) f g (⟨j, hj⟩ : Fin (t * width + t * width)) = f ⟨j, h⟩ := by
  simp [Fin.addCases, h, Fin.castLT]

theorem addCases_mr {t width : ℕ} {α : Type} (f g : Fin (t * width) → α) (j : ℕ) (hj : j < t * width + t * width)
    (h : t * width ≤ j) :
    Fin.addCases (motive := fun _ => α) f g (⟨j, hj⟩ : Fin (t * width + t * width)) = g ⟨j - t * width, by omega⟩ := by
  have : ¬ j < t * width := by omega
  simp [Fin.addCases, this, Fin.subNat]

/-! ## The transition round -/

/-- The finite control as plain lookups: halted/accepting per state; per (state, scan mask): rule present, next
control, write per tape, and the moved head position per (tape, position). -/
structure TD where
  hl : ℕ → Bool
  ac : ℕ → Bool
  pr : ℕ → ℕ → Bool
  nc : ℕ → ℕ → ℕ
  wr : ℕ → ℕ → ℕ → Option Bool
  mv : ℕ → ℕ → ℕ → ℕ → ℕ

/-- `D` represents the machine on its finite domain. -/
structure TD.Rep (D : TD) {t s : ℕ} (M : Machine t s) (accepting : Fin s → Bool) : Prop where
  hl : ∀ q : Fin s, D.hl q.val = M.halted q
  ac : ∀ q : Fin s, D.ac q.val = accepting q
  pr : ∀ (q : Fin s) (m : Fin (2 ^ t)), D.pr q.val m.val = (M.rule q (scanMask m)).isSome
  nc : ∀ (q : Fin s) (m : Fin (2 ^ t)) (a : Action t s), M.rule q (scanMask m) = some a →
    D.nc q.val m.val = a.nextControl.val
  wr : ∀ (q : Fin s) (m : Fin (2 ^ t)) (a : Action t s) (tape : Fin t), M.rule q (scanMask m) = some a →
    D.wr q.val m.val tape.val = a.write tape
  mv : ∀ (q : Fin s) (m : Fin (2 ^ t)) (a : Action t s) (tape : Fin t) (pos : ℕ), M.rule q (scanMask m) = some a →
    D.mv q.val m.val tape.val pos = (a.move tape).apply pos

/-- The scanned bit of `tape`. -/
def scannedT (t s width tape : ℕ) : List RTok :=
  anyT width (fun pos => [.wir (headI s width tape pos), .wir (cellI t s width tape pos), .conj])

/-- The table row test of `(q, m)`. -/
def rowT (t s width q m : ℕ) : List RTok :=
  [.wir q] ++ allT t (fun tape => scannedT t s width tape ++ (if m.testBit tape then [] else [.neg])) ++ [.conj]

/-- Every head move stays in the window. -/
def fitsT (D : TD) (t s width q m : ℕ) : List RTok :=
  allT t (fun tape => anyT width (fun pos =>
    [.wir (headI s width tape pos), .cst (decide (D.mv q m tape pos < width)), .conj]))

/-- The new value of window bit `j` under the action of `(q, m)`. -/
def actT (D : TD) (t s width q m j : ℕ) : List RTok :=
  if j < s then [.cst (decide (D.nc q m = j))]
  else if j < s + t * width then
    anyT width (fun old => [.wir (headI s width ((j - s) / width) old),
      .cst (decide (D.mv q m ((j - s) / width) old = (j - s) % width)), .conj])
  else
    match D.wr q m ((j - s - t * width) / width) with
    | none => [.wir (cellI t s width ((j - s - t * width) / width) ((j - s - t * width) % width))]
    | some v => [.wir (headI s width ((j - s - t * width) / width) ((j - s - t * width) % width)), .cst v, .conj,
        .wir (headI s width ((j - s - t * width) / width) ((j - s - t * width) % width)), .neg,
        .wir (cellI t s width ((j - s - t * width) / width) ((j - s - t * width) % width)), .conj, .disj]

/-- The selected value of `(q, m)` for window bit `j`. -/
def valT (D : TD) (t s width q m j : ℕ) : List RTok :=
  if D.hl q then [.wir j]
  else if D.pr q m then fitsT D t s width q m ++ actT D t s width q m j ++ [.conj]
  else [.cst false]

/-- The next value of window bit `j`. -/
def transT (D : TD) (t s width j : ℕ) : List RTok :=
  anyT s (fun q => anyT (2 ^ t) (fun m => rowT t s width q m ++ valT D t s width q m j ++ [.conj]))

/-- One round: every window bit, saved, then swap. -/
def tmplT (D : TD) (t s width : ℕ) : List RTok :=
  (List.range (windowBits t s width)).flatMap (fun j => transT D t s width j ++ [.save]) ++ [.swap]

theorem postW_scanned {t s width : ℕ} (tape : Fin t) :
    postW (scannedExpression (s := s) (width := width) tape) = scannedT t s width tape.val := by
  rw [scannedExpression, scannedT]
  apply postW_anyOfFn
  intro pos
  simp [postW, headIndex_val, cellIndex_val]

theorem postW_row {t s width : ℕ} (q : Fin s) (m : Fin (2 ^ t)) :
    postW (rowExpression (width := width) q (scanMask m)) = rowT t s width q.val m.val := by
  rw [rowExpression, rowT, postW, scanPatternExpression, postW_allOfFn _ (fun tape =>
    scannedT t s width tape ++ (if m.val.testBit tape then [] else [.neg]))]
  · simp [postW, controlIndex]
  · intro tape
    by_cases hb : m.val.testBit tape.val
    · simp [scanMask, hb, postW_scanned]
    · simp [scanMask, hb, postW, postW_scanned]

theorem postW_headSelection {t s width : ℕ} (tape : Fin t) (values : Fin width → BoolExpr (windowBits t s width))
    (f : ℕ → Bool) (hf : ∀ pos : Fin width, values pos = .const (f pos.val)) :
    postW (headSelection tape values) =
      anyT width (fun pos => [.wir (headI s width tape.val pos), .cst (f pos), .conj]) := by
  rw [headSelection]
  apply postW_anyOfFn
  intro pos
  simp [postW, hf pos, headIndex_val]

theorem postW_fits {t s width : ℕ} (D : TD) (M : Machine t s) (acc : Fin s → Bool) (hD : D.Rep M acc)
    (q : Fin s) (m : Fin (2 ^ t)) (a : Action t s) (ha : M.rule q (scanMask m) = some a) :
    postW (actionFitsExpression (s := s) (width := width) a) = fitsT D t s width q.val m.val := by
  rw [actionFitsExpression, fitsT]
  apply postW_allOfFn
  intro tape
  rw [postW_headSelection tape _ (fun pos => decide (D.mv q.val m.val tape.val pos < width))]
  intro pos
  rw [hD.mv q m a tape pos ha]

theorem postW_act {t s width : ℕ} (D : TD) (M : Machine t s) (acc : Fin s → Bool) (hD : D.Rep M acc)
    (q : Fin s) (m : Fin (2 ^ t)) (a : Action t s) (ha : M.rule q (scanMask m) = some a)
    (j : ℕ) (hj : j < windowBits t s width) :
    postW (actionExpression (width := width) a ⟨j, hj⟩) = actT D t s width q.val m.val j := by
  have hj' := hj
  unfold windowBits at hj'
  rw [actionExpression, actT]
  by_cases h1 : j < s
  · rw [addCases_wl _ _ j hj h1, if_pos h1, hD.nc q m a ha]
    simp [postW, Fin.ext_iff, eq_comm]
  · rw [addCases_wr _ _ j hj (by omega), if_neg h1]
    by_cases h2 : j < s + t * width
    · rw [addCases_ml _ _ (j - s) (by omega) (by omega), if_pos h2]
      have e1 : (finProdFinEquiv.symm (⟨j - s, by omega⟩ : Fin (t * width))).1.val = (j - s) / width := by simp
      have e2 : (finProdFinEquiv.symm (⟨j - s, by omega⟩ : Fin (t * width))).2.val = (j - s) % width := by simp
      rw [postW_headSelection _ _ (fun old => decide (D.mv q.val m.val ((j - s) / width) old = (j - s) % width))]
      · rw [e1]
      · intro old
        have hm := hD.mv q m a (finProdFinEquiv.symm (⟨j - s, by omega⟩ : Fin (t * width))).1 old ha
        rw [e1] at hm
        rw [hm, e2]
    · rw [addCases_mr _ _ (j - s) (by omega) (by omega), if_neg h2]
      have e1 : (finProdFinEquiv.symm (⟨j - s - t * width, by omega⟩ : Fin (t * width))).1.val =
          (j - s - t * width) / width := by simp
      have e2 : (finProdFinEquiv.symm (⟨j - s - t * width, by omega⟩ : Fin (t * width))).2.val =
          (j - s - t * width) % width := by simp
      rw [writtenCellExpression]
      have hwr := hD.wr q m a (finProdFinEquiv.symm (⟨j - s - t * width, by omega⟩ : Fin (t * width))).1 ha
      rw [e1] at hwr
      rw [hwr]
      cases a.write _ with
      | none => simp [postW, cellIndex_val]
      | some v => simp [postW, cellIndex_val, headIndex_val]

theorem postW_trans {t s width : ℕ} (D : TD) (M : Machine t s) (acc : Fin s → Bool) (hD : D.Rep M acc)
    (j : ℕ) (hj : j < windowBits t s width) :
    postW (transitionExpression M ⟨j, hj⟩) = transT D t s width j := by
  rw [transitionExpression, tableSelection, transT]
  apply postW_anyOfFn
  intro q
  apply postW_anyOfFn
  intro m
  rw [postW, postW_row]
  congr 2
  rw [valT, hD.hl q]
  by_cases hh : M.halted q = true
  · simp [hh, postW]
  · have hh' : M.halted q = false := by simpa using hh
    simp only [hh', Bool.false_eq_true, ↓reduceIte]
    cases hr : M.rule q (scanMask m) with
    | none =>
        have : D.pr q.val m.val = false := by rw [hD.pr q m, hr]; rfl
        simp [this, postW]
    | some a =>
        have : D.pr q.val m.val = true := by rw [hD.pr q m, hr]; rfl
        simp only [this, ↓reduceIte, postW]
        rw [postW_fits D M acc hD q m a hr, postW_act D M acc hD q m a hr j hj]

theorem tmplT_eq {t s width : ℕ} (D : TD) (M : Machine t s) (acc : Fin s → Bool) (hD : D.Rep M acc) :
    tmplT D t s width = roundToks width M := by
  rw [tmplT, roundToks, vecW]
  congr 1
  symm
  apply ofFn_flatten_range
  intro j
  rw [postW_trans D M acc hD j.val j.isLt]

/-! ## Acceptance -/

def accT (D : TD) (s : ℕ) : List RTok :=
  anyT s (fun q => [.wir q, .cst (D.hl q && D.ac q), .conj])

theorem accT_eq {t s width : ℕ} (D : TD) (M : Machine t s) (acc : Fin s → Bool) (hD : D.Rep M acc) :
    postW (acceptanceExpression (width := width) M acc) = accT D s := by
  rw [acceptanceExpression, accT]
  apply postW_anyOfFn
  intro q
  simp [postW, controlIndex, hD.hl q, hD.ac q]

/-! ## Initial vector -/

/-- `readTapeBit (frame l) pos` as a lookup (`Cells.frame_read`). -/
def frameBit (l : List Bool) (pos : ℕ) : Bool :=
  if pos % 2 = 0 then decide (pos / 2 < l.length) else l.getD (pos / 2) false

/-- The initial value of window bit `j`. -/
def initJ (t s width n start : ℕ) (input : List Bool) (j : ℕ) : List RTok :=
  if j < s then [.cst (decide (start = j))]
  else if j < s + t * width then [.cst (decide ((j - s) % width = 0))]
  else if (j - s - t * width) / width = 0 then [.cst (frameBit input ((j - s - t * width) % width))]
  else if (j - s - t * width) / width = 1 then
    (if (j - s - t * width) % width % 2 = 0 then [.cst (decide ((j - s - t * width) % width / 2 < n))]
     else if (j - s - t * width) % width / 2 < n then [.inp ((j - s - t * width) % width / 2)] else [.cst false])
  else [.cst false]

def initT (t s width n start : ℕ) (input : List Bool) : List RTok :=
  (List.range (windowBits t s width)).flatMap (fun j => initJ t s width n start input j ++ [.save]) ++ [.swap]

theorem initT_eq (v : Verifier) (input : List Bool) (n fuel : ℕ) :
    vecE (windowBits v.tapeCount v.stateCount (fuel + 1)) (verifierInitialExpression v input n fuel) ++ [.swap] =
      initT v.tapeCount v.stateCount (fuel + 1) n v.machine.start.val input := by
  rw [vecE, initT]
  congr 1
  apply ofFn_flatten_range
  intro ⟨j, hj⟩
  congr 1
  have hj' := hj
  unfold windowBits at hj'
  rw [verifierInitialExpression, initJ]
  by_cases h1 : j < v.stateCount
  · rw [addCases_wl _ _ j hj h1, if_pos h1]
    simp [postE, Fin.ext_iff]
  · rw [addCases_wr _ _ j hj (by omega), if_neg h1]
    by_cases h2 : j < v.stateCount + v.tapeCount * (fuel + 1)
    · rw [addCases_ml _ _ (j - v.stateCount) (by omega) (by omega), if_pos h2]
      simp [postE]
    · rw [addCases_mr _ _ (j - v.stateCount) (by omega) (by omega), if_neg h2]
      have e1 : (finProdFinEquiv.symm (⟨j - v.stateCount - v.tapeCount * (fuel + 1), by omega⟩ :
          Fin (v.tapeCount * (fuel + 1)))).1.val = (j - v.stateCount - v.tapeCount * (fuel + 1)) / (fuel + 1) := by
        simp
      have e2 : (finProdFinEquiv.symm (⟨j - v.stateCount - v.tapeCount * (fuel + 1), by omega⟩ :
          Fin (v.tapeCount * (fuel + 1)))).2.val = (j - v.stateCount - v.tapeCount * (fuel + 1)) % (fuel + 1) := by
        simp
      dsimp only [Fin.val_mk]
      rw [e1, e2]
      by_cases h3 : (j - v.stateCount - v.tapeCount * (fuel + 1)) / (fuel + 1) = 0
      · simp [h3, postE, frameBit, NearCubicGates.Close.Cells.frame_read]
      · by_cases h4 : (j - v.stateCount - v.tapeCount * (fuel + 1)) / (fuel + 1) = 1
        · simp only [h4, ↓reduceIte, witnessFrameExpression]
          by_cases h5 : (j - v.stateCount - v.tapeCount * (fuel + 1)) % (fuel + 1) % 2 = 0
          · simp [h5, postE]
          · by_cases h6 : (j - v.stateCount - v.tapeCount * (fuel + 1)) % (fuel + 1) / 2 < n
            · simp [h5, h6, postE]
            · simp [h5, h6, postE]
        · simp [h3, h4, postE]

/-! ## The rank comparator -/

/-- Input-shifted postfix tokens of `rankLessExpression k high`, first input at `d`. -/
def rankT (d : ℕ) : ℕ → ℕ → List RTok
  | 0, high => [.cst (decide (0 < high))]
  | k + 1, high =>
      if high ≤ 2 ^ k then [.inp d, .neg] ++ rankT (d + 1) k high ++ [.conj]
      else [.inp d, .neg, .inp d] ++ rankT (d + 1) k (high - 2 ^ k) ++ [.conj, .disj]

def shiftTok (d : ℕ) : RTok → RTok
  | .inp j => .inp (j + d)
  | x => x

theorem postE_rename {n m : ℕ} (f : Fin n → Fin m) (d : ℕ) (hf : ∀ i, (f i).val = i.val + d) (e : BoolExpr n) :
    postE (renameExpression f e) = (postE e).map (shiftTok d) := by
  induction e with
  | const b => rfl
  | input i => simp [renameExpression, postE, shiftTok, hf]
  | not c ih => simp [renameExpression, postE, ih, shiftTok]
  | and l r ihl ihr => simp [renameExpression, postE, ihl, ihr, shiftTok]
  | or l r ihl ihr => simp [renameExpression, postE, ihl, ihr, shiftTok]

theorem shiftTok_comp (d : ℕ) : shiftTok d ∘ shiftTok 1 = shiftTok (d + 1) := by
  funext x
  cases x <;> simp [shiftTok]
  omega

theorem rankT_shift (k : ℕ) : ∀ (d high : ℕ), rankT d k high = (rankT 0 k high).map (shiftTok d) := by
  induction k with
  | zero => intro d high; rfl
  | succ k ih =>
      intro d high
      simp only [rankT]
      split
      · rw [ih (d + 1), ih 1, List.map_append, List.map_append, List.map_map, shiftTok_comp]
        simp [shiftTok]
      · rw [ih (d + 1), ih 1, List.map_append, List.map_append, List.map_map, shiftTok_comp]
        simp [shiftTok]

theorem rankT_eq (k : ℕ) : ∀ high, postE (rankLessExpression k high) = rankT 0 k high := by
  induction k with
  | zero => intro high; rfl
  | succ k ih =>
      intro high
      rw [rankLessExpression, rankT]
      split
      · simp [postE, postE_rename Fin.succ 1 (fun i => rfl), ih, rankT_shift k 1]
      · simp [postE, postE_rename Fin.succ 1 (fun i => rfl), ih, rankT_shift k 1]

/-! ## The whole stream -/

/-- **The token stream in loop shape** (proof of `lem:multitape-refuter`). -/
theorem requestToks_eq (r : CNFCompilationRequest) (D : TD) (hD : D.Rep r.verifier.machine r.verifier.accepting) :
    requestToks r =
      initT r.verifier.tapeCount r.verifier.stateCount (r.fuel + 1) r.witnessLength r.verifier.machine.start.val
          r.input ++
        (List.replicate r.fuel (tmplT D r.verifier.tapeCount r.verifier.stateCount (r.fuel + 1))).flatten ++
        accT D r.verifier.stateCount ++ rankT 0 r.witnessLength r.high ++ [.conj] := by
  rw [requestToks, initT_eq, tmplT_eq D _ _ hD, accT_eq D _ _ hD, rankT_eq]

end NearCubicGates.Adapters.Compile
