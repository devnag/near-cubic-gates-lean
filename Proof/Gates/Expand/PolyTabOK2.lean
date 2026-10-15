import Proof.Gates.Expand.PolyTabOK

set_option autoImplicit false

namespace NearCubicGates.Close.Expand.PolyTab

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicGates.Close.Tabulator NearCubicGates.Close.TabMachine
open NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Expand

variable (E : ExpandMachine)

/-! ## Positions in the occurrence stream -/

theorem blk_at (ts : List (List Occ × ℤ)) (i : ℕ) (hi : i < ts.length) (i' : ℕ) (hi' : i' < ts[i].1.length) :
    ((codeRecs ts).drop (posOf (termStart ts i + 1) ts[i].1 i')).take (occLen ts[i].1[i']) = occRecs ts[i].1[i'] := by
  have e := code_drop ts i hi
  unfold posOf
  rw [show termStart ts i + 1 + ((ts[i].1.take i').map occLen).sum =
    termStart ts i + (1 + ((ts[i].1.take i').map occLen).sum) by ring, ← List.drop_drop, e]
  simp only [blkRecs, List.cons_append, List.drop_succ_cons, ← List.drop_drop, List.drop_zero]
  rw [flatMap_drop_sum occRecs occLen occRecs_length _ i' hi', List.take_append_of_le_length (by rw [occRecs_length]),
    List.take_of_length_le (by rw [occRecs_length])]

theorem le_sum_map {α : Type} (l : List α) (f : α → ℕ) (x : α) (hx : x ∈ l) : f x ≤ (l.map f).sum := by
  induction l with
  | nil => simp at hx
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    rcases List.mem_cons.mp hx with rfl | hx
    · omega
    · have := ih hx; omega

/-! ## The data at a point, a monomial, an occurrence -/

section Data
variable (r : TabReq)

def hsK : List ℕ := hList (code (tabT E r))
def tsK : List (List Occ × ℤ) := (code (tabT E r)).terms
def xsK : List ℕ := codeRecs (tsK E r)
def dOcc : Occ := ⟨false, 0, [], []⟩
def dTerm : List Occ × ℤ := ([], 0)

def cAt (j : ℕ) : ℕ := (hsK E r).getD j 0
def osAt (i : ℕ) : List Occ := ((tsK E r).getD i dTerm).1
def oAt (i i' : ℕ) : Occ := (osAt E r i).getD i' dOcc
def pAt (i i' : ℕ) : ℕ := posOf (termStart (tsK E r) i + 1) (osAt E r i) i'
def tfAt (j i i' : ℕ) : List (List ℤ) := tupF (cAt E r j) ((osAt E r i).take i')

def idx2 : List (ℕ × ℕ) := (List.range (hsK E r).length).flatMap fun j => (List.range (tsK E r).length).map fun i => (j, i)
def idx3 : List (ℕ × ℕ × ℕ) := (List.range (hsK E r).length).flatMap fun j => (List.range (tsK E r).length).flatMap
  fun i => (List.range (osAt E r i).length).map fun i' => (j, i, i')

def stepCost (x : ℕ × ℕ × ℕ) : ℕ :=
  occStepCost (Wk E r) r.s r.k (xsK E r) (pAt E r x.2.1 x.2.2) (cAt E r x.1) (oAt E r x.2.1 x.2.2)
    (tfAt E r x.1 x.2.1 x.2.2).length (x.2.2 * (r.s + 1))
def CSk : ℕ := ((idx3 E r).map (stepCost E r)).foldr max 0

def bbAt (x : ℕ × ℕ) : ℕ := (osAt E r x.2).length * (r.s + 1) + (monoTuples (cAt E r x.1) (osAt E r x.2)).length + r.s + 1 +
  (osAt E r x.2).length
def BBk : ℕ := ((idx2 E r).map (bbAt E r)).foldr max 0

def monoCost (x : ℕ × ℕ) : ℕ :=
  monoStepCost (Wk E r) r.s (Wdk E r) (CSk E r) (BBk E r) (termStart (tsK E r) x.2) (osAt E r x.2).length
    (fieldNums ((monoTuples (cAt E r x.1) (osAt E r x.2)).map List.flatten)).length
    (monoTuples (cAt E r x.1) (osAt E r x.2)).length
def CMk : ℕ := ((idx2 E r).map (monoCost E r)).foldr max 0

def outAt (x : ℕ × ℕ) : List Bool :=
  [] ++ allCuts (Wdk E r) r.s ((hsK E r).take x.1) (tsK E r) ++ cutsOf (Wdk E r) r.s (cAt E r x.1) ((tsK E r).take x.2)
def gAt (x : ℕ × ℕ) : ℕ := 0 + allCount ((hsK E r).take x.1) (tsK E r) + cutCount (cAt E r x.1) ((tsK E r).take x.2)

/-- The cap requirements of one monomial. -/
def monoCap (x : ℕ × ℕ) : ℕ :=
  let W := Wk E r; let s := r.s; let Wd := Wdk E r; let os := osAt E r x.2; let c := cAt E r x.1
  let p := termStart (tsK E r) x.2; let xs := xsK E r
  ((xs.length + 1) * (2 * (W + 1) + 1) + 2 * p + xs.getD p 0 + 2) + 2 * os.length +
  (((fieldNums ((monoTuples c os).map List.flatten)).length + 1) * (2 * (Wd + 1) + 1) +
      2 * (fieldNums ((monoTuples c os).map List.flatten)).length + 2 * os.length + 2 * (os.length * (s + 1)) +
      (monoTuples c os).length * (os.length * (s + 1)) + 2 * (s + 1) + os.length * (s + 1) + gAt E r x +
      (monoTuples c os).length + 1 + 2 * (monoTuples c os).length) +
  ((outAt E r x).length + (monoTuples c os).length * ((s + 2) * (2 * (Wd + 1) + 1)) + 1)

/-- The cap requirements of one occurrence step. -/
def stepCap (x : ℕ × ℕ × ℕ) : ℕ :=
  let W := Wk E r; let s := r.s; let k := r.k; let xs := xsK E r; let o := oAt E r x.2.1 x.2.2; let c := cAt E r x.1
  let tf := tfAt E r x.1 x.2.1 x.2.2; let M := x.2.2 * (s + 1); let K := (o.kids c).length
  let L := (s + 1) * (W + 1); let N := s + 1
  ((xs.length + 1) * (2 * (W + 1) + 1) + 2 * xs.length + 2 * k + 2 * s) +
  ((compRecs W o.outW (rTarget o c)).length + (s + 1) * (2 * (W + 1) + 1) + 2 * s + 4 * W + 8) +
  (K * (2 * L + 1) + 2 * L + 2 + 2 * (s + 1)) + (K * (s + 1) * (2 * L + 1) + 1) +
  ((K * N + 1) * (2 * L + 1) + 2 * (K * N)) + ((tf.length * M + 1) * (2 * L + 1) + 2 * (tf.length * M)) +
  (([] : List Bool).length + K * tf.length * ((N + M) * (2 * L + 1)) + 1) + (2 * K + 2 * tf.length + K * N + N) +
  (K * tf.length * (s + 1 + M) * (2 * L + 1) + 2 * L + 2) + (K * tf.length + 2 * K + tf.length + M + s + 1)

/-- Every cap requirement of the cut machine. -/
def capk : ℕ :=
  ((idx2 E r).map (monoCap E r)).sum + ((idx3 E r).map (stepCap E r)).sum + BBk E r +
  ((tsK E r).length * (2 * ((r.s + 1) * (Wk E r + 1)) + 1) + 2 * ((r.s + 1) * (Wk E r + 1)) + 2) + (xsK E r).length +
  ((hsK E r).length * (2 * (Wk E r + 1) + 1) + 2 * (Wk E r + 1) + 2) + 1

end Data

theorem mem_idx2 (r : TabReq) (j i : ℕ) (hj : j < (hsK E r).length) (hi : i < (tsK E r).length) : (j, i) ∈ idx2 E r := by
  simp only [idx2, List.mem_flatMap, List.mem_map, List.mem_range]; exact ⟨j, hj, i, hi, rfl⟩

theorem mem_idx3 (r : TabReq) (j i i' : ℕ) (hj : j < (hsK E r).length) (hi : i < (tsK E r).length)
    (hi' : i' < (osAt E r i).length) : (j, i, i') ∈ idx3 E r := by
  simp only [idx3, List.mem_flatMap, List.mem_map, List.mem_range]; exact ⟨j, hj, i, hi, i', hi', rfl⟩

end NearCubicGates.Close.Expand.PolyTab
