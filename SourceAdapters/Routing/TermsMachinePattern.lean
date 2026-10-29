import SourceAdapters.Routing.TermsMachineEmit
import SourceAdapters.Routing.CircuitEncodingPattern
import SourceAdapters.Routing.CircuitPrefixFormula
import SourceAdapters.Joins.TermsCircuit
import SourceAdapters.Routing.TermsMachinePrefixData

/-!
# Guard-gate printing from packed pattern codes

The construction in `lem:generator`: each normalized guard emits its actual selector
gates. The fixed program reads the `m` guard codes at packed-input cursor 14,
using the shared coordinate prefix's row references. It preserves the field,
physical input position, failed-input flag, and all unlisted registers.
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Routing.TermsMachine

open NearCubicWires
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Adapters.ShortPCP.Machines.FL
open NearCubicGates.Adapters.Routing.CoordinateMachine
open NearCubicGates.Adapters.Joins
open NearCubicGates.Adapters.ACSP

def patternModeWord (mode : ℕ) (w : List Bool) : List Bool := if mode = 0 then [] else w

theorem patternModeWord_append (mode : ℕ) (a b : List Bool) :
    patternModeWord mode (a ++ b) = patternModeWord mode a ++ patternModeWord mode b := by
  by_cases h : mode = 0 <;> simp [patternModeWord, h]

theorem patternModeWord_nil (mode : ℕ) : patternModeWord mode [] = [] := by
  simp [patternModeWord]

/-- Stage the three fields, then use the checked conditional gate writer. -/
def patternSend (tag : ℕ) (x y : E) : S :=
  .seq (.set 7 (.k tag)) (.seq (.set 8 x) (.seq (.set 9 y) gateStep))

theorem patternSend_spec (G : Glob) (s : FS) (tag vx vy : ℕ) (x y : E)
    (htag : tag ≤ G.cap)
    (hx : evalE G (s.setv 7 tag) x = vx)
    (hy : evalE G ((s.setv 7 tag).setv 8 vx) y = vy)
    (h7 : natBitLength tag + 2 ≤ G.K) (h8 : natBitLength vx + 2 ≤ G.K)
    (h9 : natBitLength vy + 2 ≤ G.K) (hN : G.K ≤ G.N)
    (hc : s.env 24 + 1 ≤ G.cap) :
    Appends [5, 6, 7, 8, 9, 24] s (evalS G (patternSend tag x y) s)
      (patternModeWord (s.env 31) (natWord tag ++ natWord vx ++ natWord vy)) ∧
      (evalS G (patternSend tag x y) s).env 24 = s.env 24 + 1 := by
  let t := ((s.setv 7 tag).setv 8 vx).setv 9 vy
  have he : evalS G (patternSend tag x y) s = evalS G gateStep t := by
    simp only [patternSend, evalS_seq, evalS_set, evalE, min_eq_left htag, hx, hy, t]
  have ht : Appends [5, 6, 7, 8, 9, 24] s t [] :=
    ((Appends.setv _ s 7 (by simp) tag).trans
      (Appends.setv _ _ 8 (by simp) vx)).trans (Appends.setv _ _ 9 (by simp) vy)
  obtain ⟨ha, hb⟩ := gateStep_spec G t (by simpa [t] using h7) (by simpa [t] using h8)
    (by simpa [t] using h9) hN (by simpa [t] using hc)
  rw [he]
  refine ⟨?_, by simpa [t] using hb⟩
  simpa [t, patternModeWord] using ht.trans (ha.mono (by simp))

/-- Reference to row `a` in the coordinate prefix starting at gate zero. -/
def patternCoord (m a : ℕ) : ℕ := 4 * m + a * (3 * m + 1)

theorem rowIds_patternCoord (m a d : ℕ) (ha : a < m) :
    (Circuit.PrefixFormula.rowIds m m m).getD a d = patternCoord m a := by
  simp [Circuit.PrefixFormula.rowIds, ha, patternCoord]
  omega

def patternCostCode : Option Bool → ℕ
  | none => 0
  | some true => 1
  | some false => 2

def patternCodeBlock (one cursor coord : ℕ) : Option Bool → List CodeGate
  | none => []
  | some true => [.mul (cursor - 1) coord]
  | some false => [.add one coord, .mul (cursor - 1) cursor]

theorem patternCodeBlock_length (one cursor coord : ℕ) (o : Option Bool) :
    (patternCodeBlock one cursor coord o).length = patternCostCode o := by
  cases o with
  | none => rfl
  | some b => cases b <;> rfl

def patternCodeBlocks (m one cursor : ℕ) : List (ℕ × Option Bool) → List CodeGate
  | [] => []
  | (a, o) :: rest => patternCodeBlock one cursor (patternCoord m a) o ++
      patternCodeBlocks m one (cursor + patternCostCode o) rest

def patternCodeCost (xs : List (ℕ × Option Bool)) : ℕ :=
  (xs.map fun x => patternCostCode x.2).sum

theorem patternCodeBlocks_length (m one cursor : ℕ) (xs : List (ℕ × Option Bool)) :
    (patternCodeBlocks m one cursor xs).length = patternCodeCost xs := by
  induction xs generalizing cursor with
  | nil => rfl
  | cons x xs ih =>
      rcases x with ⟨a,o⟩
      simp only [patternCodeBlocks, List.length_append, patternCodeBlock_length, ih,
        patternCodeCost, List.map_cons, List.sum_cons]

theorem patternCodeBlocks_append (m one cursor : ℕ) (as bs : List (ℕ × Option Bool)) :
    patternCodeBlocks m one cursor (as ++ bs) = patternCodeBlocks m one cursor as ++
      patternCodeBlocks m one (cursor + patternCodeCost as) bs := by
  induction as generalizing cursor with
  | nil => simp [patternCodeBlocks, patternCodeCost]
  | cons a as ih =>
      rcases a with ⟨a,o⟩
      simp only [List.cons_append, patternCodeBlocks, ih, patternCodeCost,
        List.map_cons, List.sum_cons, List.append_assoc, Nat.add_assoc]

/-- Code 1 first forms `1 + coordinate`; every nonzero code multiplies the guard. -/
def patternBranch : S :=
  .ite (.v 37)
    (.seq (.ite (.eq (.v 37) (.k 1))
      (.seq (patternSend 2 (.v 33) (.v 36)) (.set 36 (.sub (.v 24) (.k 1)))) .skip)
      (.seq (patternSend 3 (.v 35) (.v 36)) (.set 35 (.sub (.v 24) (.k 1)))))
    .skip

/-- Parse one entry, compute its coordinate reference, and emit its block. -/
def patternEntry : S :=
  .seq pNat (.seq (.set 37 (.v 5))
    (.seq (.set 36 (.add (.mul (.k 4) (.v 21))
      (.mul (.v 34) (.add (.mul (.k 3) (.v 21)) (.k 1))))) patternBranch))

/-- Constant-one initialization followed by one entry for each coordinate. -/
def patternPrint : S :=
  .seq (.set 33 (.v 24)) (.seq (.set 35 (.v 24))
    (.seq (patternSend 1 (.k 1) (.k 0)) (.loop 34 (.v 21) patternEntry)))

def patternWrites : List Var := [5, 6, 7, 8, 9, 14, 24, 33, 34, 35, 36, 37]

theorem patternBranch_spec (G : Glob) (s : FS) (o : Option Bool) (B : ℕ)
    (h37 : s.env 37 = guardCode o) (h35 : s.env 35 = s.env 24 - 1)
    (h33 : s.env 33 ≤ B) (h36 : s.env 36 ≤ B) (hc : s.env 24 + 2 ≤ B)
    (h3 : 3 ≤ B) (hcap : B ≤ G.cap)
    (hL : ∀ v ≤ B, natBitLength v + 2 ≤ G.K) (hN : G.K ≤ G.N) :
    Appends [5, 6, 7, 8, 9, 24, 35, 36] s (evalS G patternBranch s)
      (patternModeWord (s.env 31)
        ((patternCodeBlock (s.env 33) (s.env 24) (s.env 36) o).flatMap gateWord)) ∧
    (evalS G patternBranch s).env 24 = s.env 24 + patternCostCode o ∧
    (evalS G patternBranch s).env 35 = s.env 24 + patternCostCode o - 1 := by
  have h1 : min 1 G.cap = 1 := min_eq_left (by omega)
  cases o with
  | none =>
      have ht : evalS G patternBranch s = s := by
        simp [patternBranch, evalS_ite, evalE, h37, guardCode]
      simpa only [ht, patternCodeBlock, List.flatMap_nil, patternModeWord_nil,
        patternCostCode, Nat.add_zero] using
        (show Appends [5, 6, 7, 8, 9, 24, 35, 36] s s [] ∧
          s.env 24 = s.env 24 ∧ s.env 35 = s.env 24 - 1 from
          ⟨Appends.refl _ _, rfl, h35⟩)
  | some b =>
      cases b with
      | true =>
          have hs := patternSend_spec G s 3 (s.env 24 - 1) (s.env 36) (.v 35) (.v 36)
            (by omega) (by simpa [evalE] using h35) (by simp [evalE])
            (hL 3 h3) (hL _ (by omega)) (hL _ h36) hN (by omega)
          let t := evalS G (patternSend 3 (.v 35) (.v 36)) s
          have t24 : t.env 24 = s.env 24 + 1 := hs.2
          have ht : evalS G patternBranch s = t.setv 35 (s.env 24) := by
            simp [patternBranch, evalS_ite, evalE, h37, guardCode, h1,
              show (2 : ℕ) ≠ 0 by decide, t, t24]
          have hw := (hs.1.mono (W' := [5, 6, 7, 8, 9, 24, 35, 36]) (by simp)).trans
            (Appends.setv [5, 6, 7, 8, 9, 24, 35, 36] t 35 (by simp) (s.env 24))
          rw [ht]
          refine ⟨?_, ?_, ?_⟩
          · simpa [patternCodeBlock, gateWord] using hw
          · simpa [patternCostCode] using t24
          · simp [patternCostCode]
      | false =>
          have ha := patternSend_spec G s 2 (s.env 33) (s.env 36) (.v 33) (.v 36)
            (by omega) (by simp [evalE]) (by simp [evalE])
            (hL 2 (by omega)) (hL _ h33) (hL _ h36) hN (by omega)
          let t := evalS G (patternSend 2 (.v 33) (.v 36)) s
          have t24 : t.env 24 = s.env 24 + 1 := ha.2
          let u := t.setv 36 (s.env 24)
          have u24 : u.env 24 = s.env 24 + 1 := by simpa [u] using t24
          have u35 : u.env 35 = s.env 24 - 1 := by
            simpa [u] using (ha.1.env 35 (by decide)).trans h35
          have u36 : u.env 36 = s.env 24 := by simp [u]
          have hu : Appends [5, 6, 7, 8, 9, 24, 35, 36] s u
              (patternModeWord (s.env 31)
                (natWord 2 ++ natWord (s.env 33) ++ natWord (s.env 36))) := by
            simpa only [List.append_nil] using
              (ha.1.mono (W' := [5, 6, 7, 8, 9, 24, 35, 36]) (by simp)).trans
                (Appends.setv [5, 6, 7, 8, 9, 24, 35, 36] t 36 (by simp) (s.env 24))
          have u31 : u.env 31 = s.env 31 := hu.env 31 (by decide)
          have hb := patternSend_spec G u 3 (s.env 24 - 1) (s.env 24) (.v 35) (.v 36)
            (by omega) (by simpa [evalE] using u35) (by simpa [evalE] using u36)
            (hL 3 h3) (hL _ (by omega)) (hL _ (by omega)) hN (by rw [u24]; omega)
          let v := evalS G (patternSend 3 (.v 35) (.v 36)) u
          have v24 : v.env 24 = s.env 24 + 2 := by have := hb.2; rw [u24] at this; omega
          have ht : evalS G patternBranch s = v.setv 35 (s.env 24 + 1) := by
            have hta : evalS G (.seq (patternSend 2 (.v 33) (.v 36))
                (.set 36 (.sub (.v 24) (.k 1)))) s = u := by
              simp only [evalS_seq, evalS_set, evalE, h1]
              change t.setv 36 (t.env 24 - 1) = u
              simp only [t24, Nat.add_sub_cancel, u]
            simp only [patternBranch, evalS_ite, evalE, h37, guardCode, h1,
              one_ne_zero, if_false, if_true, evalS_seq]
            simp only [evalS_seq] at hta
            rw [hta]
            change v.setv 35 (evalE G v (.sub (.v 24) (.k 1))) = _
            simp only [evalE, h1, v24]
            congr 1
          have hw := hu.trans ((hb.1.mono (W' := [5, 6, 7, 8, 9, 24, 35, 36]) (by simp)).trans
            (Appends.setv [5, 6, 7, 8, 9, 24, 35, 36] v 35 (by simp) (s.env 24 + 1)))
          rw [ht]
          refine ⟨?_, ?_, ?_⟩
          · simpa [patternCodeBlock, gateWord, patternModeWord_append, u31,
              List.append_assoc] using hw
          · simpa [patternCostCode] using v24
          · simp [patternCostCode]

theorem patternEntry_spec (G : Glob) (s : FS) (m a pos Bd B : ℕ) (o : Option Bool)
    (hat : At (s.env 10) pos (natWord (guardCode o))) (h14 : s.env 14 = pos)
    (hend : pos + (natWord (guardCode o)).length ≤ Bd) (hBd : BdOk G Bd)
    (h21 : s.env 21 = m) (h34 : s.env 34 = a) (h35 : s.env 35 = s.env 24 - 1)
    (h33 : s.env 33 ≤ B) (hc : s.env 24 + 2 ≤ B)
    (hcoord : patternCoord m a ≤ B) (h4 : 4 ≤ B) (hcap : B ≤ G.cap)
    (hL : ∀ v ≤ B, natBitLength v + 2 ≤ G.K) (hN : G.K ≤ G.N) :
    Appends [5, 6, 7, 8, 9, 14, 24, 35, 36, 37] s (evalS G patternEntry s)
      (patternModeWord (s.env 31)
        ((patternCodeBlock (s.env 33) (s.env 24) (patternCoord m a) o).flatMap gateWord)) ∧
    (evalS G patternEntry s).env 14 = pos + (natWord (guardCode o)).length ∧
    (evalS G patternEntry s).env 24 = s.env 24 + patternCostCode o ∧
    (evalS G patternEntry s).env 35 = s.env 24 + patternCostCode o - 1 := by
  obtain ⟨r5, r14, rW⟩ := pNat_at G s (guardCode o) pos Bd hat h14 hend hBd
  let r := evalS G pNat s
  have hr : Appends [5, 6, 8, 9, 14] s r [] :=
    ⟨rW.env, by simpa using rW.out, rW.fl, rW.fp,
      ip_rdFree G pNat s (by decide), rW.bad⟩
  have r21 : r.env 21 = m := (rW.env 21 (by decide)).trans h21
  have r34 : r.env 34 = a := (rW.env 34 (by decide)).trans h34
  let t := (r.setv 37 (guardCode o)).setv 36 (patternCoord m a)
  have hpre : Appends [5, 6, 8, 9, 14, 36, 37] s t [] := by
    simpa only [List.nil_append] using
      ((hr.mono (W' := [5, 6, 8, 9, 14, 36, 37]) (by simp)).trans
        (Appends.setv [5, 6, 8, 9, 14, 36, 37] r 37 (by simp) (guardCode o))).trans
          (Appends.setv [5, 6, 8, 9, 14, 36, 37] _ 36 (by simp) (patternCoord m a))
  have t33 : t.env 33 = s.env 33 := hpre.env 33 (by decide)
  have t24 : t.env 24 = s.env 24 := hpre.env 24 (by decide)
  have t35 : t.env 35 = s.env 24 - 1 := (hpre.env 35 (by decide)).trans h35
  have t31 : t.env 31 = s.env 31 := hpre.env 31 (by decide)
  have t36 : t.env 36 = patternCoord m a := by simp [t]
  have hmul4 : 4 * m ≤ G.cap := by unfold patternCoord at hcoord; omega
  have hmul3 : 3 * m ≤ G.cap := by omega
  have hmul31 : 3 * m + 1 ≤ G.cap := by omega
  have hmulA : a * (3 * m + 1) ≤ G.cap := by unfold patternCoord at hcoord; omega
  have he : evalS G patternEntry s = evalS G patternBranch t := by
    simp only [patternEntry, evalS_seq, evalS_set, evalE]
    change evalS G patternBranch
      ((r.setv 37 (r.env 5)).setv 36
        (evalE G (r.setv 37 (r.env 5))
          (.add (.mul (.k 4) (.v 21)) (.mul (.v 34) (.add (.mul (.k 3) (.v 21)) (.k 1)))))) = _
    have hr5 : r.env 5 = guardCode o := r5
    simp only [hr5, evalE, FS.setv_env, Function.update_of_ne (by decide : (21 : Var) ≠ 37),
      Function.update_of_ne (by decide : (34 : Var) ≠ 37), r21, r34,
      min_eq_left (show 4 ≤ G.cap by omega), min_eq_left (show 3 ≤ G.cap by omega),
      min_eq_left (show 1 ≤ G.cap by omega), min_eq_left hmul4, min_eq_left hmul3,
      min_eq_left hmul31, min_eq_left hmulA,
      min_eq_left (show 4 * m + a * (3 * m + 1) ≤ G.cap from hcoord.trans hcap),
      t, patternCoord]
  obtain ⟨ha, hb, hc'⟩ := patternBranch_spec G t o B (by simp [t])
    (by simpa only [t24] using t35) (by simpa only [t33] using h33)
    (by simpa only [t36] using hcoord) (by simpa only [t24] using hc)
    (by omega) hcap hL hN
  rw [he]
  refine ⟨?_, ?_, by simpa only [t24] using hb, by simpa only [t24] using hc'⟩
  · simpa only [List.nil_append, t33, t24, t31, t36] using
      (hpre.mono (W' := [5, 6, 7, 8, 9, 14, 24, 35, 36, 37]) (by simp)).trans
        (ha.mono (by simp))
  · rw [ha.env 14 (by decide)]
    simpa [t] using r14

def patternEntryWord (x : ℕ × Option Bool) : List Bool := natWord (guardCode x.2)

theorem patternCodeCost_le (xs : List (ℕ × Option Bool)) : patternCodeCost xs ≤ 2 * xs.length := by
  induction xs with
  | nil => simp [patternCodeCost]
  | cons x xs ih =>
      have hx : patternCostCode x.2 ≤ 2 := by
        cases x.2 with
        | none => decide
        | some b => cases b <;> decide
      simp only [patternCodeCost, List.map_cons, List.sum_cons, List.length_cons] at *
      omega

theorem patternCodeCost_take_succ (xs : List (ℕ × Option Bool)) (j : ℕ) (hj : j < xs.length) :
    patternCodeCost (xs.take (j + 1)) = patternCodeCost (xs.take j) + patternCostCode xs[j].2 := by
  rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some]
  simp only [patternCodeCost, List.map_append, List.sum_append, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, Nat.add_zero]

theorem patternCodeBlocks_take_succ (m one cursor : ℕ) (xs : List (ℕ × Option Bool))
    (j : ℕ) (hj : j < xs.length) :
    patternCodeBlocks m one cursor (xs.take (j + 1)) =
      patternCodeBlocks m one cursor (xs.take j) ++
        patternCodeBlock one (cursor + patternCodeCost (xs.take j)) (patternCoord m xs[j].1) xs[j].2 := by
  rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some, patternCodeBlocks_append]
  simp only [patternCodeBlocks, List.append_nil]

def patternLoopWrites : List Var := [5, 6, 7, 8, 9, 14, 24, 34, 35, 36, 37]

theorem patternLoop_spec (G : Glob) (s : FS) (m pos Bd B : ℕ) (xs : List (ℕ × Option Bool))
    (hlen : xs.length = m) (hindex : ∀ (j : ℕ) (hj : j < xs.length), xs[j].1 = j)
    (hat : At (s.env 10) pos (xs.map patternEntryWord).flatten) (h14 : s.env 14 = pos)
    (hend : pos + (xs.map patternEntryWord).flatten.length ≤ Bd) (hBd : BdOk G Bd)
    (h21 : s.env 21 = m) (h35 : s.env 35 = s.env 24 - 1)
    (h33 : s.env 33 ≤ B) (hc : s.env 24 + 2 * m ≤ B)
    (hcoord : patternCoord m m ≤ B) (h4 : 4 ≤ B) (hcap : B ≤ G.cap)
    (hL : ∀ v ≤ B, natBitLength v + 2 ≤ G.K) (hN : G.K ≤ G.N) (hmN : m ≤ G.N) :
    Appends patternLoopWrites s (evalS G (.loop 34 (.v 21) patternEntry) s)
      (patternModeWord (s.env 31)
        ((patternCodeBlocks m (s.env 33) (s.env 24) xs).flatMap gateWord)) ∧
    (evalS G (.loop 34 (.v 21) patternEntry) s).env 14 =
      pos + (xs.map patternEntryWord).flatten.length ∧
    (evalS G (.loop 34 (.v 21) patternEntry) s).env 24 = s.env 24 + patternCodeCost xs ∧
    (evalS G (.loop 34 (.v 21) patternEntry) s).env 35 = s.env 24 + patternCodeCost xs - 1 := by
  have hn : min (evalE G s (.v 21)) G.N = m := by simp only [evalE, h21, min_eq_left hmN]
  have hl := loop_inv G (i := 34) (n := .v 21) (body := patternEntry) (s := s)
    (fun j t =>
      Appends patternLoopWrites s t
        (patternModeWord (s.env 31)
          ((patternCodeBlocks m (s.env 33) (s.env 24) (xs.take j)).flatMap gateWord)) ∧
      t.env 14 = pos + ((xs.take j).map patternEntryWord).flatten.length ∧
      t.env 24 = s.env 24 + patternCodeCost (xs.take j) ∧
      t.env 35 = s.env 24 + patternCodeCost (xs.take j) - 1)
    (by simpa [patternCodeBlocks, patternCodeCost, patternModeWord_nil, h14] using
      (show Appends patternLoopWrites s s [] ∧ s.env 14 = pos ∧
        s.env 24 = s.env 24 ∧ s.env 35 = s.env 24 - 1 from
        ⟨Appends.refl _ _, h14, rfl, h35⟩)) (by
      rw [hn]
      rintro j hj t ⟨tw, t14, t24, t35⟩
      have hjx : j < xs.length := by omega
      let u := t.setv 34 j
      have hu : Appends patternLoopWrites t u [] := Appends.setv _ _ _ (by simp [patternLoopWrites]) _
      have uw := tw.trans hu
      have u10 : u.env 10 = s.env 10 := uw.env 10 (by decide)
      have u21 : u.env 21 = m := (uw.env 21 (by decide)).trans h21
      have u33 : u.env 33 = s.env 33 := uw.env 33 (by decide)
      have u31 : u.env 31 = s.env 31 := uw.env 31 (by decide)
      have u24 : u.env 24 = s.env 24 + patternCodeCost (xs.take j) := by simpa [u] using t24
      have u35 : u.env 35 = u.env 24 - 1 := by simpa [u, t24] using t35
      have hword := At.flatten patternEntryWord xs hat j hjx
      have hsucc := flatten_take_succ_length patternEntryWord xs j hjx
      have hle := flatten_take_le patternEntryWord xs (j + 1)
      have hcost := patternCodeCost_le (xs.take j)
      have htake : (xs.take j).length ≤ j := List.length_take_le _ _
      have hjcoord : patternCoord m j ≤ B := by
        have hp := Nat.mul_le_mul_right (3 * m + 1) hj.le
        unfold patternCoord at *
        omega
      obtain ⟨ew, e14, e24, e35⟩ := patternEntry_spec G u m j
        (pos + ((xs.take j).map patternEntryWord).flatten.length) Bd B xs[j].2
        (by rw [u10]; exact hword) (by simpa [u] using t14) (by change _ + (patternEntryWord xs[j]).length ≤ _; omega)
        hBd u21 (by simp [u]) u35 (by simpa only [u33] using h33)
        (by rw [u24]; omega) hjcoord h4 hcap hL hN
      refine ⟨?_, ?_, ?_, ?_⟩
      · have hall := uw.trans (ew.mono (W' := patternLoopWrites) (by decide))
        simpa only [patternCodeBlocks_take_succ m (s.env 33) (s.env 24) xs j hjx,
          List.flatMap_append, patternModeWord_append, hindex j hjx, u33, u24, u31,
          List.append_nil] using hall
      · rw [e14, hsucc]
        simp only [patternEntryWord, Nat.add_assoc]
      · rw [e24, u24, patternCodeCost_take_succ xs j hjx]
        omega
      · rw [e35, u24, patternCodeCost_take_succ xs j hjx]
        omega)
  rw [hn, show xs.take m = xs by rw [← hlen, List.take_length]] at hl
  exact hl

def patternCodeGates (m start : ℕ) (xs : List (ℕ × Option Bool)) : List CodeGate :=
  .const 1 :: patternCodeBlocks m start (start + 1) xs

theorem patternPrint_codes_spec (G : Glob) (s : FS) (m pos Bd B : ℕ) (xs : List (ℕ × Option Bool))
    (hlen : xs.length = m) (hindex : ∀ (j : ℕ) (hj : j < xs.length), xs[j].1 = j)
    (hat : At (s.env 10) pos (xs.map patternEntryWord).flatten) (h14 : s.env 14 = pos)
    (hend : pos + (xs.map patternEntryWord).flatten.length ≤ Bd) (hBd : BdOk G Bd)
    (h21 : s.env 21 = m) (hc : s.env 24 + 1 + 2 * m ≤ B)
    (hcoord : patternCoord m m ≤ B) (h4 : 4 ≤ B) (hcap : B ≤ G.cap)
    (hL : ∀ v ≤ B, natBitLength v + 2 ≤ G.K) (hN : G.K ≤ G.N) (hmN : m ≤ G.N) :
    Appends patternWrites s (evalS G patternPrint s)
      (patternModeWord (s.env 31) ((patternCodeGates m (s.env 24) xs).flatMap gateWord)) ∧
    (evalS G patternPrint s).env 14 = pos + (xs.map patternEntryWord).flatten.length ∧
    (evalS G patternPrint s).env 24 = s.env 24 + 1 + patternCodeCost xs ∧
    (evalS G patternPrint s).env 35 = s.env 24 + patternCodeCost xs ∧
    (evalS G patternPrint s).env 33 = s.env 24 := by
  let u := (s.setv 33 (s.env 24)).setv 35 (s.env 24)
  have hu : Appends [33, 35] s u [] := by
    simpa only [List.nil_append] using
      (Appends.setv [33, 35] s 33 (by simp) (s.env 24)).trans
        (Appends.setv [33, 35] _ 35 (by simp) (s.env 24))
  have hemit := patternSend_spec G u 1 1 0 (.k 1) (.k 0)
    (by omega) (by simp [evalE]; omega) (by simp [evalE])
    (hL 1 (by omega)) (hL 1 (by omega)) (hL 0 (by omega)) hN (by simp [u]; omega)
  let r := evalS G (patternSend 1 (.k 1) (.k 0)) u
  have rW : Appends patternWrites s r
      (patternModeWord (s.env 31) (gateWord (.const 1))) := by
    simpa [u, gateWord] using
      (hu.mono (W' := patternWrites) (by decide)).trans
        (hemit.1.mono (by decide))
  have r24 : r.env 24 = s.env 24 + 1 := by simpa [u] using hemit.2
  have r33 : r.env 33 = s.env 24 := by simpa [u] using hemit.1.env 33 (by decide)
  have r35 : r.env 35 = r.env 24 - 1 := by
    rw [r24]
    simpa [u] using hemit.1.env 35 (by decide)
  have r14 : r.env 14 = pos := by
    exact (hemit.1.env 14 (by decide)).trans ((hu.env 14 (by decide)).trans h14)
  have r10 : r.env 10 = s.env 10 := rW.env 10 (by decide)
  have r21 : r.env 21 = m := (rW.env 21 (by decide)).trans h21
  have r31 : r.env 31 = s.env 31 := rW.env 31 (by decide)
  obtain ⟨lw, l14, l24, l35⟩ := patternLoop_spec G r m pos Bd B xs hlen hindex
    (by rw [r10]; exact hat) r14 hend hBd r21 r35 (by rw [r33]; omega)
    (by rw [r24]; exact hc) hcoord h4 hcap hL hN hmN
  have he : evalS G patternPrint s = evalS G (.loop 34 (.v 21) patternEntry) r := by
    simp only [patternPrint, evalS_seq, evalS_set, evalE, FS.setv_env,
      Function.update_of_ne (by decide : (24 : Var) ≠ 33), u, r]
  rw [he]
  refine ⟨?_, l14, by simpa only [r24] using l24, ?_, ?_⟩
  · simpa only [patternCodeGates, List.flatMap_cons, patternModeWord_append, r31, r33, r24] using
      rW.trans (lw.mono (by decide))
  · rw [l35, r24]
    omega
  · exact (lw.env 33 (by decide)).trans r33

def patternEntries {m : ℕ} (p : Pattern m) : List (ℕ × Option Bool) :=
  (List.finRange m).map fun a => (a.val, p a)

theorem patternEntries_length {m : ℕ} (p : Pattern m) : (patternEntries p).length = m := by
  simp [patternEntries]

theorem patternEntries_index {m : ℕ} (p : Pattern m) (j : ℕ) (hj : j < (patternEntries p).length) :
    (patternEntries p)[j].1 = j := by simp [patternEntries]

theorem patternEntries_word {m : ℕ} (p : Pattern m) :
    ((patternEntries p).map patternEntryWord).flatten = patternWord p := by
  simp [patternEntries, patternEntryWord, patternWord, List.ofFn_eq_map, List.flatMap_def,
    Function.comp_def]

theorem patternEntries_cost {m : ℕ} (p : Pattern m) :
    patternCodeCost (patternEntries p) = ((List.finRange m).map (Circuit.patternCost p)).sum := by
  simp only [patternCodeCost, patternEntries, List.map_map]
  rfl

theorem patternCodeBlocks_code {F : Type} {m : ℕ} (encode : F → ℕ) (p : Pattern m)
    (one cursor : ℕ) (as : List (Fin m)) :
    patternCodeBlocks m one cursor (as.map fun a => (a.val, p a)) =
      (Circuit.Encoding.patternBlocks (F := F) (Circuit.PrefixFormula.rowIds m m m) p one cursor as).map
        (codeGate encode) := by
  induction as generalizing cursor with
  | nil => rfl
  | cons a as ih =>
      simp only [List.map_cons, patternCodeBlocks, Circuit.Encoding.patternBlocks, List.map_append, ih]
      have hrow := rowIds_patternCoord m a.val one a.isLt
      cases hp : p a with
      | none => simp [patternCodeBlock, Circuit.Encoding.patternBlock,
          patternCostCode, Circuit.patternCost, hp]
      | some b =>
          cases b <;> simp only [patternCodeBlock, Circuit.Encoding.patternBlock,
            patternCostCode, Circuit.patternCost, hp, hrow, codeGate, List.map_cons, List.map_nil]

theorem patternCodeGates_code {F : Type} [Field F] {m : ℕ} (encode : F → ℕ)
    (h1 : encode 1 = 1) (p : Pattern m) (start : ℕ) :
    patternCodeGates m start (patternEntries p) =
      (Circuit.Encoding.patternGates (Circuit.PrefixFormula.rowIds m m m) p start).map (codeGate encode) := by
  simp only [patternCodeGates, patternEntries, Circuit.Encoding.patternGates, List.map_cons, codeGate, h1]
  congr 1
  exact patternCodeBlocks_code encode p start (start + 1) (List.finRange m)

/-- Exact guard compiler output, parser position, gate count, and returned guard index.
The hypotheses are only the actual packed input and explicit arithmetic room. -/
theorem patternPrint_spec {F : Type} [Field F] (G : Glob) (s : FS) {m : ℕ}
    (encode : F → ℕ) (hone : encode 1 = 1) (p : Pattern m) (pos Bd B : ℕ)
    (hat : At (s.env 10) pos (patternWord p)) (h14 : s.env 14 = pos)
    (hend : pos + (patternWord p).length ≤ Bd) (hBd : BdOk G Bd)
    (h21 : s.env 21 = m) (hc : s.env 24 + 1 + 2 * m ≤ B)
    (hcoord : patternCoord m m ≤ B) (h4 : 4 ≤ B) (hcap : B ≤ G.cap)
    (hL : ∀ v ≤ B, natBitLength v + 2 ≤ G.K) (hN : G.K ≤ G.N) (hmN : m ≤ G.N) :
    Appends patternWrites s (evalS G patternPrint s)
      (patternModeWord (s.env 31)
        (((Circuit.Encoding.patternGates (Circuit.PrefixFormula.rowIds m m m) p (s.env 24)).map
          (codeGate encode)).flatMap gateWord)) ∧
    (evalS G patternPrint s).env 14 = pos + (patternWord p).length ∧
    (evalS G patternPrint s).env 24 =
      s.env 24 + 1 + ((List.finRange m).map (Circuit.patternCost p)).sum ∧
    (evalS G patternPrint s).env 35 =
      s.env 24 + ((List.finRange m).map (Circuit.patternCost p)).sum ∧
    (evalS G patternPrint s).env 33 = s.env 24 := by
  have h := patternPrint_codes_spec G s m pos Bd B (patternEntries p)
    (patternEntries_length p) (patternEntries_index p)
    (by simpa only [patternEntries_word] using hat) h14
    (by simpa only [patternEntries_word] using hend) hBd h21 hc hcoord h4 hcap hL hN hmN
  simpa only [patternCodeGates_code encode hone p, patternEntries_word, patternEntries_cost] using h

theorem patternCodeBlocks_all_none (m one cursor : ℕ) (xs : List (ℕ × Option Bool))
    (h : ∀ x ∈ xs, x.2 = none) :
    patternCodeBlocks m one cursor xs = [] ∧ patternCodeCost xs = 0 := by
  induction xs generalizing cursor with
  | nil => exact ⟨rfl, rfl⟩
  | cons x xs ih =>
      rcases x with ⟨a,o⟩
      have ho : o = none := h (a,o) (by simp)
      have ht := ih cursor (fun x hx => h x (by simp [hx]))
      simpa only [patternCodeBlocks, patternCodeCost, List.map_cons, List.sum_cons,
        ho, patternCodeBlock, patternCostCode, Nat.add_zero, Nat.zero_add, List.nil_append]
        using ht

/-- Every all-none pattern, including the zero-coordinate case, retains the initial one gate. -/
theorem patternPrint_none_spec (G : Glob) (s : FS) (m pos Bd B : ℕ)
    (hat : At (s.env 10) pos (patternWord (fun _ : Fin m => none))) (h14 : s.env 14 = pos)
    (hend : pos + (patternWord (fun _ : Fin m => none)).length ≤ Bd) (hBd : BdOk G Bd)
    (h21 : s.env 21 = m) (hc : s.env 24 + 1 + 2 * m ≤ B)
    (hcoord : patternCoord m m ≤ B) (h4 : 4 ≤ B) (hcap : B ≤ G.cap)
    (hL : ∀ v ≤ B, natBitLength v + 2 ≤ G.K) (hN : G.K ≤ G.N) (hmN : m ≤ G.N) :
    Appends patternWrites s (evalS G patternPrint s)
      (patternModeWord (s.env 31) (gateWord (.const 1))) ∧
    (evalS G patternPrint s).env 14 = pos + (patternWord (fun _ : Fin m => none)).length ∧
    (evalS G patternPrint s).env 24 = s.env 24 + 1 ∧
    (evalS G patternPrint s).env 35 = s.env 24 ∧
    (evalS G patternPrint s).env 33 = s.env 24 := by
  let p : Pattern m := fun _ => none
  have h := patternPrint_codes_spec G s m pos Bd B (patternEntries p)
    (patternEntries_length p) (patternEntries_index p)
    (by simpa only [patternEntries_word] using hat) h14
    (by simpa only [patternEntries_word] using hend) hBd h21 hc hcoord h4 hcap hL hN hmN
  obtain ⟨hb, hc'⟩ := patternCodeBlocks_all_none m (s.env 24) (s.env 24 + 1) (patternEntries p) (by
    intro x hx
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hx
    rfl)
  simpa only [patternCodeGates, hb, hc', Nat.add_zero, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, patternEntries_word, p] using h

theorem patternSend_wf (tag : ℕ) (x y : E) (d : ℕ) (hd : d < 8)
    (hx : dE x < 16) (hy : dE y < 16) : wfS (patternSend tag x y) d = true := by
  simp [patternSend, wfS, dE, gateStep_wf d hd, hx, hy]

theorem patternBranch_wf (d : ℕ) (hd : d < 8) : wfS patternBranch d = true := by
  simp [patternBranch, patternSend, wfS, dE, gateStep_wf d hd]

theorem patternEntry_wf (d : ℕ) (hd : d < 8) : wfS patternEntry d = true := by
  simp [patternEntry, pNat, pNatOnes, pNatBits, bitE, wfS, dE, hd,
    patternBranch_wf d hd]

theorem patternPrint_wf (d : ℕ) (hd : d < 7) : wfS patternPrint d = true := by
  have h8 : d < 8 := by omega
  simp [patternPrint, patternSend, wfS, dE, gateStep_wf d h8,
    patternEntry_wf (d + 1) (by omega), h8]

end NearCubicGates.Adapters.Routing.TermsMachine
