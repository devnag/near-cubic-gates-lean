import SourceAdapters.ShortPCP.Machines.FLangParseMain
import SourceAdapters.ShortPCP.Machines.FLangComp

/-!
# Bounded first-occurrence lookup in a packed translation bank

The read-index convention is one plus the first matching bank position, with
one plus the bank length for an absent mask. The counted scan visits only the
bank entries and preserves all parsing and circuit-construction registers.
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Routing.TermsMachine

open NearCubicGates.Adapters.ShortPCP.Machines.FL

/-- Entry at position `43`, with packed bank `23` and entry width `30`. -/
def bankEntry : E :=
  .md (.shr (.v 23) (.mul (.v 43) (.v 30))) (.shl (.k 1) (.v 30))

/-- Retain the first match. Zero marks that no earlier entry matched. -/
def lookupStep : S :=
  .ite (.eq (.v 15) (.k 0))
    (.ite (.eq bankEntry (.v 46)) (.set 15 (.add (.v 43) (.k 1))) .skip) .skip

def lookup : S :=
  .seq (.set 15 (.k 0)) (.seq (.loop 43 (.v 26) lookupStep)
    (.ite (.eq (.v 15) (.k 0)) (.set 15 (.add (.v 26) (.k 1))) .skip))

/-- Before the first match, an entry matches exactly at the first index. -/
theorem entry_eq_iff (bank : List ℕ) (target j : ℕ) (hj : j < bank.length)
    (hfirst : j ≤ bank.idxOf target) :
    bank.getD j 0 = target ↔ bank.idxOf target = j := by
  rw [List.getD_eq_getElem _ _ hj]
  constructor
  · intro h
    by_contra he
    have hlt : j < bank.idxOf target := by omega
    have hn := List.not_of_lt_findIdx (xs := bank) (p := fun x => x == target) hlt
    have hn' : (bank[j] == target) = false := hn
    simp [h] at hn'
  · intro he
    subst j
    exact List.getElem_idxOf hj

/-- Actual counted lookup, including repeated entries and absent masks. -/
theorem lookup_spec (G : Glob) (s : FS) (bank : List ℕ) (width target : ℕ)
    (h23 : s.env 23 = packW width bank) (h26 : s.env 26 = bank.length)
    (h30 : s.env 30 = width) (h46 : s.env 46 = target)
    (hwords : ∀ x ∈ bank, x < 2 ^ width)
    (hN : bank.length ≤ G.N) (hcount : bank.length + 1 ≤ G.cap)
    (hproduct : bank.length * width ≤ G.cap) (hwidth : 2 ^ width ≤ G.cap) :
    let t := evalS G lookup s
    t.env 15 = 1 + bank.idxOf target ∧ Wr [15, 43] s t ∧ t.ip = s.ip := by
  have h1 : min 1 G.cap = 1 := by omega
  let start := s.setv 15 0
  have hmin : min (evalE G start (.v 26)) G.N = bank.length := by
    simpa [start, evalE, h26] using min_eq_left hN
  have hloop := loop_inv G (i := 43) (n := .v 26) (body := lookupStep) (s := start)
    (fun j t => t.env 15 = (if bank.idxOf target < j then 1 + bank.idxOf target else 0) ∧
      Wr [15, 43] s t)
    ⟨by simp [start], Wr.setv s (by simp) 0⟩ (by
      rw [hmin]
      rintro j hj t ⟨ht15, htW⟩
      let u := t.setv 43 j
      have huW : Wr [15, 43] s u := htW.trans (Wr.setv t (by simp) j)
      have hu15 : u.env 15 = t.env 15 := by simp [u]
      have hu23 : u.env 23 = packW width bank := (huW.env 23 (by decide)).trans h23
      have hu30 : u.env 30 = width := (huW.env 30 (by decide)).trans h30
      have hu46 : u.env 46 = target := (huW.env 46 (by decide)).trans h46
      have hmul : min (j * width) G.cap = j * width := by
        apply min_eq_left
        exact (Nat.mul_le_mul_right width hj.le).trans hproduct
      have hentry : evalE G u bankEntry = bank.getD j 0 := by
        simp only [bankEntry, evalE, hu23, hu30, show u.env 43 = j by simp [u],
          hmul, h1, one_mul, min_eq_left hwidth]
        exact packW_get width bank hwords j
      have hinc : evalE G u (.add (.v 43) (.k 1)) = j + 1 := by
        simp only [evalE, show u.env 43 = j by simp [u], h1]
        apply min_eq_left
        omega
      change (evalS G lookupStep u).env 15 = _ ∧ Wr [15, 43] s (evalS G lookupStep u)
      by_cases hbefore : bank.idxOf target < j
      · have hnonzero : t.env 15 ≠ 0 := by rw [ht15, if_pos hbefore]; omega
        have he : evalS G lookupStep u = u := by
          simp only [lookupStep, evalS_ite, evalE, hu15, Nat.zero_min, hnonzero,
            if_false, if_true, evalS_skip]
        rw [he]
        refine ⟨?_, huW⟩
        rw [hu15, ht15, if_pos hbefore, if_pos (by omega)]
      · have hz : u.env 15 = 0 := by rw [hu15, ht15, if_neg hbefore]
        have heq := entry_eq_iff bank target j hj (by omega)
        by_cases hm : bank.getD j 0 = target
        · have hi : bank.idxOf target = j := heq.mp hm
          have he : evalS G lookupStep u = u.setv 15 (j + 1) := by
            simp only [lookupStep, evalS_ite, evalE, hz, Nat.zero_min,
              if_true, one_ne_zero, if_false, hentry, hu46, hm, evalS_set]
            exact congrArg (u.setv 15) hinc
          rw [he]
          refine ⟨?_, huW.trans (Wr.setv u (by simp) _)⟩
          simp [hi, Nat.add_comm]
        · have hn : ¬bank.idxOf target < j + 1 := by
            have := mt heq.mpr hm
            omega
          have he : evalS G lookupStep u = u := by
            simp only [lookupStep, evalS_ite, evalE, hz, Nat.zero_min,
              if_true, one_ne_zero, if_false, hentry, hu46, hm, evalS_skip]
          rw [he]
          exact ⟨by rw [hz, if_neg hn], huW⟩)
  rw [hmin] at hloop
  generalize ht : evalS G (.loop 43 (.v 26) lookupStep) start = t at hloop
  obtain ⟨ht15, htW⟩ := hloop
  have ht26 : t.env 26 = bank.length := (htW.env 26 (by decide)).trans h26
  have hhead : evalS G (.set 15 (.k 0)) s = start := by simp [start, evalE]
  have htail : evalS G lookup s = evalS G
      (.ite (.eq (.v 15) (.k 0)) (.set 15 (.add (.v 26) (.k 1))) .skip) t := by
    simp only [lookup, evalS_seq, hhead, ht]
  have hip : (evalS G lookup s).ip = s.ip := ip_rdFree G lookup s (by decide)
  refine ⟨?_, ?_, hip⟩
  · rw [htail]
    by_cases hm : bank.idxOf target < bank.length
    · have hz : t.env 15 ≠ 0 := by rw [ht15, if_pos hm]; omega
      simpa only [evalS_ite, evalE, Nat.zero_min, hz, if_false, if_true, evalS_skip]
        using ht15.trans (if_pos hm)
    · have hi : bank.idxOf target = bank.length := le_antisymm List.idxOf_le_length (by omega)
      have hz : t.env 15 = 0 := ht15.trans (if_neg hm)
      simp only [evalS_ite, evalE, hz, Nat.zero_min, if_true, one_ne_zero, if_false, evalS_set,
        ht26, h1, FS.setv_env, Function.update_self, min_eq_left hcount, hi]
      omega
  · rw [htail, evalS_ite]
    split
    · exact htW
    · exact htW.trans (Wr.setv t (by simp) _)

theorem lookup_wf (d : ℕ) (hd : d ≤ 7) : wfS lookup d = true := by
  simp [lookup, lookupStep, bankEntry, wfS, dE]
  omega

end NearCubicGates.Adapters.Routing.TermsMachine
