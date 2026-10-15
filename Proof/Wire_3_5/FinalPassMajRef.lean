import Proof.Wire_3_5.FinalPassFlatTable
import Proof.Wire_3_5.FinalPassSym

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.Maj
open NearCubicWires NearCubicWires.WireExponent3_5.FinalPass NearCubicWires.WireExponent3_5.FinalPass.ListEval
open NearCubicWires.WireExponent3_5.Lists NearCubicWires.SupplierWalk
open Finset

variable (P : FlatListParams) (e : P.FlatSeed) (L : ℕ) (Z : List Bool)

/-- The level rows of visit `k` (the rows of `flatTable`'s `k`-th visit word). -/
def visitRows (k : Fin P.walkLen) : ℕ → List Bool := rowsOf (P.base.data (P.decode (e.vertex k))) L

/-- The visits reporting `s`. -/
def majCount (s : ℕ) : ℕ := (univ.filter fun k : Fin P.walkLen => visitReportFast P e k Z = s).card

theorem majStateFast_eq (s : ℕ) :
    majStateFast P e Z s = decide (majorityThreshold P.walkLen ≤ majCount P e Z s) := by
  unfold majStateFast concreteMajorityFailure concreteBadTimes majCount visitReportFast
  congr 2
  congr 1
  ext k
  simp [concreteBadAt]

/-- **A visit's stage-5 report is the visit's report.** -/
theorem reportRef_visit (hZ : Z.length = L) (k : Fin P.walkLen) :
    reportRef P.M P.base.J P.base.W (visitRows P e L k) Z = visitReportFast P e k Z :=
  reportRef_eq_fast (P.base.data (P.decode (e.vertex k))) L Z hZ

theorem majStateFast_unique {s s' : ℕ} (hs : majStateFast P e Z s = true) (hs' : majStateFast P e Z s' = true) :
    s = s' := by
  rw [← majState_eq_fast] at hs hs'
  exact P.majState_unique e Z hs hs'

/-- The majority test as the machine decides it: `(t+1)/2 ≤ A` iff not `2A < t`. -/
theorem thr_iff (t A : ℕ) : majorityThreshold t ≤ A ↔ ¬ (2 * A < t) := by
  unfold majorityThreshold
  omega

/-- The count in table order. -/
theorem majCount_eq_sum (s : ℕ) :
    majCount P e Z s = ((List.finRange P.walkLen).map fun k => if visitReportFast P e k Z = s then 1 else 0).sum := by
  unfold majCount
  rw [card_filter, Fin.sum_univ_def]

/-- A sum of the members that satisfy a predicate held by at most one member is the first such member. -/
theorem sum_ite_unique (p : ℕ → Bool) (hp : ∀ a b, p a = true → p b = true → a = b) :
    ∀ l : List ℕ, l.Nodup → (l.map fun x => if p x then x else 0).sum = (l.find? p).getD 0
  | [], _ => rfl
  | x :: xs, hnd => by
    have hx : x ∉ xs := (List.nodup_cons.mp hnd).1
    have ih := sum_ite_unique p hp xs (List.nodup_cons.mp hnd).2
    rw [List.map_cons, List.sum_cons, List.find?_cons]
    by_cases h : p x = true
    · rw [if_pos h, h]
      have hz : (xs.map fun x => if p x then x else 0).sum = 0 := by
        rw [List.sum_eq_zero]
        intro y hy
        obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hy
        by_cases hpz : p z = true
        · exact absurd (hp x z h hpz ▸ hz) hx
        · rw [if_neg hpz]
      rw [hz]
      rfl
    · rw [if_neg h, ih]
      simp only [Bool.not_eq_true] at h
      rw [h]
      simp

/-- The result register after the states `1, …, m`. -/
def accR (m : ℕ) : ℕ := ((List.range m).map fun i => if majStateFast P e Z (i + 1) then i + 1 else 0).sum

theorem accR_succ (m : ℕ) :
    accR P e Z (m + 1) = accR P e Z m + if majStateFast P e Z (m + 1) then m + 1 else 0 := by
  unfold accR
  rw [List.range_succ, List.map_append, List.sum_append]
  simp

/-- **After `s = M` the result is the amplified list's report.** -/
theorem accR_M : accR P e Z P.M = flatReportFast P e Z := by
  unfold accR flatReportFast
  have h := sum_ite_unique (majStateFast P e Z) (fun a b ha hb => majStateFast_unique P e Z ha hb)
    ((List.range P.M).map (· + 1)) ((List.nodup_range).map (fun a b h => by simpa using h))
  rw [← h, List.map_map]
  rfl

end NearCubicWires.WireExponent3_5.FinalPass.Maj
