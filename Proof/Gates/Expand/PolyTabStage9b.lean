import Proof.Gates.Expand.PolyTabStage9a

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

namespace NearCubicGates.Close.Expand.PolyTab

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)
open NearCubicGates.Close.WordPrograms
open NearCubicGates.Close.CounterMachine NearCubicGates.Close.Tabulator NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.TabMachine
open NearCubicGates.Close.WordPrograms.SInt (encS)

/-- The occurrence table's numbers. -/
def VTn (E : ExpandMachine) (r : TabReq) : List ℕ := (List.finRange r.V).flatMap fun v => occRecs (occ (tabT E r) v)

theorem occRecs_occ_length (E : ExpandMachine) (r : TabReq) (v : Fin r.V) :
    (occRecs (occ (tabT E r) v)).length = r.k + r.s + 2 := by
  simp [occRecs, occ]; try ring

theorem flatMap_drop_take {α β : Type} (f : α → List β) (c : ℕ) :
    ∀ (l : List α), (∀ a ∈ l, (f a).length = c) → ∀ (b : ℕ) (hb : b < l.length),
      ((l.flatMap f).drop (c * b)).take c = f l[b]
  | [], _, b, hb => by simp at hb
  | a :: l, h, b, hb => by
    have ha := h a (by simp)
    rw [List.flatMap_cons]
    cases b with
    | zero => simp [← ha]
    | succ b =>
      rw [show c * (b + 1) = (f a).length + c * b by rw [ha]; ring, ← List.drop_drop, List.drop_left]
      rw [flatMap_drop_take f c l (fun x hx => h x (by simp [hx])) b (by simpa using hb)]
      simp

theorem vt_seg (Wb : ℕ) (E : ExpandMachine) (r : TabReq) (v : Fin r.V) :
    segRecs Wb (VTn E r) (v.val * (r.k + r.s + 2)) (r.k + r.s + 2) =
      (occRecs (occ (tabT E r) v)).flatMap fun x => frame (binary Wb x) := by
  unfold segRecs VTn
  rw [mul_comm, flatMap_drop_take _ (r.k + r.s + 2) _ (fun v _ => occRecs_occ_length E r v) v.val (by simp)]
  simp

theorem VTn_length (E : ExpandMachine) (r : TabReq) : (VTn E r).length = r.V * (r.k + r.s + 2) := by
  unfold VTn
  rw [flatMap_len_const _ _ (r.k + r.s + 2) (fun v _ => occRecs_occ_length E r v)]
  simp

theorem vtRecs_VTn (Wb : ℕ) (E : ExpandMachine) (r : TabReq) :
    vtRecs Wb E r r.V = ((VTn E r).map (binary Wb)).flatMap frame := by
  unfold vtRecs VTn vRecs
  rw [List.take_of_length_le (by simp), List.map_flatMap, List.flatMap_assoc]
  simp [List.flatMap_map]

/-- The variable list of a monomial, increasing. -/
def mvars {V : ℕ} (t : Finset (Fin V) × ℤ) : List (Fin V) := t.1.sort (· ≤ ·)

/-- One monomial's occurrence records. -/
theorem blkRecs_term (E : ExpandMachine) (r : TabReq) (t : Finset (Fin r.V) × ℤ) :
    blkRecs (((mvars t).map (occ (tabT E r))).reverse, t.2) =
      (mvars t).length :: ((mvars t).reverse.flatMap fun v => occRecs (occ (tabT E r) v)) := by
  simp only [blkRecs, List.length_reverse, List.length_map, ← List.map_reverse, List.flatMap_map]

theorem tsK_eq (E : ExpandMachine) (r : TabReq) :
    tsK E r = (E.expand ⟨r.V, r.F⟩).map fun t => (((mvars t).map (occ (tabT E r))).reverse, t.2) := by
  rfl

end NearCubicGates.Close.Expand.PolyTab
