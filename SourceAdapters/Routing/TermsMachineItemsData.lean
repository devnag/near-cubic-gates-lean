import SourceAdapters.Routing.CircuitEncodingExpr
import SourceAdapters.Routing.CircuitEncodingPattern
import SourceAdapters.Routing.CircuitPrefixFormula
import SourceAdapters.Routing.TermsMachinePrefixData

/-! # Exact ordered gates of the whole shared-prefix item compiler -/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Routing.TermsMachine.Items

open NearCubicGates.Adapters.ACSP
open Circuit Circuit.Encoding Circuit.PrefixFormula

variable {F : Type} [Field F]

/-- One item's gates, including its product and new global accumulator. -/
def itemGates (l : Layout) (ids : List ℕ) (item : Item l.m F) (acc start : ℕ) : Gates F :=
  let pat := patternGates ids item.1 start
  let exprStart := start + pat.length
  let next := exprStart + gateCount item.2
  pat ++ expressionGates l exprStart item.2 ++
    [.mul (exprStart - 1) (next - 1), .add acc next]

theorem itemGates_length (l : Layout) (ids : List ℕ) (item : Item l.m F) (acc start : ℕ) :
    (itemGates l ids item acc start).length = itemCost item := by
  simp only [itemGates, List.length_append, expressionGates_length, List.length_cons,
    List.length_nil, patternGates_length, itemCost]
  omega

/-- The exact suffix and returned index, with no read-validity premise. -/
theorem termStep_exact (l : Layout) (ids : List ℕ) (item : Item l.m F) (acc : ℕ) (gs : Gates F) :
    (termStep l ids item acc).run gs =
      (gs.length + itemCost item - 1, gs ++ itemGates l ids item acc gs.length) := by
  change (let rp := (compilePattern ids item.1).run gs
    let re := (compileExpr l item.2).run rp.2
    ((re.2 ++ [ArithGate.mul rp.1 re.1]).length,
      (re.2 ++ [ArithGate.mul rp.1 re.1]) ++ [ArithGate.add acc re.2.length])) = _
  rw [compilePattern_run]
  simp only [compileExpr_run, List.length_append, patternGates_length,
    expressionGates_length, List.length_singleton]
  simp only [itemGates, patternGates_length, itemCost, List.append_assoc, List.singleton_append]
  congr 5 <;> first | omega | (congr 1; omega)

/-- Ordered item suffixes, carrying their exact accumulator and next gate index. -/
def itemsGates (l : Layout) (ids : List ℕ) : List (Item l.m F) → ℕ → ℕ → Gates F
  | [], _, _ => []
  | item :: items, acc, start =>
      itemGates l ids item acc start ++
        itemsGates l ids items (start + itemCost item - 1) (start + itemCost item)

theorem itemsGates_length (l : Layout) (ids : List ℕ) (items : List (Item l.m F)) (acc start : ℕ) :
    (itemsGates l ids items acc start).length = (items.map itemCost).sum := by
  induction items generalizing acc start with
  | nil => rfl
  | cons i items ih => simp only [itemsGates, List.length_append, itemGates_length, ih,
      List.map_cons, List.sum_cons]

/-- The accumulator remains the last gate after every prefix of the item list. -/
theorem termLoop_exact (l : Layout) (ids : List ℕ) (items : List (Item l.m F))
    (acc : ℕ) (gs : Gates F) (hlast : acc + 1 = gs.length) :
    (loop (termStep l ids) items acc).run gs =
      (gs.length + (items.map itemCost).sum - 1, gs ++ itemsGates l ids items acc gs.length) := by
  induction items generalizing acc gs with
  | nil =>
      change (acc, gs) = (gs.length + 0 - 1, gs ++ [])
      have hh : acc = gs.length - 1 := by omega
      simp [hh]
  | cons i items ih =>
      let st := (termStep l ids i acc).run gs
      have hs : st = (gs.length + itemCost i - 1, gs ++ itemGates l ids i acc gs.length) :=
        termStep_exact l ids i acc gs
      have hlen : st.2.length = gs.length + itemCost i := by
        rw [hs]
        simp only [List.length_append, itemGates_length]
      have hlast' : st.1 + 1 = st.2.length := by rw [hlen, hs]; simp only; omega
      change (loop (termStep l ids) items st.1).run st.2 = _
      rw [ih st.1 st.2 hlast', hlen, hs]
      simp only [itemsGates, List.map_cons, List.sum_cons, Nat.add_assoc, List.append_assoc]

/-- The whole circuit as its exact prefix, zero accumulator, and ordered item suffix. -/
theorem compileTerms_exact (l : Layout) {e : Fin l.m → F} (coords : Coordinates l.m e)
    (items : List (Item l.m F)) :
    (compileTerms l e coords items).gates =
      prefixGates l coords 0 ++ [.const 0] ++
        itemsGates l (rowIds l.m l.m l.m) items (3 * l.m ^ 2 + 2 * l.m)
          (3 * l.m ^ 2 + 2 * l.m + 1) := by
  simp only [compileTerms, bind_run, push_run, compileCoordinates_exact l coords [],
    List.length_nil, Nat.zero_add, List.nil_append]
  rw [termLoop_exact l _ items _ _ (by simp)]
  simp only [List.length_append, List.length_singleton, prefixGates_length]

/-- Any constant encoding preserves the exact order and repeated gates. -/
theorem compileTerms_codes (l : Layout) {e : Fin l.m → F} (coords : Coordinates l.m e)
    (items : List (Item l.m F)) (encode : F → ℕ) :
    (compileTerms l e coords items).gates.map (codeGate encode) =
      (prefixGates l coords 0).map (codeGate encode) ++ [Joins.CodeGate.const (encode 0)] ++
        (itemsGates l (rowIds l.m l.m l.m) items (3 * l.m ^ 2 + 2 * l.m)
          (3 * l.m ^ 2 + 2 * l.m + 1)).map (codeGate encode) := by
  rw [compileTerms_exact]
  simp only [List.map_append, List.map_cons, List.map_nil, codeGate]

end NearCubicGates.Adapters.Routing.TermsMachine.Items
