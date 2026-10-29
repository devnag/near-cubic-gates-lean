import SourceAdapters.Routing.CircuitTerms

/-!
# Unconditional syntactic count of the shared-prefix circuit compiler

The compiler of `lem:generator` emits the constraint circuit term by term.
Its serialized `listWord` output begins with the exact gate count.
Counts do not depend on read membership, well-formed gate references, input
length restrictions, or the truth of the emitted equations.

The coordinate prefix count reuses compileCoordinates_spec at the empty prefix.
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Routing.Circuit.Encoding

open NearCubicGates.Adapters.ACSP

variable {F : Type}

theorem compileExpr_length (l : Layout) (E : Expr F) (gs : Gates F) :
    ((compileExpr l E).run gs).2.length = gs.length + gateCount E := by
  induction E generalizing gs with
  | const c => simp [compileExpr, gateCount]
  | read v => simp [compileExpr, gateCount]
  | add a b ha hb =>
      change (((compileExpr l b).run ((compileExpr l a).run gs).2).2 ++
        [ArithGate.add ((compileExpr l a).run gs).1
          ((compileExpr l b).run ((compileExpr l a).run gs).2).1]).length = _
      simp only [List.length_append, List.length_singleton, hb, ha, gateCount, Nat.add_assoc]
  | mul a b ha hb =>
      change (((compileExpr l b).run ((compileExpr l a).run gs).2).2 ++
        [ArithGate.mul ((compileExpr l a).run gs).1
          ((compileExpr l b).run ((compileExpr l a).run gs).2).1]).length = _
      simp only [List.length_append, List.length_singleton, hb, ha, gateCount, Nat.add_assoc]
  | square a ha =>
      change (((compileExpr l a).run gs).2 ++
        [ArithGate.mul ((compileExpr l a).run gs).1 ((compileExpr l a).run gs).1]).length = _
      simp only [List.length_append, List.length_singleton, ha, gateCount, Nat.add_assoc]

theorem patternStep_length {m : ℕ} (ids : List ℕ) (p : Pattern m) (one : ℕ)
    (a : Fin m) (acc : ℕ) (gs : Gates F) :
    ((patternStep ids p one a acc).run gs).2.length = gs.length + patternCost p a := by
  cases hp : p a with
  | none =>
      simp only [patternStep, patternCost, hp]
      rfl
  | some b =>
      cases b with
      | false =>
          simp only [patternStep, patternCost, hp]
          change ((gs ++ [ArithGate.add one (ids.getD a.val one)]) ++
            [ArithGate.mul acc gs.length]).length = gs.length + 2
          simp
      | true =>
          simp only [patternStep, patternCost, hp]
          change (gs ++ [ArithGate.mul acc (ids.getD a.val one)]).length = gs.length + 1
          simp

theorem patternLoop_length {m : ℕ} (ids : List ℕ) (p : Pattern m) (one : ℕ)
    (as : List (Fin m)) (acc : ℕ) (gs : Gates F) :
    ((loop (patternStep ids p one) as acc).run gs).2.length =
      gs.length + (as.map (patternCost p)).sum := by
  induction as generalizing acc gs with
  | nil => rfl
  | cons a as ih =>
      change ((loop (patternStep ids p one) as ((patternStep ids p one a acc).run gs).1).run
        ((patternStep ids p one a acc).run gs).2).2.length = _
      rw [ih, patternStep_length]
      simp only [List.map_cons, List.sum_cons, Nat.add_assoc]

variable [Field F]

theorem compilePattern_length {m : ℕ} (ids : List ℕ) (p : Pattern m) (gs : Gates F) :
    ((compilePattern ids p).run gs).2.length =
      gs.length + (1 + ((List.finRange m).map (patternCost p)).sum) := by
  rw [compilePattern_eq]
  change ((loop (patternStep ids p gs.length) (List.finRange m) gs.length).run
    (gs ++ [ArithGate.const (1 : F)])).2.length = _
  rw [patternLoop_length]
  simp only [List.length_append, List.length_singleton, Nat.add_assoc]

theorem termStep_length (l : Layout) (ids : List ℕ) (item : Item l.m F) (acc : ℕ) (gs : Gates F) :
    ((termStep l ids item acc).run gs).2.length = gs.length + itemCost item := by
  let rp := (compilePattern ids item.1).run gs
  let re := (compileExpr l item.2).run rp.2
  have hp : rp.2.length = gs.length + (1 + ((List.finRange l.m).map (patternCost item.1)).sum) :=
    compilePattern_length ids item.1 gs
  have he : re.2.length = rp.2.length + gateCount item.2 := compileExpr_length l item.2 rp.2
  change ((re.2 ++ [ArithGate.mul rp.1 re.1]) ++ [ArithGate.add acc re.2.length]).length = _
  simp only [List.length_append, List.length_singleton, he, hp, itemCost]
  omega

theorem termLoop_length (l : Layout) (ids : List ℕ) (items : List (Item l.m F))
    (acc : ℕ) (gs : Gates F) :
    ((loop (termStep l ids) items acc).run gs).2.length = gs.length + (items.map itemCost).sum := by
  induction items generalizing acc gs with
  | nil => rfl
  | cons item items ih =>
      change ((loop (termStep l ids) items ((termStep l ids item acc).run gs).1).run
        ((termStep l ids item acc).run gs).2).2.length = _
      rw [ih, termStep_length]
      simp only [List.map_cons, List.sum_cons, Nat.add_assoc]

theorem compileTerms_length (l : Layout) (e : Fin l.m → F) (coords : Coordinates l.m e)
    (items : List (Item l.m F)) :
    (compileTerms l e coords items).gates.length =
      3 * l.m ^ 2 + 2 * l.m + 1 + (items.map itemCost).sum := by
  let cr := (compileCoordinates coords).run ([] : Gates F)
  have hc : cr.2.length = 3 * l.m ^ 2 + 2 * l.m := by
    simpa only [List.length_nil, zero_add] using
      (compileCoordinates_spec l coords [] (by intro i; exact Fin.elim0 i)).2.2
  change ((loop (termStep l cr.1) items cr.2.length).run (cr.2 ++ [ArithGate.const (0 : F)])).2.length = _
  rw [termLoop_length]
  simp only [List.length_append, List.length_singleton, hc]

theorem compileTerms_size (l : Layout) (e : Fin l.m → F) (coords : Coordinates l.m e)
    (items : List (Item l.m F)) :
    (compileTerms l e coords items).size =
      3 * l.m ^ 2 + 2 * l.m + 1 + (items.map itemCost).sum :=
  compileTerms_length l e coords items


end NearCubicGates.Adapters.Routing.Circuit.Encoding
