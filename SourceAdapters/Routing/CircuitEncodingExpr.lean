import SourceAdapters.Routing.CircuitTerms

/-! Exact gate suffix of expression compilation. See `lem:generator`. -/
set_option autoImplicit false

namespace NearCubicGates.Adapters.Routing.Circuit.Encoding
open NearCubicGates.Adapters.ACSP

variable {F : Type}

def expressionGates (l : Layout) (s : ℕ) : Expr F → List (ArithGate F)
  | .const c => [.const c]
  | .read v => [.input (readIndex l v)]
  | .add a b =>
      expressionGates l s a ++ expressionGates l (s + gateCount a) b ++
        [.add (s + gateCount a - 1) (s + gateCount a + gateCount b - 1)]
  | .mul a b =>
      expressionGates l s a ++ expressionGates l (s + gateCount a) b ++
        [.mul (s + gateCount a - 1) (s + gateCount a + gateCount b - 1)]
  | .square a =>
      expressionGates l s a ++ [.mul (s + gateCount a - 1) (s + gateCount a - 1)]

theorem expressionGates_length (l : Layout) (s : ℕ) (e : Expr F) :
    (expressionGates l s e).length = gateCount e := by
  induction e generalizing s with
  | const c => rfl
  | read v => rfl
  | add a b ha hb => simp [expressionGates, gateCount, ha, hb, Nat.add_assoc]
  | mul a b ha hb => simp [expressionGates, gateCount, ha, hb, Nat.add_assoc]
  | square a ha => simp [expressionGates, gateCount, ha]

theorem compileExpr_run (l : Layout) (e : Expr F) (gs : List (ArithGate F)) :
    (compileExpr l e).run gs =
      (gs.length + gateCount e - 1, gs ++ expressionGates l gs.length e) := by
  induction e generalizing gs with
  | const c =>
      change (gs.length, gs ++ [_]) = _
      simp [expressionGates, gateCount]
  | read v =>
      change (gs.length, gs ++ [_]) = _
      simp [expressionGates, gateCount]
  | add a b ha hb =>
      change (let ra := (compileExpr l a).run gs
        let rb := (compileExpr l b).run ra.2
        (rb.2.length, rb.2 ++ [ArithGate.add ra.1 rb.1])) = _
      simp only [ha, hb]
      simp [expressionGates, gateCount, expressionGates_length, List.append_assoc, Nat.add_assoc]
      omega
  | mul a b ha hb =>
      change (let ra := (compileExpr l a).run gs
        let rb := (compileExpr l b).run ra.2
        (rb.2.length, rb.2 ++ [ArithGate.mul ra.1 rb.1])) = _
      simp only [ha, hb]
      simp [expressionGates, gateCount, expressionGates_length, List.append_assoc, Nat.add_assoc]
      omega
  | square a ha =>
      change (let ra := (compileExpr l a).run gs
        (ra.2.length, ra.2 ++ [ArithGate.mul ra.1 ra.1])) = _
      simp only [ha]
      simp [expressionGates, gateCount, expressionGates_length]

theorem compileExpr_gateWords (l : Layout) (e : Expr F) (gs : List (ArithGate F))
    (word : ArithGate F → List Bool) :
    (((compileExpr l e).run gs).2.flatMap word) =
      gs.flatMap word ++ (expressionGates l gs.length e).flatMap word := by
  rw [compileExpr_run]
  exact List.flatMap_append

def mapExpression {K : Type} (f : F → K) : Expr F → Expr K
  | .const c => .const (f c)
  | .read v => .read v
  | .add a b => .add (mapExpression f a) (mapExpression f b)
  | .mul a b => .mul (mapExpression f a) (mapExpression f b)
  | .square a => .square (mapExpression f a)

def mapGate {K : Type} (f : F → K) : ArithGate F → ArithGate K
  | .const c => .const (f c)
  | .input i => .input i
  | .add i j => .add i j
  | .mul i j => .mul i j

theorem gateCount_mapExpression {K : Type} (f : F → K) (e : Expr F) :
    gateCount (mapExpression f e) = gateCount e := by
  induction e with
  | const c => rfl
  | read v => rfl
  | add a b ha hb => simp [mapExpression, gateCount, ha, hb]
  | mul a b ha hb => simp [mapExpression, gateCount, ha, hb]
  | square a ha => simp [mapExpression, gateCount, ha]

theorem expressionGates_map {K : Type} (f : F → K) (l : Layout) (s : ℕ) (e : Expr F) :
    expressionGates l s (mapExpression f e) = (expressionGates l s e).map (mapGate f) := by
  induction e generalizing s with
  | const c => rfl
  | read v => rfl
  | add a b ha hb =>
      simp [mapExpression, expressionGates, gateCount_mapExpression, ha, hb, mapGate]
  | mul a b ha hb =>
      simp [mapExpression, expressionGates, gateCount_mapExpression, ha, hb, mapGate]
  | square a ha => simp [mapExpression, expressionGates, gateCount_mapExpression, ha, mapGate]

theorem compileExpr_map {K : Type} (f : F → K) (l : Layout) (e : Expr F)
    (gs : List (ArithGate F)) :
    (compileExpr l (mapExpression f e)).run (gs.map (mapGate f)) =
      (((compileExpr l e).run gs).1, ((compileExpr l e).run gs).2.map (mapGate f)) := by
  simp only [compileExpr_run, List.length_map, gateCount_mapExpression, expressionGates_map,
    List.map_append]


end NearCubicGates.Adapters.Routing.Circuit.Encoding
