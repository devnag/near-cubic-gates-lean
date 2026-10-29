import SourceAdapters.Routing.CircuitCoordinates

/-! The construction in `lem:generator`: the exact ordered coordinate-prefix gate list. -/
set_option autoImplicit false
noncomputable section

namespace NearCubicGates.Adapters.Routing.Circuit.PrefixFormula

open NearCubicGates.Adapters.ACSP
variable {F : Type}

theorem bind_run {α β : Type} (u : Builder F α) (v : α → Builder F β) (gs : Gates F) :
    (u >>= v).run gs = (v (u.run gs).1).run (u.run gs).2 := rfl

theorem push_run (g : ArithGate F) (gs : Gates F) :
    (pushGate g).run gs = (gs.length, gs ++ [g]) := rfl

theorem loop_append_run {α β : Type} (f : α → β → Builder F β)
    (as bs : List α) (b : β) (gs : Gates F) :
    (loop f (as ++ bs) b).run gs =
      (loop f bs ((loop f as b).run gs).1).run ((loop f as b).run gs).2 := by
  induction as generalizing b gs with
  | nil => rfl
  | cons a as ih =>
      exact ih ((f a b).run gs).1 ((f a b).run gs).2

theorem loop_snoc_run {α β : Type} (f : α → β → Builder F β)
    (as : List α) (a : α) (b : β) (gs : Gates F) :
    (loop f (as ++ [a]) b).run gs =
      (f a ((loop f as b).run gs).1).run ((loop f as b).run gs).2 := by
  rw [loop_append_run]
  rfl

def squareGates (s k : ℕ) : Gates F :=
  (List.range k).map fun r => ArithGate.mul (R := F) (s + r) (s + r)

def powerIds (s k : ℕ) : List ℕ := (List.range (k + 1)).map (s + ·)

theorem powerIds_last (s k d : ℕ) : (powerIds s k).getLastD d = s + k := by
  simp [powerIds, List.range_succ]

theorem powers_exact (gs : Gates F) (k : ℕ) :
    (loop (powerStep gs.length) (List.range k) [gs.length]).run (gs ++ [ArithGate.input (R := F) 0]) =
      (powerIds gs.length k, gs ++ [ArithGate.input (R := F) 0] ++ squareGates gs.length k) := by
  induction k with
  | zero => simp [loop, powerIds, squareGates, StateT.run, pure, StateT.pure]
  | succ k ih =>
      rw [List.range_succ, loop_snoc_run, ih]
      change (powerIds gs.length k ++ [(gs ++ [ArithGate.input (R := F) 0] ++ squareGates gs.length k).length],
        (gs ++ [ArithGate.input (R := F) 0] ++ squareGates gs.length k) ++
          [ArithGate.mul (R := F) ((powerIds gs.length k).getLastD gs.length)
            ((powerIds gs.length k).getLastD gs.length)]) = _
      rw [powerIds_last]
      simp [powerIds, squareGates, List.range_succ, List.append_assoc, Nat.add_assoc]


def coefficientGates {α : Type} (coeff : α → F) (index : α → ℕ)
    (b : ℕ) (rs : List α) : Gates F :=
  rs.zipIdx.flatMap fun (r,j) =>
    [ArithGate.const (coeff r), ArithGate.mul (R := F) (b + 1 + 3*j) (index r), ArithGate.add (R := F) (b + 3*j) (b + 2 + 3*j)]

theorem coefficientGates_length {α : Type} (coeff : α → F) (index : α → ℕ)
    (b : ℕ) (rs : List α) : (coefficientGates coeff index b rs).length = 3 * rs.length := by
  simp [coefficientGates, List.length_flatMap, Nat.mul_comm]

theorem coefficientGates_snoc {α : Type} (coeff : α → F) (index : α → ℕ)
    (b : ℕ) (rs : List α) (r : α) :
    coefficientGates coeff index b (rs ++ [r]) = coefficientGates coeff index b rs ++
      [ArithGate.const (coeff r), ArithGate.mul (R := F) (b + 1 + 3*rs.length) (index r),
        ArithGate.add (R := F) (b + 3*rs.length) (b + 2 + 3*rs.length)] := by
  simp [coefficientGates, List.zipIdx_append]

theorem coefficients_exact {α : Type} (coeff : α → F) (index : α → ℕ)
    (rs : List α) (b : ℕ) (gs : Gates F) (hl : gs.length = b + 1) :
    (loop (coeffStep coeff index) rs b).run gs =
      (b + 3*rs.length, gs ++ coefficientGates coeff index b rs) := by
  induction rs using List.reverseRecOn with
  | nil => simp [loop, coefficientGates, StateT.run, pure, StateT.pure]
  | append_singleton rs r ih =>
      rw [loop_snoc_run, ih]
      change (((gs ++ coefficientGates coeff index b rs ++ [ArithGate.const (coeff r)]) ++
          [ArithGate.mul (R := F) (gs ++ coefficientGates coeff index b rs).length (index r)]).length,
        ((gs ++ coefficientGates coeff index b rs) ++ [ArithGate.const (coeff r)]) ++
          [ArithGate.mul (R := F) (gs ++ coefficientGates coeff index b rs).length (index r)] ++
          [ArithGate.add (R := F) (b + 3*rs.length) (gs ++ coefficientGates coeff index b rs ++ [ArithGate.const (coeff r)]).length]) = _
      simp [coefficientGates_snoc, coefficientGates_length, hl, List.append_assoc,
        Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
      omega


theorem zipIdx_finRange (m : ℕ) : (List.finRange m).zipIdx =
    (List.finRange m).map (fun r => (r, r.val)) := by
  apply List.ext_getElem
  · simp
  · intro i hi hi'
    simp

variable [Field F]

def rowGates {m : ℕ} (coeff : Fin m → F) (s b : ℕ) : Gates F :=
  [ArithGate.const 0] ++ (List.finRange m).flatMap fun r =>
    [ArithGate.const (coeff r), ArithGate.mul (b+1+3*r.val) (s+r.val),
      ArithGate.add (b+3*r.val) (b+2+3*r.val)]

theorem rowGates_eq {m : ℕ} (coeff : Fin m → F) (s b : ℕ) :
    rowGates coeff s b = [ArithGate.const 0] ++
      coefficientGates coeff (fun r => s+r.val) b (List.finRange m) := by
  simp [rowGates, coefficientGates, zipIdx_finRange, List.flatMap_map]

theorem rowGates_length {m : ℕ} (coeff : Fin m → F) (s b : ℕ) :
    (rowGates coeff s b).length = 3*m+1 := by
  simp [rowGates_eq, coefficientGates_length, Nat.add_comm]

theorem coordinateRow_exact (l : Layout) {e : Fin l.m → F} (coords : Coordinates l.m e)
    (ps : List ℕ) (x s : ℕ) (a : Fin l.m) (gs : Gates F)
    (hp : ∀ r : Fin l.m, ps.getD r.val x = s+r.val) :
    (coordinateRow l coords ps x a).run gs =
      (gs.length+3*l.m, gs ++ rowGates (coords.coeff a) s gs.length) := by
  have hp' : (fun r : Fin l.m => ps.getD r.val x) = (fun r => s+r.val) := funext hp
  change (loop (coeffStep (coords.coeff a) (fun r => ps.getD r.val x))
    (List.finRange l.m) gs.length).run (gs ++ [ArithGate.const 0]) = _
  rw [hp', coefficients_exact _ _ _ _ _ (by simp)]
  simp only [List.length_finRange, rowGates_eq, List.append_assoc]

def rowsGates (l : Layout) {e : Fin l.m → F} (coords : Coordinates l.m e)
    (s b : ℕ) (as : List (Fin l.m)) : Gates F :=
  as.zipIdx.flatMap fun (a,j) => rowGates (coords.coeff a) s (b+j*(3*l.m+1))

def rowIds (m b k : ℕ) : List ℕ := (List.range k).map fun j => b+j*(3*m+1)+3*m

theorem rowsGates_length (l : Layout) {e : Fin l.m → F} (coords : Coordinates l.m e)
    (s b : ℕ) (as : List (Fin l.m)) :
    (rowsGates l coords s b as).length = (3*l.m+1)*as.length := by
  simp [rowsGates, List.length_flatMap, rowGates_length, Nat.mul_comm]

theorem rowsGates_snoc (l : Layout) {e : Fin l.m → F} (coords : Coordinates l.m e)
    (s b : ℕ) (as : List (Fin l.m)) (a : Fin l.m) :
    rowsGates l coords s b (as ++ [a]) = rowsGates l coords s b as ++
      rowGates (coords.coeff a) s (b+as.length*(3*l.m+1)) := by
  simp [rowsGates, List.zipIdx_append]

theorem coordinateStep_run (l : Layout) {e : Fin l.m → F} (coords : Coordinates l.m e)
    (ps : List ℕ) (x : ℕ) (a : Fin l.m) (outputs : List ℕ) (gs : Gates F) :
    (coordinateStep l coords ps x a outputs).run gs =
      (outputs ++ [((coordinateRow l coords ps x a).run gs).1],
        ((coordinateRow l coords ps x a).run gs).2) := rfl

theorem rows_exact (l : Layout) {e : Fin l.m → F} (coords : Coordinates l.m e)
    (ps : List ℕ) (x s : ℕ) (as : List (Fin l.m)) (outputs : List ℕ) (gs : Gates F)
    (hp : ∀ r : Fin l.m, ps.getD r.val x = s+r.val) :
    (loop (coordinateStep l coords ps x) as outputs).run gs =
      (outputs ++ rowIds l.m gs.length as.length, gs ++ rowsGates l coords s gs.length as) := by
  induction as using List.reverseRecOn with
  | nil => simp [loop, rowIds, rowsGates, StateT.run, pure, StateT.pure]
  | append_singleton as a ih =>
      rw [loop_snoc_run, ih, coordinateStep_run, coordinateRow_exact l coords ps x s a _ hp]
      simp [rowIds, rowsGates_snoc, rowsGates_length, List.range_succ, List.append_assoc,
        Nat.mul_comm, Nat.add_assoc]


def prefixGates (l : Layout) {e : Fin l.m → F} (coords : Coordinates l.m e) (s : ℕ) : Gates F :=
  [ArithGate.input 0] ++ squareGates s (l.m - 1) ++
    (List.finRange l.m).flatMap fun a =>
      rowGates (coords.coeff a) s (s+l.m+a.val*(3*l.m+1))

/-- Exact appended list and returned coordinate references, after any prefix.
There is no well-formedness assumption on the preexisting prefix. -/
theorem compileCoordinates_exact (l : Layout) {e : Fin l.m → F} (coords : Coordinates l.m e)
    (gs : Gates F) :
    (compileCoordinates coords).run gs =
      (rowIds l.m (gs.length+l.m) l.m, gs ++ prefixGates l coords gs.length) := by
  have hm : 1 ≤ l.m := by simp only [Layout.m]; omega
  have hp : ∀ r : Fin l.m, (powerIds gs.length (l.m-1)).getD r.val gs.length = gs.length+r.val := by
    intro r
    have hm' : l.m-1+1=l.m := by omega
    simp [powerIds, hm', r.isLt]
  rw [compileCoordinates_eq l coords, bind_run, push_run, bind_run, powers_exact]
  rw [rows_exact l coords _ _ gs.length _ _ _ hp]
  have hlen : (gs ++ [ArithGate.input (R := F) 0] ++ squareGates gs.length (l.m-1)).length =
      gs.length+l.m := by
    simp only [List.length_append, List.length_singleton, squareGates, List.length_map, List.length_range]
    omega
  simp only [hlen, List.length_finRange, List.nil_append]
  simp [prefixGates, rowsGates, zipIdx_finRange, List.flatMap_map, List.append_assoc]

/-- The returned reference of row `a` is its final accumulation gate. -/
theorem compileCoordinates_ref (l : Layout) {e : Fin l.m → F} (coords : Coordinates l.m e)
    (gs : Gates F) (a d : ℕ) (ha : a < l.m) :
    ((compileCoordinates coords).run gs).1.getD a d =
      gs.length+l.m+a*(3*l.m+1)+3*l.m := by
  rw [compileCoordinates_exact]
  simp [rowIds, ha]

theorem previousAccumulator (b r : ℕ) : (if r=0 then b else b+3*r) = b+3*r := by
  split <;> simp_all


theorem prefixGates_length (l : Layout) {e : Fin l.m → F} (coords : Coordinates l.m e) (s : ℕ) :
    (prefixGates l coords s).length = 3*l.m^2+2*l.m := by
  have hm : 1 ≤ l.m := by simp only [Layout.m]; omega
  have hm' : l.m-1+1=l.m := by omega
  simp [prefixGates, squareGates, List.length_flatMap, rowGates_length]
  nlinarith

theorem compileCoordinates_length (l : Layout) {e : Fin l.m → F} (coords : Coordinates l.m e)
    (gs : Gates F) : ((compileCoordinates coords).run gs).2.length = gs.length+3*l.m^2+2*l.m := by
  rw [compileCoordinates_exact]
  simp [prefixGates_length, Nat.add_assoc]

end NearCubicGates.Adapters.Routing.Circuit.PrefixFormula
end
