import Proof.Wire_3_5.CompilerMachinePoolFlips

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.CompilerMachine.Pool
open NearCubicWires NearCubicWires.WireExponent3_5.CompilerMachine NearCubicWires.WireExponent3_5.CompilerMachine.Unions
open NearCubicWires.WireExponent3_5.CompilerMachine.Masks
open NearCubicWires.WireExponent3_5.Block
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)

/-- Outside the mask the bit is kept; inside it the previous bit comes out. -/
def shOut (a b old : Bool) : Bool := if b then old else a

/-- The carried bit: the current bit inside the mask, `false` outside. -/
def shNxt (a b _old : Bool) : Bool := if b then a else false

/-- The constant mask of an entry: `Q + 1` kept cells, then `W` shifted cells. -/
def shiftMask (Q W : ℕ) : List Bool := List.replicate (Q + 1) false ++ List.replicate W true

theorem map_keep : ∀ (p r1 r2 : List Bool), ZipMap.map shOut shNxt (p ++ r1) (List.replicate p.length false ++ r2) false =
    p ++ ZipMap.map shOut shNxt r1 r2 false
  | [], _, _ => rfl
  | a :: p, r1, r2 => by
    simp only [List.cons_append, List.length_cons, List.replicate_succ, ZipMap.map, shOut, shNxt, if_false,
      Bool.false_eq_true]
    rw [map_keep p r1 r2]

theorem map_shift : ∀ (l : List Bool) (c : Bool), ZipMap.map shOut shNxt l (List.replicate l.length true) c =
    (c :: l).take l.length
  | [], _ => rfl
  | a :: l, c => by
    simp only [List.length_cons, List.replicate_succ, ZipMap.map, shOut, shNxt, if_true]
    rw [map_shift l a]
    simp

theorem binary_double : ∀ (k y : ℕ), binary (k + 1) (2 * y) = false :: binary k y
  | k, y => by
    simp only [binary]
    have h1 : (2 * y % 2 == 1) = false := by simp
    have h2 : 2 * y / 2 = y := by omega
    rw [h1, h2]

theorem take_binary : ∀ (k y : ℕ), (binary (k + 1) y).take k = binary k y
  | 0, _ => rfl
  | k + 1, y => by
    show ((y % 2 == 1) :: binary (k + 1) (y / 2)).take (k + 1) = (y % 2 == 1) :: binary k (y / 2)
    rw [List.take_succ_cons, take_binary k (y / 2)]

/-- **The next label's entry**: shifting the mask bits of `ew Q W (0, y)` gives `ew Q W (0, 2y)`. -/
theorem shift_entry (Q W y : ℕ) :
    ZipMap.map shOut shNxt (entryWord Q W 0 y) (shiftMask Q W) false = entryWord Q W 0 (2 * y) := by
  unfold entryWord shiftMask thermo
  simp only [List.replicate_zero, List.nil_append, Nat.sub_zero]
  have e1 : List.replicate Q false ++ true :: binary W y = (List.replicate Q false ++ [true]) ++ binary W y := by simp
  have e2 : List.replicate (Q + 1) false = List.replicate (List.replicate Q false ++ [true]).length false := by simp
  rw [e1, e2, map_keep]
  have e3 : List.replicate W true = List.replicate (binary W y).length true := by simp
  rw [e3, map_shift]
  cases W with
  | zero => simp [binary]
  | succ k =>
    rw [binary_double, binary_length, List.take_succ_cons, take_binary]
    simp

/-! ## The children table from the per-atom counts -/

/-- The atom streams of consecutive labels: `v` labels per atom, starting at label `c0`. -/
def tableOf {β : Type} (ent : ℕ → β) : ℕ → List ℕ → List (List β)
  | _, [] => []
  | c0, v :: vs => ((List.range' c0 v).map ent) :: tableOf ent (c0 + v) vs

theorem tableOf_aux {β : Type} (ent : ℕ → β) : ∀ (ls : List ℕ) (c0 : ℕ),
    (List.range ls.length).map (fun a => (List.range' (c0 + (ls.take a).sum) (ls.getD a 0)).map ent) =
      tableOf ent c0 ls
  | [], _ => rfl
  | v :: ls, c0 => by
    rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map]
    simp only [List.take_zero, List.sum_nil, Nat.add_zero, List.getD_cons_zero, tableOf]
    congr 1
    rw [← tableOf_aux ent ls (c0 + v)]
    apply List.map_congr_left
    intro a _
    simp only [Function.comp, List.take_succ_cons, List.sum_cons, List.getD_cons_succ, Nat.add_assoc]

/-- **The children table is the consecutive-label table of the atoms' child counts.** -/
theorem childTable_eq (Q : ℕ) (pool : List (List SynEq)) :
    childTable Q pool = tableOf (fun c => ew Q pool.flatten.length (0, 2 ^ c)) 0 (pool.map List.length) := by
  rw [← tableOf_aux]
  unfold childTable labelsOf
  rw [List.length_map]
  apply List.map_congr_left
  intro a ha
  have ha' := List.mem_range.mp ha
  rw [Nat.zero_add, ← List.map_take, List.getD_eq_getElem _ _ ha',
    List.getD_eq_getElem _ _ (by simpa using ha')]
  simp

end NearCubicWires.WireExponent3_5.CompilerMachine.Pool
