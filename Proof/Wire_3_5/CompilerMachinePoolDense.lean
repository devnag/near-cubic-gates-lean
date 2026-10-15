import Proof.Wire_3_5.CompilerMachinePoolCoord

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.CompilerMachine.Pool
open NearCubicWires NearCubicWires.RepairRepresentation NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)

/-- A signed field's two words. -/
def pnWords (h : ℕ) (z : ℤ) : List (List Bool) := [binary h (pn z).1, binary h (pn z).2]

theorem pn_flip (f : Bool) (w : ℤ) : pn (flipW f w) = if f then ((pn w).2, (pn w).1) else pn w := by
  cases f <;> simp [flipW, pn]

/-- A coordinate's pair as the pass writes it is the framed words of its flipped weight. -/
theorem pairF_eq (h : ℕ) (f : Bool) (w : ℤ) : pairF h f (pn w) = (pnWords h (flipW f w)).flatMap frame := by
  cases f <;> simp [pairF, pnWords, flipW, pn]

/-- The left part the pass writes. -/
def leftPart (h : ℕ) (cs : List Coord) : List Bool := (cs.filter fun c => c.1).flatMap fun c => pairF h c.2.1 (pn c.2.2)

/-- The right part the pass writes. -/
def rightPart (h : ℕ) (cs : List Coord) : List Bool :=
  (cs.filter fun c => !c.1).flatMap fun c => pairF h c.2.1 (pn c.2.2)

/-- The target's accumulated P part: the flipped weights' N parts, then the target's P part. -/
def targetP (cs : List Coord) (t : ℤ) : ℕ := (cs.map fun c => if c.2.1 then (pn c.2.2).2 else 0).sum + (pn t).1

/-- The target's accumulated N part. -/
def targetN (cs : List Coord) (t : ℤ) : ℕ := (cs.map fun c => if c.2.1 then (pn c.2.2).1 else 0).sum + (pn t).2

theorem flat_pairs (h : ℕ) : ∀ l : List Coord, l.flatMap (fun c => pairF h c.2.1 (pn c.2.2)) =
    ((l.map fun c => flipW c.2.1 c.2.2).flatMap (pnWords h)).flatMap frame
  | [] => rfl
  | c :: l => by
    rw [List.flatMap_cons, flat_pairs h l, List.map_cons, List.flatMap_cons, List.flatMap_append, pairF_eq]

theorem leftPart_eq (h : ℕ) (cs : List Coord) : leftPart h cs = ((routeL cs).flatMap (pnWords h)).flatMap frame :=
  flat_pairs h _

theorem rightPart_eq (h : ℕ) (cs : List Coord) : rightPart h cs = ((routeR cs).flatMap (pnWords h)).flatMap frame :=
  flat_pairs h _

theorem splitTarget_eq (cs : List Coord) (t : ℤ) : splitTarget cs t = (targetP cs t, targetN cs t) := by
  unfold splitTarget targetP targetN pn
  have e1 : ∀ c : Coord, (if c.2.1 then ((c.2.2).toNat, (-c.2.2).toNat).2 else 0) =
      (if c.2.1 then (-c.2.2).toNat else 0) := fun c => by split_ifs <;> rfl
  have e2 : ∀ c : Coord, (if c.2.1 then ((c.2.2).toNat, (-c.2.2).toNat).1 else 0) =
      (if c.2.1 then (c.2.2).toNat else 0) := fun c => by split_ifs <;> rfl
  simp only [e1, e2]
  ext <;> simp <;> omega

theorem range_split (w : ℕ) : List.range (w + w + 1) = List.range w ++ (List.range w).map (w + ·) ++ [w + w] := by
  rw [List.range_succ, List.range_add]

theorem range_flatMap_getD {β : Type} (g : ℤ → List β) : ∀ X : List ℤ,
    (List.range X.length).flatMap (fun p => g (X.getD p 0)) = X.flatMap g
  | [] => rfl
  | x :: X => by
    rw [List.length_cons, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
    simp only [List.getD_cons_zero, List.getD_cons_succ]
    rw [range_flatMap_getD g X, List.flatMap_cons]

/-- The words of a padded list of fields: the list's words, then zero pairs up to the width. -/
theorem padded_words (h w : ℕ) (L M : List ℤ) (hL : L.length ≤ w) :
    (List.range w).flatMap (fun p => pnWords h ((padTo w L ++ M).getD p 0)) =
      L.flatMap (pnWords h) ++ (List.replicate (w - L.length) (pnWords h 0)).flatten := by
  have hP : (padTo w L).length = w := padTo_length w L hL
  have e : ∀ p ∈ List.range w, pnWords h ((padTo w L ++ M).getD p 0) = pnWords h ((padTo w L).getD p 0) := by
    intro p hp
    rw [List.getD_append _ _ _ _ (by rw [hP]; exact List.mem_range.mp hp)]
  rw [List.flatMap_congr e]
  have e2 := range_flatMap_getD (pnWords h) (padTo w L)
  rw [hP] at e2
  rw [e2]
  simp [padTo, List.flatMap_append, List.flatMap_replicate]

/-- The zero pairs up to the width, framed. -/
def zeroPart (h k : ℕ) : List Bool := ((List.replicate k (pnWords h 0)).flatten).flatMap frame

/-- The dense child's records in the five parts the pass writes. -/
theorem denseRecs_eq (h : ℕ) {n : ℕ} (side f : List Bool) (width : ℕ) (e : ExactThresholdGate n)
    (hL : (routeL (coords side f e)).length ≤ width) (hR : (routeR (coords side f e)).length ≤ width) :
    denseRecs h side f width e = ((routeL (coords side f e)).flatMap (pnWords h) ++
      (List.replicate (width - (routeL (coords side f e)).length) (pnWords h 0)).flatten) ++
      ((routeR (coords side f e)).flatMap (pnWords h) ++
        (List.replicate (width - (routeR (coords side f e)).length) (pnWords h 0)).flatten) ++
      [binary h (targetP (coords side f e) e.target), binary h (targetN (coords side f e) e.target)] := by
  set cs := coords side f e
  have hfw : ∀ p, p < width + width →
      [binary h (fieldPN side f width e p).1, binary h (fieldPN side f width e p).2] =
        pnWords h ((denseWeights side f width e).getD p 0) := by
    intro p hp; simp [fieldPN, hp, pnWords]
  have hPL : (padTo width (routeL cs)).length = width := padTo_length width _ hL
  have p1 : (List.range width).flatMap (fun p => [binary h (fieldPN side f width e p).1,
      binary h (fieldPN side f width e p).2]) =
      (routeL cs).flatMap (pnWords h) ++ (List.replicate (width - (routeL cs).length) (pnWords h 0)).flatten := by
    rw [List.flatMap_congr (fun p hp => hfw p (by have := List.mem_range.mp hp; omega))]
    exact padded_words h width (routeL cs) (padTo width (routeR cs)) hL
  have p2 : ((List.range width).map (width + ·)).flatMap (fun p => [binary h (fieldPN side f width e p).1,
      binary h (fieldPN side f width e p).2]) =
      (routeR cs).flatMap (pnWords h) ++ (List.replicate (width - (routeR cs).length) (pnWords h 0)).flatten := by
    rw [List.flatMap_map]
    have e1 : ∀ q ∈ List.range width, [binary h (fieldPN side f width e (width + q)).1,
        binary h (fieldPN side f width e (width + q)).2] = pnWords h ((padTo width (routeR cs) ++ []).getD q 0) := by
      intro q hq
      have hq' := List.mem_range.mp hq
      rw [hfw (width + q) (by omega)]
      unfold denseWeights
      rw [List.getD_append_right _ _ _ _ (by rw [hPL]; omega), hPL, Nat.add_sub_cancel_left, List.append_nil]
    rw [List.flatMap_congr e1]
    exact padded_words h width (routeR cs) [] hR
  have p3 : [width + width].flatMap (fun p => [binary h (fieldPN side f width e p).1,
      binary h (fieldPN side f width e p).2]) = [binary h (targetP cs e.target), binary h (targetN cs e.target)] := by
    simp [fieldPN, splitTarget_eq, cs]
  have hd : denseRecs h side f width e = ((routeL cs).flatMap (pnWords h) ++
      (List.replicate (width - (routeL cs).length) (pnWords h 0)).flatten) ++
      ((routeR cs).flatMap (pnWords h) ++ (List.replicate (width - (routeR cs).length) (pnWords h 0)).flatten) ++
      [binary h (targetP cs e.target), binary h (targetN cs e.target)] := by
    unfold denseRecs
    rw [range_split, List.flatMap_append, List.flatMap_append, p1, p2, p3]
  exact hd

theorem dense_parts (h : ℕ) {n : ℕ} (side f : List Bool) (width : ℕ) (e : ExactThresholdGate n)
    (hL : (routeL (coords side f e)).length ≤ width) (hR : (routeR (coords side f e)).length ≤ width) :
    (denseRecs h side f width e).flatMap frame =
      leftPart h (coords side f e) ++ zeroPart h (width - (routeL (coords side f e)).length) ++
        rightPart h (coords side f e) ++ zeroPart h (width - (routeR (coords side f e)).length) ++
        frame (binary h (targetP (coords side f e) e.target)) ++ frame (binary h (targetN (coords side f e) e.target)) := by
  rw [denseRecs_eq h side f width e hL hR]
  simp only [List.flatMap_append, leftPart_eq, rightPart_eq, zeroPart, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, List.append_assoc]

end NearCubicWires.WireExponent3_5.CompilerMachine.Pool
