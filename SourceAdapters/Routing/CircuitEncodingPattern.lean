import SourceAdapters.Routing.CircuitTerms

/-!
# Exact syntactic gate suffix of a compiled pattern

The construction in `lem:generator`: the guard printer writes the normalized
selector's actual gates. These equalities describe the compiler on arbitrary
patterns and reference lists; no read membership or circuit validity is assumed.
The fixed initial constant-one gate makes the prior accumulator cursor minus one,
including when every assignment is `none`. No paid-machine claim is made here.
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Routing.Circuit.Encoding

open NearCubicGates.Adapters.ACSP

variable {F : Type}

/-- The gates emitted at a single coordinate; `cursor` is the next free gate. -/
def patternBlock {m : ℕ} (ids : List ℕ) (p : Pattern m) (one cursor : ℕ) (a : Fin m) :
    List (ArithGate F) :=
  match p a with
  | none => []
  | some true => [.mul (cursor - 1) (ids.getD a.val one)]
  | some false => [.add one (ids.getD a.val one), .mul (cursor - 1) cursor]

/-- Explicit blocks, carrying the next free gate index through the coordinate list. -/
def patternBlocks {m : ℕ} (ids : List ℕ) (p : Pattern m) (one cursor : ℕ) :
    List (Fin m) → List (ArithGate F)
  | [] => []
  | a :: as => patternBlock ids p one cursor a ++
      patternBlocks ids p one (cursor + patternCost p a) as

theorem patternBlock_length {m : ℕ} (ids : List ℕ) (p : Pattern m) (one cursor : ℕ) (a : Fin m) :
    (patternBlock (F := F) ids p one cursor a).length = patternCost p a := by
  cases hp : p a with
  | none => simp [patternBlock, patternCost, hp]
  | some b => cases b <;> simp [patternBlock, patternCost, hp]

theorem patternBlocks_length {m : ℕ} (ids : List ℕ) (p : Pattern m) (one cursor : ℕ)
    (as : List (Fin m)) :
    (patternBlocks (F := F) ids p one cursor as).length = (as.map (patternCost p)).sum := by
  induction as generalizing cursor with
  | nil => rfl
  | cons a as ih => simp only [patternBlocks, List.length_append, patternBlock_length, ih,
      List.map_cons, List.sum_cons]

/-- Exact one-step state; the only premise is the cursor/accumulator arithmetic invariant. -/
theorem patternStep_run {m : ℕ} (ids : List ℕ) (p : Pattern m) (one : ℕ)
    (a : Fin m) (acc : ℕ) (gs : Gates F) (hlast : acc + 1 = gs.length) :
    (patternStep ids p one a acc).run gs =
      (gs.length + patternCost p a - 1, gs ++ patternBlock ids p one gs.length a) := by
  have ha : acc = gs.length - 1 := by omega
  cases hp : p a with
  | none =>
      simp only [patternStep, patternCost, patternBlock, hp]
      change (acc, gs) = (gs.length + 0 - 1, gs ++ [])
      simp [ha]
  | some b =>
      cases b with
      | false =>
          simp only [patternStep, patternCost, patternBlock, hp]
          change ((gs ++ [ArithGate.add one (ids.getD a.val one)]).length,
            (gs ++ [ArithGate.add one (ids.getD a.val one)]) ++
            [ArithGate.mul acc gs.length]) =
              (gs.length + 2 - 1, gs ++ [.add one (ids.getD a.val one), .mul (gs.length - 1) gs.length])
          simp [ha, List.append_assoc]
      | true =>
          simp only [patternStep, patternCost, patternBlock, hp]
          change (gs.length, gs ++ [ArithGate.mul acc (ids.getD a.val one)]) =
            (gs.length + 1 - 1, gs ++ [.mul (gs.length - 1) (ids.getD a.val one)])
          simp [ha]

theorem patternLoop_run {m : ℕ} (ids : List ℕ) (p : Pattern m) (one : ℕ)
    (as : List (Fin m)) (acc : ℕ) (gs : Gates F) (hlast : acc + 1 = gs.length) :
    (loop (patternStep ids p one) as acc).run gs =
      (gs.length + (as.map (patternCost p)).sum - 1, gs ++ patternBlocks ids p one gs.length as) := by
  induction as generalizing acc gs with
  | nil =>
      change (acc, gs) = (gs.length + 0 - 1, gs ++ [])
      have ha : acc = gs.length - 1 := by omega
      simp [ha]
  | cons a as ih =>
      let st := (patternStep ids p one a acc).run gs
      have hs : st = (gs.length + patternCost p a - 1, gs ++ patternBlock ids p one gs.length a) :=
        patternStep_run ids p one a acc gs hlast
      have hsl : st.2.length = gs.length + patternCost p a := by
        rw [hs]
        simp only [List.length_append, patternBlock_length]
      have hlast' : st.1 + 1 = st.2.length := by rw [hsl, hs]; simp only; omega
      change (loop (patternStep ids p one) as st.1).run st.2 = _
      rw [ih st.1 st.2 hlast', hsl, hs]
      simp only [patternBlocks, List.map_cons, List.sum_cons, Nat.add_assoc, List.append_assoc]

variable [Field F]

/-- The whole suffix includes its initial constant-one gate at position `start`. -/
def patternGates {m : ℕ} (ids : List ℕ) (p : Pattern m) (start : ℕ) : List (ArithGate F) :=
  .const 1 :: patternBlocks ids p start (start + 1) (List.finRange m)

theorem patternGates_length {m : ℕ} (ids : List ℕ) (p : Pattern m) (start : ℕ) :
    (patternGates (F := F) ids p start).length = 1 + ((List.finRange m).map (patternCost p)).sum := by
  simp only [patternGates, List.length_cons, patternBlocks_length, Nat.add_comm]

/-- Exact final index and appended gates, without any validity premise. -/
theorem compilePattern_run {m : ℕ} (ids : List ℕ) (p : Pattern m) (gs : Gates F) :
    (compilePattern ids p).run gs =
      (gs.length + ((List.finRange m).map (patternCost p)).sum, gs ++ patternGates ids p gs.length) := by
  rw [compilePattern_eq]
  change (loop (patternStep ids p gs.length) (List.finRange m) gs.length).run
    (gs ++ [ArithGate.const (1 : F)]) = _
  rw [patternLoop_run ids p gs.length _ _ _ (by simp)]
  simp only [List.length_append, List.length_singleton, patternGates, List.append_assoc, List.singleton_append]
  congr 1
  omega

/-- Serialization may traverse the explicit suffix directly. -/
theorem compilePattern_gateWords {m : ℕ} (ids : List ℕ) (p : Pattern m) (gs : Gates F)
    (word : ArithGate F → List Bool) :
    ((compilePattern ids p).run gs).2.flatMap word =
      gs.flatMap word ++ (patternGates ids p gs.length).flatMap word := by
  rw [compilePattern_run]
  exact List.flatMap_append


end NearCubicGates.Adapters.Routing.Circuit.Encoding
