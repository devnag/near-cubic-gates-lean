import SourceAdapters.RAMACSP.GenSizeEq
import SourceAdapters.RAMACSP.ConstraintEmit

/-!
# Sizes of the emitted terms (for `lem:generator`)

Paper: `lem:generator`. The number of normalized guards is polynomial in
the layout dimensions; each pattern fixes at most mH coordinates, and the
equation templates are counted at their active bit indices.

Every item of `ownItems` (routing items, then the machine catalog) has an equation of at most
`itemBound = 30 L + m² + 4m + 70` gates (`L` code length, `m = mH`; `ownItems_gateCount_le`), and there are at most
`itemCount` items (`ownItems_length_le`), a polynomial in `w, τ, k, q, K, L`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

noncomputable section

namespace NearCubicGates.Adapters.RAMACSP.Gen

open NearCubicGates.Adapters NearCubicGates.Adapters.ACSP NearCubicGates.Adapters.RAMTrace
open NearCubicGates.Adapters.ShortPCP

section Items

variable {F : Type} [Field F] [CharP F 2]

/-- The per-item gate bound. -/
def itemBound (Lc m : ℕ) : ℕ := 30 * Lc + m * m + 4 * m + 70

theorem routing_gateCount_le (l : Routing.Layout) :
    ∀ x ∈ (routingPairs l : List (Routing.Pattern l.m × Routing.Expr F)), Routing.Circuit.gateCount x.2 ≤ 9 := by
  intro x hx
  simp only [routingPairs, List.mem_map] at hx
  obtain ⟨t, -, rfl⟩ := hx
  cases t <;> simp [Routing.RoutingItem.expr, Routing.Circuit.gateCount]

theorem machine_gateCount_le (l : Routing.Layout) (om K L : ℕ) (M : Ram) (kind : Fin M.ops → AluOp) (τ a : ℕ)
    (lam : ℕ → Routing.Expr F) (hlam : ∀ j, Routing.Circuit.gateCount (lam j) ≤ l.m * l.m + 4 * l.m + 1) :
    ∀ x ∈ machineItems l om K L M kind τ a lam, Routing.Circuit.gateCount x.2 ≤ itemBound M.code.length l.m := by
  intro x hx
  have hT := fun q => timeEq_size_le M kind τ q
  have hS := fun q => sortEq_size_le (dims M τ) q
  have hO := outE_size_le M
  have hA := accE_size_le M
  unfold itemBound
  simp only [machineItems, List.mem_append, List.mem_map, List.mem_flatMap, List.mem_cons] at hx
  rcases hx with ((((((h1 | h2) | h3) | h4) | h5) | h6) | h7) | h8
  · obtain ⟨q, -, rfl⟩ := h1; simp only [gateCount_toRouting]; have := hT q; omega
  · obtain ⟨s, -, rfl⟩ := h2; simp [boolExpr, Routing.Circuit.gateCount]
  · obtain ⟨cp, -, h3⟩ := h3
    rcases h3 with rfl | ⟨t, -, rfl⟩ <;> simp [Routing.Circuit.gateCount]
  · rcases h4 with ⟨b, -, rfl⟩ | (rfl | h)
    · simp only [gateCount_toRouting]; omega
    · simp only [gateCount_toRouting]; omega
    · simp at h
  · obtain ⟨q, -, rfl⟩ := h5; simp only [gateCount_toRouting]; have := hS q; omega
  · obtain ⟨s, -, rfl⟩ := h6; simp [boolExpr, Routing.Circuit.gateCount]
  · obtain ⟨s, -, h7⟩ := h7
    rcases h7 with rfl | ⟨t, -, rfl⟩ <;> simp [Routing.Circuit.gateCount]
  · obtain ⟨⟨f, j⟩, -, h8⟩ := h8
    rcases h8 with ⟨E, hE, rfl⟩ | ⟨i, -, rfl⟩
    · cases f <;> simp only [inputEqs, List.mem_cons, List.not_mem_nil, or_false] at hE
      all_goals first
        | (subst hE; simp [Routing.Circuit.gateCount]; done)
        | (subst hE; split_ifs <;> simp only [Routing.Circuit.gateCount] <;> (have := hlam j; omega))
    · simp [Routing.Circuit.gateCount]

theorem sum_map_le {α : Type} (l : List α) (f : α → ℕ) (B : ℕ) (h : ∀ a ∈ l, f a ≤ B) :
    (l.map f).sum ≤ l.length * B := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have := h a (by simp); have := ih (fun b hb => h b (by simp [hb])); nlinarith

/-- The parameter scale of the catalog. -/
def catX (M : Ram) (τ k : ℕ) : ℕ := M.w + M.k + M.code.length + τ + k + 2

theorem lists_le (d : Dims) :
    (timeEqList d).length ≤ 2 * (d.K * d.w) + 4 * d.K + 2 * d.L + 30 * d.w + 10 * d.τ + 5 * d.β + 40 ∧
    (timeSlotList d).length ≤ 2 * (d.K * d.w) + 4 * d.K + 2 * d.L + 30 * d.w + 10 * d.τ + 5 * d.β + 40 ∧
    (copyList d).length ≤ d.K * d.w + d.K + d.w + 3 * d.τ + 2 * d.β + 5 ∧
    (sortEqList d).length ≤ d.κ + 5 * d.w + 15 ∧
    (sortSlotList d).length ≤ 5 * d.w + 3 * d.τ + 2 * d.κ + 20 ∧
    (recSlotList d).length ≤ 2 * d.w + d.τ + 4 ∧
    (([RecField.va, .ad, .ts, .ph, .rgn, .act].flatMap fun f =>
      (List.range (f.width d.w d.τ)).map fun j => (f, j))).length ≤ 2 * d.w + d.τ + 3 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [timeEqList, timeSlotList, copyList, sortEqList, sortSlotList, recSlotList, recFields, RecField.width,
      List.length_flatMap, Function.comp_def] <;> omega

theorem machineItems_length_le {F : Type} [Field F] [CharP F 2] (l : Routing.Layout) (om K L : ℕ) (M : Ram)
    (kind : Fin M.ops → AluOp) (τ a : ℕ) (lam : ℕ → Routing.Expr F) :
    (machineItems l om K L M kind τ a lam).length ≤ 1000 * catX M τ l.k ^ 3 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := lists_le (dims M τ)
  have hw : (dims M τ).w = M.w := rfl
  have hK : (dims M τ).K = M.k := rfl
  have hL : (dims M τ).L = M.code.length := rfl
  have hτ : (dims M τ).τ = τ := rfl
  have hβ : (dims M τ).β ≤ τ := by show τ - Nat.log 2 M.w ≤ τ; omega
  have hκ : (dims M τ).κ = M.w + τ + 2 := rfl
  unfold machineItems
  simp only [List.length_append, List.length_map, List.length_flatMap, List.length_cons, List.length_range,
    List.length_nil]
  have s1 := sum_map_le (copyList (dims M τ)) (fun _ => τ + 1) (τ + 1) (fun _ _ => le_rfl)
  have s2 := sum_map_le ([RecField.va, .ad, .ts, .ph, .rgn, .act].flatMap fun f =>
      (List.range (f.width (dims M τ).w (dims M τ).τ)).map fun j => (f, j)) (fun _ => l.k + 1) (l.k + 1) (fun _ _ => le_rfl)
  refine le_trans (Nat.add_le_add_left (sum_map_le _ _ (τ + 1) (fun s _ => ?_)) _) ?_
  · have : (inputEqs τ lam (Routing.Expr.read (some (localOffset l om
        { tag := (recCell s).tag, bit := (recCell s).bit, role := 7, area := 1 } (recCell s)))) s).length ≤ 1 := by
      unfold inputEqs; split <;> simp
    omega
  set X := catX M τ l.k with hX
  have hX1 : 1 ≤ X := by simp only [hX, catX]; omega
  have hwX : M.w ≤ X := by simp only [hX, catX]; omega
  have hKX : M.k ≤ X := by simp only [hX, catX]; omega
  have hLX : M.code.length ≤ X := by simp only [hX, catX]; omega
  have hτX : τ + 1 ≤ X := by simp only [hX, catX]; omega
  have hkX : l.k + 1 ≤ X := by simp only [hX, catX]; omega
  have hKw : M.k * M.w ≤ X * X := Nat.mul_le_mul hKX hwX
  have hXX : X ≤ X * X := Nat.le_mul_of_pos_left _ (by omega)
  have hX3 : X * X ≤ X * X * X := Nat.le_mul_of_pos_right _ (by omega)
  have hKw' : (dims M τ).K * (dims M τ).w ≤ X * X := by rw [hK, hw]; exact hKw
  have c1 : (copyList (dims M τ)).length ≤ 10 * (X * X) := by omega
  have c2 : (recSlotList (dims M τ)).length ≤ 10 * X := by omega
  have c3 : ([RecField.va, .ad, .ts, .ph, .rgn, .act].flatMap fun f =>
      (List.range (f.width (dims M τ).w (dims M τ).τ)).map fun j => (f, j)).length ≤ 10 * X := by omega
  have p1 : (copyList (dims M τ)).length * (τ + 1) ≤ 10 * (X * X) * X := Nat.mul_le_mul c1 (by omega)
  have p2 : (recSlotList (dims M τ)).length * (τ + 1) ≤ 10 * X * X := Nat.mul_le_mul c2 (by omega)
  have p3 : ([RecField.va, .ad, .ts, .ph, .rgn, .act].flatMap fun f =>
      (List.range (f.width (dims M τ).w (dims M τ).τ)).map fun j => (f, j)).length * (l.k + 1) ≤ 10 * X * X := Nat.mul_le_mul c3 (by omega)
  have e3 : X ^ 3 = X * X * X := by ring
  have e4 : 10 * (X * X) * X = 10 * (X * X * X) := by ring
  have e5 : 10 * X * X = 10 * (X * X) := by ring
  rw [e3]
  omega

end Items


end NearCubicGates.Adapters.RAMACSP.Gen
