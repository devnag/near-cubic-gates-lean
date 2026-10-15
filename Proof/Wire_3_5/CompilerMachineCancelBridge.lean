import Proof.Wire_3_5.CompilerMachineStream
import Proof.Wire_3_5.CompilerMachineCancelAll

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.CompilerMachine.Bridge
open NearCubicWires NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Compiler
open NearCubicWires.WireExponent3_5.CompilerMachine NearCubicWires.WireExponent3_5.CompilerMachine.Cancel
open NearCubicWires.WireExponent3_5.CompilerMachine.Kit
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length binary_value)

/-- A mask of labels below `W` as a register word: a marker bit, then its bits, low label first. -/
def maskWord (W U : ℕ) : List Bool := true :: binary W U

@[simp] theorem maskWord_length (W U : ℕ) : (maskWord W U).length = W + 1 := by simp [maskWord]

theorem maskWord_ne_nil (W U : ℕ) : maskWord W U ≠ [] := by simp [maskWord]

theorem maskWord_inj (W U V : ℕ) (hU : U < 2 ^ W) (hV : V < 2 ^ W) (h : maskWord W U = maskWord W V) : U = V := by
  have h1 : binary W U = binary W V := (List.cons.inj h).2
  have h2 := congrArg RadixSemantics.value h1
  rwa [binary_value W U hU, binary_value W V hV] at h2

theorem mem_symInsert (G : List ℕ) (x u : ℕ) (h : u ∈ symInsert G x) : u ∈ G ∨ u = x := by
  unfold symInsert at h
  split_ifs at h
  · exact Or.inl (List.mem_filter.mp h).1
  · simpa using h

/-- **Insertion commutes with the word map** on masks below `2^W`. -/
theorem symInsert_map (W : ℕ) (G : List ℕ) (x : ℕ) (hG : ∀ u ∈ G, u < 2 ^ W) (hx : x < 2 ^ W) :
    (symInsert G x).map (maskWord W) = symInsertW (G.map (maskWord W)) (maskWord W x) := by
  have hmem : maskWord W x ∈ G.map (maskWord W) ↔ x ∈ G := by
    constructor
    · intro h
      obtain ⟨u, hu, he⟩ := List.mem_map.mp h
      rwa [← maskWord_inj W u x (hG u hu) hx he]
    · intro h
      exact List.mem_map_of_mem h
  unfold symInsert symInsertW
  by_cases h : x ∈ G
  · rw [if_pos h, if_pos (hmem.mpr h), List.filter_map]
    congr 1
    apply List.filter_congr
    intro u hu
    have hiff : (maskWord W u = maskWord W x) ↔ (u = x) := ⟨maskWord_inj W u x (hG u hu) hx, fun h => h ▸ rfl⟩
    simp only [Function.comp, ne_eq, hiff]
  · rw [if_neg h, if_neg (fun h' => h (hmem.mp h'))]
    simp

theorem foldl_symInsert_map (W : ℕ) : ∀ (M G : List ℕ), (∀ u ∈ G, u < 2 ^ W) → (∀ u ∈ M, u < 2 ^ W) →
    (M.foldl symInsert G).map (maskWord W) = (M.map (maskWord W)).foldl symInsertW (G.map (maskWord W))
  | [], _, _, _ => rfl
  | x :: M, G, hG, hM => by
    rw [List.foldl_cons, List.map_cons, List.foldl_cons, ← symInsert_map W G x hG (hM x List.mem_cons_self)]
    refine foldl_symInsert_map W M (symInsert G x) ?_ (fun u hu => hM u (List.mem_cons_of_mem x hu))
    intro u hu
    rcases mem_symInsert G x u hu with h | h
    · exact hG u h
    · rw [h]; exact hM x List.mem_cons_self

/-- Every mask of a monomial is below `2^{P_ex}`. -/
theorem monoMasks_lt (pool : List (List SynEq)) : ∀ (mono : List ℕ), ∀ u ∈ monoMasks pool mono,
    u < 2 ^ pool.flatten.length
  | [], u, hu => by
    simp only [monoMasks, List.mem_singleton] at hu
    subst hu
    exact Nat.two_pow_pos _
  | a :: as, u, hu => by
    simp only [monoMasks, List.mem_flatMap, List.mem_map] at hu
    obtain ⟨c, hc, u', hu', rfl⟩ := hu
    exact Nat.or_lt_two_pow (Nat.pow_lt_pow_right (by norm_num) (labelsOf_lt pool a c hc))
      (monoMasks_lt pool as u' hu')

/-- **The streaming cancellation, as words.** -/
theorem oddMasksM_words (pool : List (List SynEq)) (p : F2Poly ℕ) :
    (oddMasksM pool p).map (maskWord pool.flatten.length) =
      ((p.flatMap (monoMasks pool)).map (maskWord pool.flatten.length)).foldl symInsertW [] := by
  unfold oddMasksM
  rw [foldl_symInsert_map _ _ [] (by simp)]
  · rfl
  · intro u hu
    obtain ⟨mono, _, hu⟩ := List.mem_flatMap.mp hu
    exact monoMasks_lt pool mono u hu

theorem cancel_run (pool : List (List SynEq)) (p : F2Poly ℕ) (staleS O xp y staleL : List Bool) (e : Bool)
    (cap cap2 cap3 : ℕ) (hxp : xp.length = pool.flatten.length + 1) (hy : y.length = pool.flatten.length + 1)
    (hcap : 2 * (pool.flatten.length + 1) + 1 ≤ cap)
    (hcap2 : filterLoopCost (p.flatMap (monoMasks pool)).length (pool.flatten.length + 1) ≤ cap2 ∧
      copyLoopCost ((p.flatMap (monoMasks pool)).length + 1) (pool.flatten.length + 1) ≤ cap2)
    (hcap3 : (p.flatMap (monoMasks pool)).length *
      (allCost (p.flatMap (monoMasks pool)).length (pool.flatten.length + 1) + 2) + 1 ≤ cap3) :
    ∃ fin : AllState, fin.G = (oddMasksM pool p).map (maskWord pool.flatten.length) ∧
      Step insertAllM (insertAllCost (p.flatMap (monoMasks pool)).length 0 (pool.flatten.length + 1)) (fun _ => 0)
        ![streamTape [] staleS, O, frame xp, frame y, [e], [false], List.replicate cap false,
          List.replicate cap2 false,
          streamTape ((p.flatMap (monoMasks pool)).map (maskWord pool.flatten.length)) staleL,
          List.replicate cap3 false]
        (fun _ => 0)
        ![streamTape fin.G fin.staleS, fin.O, frame fin.xp, frame fin.y, [fin.e], [false], List.replicate cap false,
          List.replicate cap2 false,
          streamTape ((p.flatMap (monoMasks pool)).map (maskWord pool.flatten.length)) staleL,
          List.replicate cap3 false] := by
  set W := pool.flatten.length
  set Ls := (p.flatMap (monoMasks pool)).map (maskWord W)
  have hlen : Ls.length = (p.flatMap (monoMasks pool)).length := List.length_map _
  let s0 : AllState := ⟨[], staleS, O, xp, y, e⟩
  have h0 : AllInv (W + 1) 0 s0 := ⟨by simp [s0], hxp, hy, by simp [s0]⟩
  have hL : ∀ x ∈ Ls, x.length = W + 1 := by
    intro x hx
    obtain ⟨u, _, rfl⟩ := List.mem_map.mp hx
    exact maskWord_length W u
  have h := insertAll_run Ls staleL cap cap2 cap3 (W + 1) 0 s0 hL (by omega) h0 hcap
    (by rw [hlen, Nat.zero_add]; exact hcap2) (by rw [hlen, Nat.zero_add]; exact hcap3)
  refine ⟨Ls.foldl allStep s0, ?_, ?_⟩
  · rw [foldl_allStep_G]
    exact (oddMasksM_words pool p).symm
  · rw [hlen] at h
    exact h

/-! ## Twin -/

/-- On the twin pool (labels 0, 1, 2), the polynomial `x₀x₁ + x₀x₁ + x₀` as words: the repeated monomial cancels. -/
theorem cancel_twin :
    ((([[0, 1], [0, 1], [0]] : F2Poly ℕ).flatMap (monoMasks twinPool)).map (maskWord 3)).foldl symInsertW [] =
      (oddMasksM twinPool [[0, 1], [0, 1], [0]]).map (maskWord 3) := by
  decide

end NearCubicWires.WireExponent3_5.CompilerMachine.Bridge
