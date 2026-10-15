import Proof.Wire_3_5.CompilerMachineCancelBridge
import Proof.Wire_3_5.CompilerMachineUnionsAll

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.CompilerMachine.Bridge
open NearCubicWires NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Compiler
open NearCubicWires.WireExponent3_5.CompilerMachine NearCubicWires.WireExponent3_5.CompilerMachine.Cancel
open NearCubicWires.WireExponent3_5.CompilerMachine.Kit NearCubicWires.WireExponent3_5.CompilerMachine.Unions
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch

/-- Insertion commutes with any word map injective on masks below `2^W`. -/
theorem symInsert_map_of (W : ℕ) (f : ℕ → List Bool) (hf : ∀ u v, u < 2 ^ W → v < 2 ^ W → f u = f v → u = v)
    (G : List ℕ) (x : ℕ) (hG : ∀ u ∈ G, u < 2 ^ W) (hx : x < 2 ^ W) :
    (symInsert G x).map f = symInsertW (G.map f) (f x) := by
  have hmem : f x ∈ G.map f ↔ x ∈ G := by
    constructor
    · intro h
      obtain ⟨u, hu, he⟩ := List.mem_map.mp h
      rwa [← hf u x (hG u hu) hx he]
    · intro h
      exact List.mem_map_of_mem h
  unfold symInsert symInsertW
  by_cases h : x ∈ G
  · rw [if_pos h, if_pos (hmem.mpr h), List.filter_map]
    congr 1
    apply List.filter_congr
    intro u hu
    have hiff : (f u = f x) ↔ (u = x) := ⟨hf u x (hG u hu) hx, fun h => h ▸ rfl⟩
    simp only [Function.comp, ne_eq, hiff]
  · rw [if_neg h, if_neg (fun h' => h (hmem.mp h'))]
    simp

theorem foldl_symInsert_map_of (W : ℕ) (f : ℕ → List Bool) (hf : ∀ u v, u < 2 ^ W → v < 2 ^ W → f u = f v → u = v) :
    ∀ (M G : List ℕ), (∀ u ∈ G, u < 2 ^ W) → (∀ u ∈ M, u < 2 ^ W) →
      (M.foldl symInsert G).map f = (M.map f).foldl symInsertW (G.map f)
  | [], _, _, _ => rfl
  | x :: M, G, hG, hM => by
    rw [List.foldl_cons, List.map_cons, List.foldl_cons, ← symInsert_map_of W f hf G x hG (hM x List.mem_cons_self)]
    refine foldl_symInsert_map_of W f hf M (symInsert G x) ?_ (fun u hu => hM u (List.mem_cons_of_mem x hu))
    intro u hu
    rcases mem_symInsert G x u hu with h | h
    · exact hG u h
    · rw [h]; exact hM x List.mem_cons_self

/-- The size-`0` entries are injective on masks below `2^W`. -/
theorem entry0_inj (Q W : ℕ) : ∀ u v, u < 2 ^ W → v < 2 ^ W → ew Q W (0, u) = ew Q W (0, v) → u = v :=
  fun u v hu hv h => (entryWord_inj Q W 0 0 u v (by omega) (by omega) hu hv h).2

/-- **The streaming cancellation in the lift's entry format.** -/
theorem oddMasksM_entries (pool : List (List SynEq)) (p : F2Poly ℕ) (Q : ℕ) :
    (oddMasksM pool p).map (fun U => ew Q pool.flatten.length (0, U)) =
      ((p.flatMap (monoMasks pool)).map (fun U => ew Q pool.flatten.length (0, U))).foldl symInsertW [] := by
  unfold oddMasksM
  rw [foldl_symInsert_map_of _ _ (entry0_inj Q pool.flatten.length) _ [] (by simp)]
  · rfl
  · intro u hu
    obtain ⟨mono, _, hu⟩ := List.mem_flatMap.mp hu
    exact monoMasks_lt pool mono u hu

/-- **C3.4 in the lift's format**: from the empty list and the stream of the size-`0` entries of `p`'s expansion masks,
the insert-all machine leaves the size-`0` entries of the cancelled masks `oddMasksM pool p` on tape 0. -/
theorem cancel_run_entry (pool : List (List SynEq)) (p : F2Poly ℕ) (Q : ℕ) (staleS O xp y staleL : List Bool) (e : Bool)
    (cap cap2 cap3 : ℕ) (hxp : xp.length = Q + pool.flatten.length + 1) (hy : y.length = Q + pool.flatten.length + 1)
    (hcap : 2 * (Q + pool.flatten.length + 1) + 1 ≤ cap)
    (hcap2 : filterLoopCost (p.flatMap (monoMasks pool)).length (Q + pool.flatten.length + 1) ≤ cap2 ∧
      copyLoopCost ((p.flatMap (monoMasks pool)).length + 1) (Q + pool.flatten.length + 1) ≤ cap2)
    (hcap3 : (p.flatMap (monoMasks pool)).length *
      (allCost (p.flatMap (monoMasks pool)).length (Q + pool.flatten.length + 1) + 2) + 1 ≤ cap3) :
    ∃ fin : AllState, fin.G = (oddMasksM pool p).map (fun U => ew Q pool.flatten.length (0, U)) ∧
      Step insertAllM (insertAllCost (p.flatMap (monoMasks pool)).length 0 (Q + pool.flatten.length + 1))
        (fun _ => 0)
        ![streamTape [] staleS, O, frame xp, frame y, [e], [false], List.replicate cap false,
          List.replicate cap2 false,
          streamTape ((p.flatMap (monoMasks pool)).map (fun U => ew Q pool.flatten.length (0, U))) staleL,
          List.replicate cap3 false]
        (fun _ => 0)
        ![streamTape fin.G fin.staleS, fin.O, frame fin.xp, frame fin.y, [fin.e], [false], List.replicate cap false,
          List.replicate cap2 false,
          streamTape ((p.flatMap (monoMasks pool)).map (fun U => ew Q pool.flatten.length (0, U))) staleL,
          List.replicate cap3 false] := by
  set W := pool.flatten.length
  set Ls := (p.flatMap (monoMasks pool)).map (fun U => ew Q W (0, U))
  have hlen : Ls.length = (p.flatMap (monoMasks pool)).length := List.length_map _
  let s0 : AllState := ⟨[], staleS, O, xp, y, e⟩
  have h0 : AllInv (Q + W + 1) 0 s0 := ⟨by simp [s0], hxp, hy, by simp [s0]⟩
  have hL : ∀ x ∈ Ls, x.length = Q + W + 1 := by
    intro x hx
    obtain ⟨u, _, rfl⟩ := List.mem_map.mp hx
    exact entryWord_length Q W 0 u (by omega)
  have h := insertAll_run Ls staleL cap cap2 cap3 (Q + W + 1) 0 s0 hL (by omega) h0 hcap
    (by rw [hlen, Nat.zero_add]; exact hcap2) (by rw [hlen, Nat.zero_add]; exact hcap3)
  refine ⟨Ls.foldl allStep s0, ?_, ?_⟩
  · rw [foldl_allStep_G]
    exact (oddMasksM_entries pool p Q).symm
  · rw [hlen] at h
    exact h

/-! ## Twin -/

/-- The unions of the monomials `1, 2, 4` below size `2`, as entries of mask width `3`: `unionsM` read through the
entry words is the lift steps on words. -/
theorem unions_twin :
    (unionsM 2 [1, 2, 4]).map (ew 2 3) = (([1, 2, 4] : List ℕ).map fun g => ew 2 3 (0, g)).foldl (liftStepW 2 3) [] := by
  decide

end NearCubicWires.WireExponent3_5.CompilerMachine.Bridge
