import Proof.MachineModel.BlockLoop

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Block
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform

/-! ## Port maps -/

/-- A typed port map: a worker's `t` tapes placed injectively among `u` ambient tapes. -/
structure PortMap (t u : ℕ) where
  slot : Fin t → Fin u
  inj : Function.Injective slot

namespace PortMap
variable {t u v : ℕ}

/-- The ambient tapes the map touches (decidable, so a concrete layout is checked by `decide`). -/
def touches (P : PortMap t u) (i : Fin u) : Bool := decide (∃ j, P.slot j = i)

theorem touches_slot (P : PortMap t u) (j : Fin t) : P.touches (P.slot j) = true := by
  simp only [touches, decide_eq_true_eq]
  exact ⟨j, rfl⟩

theorem touches_false (P : PortMap t u) {i : Fin u} (h : P.touches i = false) : ∀ j, P.slot j ≠ i := by
  intro j hj
  have := P.touches_slot j
  rw [hj, h] at this
  contradiction

/-- The identity layout. -/
def id (t : ℕ) : PortMap t t := ⟨fun i => i, fun _ _ h => h⟩

/-- Composition: a worker placed in a middle layout, itself placed in the ambient one. -/
def comp (Q : PortMap u v) (P : PortMap t u) : PortMap t v :=
  ⟨fun i => Q.slot (P.slot i), fun _ _ h => P.inj (Q.inj h)⟩

/-- The first `t` of `t + e` tapes (the layout of `BlockPlatform.embedded`). -/
def castAdd (t e : ℕ) : PortMap t (t + e) := ⟨fun i => i.castAdd e, fun _ _ h => Fin.castAdd_inj.mp h⟩

/-- A concrete layout from a vector, with injectivity checked by `decide`. -/
def ofVec (s : Fin t → Fin u) (h : Function.Injective s) : PortMap t u := ⟨s, h⟩

end PortMap

/-! ## Moves -/

/-- The block changed at most the tapes marked `M`: every other tape exits with its entry head and
contents. -/
def Moves {u : ℕ} (b : Block u) (M : Fin u → Bool) : Prop :=
  ∀ i, M i = false → b.exitH i = b.entryH i ∧ b.exitA i = b.entryA i

namespace Moves
variable {t u : ℕ}

theorem mono {b : Block u} {M N : Fin u → Bool} (h : Moves b M) (hMN : ∀ i, M i = true → N i = true) :
    Moves b N := by
  intro i hi
  apply h i
  cases hm : M i
  · rfl
  · have := hMN i hm
    rw [hi] at this
    contradiction

theorem all (b : Block u) : Moves b (fun _ => true) := by
  intro i hi
  contradiction

theorem exitA {b : Block u} {M : Fin u → Bool} (h : Moves b M) {i : Fin u} (hi : M i = false) :
    b.exitA i = b.entryA i := (h i hi).2

theorem exitH {b : Block u} {M : Fin u → Bool} (h : Moves b M) {i : Fin u} (hi : M i = false) :
    b.exitH i = b.entryH i := (h i hi).1

end Moves

/-! ## The generators -/

section
variable {t u e : ℕ}

/-- Docking along a port map. -/
noncomputable def dock (b : Block t) (P : PortMap t u) (H : Fin u → ℕ) (A : Fin u → List Bool)
    (hH : ∀ j, H (P.slot j) = b.entryH j) (hA : ∀ j, A (P.slot j) = b.entryA j) : Block u :=
  focusedInto b P.slot P.inj H A hH hA

@[simp] theorem dock_cost (b : Block t) (P : PortMap t u) (H : Fin u → ℕ) (A : Fin u → List Bool)
    (hH : ∀ j, H (P.slot j) = b.entryH j) (hA : ∀ j, A (P.slot j) = b.entryA j) :
    (dock b P H A hH hA).cost = b.cost := rfl

@[simp] theorem dock_entryH (b : Block t) (P : PortMap t u) (H : Fin u → ℕ) (A : Fin u → List Bool)
    (hH : ∀ j, H (P.slot j) = b.entryH j) (hA : ∀ j, A (P.slot j) = b.entryA j) :
    (dock b P H A hH hA).entryH = H := rfl

@[simp] theorem dock_entryA (b : Block t) (P : PortMap t u) (H : Fin u → ℕ) (A : Fin u → List Bool)
    (hH : ∀ j, H (P.slot j) = b.entryH j) (hA : ∀ j, A (P.slot j) = b.entryA j) :
    (dock b P H A hH hA).entryA = A := rfl

/-- At a port, the docked block exits with the worker's exit. -/
theorem dock_exitA_slot (b : Block t) (P : PortMap t u) (H : Fin u → ℕ) (A : Fin u → List Bool)
    (hH : ∀ j, H (P.slot j) = b.entryH j) (hA : ∀ j, A (P.slot j) = b.entryA j) (j : Fin t) :
    (dock b P H A hH hA).exitA (P.slot j) = b.exitA j :=
  install_slot P.slot P.inj A b.exitA j

theorem dock_exitH_slot (b : Block t) (P : PortMap t u) (H : Fin u → ℕ) (A : Fin u → List Bool)
    (hH : ∀ j, H (P.slot j) = b.entryH j) (hA : ∀ j, A (P.slot j) = b.entryA j) (j : Fin t) :
    (dock b P H A hH hA).exitH (P.slot j) = b.exitH j :=
  dockH_slot P.slot P.inj H b.exitH j

/-- **A docked worker moves only its ports.** -/
theorem moves_dock (b : Block t) (P : PortMap t u) (H : Fin u → ℕ) (A : Fin u → List Bool)
    (hH : ∀ j, H (P.slot j) = b.entryH j) (hA : ∀ j, A (P.slot j) = b.entryA j) :
    Moves (dock b P H A hH hA) P.touches := by
  intro i hi
  have hne := P.touches_false hi
  exact ⟨dockH_other P.slot H b.exitH i hne, install_other P.slot A b.exitA i hne⟩

/-- **Sequencing unions the moved sets.** -/
theorem moves_seq {b c : Block u} (hH : b.exitH = c.entryH) (hA : b.exitA = c.entryA) {M N : Fin u → Bool}
    (hb : Moves b M) (hc : Moves c N) : Moves (seq b c hH hA) (fun i => M i || N i) := by
  intro i hi
  have hM : M i = false := by cases hm : M i <;> simp_all
  have hN : N i = false := by cases hn : N i <;> simp_all
  obtain ⟨cH, cA⟩ := hc i hN
  obtain ⟨bH, bA⟩ := hb i hM
  refine ⟨?_, ?_⟩
  · change c.exitH i = b.entryH i
    rw [cH, ← hH, bH]
  · change c.exitA i = b.entryA i
    rw [cA, ← hA, bA]

/-- Reading through a sequence: a tape the second block did not move exits with the first block's exit. -/
theorem seq_exitA_right {b c : Block u} (hH : b.exitH = c.entryH) (hA : b.exitA = c.entryA) {N : Fin u → Bool}
    (hc : Moves c N) {i : Fin u} (hi : N i = false) : (seq b c hH hA).exitA i = b.exitA i := by
  change c.exitA i = b.exitA i
  rw [hc.exitA hi, ← hA]

theorem seq_exitH_right {b c : Block u} (hH : b.exitH = c.entryH) (hA : b.exitA = c.entryA) {N : Fin u → Bool}
    (hc : Moves c N) {i : Fin u} (hi : N i = false) : (seq b c hH hA).exitH i = b.exitH i := by
  change c.exitH i = b.exitH i
  rw [hc.exitH hi, ← hH]

theorem moves_upto {b : Block u} {M : Fin u → Bool} (hb : Moves b M) (n : ℕ) (h : b.cost ≤ n) :
    Moves (upto b n h) M := hb

theorem moves_congrExit {b : Block u} {H : Fin u → ℕ} {A : Fin u → List Bool} (hH : b.exitH = H)
    (hA : b.exitA = A) {M : Fin u → Bool} (hb : Moves b M) : Moves (congrExit b hH hA) M := by
  intro i hi
  obtain ⟨h1, h2⟩ := hb i hi
  exact ⟨(congrFun hH i).symm.trans h1, (congrFun hA i).symm.trans h2⟩

/-- Extension by fresh tapes moves none of them. -/
theorem moves_embedded {b : Block t} {M : Fin t → Bool} (hb : Moves b M) (eh : Fin e → ℕ)
    (et : Fin e → List Bool) :
    Moves (embedded b eh et) (Fin.addCases (m := t) (n := e) (motive := fun _ => Bool) M (fun _ => false)) := by
  intro i hi
  refine Fin.addCases (m := t) (n := e) (motive := fun i => Fin.addCases (m := t) (n := e)
    (motive := fun _ => Bool) M (fun _ => false) i = false →
      (embedded b eh et).exitH i = (embedded b eh et).entryH i ∧
      (embedded b eh et).exitA i = (embedded b eh et).entryA i) ?_ ?_ i hi
  · intro j hj
    rw [Fin.addCases_left] at hj
    obtain ⟨h1, h2⟩ := hb j hj
    simp only [embedded, Fin.addCases_left]
    exact ⟨h1, h2⟩
  · intro j _
    simp [embedded]

/-- The paid masked reset: selected heads return to 0, where they started, and the reset tape is
restored. So it moves nothing beyond the worker's own moves. -/
theorem moves_masked {b : Block t} {M : Fin t → Bool} (hb : Moves b M) (selected : Fin t → Bool) (cap : ℕ)
    (hstart : ∀ i, selected i = true → b.entryH i = 0) (hcap : b.cost ≤ cap) :
    Moves (masked b selected cap hstart hcap)
      (Fin.addCases (m := t) (n := 1) (motive := fun _ => Bool) M (fun _ => false)) := by
  intro i hi
  refine Fin.addCases (m := t) (n := 1) (motive := fun i => Fin.addCases (m := t) (n := 1)
    (motive := fun _ => Bool) M (fun _ => false) i = false →
      (masked b selected cap hstart hcap).exitH i = (masked b selected cap hstart hcap).entryH i ∧
      (masked b selected cap hstart hcap).exitA i = (masked b selected cap hstart hcap).entryA i) ?_ ?_ i hi
  · intro j hj
    rw [Fin.addCases_left] at hj
    obtain ⟨h1, h2⟩ := hb j hj
    simp only [masked, Fin.addCases_left]
    refine ⟨?_, h2⟩
    by_cases hs : selected j = true
    · rw [if_pos hs, hstart j hs]
    · rw [if_neg hs, h1]
  · intro j _
    simp [masked]

end

/-! ## A tiny executable check of a concrete layout -/

/-- Two workers, one on ports `0,2` and one on port `1`, of a 4-tape layout never touch tape 3. -/
def examplePorts : PortMap 2 4 := PortMap.ofVec ![0, 2] (by decide)
def examplePort1 : PortMap 1 4 := PortMap.ofVec ![1] (by decide)

theorem example_untouched :
    (examplePorts.touches 3 || examplePort1.touches 3) = false ∧
      examplePorts.touches 2 = true ∧ examplePort1.touches 2 = false := by
  decide

end NearCubicWires.WireExponent3_5.Block
