import SourceAdapters.Joins.AffineRouting
import SourceAdapters.Routing.SwitchChain

/-!
# Soundness of the actual binary-lane switch network

The construction in `lem:routing`: XOR partners are involutions, coherent switches
are permutations, and the local equations transport one arbitrary whole
record through the same composed path. This proves the soundness
contract. It neither assumes nor proves routing completeness.
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Routing.Soundness

/-- XOR with the same partner mask twice is the identity, at every width. -/
theorem partner_involutive (k d : ℕ) : Function.Involutive (partner k d) := by
  intro x
  simp [partner, BitVec.xor_assoc]

theorem stageMap_involutive (k : ℕ) (s : Settings k) (j : ℕ)
    (hs : ∀ x, s j (partner k (dimension k j) x) = s j x) :
    Function.Involutive (stageMap k s j) :=
  SwitchChain.choose_involutive _ _ (partner_involutive k (dimension k j)) hs

theorem stageMap_bijective (k : ℕ) (s : Settings k) (j : ℕ)
    (hs : ∀ x, s j (partner k (dimension k j) x) = s j x) :
    Function.Bijective (stageMap k s j) :=
  (stageMap_involutive k s j hs).bijective

theorem path_bijective (k : ℕ) (s : Settings k) (hs : Coherent k s) :
    Function.Bijective (path k s) :=
  SwitchChain.path_bijective (stageMap k s) (switchCount k)
    (fun j hj => stageMap_bijective k s j (hs j hj))

/-- All fields of an arbitrary record move under the same path. -/
theorem path_transport (k : ℕ) (s : Settings k) (R : Type*) (D : ℕ → Lane k → R)
    (ht : ∀ j < switchCount k, ∀ x, D (j+1) (stageMap k s j x) = D j x) :
    ∀ x, D (switchCount k) (path k s x) = D 0 x :=
  SwitchChain.path_transport (stageMap k s) (switchCount k) R D ht

/-- Width zero has no stages; its path is the identity. -/
theorem path_zero (s : Settings 0) (x : Lane 0) : path 0 s x = x := rfl

/-- Exact endpoint; the supporting theorems also cover k=0. -/
theorem benesSoundness : BenesSoundness := by
  intro k _ s hs
  exact ⟨path_bijective k s hs, fun R D ht => path_transport k s R D ht⟩

end NearCubicGates.Adapters.Routing.Soundness
