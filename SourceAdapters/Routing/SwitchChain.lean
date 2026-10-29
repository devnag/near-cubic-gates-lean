import Mathlib.Logic.Equiv.Basic
import Mathlib.Data.List.Range

/-!
# Coherent switches and whole-record transport through finite schedules

The construction in `lem:routing`: pair coherence makes each stay-or-swap map an
involution. Composition gives one permutation shared by all record fields,
and the local transport equations compose to the endpoint equality.
No distinctness assumption is made about record values. This generic
helper imports no routing contract and includes empty schedules.
-/

set_option autoImplicit false

universe u v

namespace NearCubicGates.Adapters.Routing.SwitchChain

variable {α : Type u}

/-- A switch either applies its partner involution or leaves the lane fixed. -/
def choose (σ : α → α) (b : α → Bool) (x : α) : α :=
  if b x then σ x else x

theorem choose_involutive (σ : α → α) (b : α → Bool)
    (hσ : Function.Involutive σ) (hb : ∀ x, b (σ x) = b x) :
    Function.Involutive (choose σ b) := by
  intro x
  cases hx : b x <;> simp [choose, hx, hb, hσ x]

theorem choose_bijective (σ : α → α) (b : α → Bool)
    (hσ : Function.Involutive σ) (hb : ∀ x, b (σ x) = b x) :
    Function.Bijective (choose σ b) :=
  (choose_involutive σ b hσ hb).bijective

/-- Explicit permutation; its inverse is the same coherent switch. -/
def choosePerm (σ : α → α) (b : α → Bool)
    (hσ : Function.Involutive σ) (hb : ∀ x, b (σ x) = b x) : Equiv.Perm α :=
  (choose_involutive σ b hσ hb).toPerm (choose σ b)

/-- Execute a finite list in its displayed order. -/
def run (stages : List (α → α)) (x : α) : α :=
  stages.foldl (fun y f => f y) x

theorem run_nil (x : α) : run [] x = x := rfl

theorem run_cons (f : α → α) (stages : List (α → α)) (x : α) :
    run (f :: stages) x = run stages (f x) := rfl

theorem run_bijective (stages : List (α → α))
    (hs : ∀ f ∈ stages, Function.Bijective f) : Function.Bijective (run stages) := by
  induction stages with
  | nil => exact Function.bijective_id
  | cons f stages ih =>
    change Function.Bijective (run stages ∘ f)
    exact (ih (fun g hg => hs g (by simp [hg]))).comp (hs f (by simp))

/-- Arbitrary whole records propagate; their values need not be distinct. -/
theorem run_transport (stages : List (α → α)) (R : Type v) (D : ℕ → α → R)
    (ht : ∀ j (hj : j < stages.length), ∀ x, D (j+1) (stages[j] x) = D j x) :
    ∀ x, D stages.length (run stages x) = D 0 x := by
  induction stages generalizing D with
  | nil => intro x; rfl
  | cons f stages ih =>
    intro x
    have htail : ∀ j (hj : j < stages.length), ∀ y,
        D ((j+1)+1) (stages[j] y) = D (j+1) y := by
      intro j hj y
      exact ht (j+1) (Nat.succ_lt_succ hj) y
    change D (stages.length+1) (run stages (f x)) = D 0 x
    exact (ih (fun j => D (j+1)) htail (f x)).trans (ht 0 (by simp) x)

/-- Indexing agrees literally with the routing range/foldl path. -/
def path (stage : ℕ → α → α) (count : ℕ) (x : α) : α :=
  (List.range count).foldl (fun y j => stage j y) x

theorem path_zero (stage : ℕ → α → α) (x : α) : path stage 0 x = x := rfl

theorem path_succ (stage : ℕ → α → α) (n : ℕ) (x : α) :
    path stage (n+1) x = stage n (path stage n x) := by
  simp [path, List.range_succ, List.foldl_append]

theorem path_bijective (stage : ℕ → α → α) (count : ℕ)
    (hs : ∀ j < count, Function.Bijective (stage j)) :
    Function.Bijective (path stage count) := by
  induction count with
  | zero => exact Function.bijective_id
  | succ n ih =>
    have he : path stage (n+1) = stage n ∘ path stage n := funext (path_succ stage n)
    rw [he]
    exact (hs n (Nat.lt_succ_self n)).comp
      (ih (fun j hj => hs j (Nat.lt_trans hj (Nat.lt_succ_self n))))

theorem path_transport (stage : ℕ → α → α) (count : ℕ) (R : Type v) (D : ℕ → α → R)
    (ht : ∀ j < count, ∀ x, D (j+1) (stage j x) = D j x) :
    ∀ x, D count (path stage count x) = D 0 x := by
  induction count with
  | zero => intro x; rfl
  | succ n ih =>
    intro x
    rw [path_succ, ht n (Nat.lt_succ_self n)]
    exact ih (fun j hj => ht j (Nat.lt_trans hj (Nat.lt_succ_self n))) x

/-- The exact generic soundness package for any finite coherent switch schedule. -/
theorem coherent_path_sound (σ : ℕ → α → α) (b : ℕ → α → Bool) (count : ℕ)
    (hσ : ∀ j < count, Function.Involutive (σ j))
    (hb : ∀ j < count, ∀ x, b j (σ j x) = b j x) :
    Function.Bijective (path (fun j => choose (σ j) (b j)) count) ∧
      ∀ (R : Type v) (D : ℕ → α → R),
        (∀ j < count, ∀ x, D (j+1) (choose (σ j) (b j) x) = D j x) →
        ∀ x, D count (path (fun j => choose (σ j) (b j)) count x) = D 0 x := by
  constructor
  · exact path_bijective _ count (fun j hj => choose_bijective _ _ (hσ j hj) (hb j hj))
  · exact fun R D ht => path_transport _ count R D ht

end NearCubicGates.Adapters.Routing.SwitchChain
