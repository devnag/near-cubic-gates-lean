import Proof.Gates.Expand.Rpn
import Proof.Gates.WordPrograms.BinWDiv
import Proof.Gates.WordPrograms.Sort
import Proof.Gates.WordPrograms.Hoare
import Proof.Gates.Codec.Basic

set_option autoImplicit false

namespace NearCubicGates.Close.Expand

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length binary_value)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (NumOn)
open NearCubicWires.WireExponent3_5.UnionMachine.RegRat (mulCost)
open NearCubicGates.Close.WordPrograms.BinW (numOn_sets_ne numOn_sets_self numOn_setv)

/-! ## The stack number -/

/-- The stack `[x₀, x₁, …]` (top first) as one number in base `m`. -/
def senc (m : ℕ) : List ℕ → ℕ
  | [] => 0
  | x :: xs => x + m * senc m xs

theorem senc_lt (m : ℕ) : ∀ xs : List ℕ, (∀ x ∈ xs, x < m) → senc m xs < m ^ xs.length
  | [], _ => by simp [senc]
  | x :: xs, h => by
    have hx := h x (by simp)
    have ih := senc_lt m xs (fun y hy => h y (by simp [hy]))
    simp only [senc, List.length_cons, pow_succ]
    have : m * senc m xs + m ≤ m * m ^ xs.length := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left m ih
    nlinarith

theorem senc_div (m x : ℕ) (xs : List ℕ) (hx : x < m) : senc m (x :: xs) / m = senc m xs := by
  have hm : 0 < m := by omega
  simp only [senc]
  rw [Nat.add_mul_div_left _ _ hm, Nat.div_eq_of_lt hx, zero_add]

theorem senc_mod (m x : ℕ) (xs : List ℕ) (hx : x < m) : senc m (x :: xs) % m = x := by
  simp only [senc]
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx]

variable {ns nr : ℕ}

/-! ## The evaluator's layout -/

section Layout
variable (U : Fin 10 ↪ Fin (ns + 1)) (R : Fin 12 ↪ Fin nr)

/-- The evaluator's streams and registers at rest. -/
structure Ev (Wb m k t : ℕ) (σ : WState ns nr) : Prop where
  num : ∀ i : Fin 10, i ∈ [(1 : Fin 10), 2, 3, 4, 5] → ∃ v, NumOn σ (U i) Wb v
  mm : NumOn σ (U 6) Wb m
  km : NumOn σ (U 7) Wb k
  one : NumOn σ (U 8) Wb 1
  pt : NumOn σ (U 9) Wb t
  zero : ∀ j : Fin 12, j ≠ 11 → σ.val (R j) = 0

variable {U R}

theorem Ev.sets {Wb m k t : ℕ} {σ : WState ns nr} (h : Ev U R Wb m k t σ) (i : Fin 10)
    (hi : i ∈ [(1 : Fin 10), 2, 3, 4, 5]) (v : ℕ) : Ev U R Wb m k t (σ.sets (U i) (frame (binary Wb v))) := by
  have hsh : σ.sh (U i) = 0 := by obtain ⟨w, hw⟩ := h.num i hi; exact hw.2
  have hne : ∀ j : Fin 10, j ∉ [(1 : Fin 10), 2, 3, 4, 5] → U j ≠ U i := by
    intro j hj e
    rw [U.injective e] at hj
    exact hj hi
  refine ⟨fun j hj => ?_, numOn_sets_ne h.mm (hne 6 (by decide)) _, numOn_sets_ne h.km (hne 7 (by decide)) _,
    numOn_sets_ne h.one (hne 8 (by decide)) _, numOn_sets_ne h.pt (hne 9 (by decide)) _, h.zero⟩
  by_cases e : j = i
  · subst e; exact ⟨v, numOn_sets_self σ _ Wb v hsh⟩
  · obtain ⟨w, hw⟩ := h.num j hj
    exact ⟨w, numOn_sets_ne hw (fun h' => e (U.injective h')) _⟩

theorem Ev.seth {Wb m k t : ℕ} {σ : WState ns nr} (h : Ev U R Wb m k t σ) (n : ℕ) :
    Ev U R Wb m k t (σ.seth (U 0) n) := by
  have hne : ∀ j : Fin 10, j ≠ 0 → U j ≠ U 0 := fun j hj e => hj (U.injective e)
  have tr : ∀ j : Fin 10, j ≠ 0 → ∀ {W v : ℕ}, NumOn σ (U j) W v → NumOn (σ.seth (U 0) n) (U j) W v :=
    fun j hj W v hn => ⟨by simpa using hn.1, by simp [Function.update_of_ne (hne j hj), hn.2]⟩
  refine ⟨fun j hj => ?_, tr 6 (by decide) h.mm, tr 7 (by decide) h.km, tr 8 (by decide) h.one,
    tr 9 (by decide) h.pt, h.zero⟩
  obtain ⟨w, hw⟩ := h.num j hj
  have hj0 : j ≠ 0 := by
    intro e; subst e; simp at hj
  exact ⟨w, tr j hj0 hw⟩

theorem Ev.setv {Wb m k t : ℕ} {σ : WState ns nr} (h : Ev U R Wb m k t σ) (j : Fin 12) (hj : j = 11) (v : ℕ) :
    Ev U R Wb m k t (σ.setv (R j) v) := by
  subst hj
  refine ⟨fun i hi => ?_, numOn_setv h.mm _ _, numOn_setv h.km _ _, numOn_setv h.one _ _, numOn_setv h.pt _ _,
    fun j hj => ?_⟩
  · obtain ⟨w, hw⟩ := h.num i hi; exact ⟨w, numOn_setv hw _ _⟩
  · simp only [WState.setv_val]
    rw [Function.update_of_ne (fun e => hj (R.injective e))]
    exact h.zero j hj

theorem Ev.num' {Wb m k t : ℕ} {σ : WState ns nr} (h : Ev U R Wb m k t σ) (i : Fin 10)
    (hi : i ∈ [(1 : Fin 10), 2, 3, 4, 5]) : ∃ v, NumOn σ (U i) Wb v := h.num i hi

theorem Ev.reg {Wb m k t : ℕ} {σ : WState ns nr} (h : Ev U R Wb m k t σ) (j : Fin 12) (hj : j ≠ 11 := by decide) :
    σ.val (R j) = 0 := h.zero j hj

theorem Ev.cap_ok {Wb m k t : ℕ} {σ : WState ns nr} (_h : Ev U R Wb m k t σ) : True := trivial

end Layout

/-! ## Pop and push -/

section PopPush
variable (U : Fin 10 ↪ Fin (ns + 1)) (R : Fin 12 ↪ Fin nr)

theorem uN {i j : Fin 10} (h : i ≠ j) : U i ≠ U j := fun e => h (U.injective e)
theorem rN {i j : Fin 12} (h : i ≠ j) : R i ≠ R j := fun e => h (R.injective e)

/-- `A := top`, the stack popped. -/
def pop : WMX ns nr :=
  .seq (BinW.divmod (U 1) (U 6) (U 4) (U 2) (U 5) (R 2) (R 3) (R 5) (R 6)) (BinW.copy (U 1) (U 4) (R 2) (R 3))

def popCost (Wb : ℕ) : ℕ := BinW.divCost Wb + 1 + (41 * Wb + 3)

variable {U R}

theorem pop_spec (cap Wb m k t : ℕ) (σ : WState ns nr) (h : Ev U R Wb m k t σ) (x : ℕ) (xs : List ℕ)
    (hS : NumOn σ (U 1) Wb (senc m (x :: xs))) (hx : x < m) (hs : senc m (x :: xs) < 2 ^ Wb)
    (h2m : 2 * m ≤ 2 ^ Wb) (hcap : 2 * Wb + 1 ≤ cap) :
    Runs cap (pop U R) σ (popCost Wb) (fun τ => Ev U R Wb m k t τ ∧ NumOn τ (U 1) Wb (senc m xs) ∧
      NumOn τ (U 2) Wb x ∧ SameExcept σ τ [U 1, U 2, U 4, U 5] []) := by
  obtain ⟨a0, hA⟩ := h.num 2 (by decide)
  obtain ⟨c0, hC⟩ := h.num 4 (by decide)
  obtain ⟨x0, hX⟩ := h.num 5 (by decide)
  have hm : 0 < m := by omega
  have d := BinW.divmod_spec cap Wb (uN U (by decide)) (uN U (by decide)) (uN U (by decide)) (uN U (by decide))
    (uN U (by decide)) (uN U (by decide)) (uN U (by decide)) (uN U (by decide)) (uN U (by decide))
    (rN R (by decide)) (rN R (by decide)) (rN R (by decide)) (rN R (by decide)) σ _ _ c0 a0 x0 hS h.mm hC hA hX
    (h.reg 2) (h.reg 3) (h.reg 5) (h.reg 6) hs hm h2m hcap
  rw [senc_div m x xs hx, senc_mod m x xs hx] at d
  set τ1 := ((σ.sets (U 4) (frame (binary Wb (senc m xs)))).sets (U 2) (frame (binary Wb x))).sets (U 5)
    (frame (binary Wb 0)) with hτ1
  have e1 : Ev U R Wb m k t τ1 := ((h.sets 4 (by decide) _).sets 2 (by decide) _).sets 5 (by decide) _
  have hC1 : NumOn τ1 (U 4) Wb (senc m xs) :=
    numOn_sets_ne (numOn_sets_ne (numOn_sets_self σ _ Wb _ hC.2) (uN U (by decide)) _) (uN U (by decide)) _
  have hS1 : NumOn τ1 (U 1) Wb (senc m (x :: xs)) :=
    numOn_sets_ne (numOn_sets_ne (numOn_sets_ne hS (uN U (by decide)) _) (uN U (by decide)) _) (uN U (by decide)) _
  have c := BinW.copy_spec cap Wb (uN U (by decide)) (rN R (by decide)) τ1 _ _ hS1 hC1 (e1.reg 2) (e1.reg 3) hcap
  refine ⟨_, WXExec.seq d c, e1.sets 1 (by decide) _, numOn_sets_self τ1 _ Wb _ hS1.2, ?_, ?_⟩
  · exact numOn_sets_ne (numOn_sets_ne (numOn_sets_self _ _ Wb _ (by simpa using hA.2)) (uN U (by decide)) _)
      (uN U (by decide)) _
  · rw [hτ1]
    refine SameExcept.trans (SameExcept.trans (SameExcept.trans (sameExcept_sets σ (by simp) _)
      (sameExcept_sets _ (by simp) _)) (sameExcept_sets _ (by simp) _)) (sameExcept_sets _ (by simp) _)

/-- Push `A` (kept) on the stack. -/
def push (U : Fin 10 ↪ Fin (ns + 1)) (R : Fin 12 ↪ Fin nr) : WMX ns nr :=
  .seq (BinW.mul (U 1) (U 6) (U 4) (U 5) (R 2) (R 3) (R 4))
    (.seq (BinW.add (U 4) (U 2) (R 2) (R 3)) (BinW.copy (U 1) (U 4) (R 2) (R 3)))

def pushCost (Wb : ℕ) : ℕ := mulCost Wb + 1 + ((41 * Wb + 3) + 1 + (41 * Wb + 3))

theorem push_spec (cap Wb m k t : ℕ) (σ : WState ns nr) (h : Ev U R Wb m k t σ) (x : ℕ) (xs : List ℕ)
    (hS : NumOn σ (U 1) Wb (senc m xs)) (hA : NumOn σ (U 2) Wb x) (hs : senc m (x :: xs) < 2 ^ Wb)
    (hm : m < 2 ^ Wb) (hcap : 2 * Wb + 1 ≤ cap) :
    Runs cap (push U R) σ (pushCost Wb) (fun τ => Ev U R Wb m k t τ ∧ NumOn τ (U 1) Wb (senc m (x :: xs)) ∧
      NumOn τ (U 2) Wb x ∧ SameExcept σ τ [U 1, U 4, U 5] []) := by
  obtain ⟨c0, hC⟩ := h.num 4 (by decide)
  obtain ⟨x0, hX⟩ := h.num 5 (by decide)
  have hsm : senc m xs * m < 2 ^ Wb := by
    have : senc m xs * m ≤ senc m (x :: xs) := by simp only [senc]; rw [mul_comm]; omega
    omega
  have d := BinW.mul_spec cap Wb (uN U (by decide)) (uN U (by decide)) (uN U (by decide)) (uN U (by decide))
    (uN U (by decide)) (uN U (by decide)) (rN R (by decide)) (rN R (by decide)) (rN R (by decide)) σ _ _ c0 x0
    hS h.mm hC hX (h.reg 2) (h.reg 3) (h.reg 4) hsm hm hcap
  set τ1 := (σ.sets (U 4) (frame (binary Wb (senc m xs * m)))).sets (U 5) (frame (binary Wb 0)) with hτ1
  have e1 : Ev U R Wb m k t τ1 := (h.sets 4 (by decide) _).sets 5 (by decide) _
  have hC1 : NumOn τ1 (U 4) Wb (senc m xs * m) :=
    numOn_sets_ne (numOn_sets_self σ _ Wb _ hC.2) (uN U (by decide)) _
  have hA1 : NumOn τ1 (U 2) Wb x := numOn_sets_ne (numOn_sets_ne hA (uN U (by decide)) _) (uN U (by decide)) _
  have hS1 : NumOn τ1 (U 1) Wb (senc m xs) :=
    numOn_sets_ne (numOn_sets_ne hS (uN U (by decide)) _) (uN U (by decide)) _
  have e2v : senc m xs * m + x = senc m (x :: xs) := by simp only [senc]; ring
  have a := BinW.add_spec cap Wb (uN U (by decide)) (rN R (by decide)) τ1 _ _ hC1 hA1 (e1.reg 2) (e1.reg 3)
    (by rw [e2v]; exact hs) hcap
  rw [e2v] at a
  set τ2 := τ1.sets (U 4) (frame (binary Wb (senc m (x :: xs)))) with hτ2
  have e2 : Ev U R Wb m k t τ2 := e1.sets 4 (by decide) _
  have hC2 : NumOn τ2 (U 4) Wb (senc m (x :: xs)) := numOn_sets_self τ1 _ Wb _ hC1.2
  have hS2 : NumOn τ2 (U 1) Wb (senc m xs) := numOn_sets_ne hS1 (uN U (by decide)) _
  have c := BinW.copy_spec cap Wb (uN U (by decide)) (rN R (by decide)) τ2 _ _ hS2 hC2 (e2.reg 2) (e2.reg 3) hcap
  refine ⟨_, WXExec.seq d (WXExec.seq a c), e2.sets 1 (by decide) _, numOn_sets_self τ2 _ Wb _ hS2.2,
    numOn_sets_ne (numOn_sets_ne hA1 (uN U (by decide)) _) (uN U (by decide)) _, ?_⟩
  rw [hτ2, hτ1]
  exact SameExcept.trans (SameExcept.trans (SameExcept.trans (sameExcept_sets σ (by simp) _)
    (sameExcept_sets _ (by simp) _)) (sameExcept_sets _ (by simp) _)) (sameExcept_sets _ (by simp) _)

end PopPush

end NearCubicGates.Close.Expand
