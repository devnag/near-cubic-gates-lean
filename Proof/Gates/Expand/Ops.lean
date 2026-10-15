import Proof.Gates.Expand.Loop

set_option autoImplicit false

namespace NearCubicGates.Close.Expand

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length binary_value)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (NumOn)
open NearCubicWires.WireExponent3_5.UnionMachine.RegRat (mulCost)
open NearCubicGates.Close.WordPrograms.BinW (numOn_sets_ne numOn_sets_self numOn_setv)

variable {ns nr : ℕ}

section EvV
variable (U : Fin 10 ↪ Fin (ns + 1)) (R : Fin 12 ↪ Fin nr)

/-- The evaluator state by values. -/
structure EvV (Wb : ℕ) (inp : List Bool) (hd e : ℕ) (v : Fin 10 → ℕ) (σ : WState ns nr) : Prop where
  num : ∀ i : Fin 10, i ≠ 0 → NumOn σ (U i) Wb (v i)
  inp : σ.st (U 0) = inp
  hd : σ.sh (U 0) = hd
  r1 : σ.val (R 1) = e
  zero : ∀ j : Fin 12, j ≠ 1 → j ≠ 11 → σ.val (R j) = 0

/-- The scratch streams (the ones a token program may write). -/
def Scr (i : Fin 10) : Prop := i ∈ ([1, 2, 3, 4, 5] : List (Fin 10))

instance (i : Fin 10) : Decidable (Scr i) := by unfold Scr; infer_instance

/-- A state reached from `σ0` inside a token program. -/
def Post (σ0 : WState ns nr) (Wb : ℕ) (inp : List Bool) (hd e : ℕ) (v : Fin 10 → ℕ) (τ : WState ns nr) : Prop :=
  EvV U R Wb inp hd e v τ ∧ SameExcept σ0 τ (evS U) (evR R)

variable {U R}

theorem Scr.ne0 {i : Fin 10} (h : Scr i) : i ≠ 0 := by
  intro e; subst e; simp [Scr] at h

theorem Scr.mem {i : Fin 10} (h : Scr i) : U i ∈ evS U := by
  simp only [Scr, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl <;> simp [evS]

theorem EvV.sets {Wb hd e : ℕ} {inp : List Bool} {v : Fin 10 → ℕ} {σ : WState ns nr}
    (h : EvV U R Wb inp hd e v σ) (i : Fin 10) (hi : i ≠ 0) (x : ℕ) :
    EvV U R Wb inp hd e (Function.update v i x) (σ.sets (U i) (frame (binary Wb x))) := by
  refine ⟨fun j hj => ?_, ?_, ?_, by simpa using h.r1, fun j h1 h2 => by simpa using h.zero j h1 h2⟩
  · by_cases e : j = i
    · subst e
      rw [Function.update_self]
      exact numOn_sets_self σ _ Wb x (h.num j hj).2
    · rw [Function.update_of_ne e]
      exact numOn_sets_ne (h.num j hj) (uN U e) _
  · simp only [WState.sets_st]; rw [Function.update_of_ne (uN U (Ne.symm hi))]; exact h.inp
  · simpa using h.hd

theorem Post.sets {σ0 : WState ns nr} {Wb hd e : ℕ} {inp : List Bool} {v : Fin 10 → ℕ} {σ : WState ns nr}
    (h : Post U R σ0 Wb inp hd e v σ) (i : Fin 10) (hi : Scr i) (x : ℕ) :
    Post U R σ0 Wb inp hd e (Function.update v i x) (σ.sets (U i) (frame (binary Wb x))) :=
  ⟨h.1.sets i hi.ne0 x, SameExcept.trans h.2 (sameExcept_sets σ hi.mem _)⟩

theorem Post.reg {σ0 : WState ns nr} {Wb hd e : ℕ} {inp : List Bool} {v : Fin 10 → ℕ} {σ : WState ns nr}
    (h : Post U R σ0 Wb inp hd e v σ) (j : Fin 12) (h1 : j ≠ 1 := by decide) (h11 : j ≠ 11 := by decide) :
    σ.val (R j) = 0 := h.1.zero j h1 h11

theorem Post.num {σ0 : WState ns nr} {Wb hd e : ℕ} {inp : List Bool} {v : Fin 10 → ℕ} {σ : WState ns nr}
    (h : Post U R σ0 Wb inp hd e v σ) (i : Fin 10) (hi : i ≠ 0 := by decide) : NumOn σ (U i) Wb (v i) :=
  h.1.num i hi

theorem Post.refl {Wb hd e : ℕ} {inp : List Bool} {v : Fin 10 → ℕ} {σ : WState ns nr}
    (h : EvV U R Wb inp hd e v σ) : Post U R σ Wb inp hd e v σ := ⟨h, SameExcept.refl σ _ _⟩

end EvV

/-! ## The operations -/

section Ops
variable {U : Fin 10 ↪ Fin (ns + 1)} {R : Fin 12 ↪ Fin nr} {σ0 σ : WState ns nr} {Wb hd e : ℕ}
  {inp : List Bool} {v : Fin 10 → ℕ} (cap : ℕ)

theorem opAdd (a b : Fin 10) (ha : Scr a) (hb : b ≠ 0) (hab : a ≠ b) (h : Post U R σ0 Wb inp hd e v σ)
    (hlt : v a + v b < 2 ^ Wb) (hcap : 2 * Wb + 1 ≤ cap) :
    Runs cap (BinW.add (U a) (U b) (R 2) (R 3)) σ (41 * Wb + 3)
      (Post U R σ0 Wb inp hd e (Function.update v a (v a + v b))) :=
  ⟨_, BinW.add_spec cap Wb (uN U hab) (rN R (by decide)) σ _ _ (h.num a ha.ne0) (h.num b hb) (h.reg 2) (h.reg 3)
    hlt hcap, h.sets a ha _⟩

theorem opSub (a b : Fin 10) (ha : Scr a) (hb : b ≠ 0) (hab : a ≠ b) (h : Post U R σ0 Wb inp hd e v σ)
    (hle : v b ≤ v a) (hlt : v a < 2 ^ Wb) (hcap : 2 * Wb + 1 ≤ cap) :
    Runs cap (BinW.sub (U a) (U b) (R 2) (R 3)) σ (41 * Wb + 9)
      (Post U R σ0 Wb inp hd e (Function.update v a (v a - v b))) :=
  ⟨_, BinW.sub_spec cap Wb (uN U hab) (rN R (by decide)) σ _ _ (h.num a ha.ne0) (h.num b hb) (h.reg 2) (h.reg 3)
    hle hlt hcap, h.sets a ha _⟩

theorem opCopy (a b : Fin 10) (ha : Scr a) (hb : b ≠ 0) (hab : a ≠ b) (h : Post U R σ0 Wb inp hd e v σ)
    (hcap : 2 * Wb + 1 ≤ cap) :
    Runs cap (BinW.copy (U a) (U b) (R 2) (R 3)) σ (41 * Wb + 3)
      (Post U R σ0 Wb inp hd e (Function.update v a (v b))) :=
  ⟨_, BinW.copy_spec cap Wb (uN U hab) (rN R (by decide)) σ _ _ (h.num a ha.ne0) (h.num b hb) (h.reg 2) (h.reg 3)
    hcap, h.sets a ha _⟩

theorem opInc (a b : Fin 10) (ha : Scr a) (hb : b ≠ 0) (hab : a ≠ b) (h : Post U R σ0 Wb inp hd e v σ)
    (hlt : v a + 1 < 2 ^ Wb) (hcap : 2 * Wb + 1 ≤ cap) :
    Runs cap (BinW.inc (U a) (U b) (R 2) (R 3)) σ (41 * Wb + 7)
      (Post U R σ0 Wb inp hd e (Function.update v a (v a + 1))) :=
  ⟨_, BinW.inc_spec cap Wb (uN U hab) (rN R (by decide)) σ _ _ (h.num a ha.ne0) (h.num b hb) (h.reg 2) (h.reg 3)
    hlt hcap, h.sets a ha _⟩

theorem opZero (a b : Fin 10) (ha : Scr a) (hb : b ≠ 0) (hab : a ≠ b) (h : Post U R σ0 Wb inp hd e v σ)
    (hcap : 2 * Wb + 1 ≤ cap) :
    Runs cap (BinW.zero (U a) (U b) (R 2) (R 3)) σ (41 * Wb + 3)
      (Post U R σ0 Wb inp hd e (Function.update v a 0)) :=
  ⟨_, BinW.zero_spec cap Wb (uN U hab) (rN R (by decide)) σ _ _ (h.num a ha.ne0) (h.num b hb) (h.reg 2) (h.reg 3)
    hcap, h.sets a ha _⟩

theorem opAnd (a b : Fin 10) (ha : Scr a) (hb : b ≠ 0) (hab : a ≠ b) (h : Post U R σ0 Wb inp hd e v σ)
    (hcap : 2 * Wb + 1 ≤ cap) :
    Runs cap (andX (U a) (U b) (R 2) (R 3)) σ (41 * Wb + 3)
      (Post U R σ0 Wb inp hd e (Function.update v a (v a &&& v b))) :=
  ⟨_, WXExec.wm (andW_spec cap Wb (uN U hab) (rN R (by decide)) σ _ _ (h.num a ha.ne0) (h.num b hb) (h.reg 2)
    (h.reg 3) hcap), h.sets a ha _⟩

theorem opHalf (a : Fin 10) (ha : Scr a) (h : Post U R σ0 Wb inp hd e v σ) (hlt : v a < 2 ^ Wb)
    (hcap : 2 * Wb + 1 ≤ cap) :
    Runs cap (BinW.half (U a) (R 3)) σ (34 * Wb + 3)
      (Post U R σ0 Wb inp hd e (Function.update v a (v a / 2))) :=
  ⟨_, BinW.half_spec cap Wb σ _ (h.num a ha.ne0) (h.reg 3) hlt (by omega), h.sets a ha _⟩

theorem opMul (a b c x : Fin 10) (hc : Scr c) (hx : Scr x) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) (hac : a ≠ c)
    (hax : a ≠ x) (hbc : b ≠ c) (hbx : b ≠ x) (hcx : c ≠ x) (h : Post U R σ0 Wb inp hd e v σ)
    (hlt : v a * v b < 2 ^ Wb) (hblt : v b < 2 ^ Wb) (hcap : 2 * Wb + 1 ≤ cap) :
    Runs cap (BinW.mul (U a) (U b) (U c) (U x) (R 2) (R 3) (R 4)) σ (mulCost Wb)
      (Post U R σ0 Wb inp hd e (Function.update (Function.update v c (v a * v b)) x 0)) :=
  ⟨_, BinW.mul_spec cap Wb (uN U hab) (uN U hac) (uN U hax) (uN U hbc) (uN U hbx) (uN U hcx) (rN R (by decide))
    (rN R (by decide)) (rN R (by decide)) σ _ _ _ _ (h.num a ha) (h.num b hb) (h.num c hc.ne0) (h.num x hx.ne0)
    (h.reg 2) (h.reg 3) (h.reg 4) hlt hblt hcap, (h.sets c hc _).sets x hx _⟩

theorem opDivmod (a b q mm x : Fin 10) (hq : Scr q) (hmm : Scr mm) (hx : Scr x) (ha : a ≠ 0) (hb : b ≠ 0)
    (haq : a ≠ q) (ham : a ≠ mm) (hax : a ≠ x) (hbq : b ≠ q) (hbm : b ≠ mm) (hbx : b ≠ x) (hqm : q ≠ mm)
    (hqx : q ≠ x) (hmx : mm ≠ x) (h : Post U R σ0 Wb inp hd e v σ)
    (hlt : v a < 2 ^ Wb) (hb0 : 0 < v b) (h2b : 2 * v b ≤ 2 ^ Wb) (hcap : 2 * Wb + 1 ≤ cap) :
    Runs cap (BinW.divmod (U a) (U b) (U q) (U mm) (U x) (R 2) (R 3) (R 5) (R 6)) σ (BinW.divCost Wb)
      (Post U R σ0 Wb inp hd e
        (Function.update (Function.update (Function.update v q (v a / v b)) mm (v a % v b)) x 0)) :=
  ⟨_, BinW.divmod_spec cap Wb (uN U haq) (uN U ham) (uN U hax) (uN U hbq) (uN U hbm) (uN U hbx) (uN U hqm)
    (uN U hqx) (uN U hmx) (rN R (by decide)) (rN R (by decide)) (rN R (by decide)) (rN R (by decide)) σ _ _ _ _ _
    (h.num a ha) (h.num b hb) (h.num q hq.ne0) (h.num mm hmm.ne0) (h.num x hx.ne0) (h.reg 2) (h.reg 3) (h.reg 5)
    (h.reg 6) hlt hb0 h2b hcap, ((h.sets q hq _).sets mm hmm _).sets x hx _⟩

/-- `if v a < v b then x := v y`. -/
def cmov (U : Fin 10 ↪ Fin (ns + 1)) (R : Fin 12 ↪ Fin nr) (a b x y : Fin 10) : WMX ns nr :=
  .seq (BinW.lt (U a) (U b) (R 2) (R 3))
    (.ifr (R 2) (.seq (WMX.dec (R 2)) (BinW.copy (U x) (U y) (R 2) (R 3))) WMX.skip)

def cmovCost (Wb : ℕ) : ℕ := (41 * Wb + 3) + 1 + ((1 + 1 + (41 * Wb + 3)) + 1)

theorem opCmov (a b x y : Fin 10) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) (hx : Scr x) (hy : y ≠ 0) (hxy : x ≠ y)
    (h : Post U R σ0 Wb inp hd e v σ) (halt : v a < 2 ^ Wb) (hblt : v b < 2 ^ Wb) (hcap : 2 * Wb + 1 ≤ cap) :
    Runs cap (cmov U R a b x y) σ (cmovCost Wb)
      (Post U R σ0 Wb inp hd e (if v a < v b then Function.update v x (v y) else v)) := by
  have hl := BinW.lt_spec cap Wb (uN U hab) (rN R (by decide)) σ _ _ (h.num a ha) (h.num b hb) (h.reg 2) (h.reg 3)
    halt hblt hcap
  refine Runs.seqE hl ?_
  by_cases hc : v a < v b
  · rw [if_pos hc]
    have hv : (σ.setv (R 2) (decide (v a < v b)).toNat).val (R 2) ≠ 0 := by simp [hc]
    have hd := WXExec.dec cap (R 2) (σ.setv (R 2) (decide (v a < v b)).toNat) (by simp [hc]; omega)
    have e1 : (σ.setv (R 2) (decide (v a < v b)).toNat).setv (R 2)
        ((σ.setv (R 2) (decide (v a < v b)).toNat).val (R 2) - 1) = σ := by
      rw [wsetv_setv]; simp [hc]
      have := h.reg 2; rw [← this]; exact wsetv_same σ (R 2)
    rw [e1] at hd
    have hcp := opCopy cap x y hx hy hxy h hcap
    exact (Runs.ifrT hv (Runs.seqE hd hcp)).cost (by omega)
  · rw [if_neg hc]
    have hv : (σ.setv (R 2) (decide (v a < v b)).toNat).val (R 2) = 0 := by simp [hc]
    have e1 : σ.setv (R 2) (decide (v a < v b)).toNat = σ := by
      simp [hc]; have := h.reg 2; rw [← this]; exact wsetv_same σ (R 2)
    rw [e1] at hv ⊢
    exact (Runs.ifrF hv (Runs.of (WXExec.skip cap σ) h)).cost (by omega)

end Ops

end NearCubicGates.Close.Expand
