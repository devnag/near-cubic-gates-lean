import Proof.Wire_3_5.GF2Primitive
import Proof.Wire_3_5.BlockBranch
import Proof.Wire_3_5.BlockCopy

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Block
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.GF2
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.SignedSortKey NearCubicWires.RepairOrdinary.RadixSemantics
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay overlay_write overlay_length)

/-! ## Step-level branches over `branchM` -/

theorem branch_true {t s₁ s₂ n : ℕ} (i : Fin t) {p : Machine t s₁} (q : Machine t s₂) {H H' : Fin t → ℕ}
    {A A' : Fin t → List Bool} (h : Step p n H A H' A') (hb : readTapeBit (A i) (H i) = true) :
    Step (branchM i p q) (n + 2) H A H' A' := by
  obtain ⟨r, hr, hh, ht, _⟩ := h
  obtain ⟨m, hm, htimed⟩ := branchM_timed i p q 1 (Or.inl rfl) H A (by simp [entryBit, hb]) n r hr
  obtain ⟨actual, ha, haf, _⟩ := htimed.run (by simp [branchM, RecoveryCalls.machine, RecoveryCalls.stopped])
  have more := runFrom_moreFuel (branchM i p q) m (n + 2 - m) _ actual ha
  rw [Nat.add_sub_of_le (by omega)] at more
  refine ⟨actual, more, ?_, ?_, by omega⟩
  · rw [haf, ← hh]; rfl
  · rw [haf, ← ht]; rfl

theorem branch_false {t s₁ s₂ n : ℕ} (i : Fin t) (p : Machine t s₁) {q : Machine t s₂} {H H' : Fin t → ℕ}
    {A A' : Fin t → List Bool} (h : Step q n H A H' A') (hb : readTapeBit (A i) (H i) = false) :
    Step (branchM i p q) (n + 2) H A H' A' := by
  obtain ⟨r, hr, hh, ht, _⟩ := h
  obtain ⟨m, hm, htimed⟩ := branchM_timed i p q 2 (Or.inr rfl) H A (by simp [entryBit, hb]) n r hr
  obtain ⟨actual, ha, haf, _⟩ := htimed.run (by simp [branchM, RecoveryCalls.machine, RecoveryCalls.stopped])
  have more := runFrom_moreFuel (branchM i p q) m (n + 2 - m) _ actual ha
  rw [Nat.add_sub_of_le (by omega)] at more
  refine ⟨actual, more, ?_, ?_, by omega⟩
  · rw [haf, ← hh]; rfl
  · rw [haf, ← ht]; rfl

/-! ## A docked stage that keeps the other heads where they are -/

theorem dockKeep {k s n u : ℕ} {M : Machine k s} {tin tout : Fin k → List Bool}
    (h : Step M n (fun _ => 0) tin (fun _ => 0) tout) (slots : Fin k → Fin u) (hi : Function.Injective slots)
    (H : Fin u → ℕ) (A : Fin u → List Bool) (hH : ∀ j, H (slots j) = 0) (hA : ∀ j, A (slots j) = tin j) :
    Step (RecoveryFocus.machine slots M) n H A H (RecoveryRootRound.install slots A tout) := by
  have hd := dockRun h slots hi H A hH hA
  have e : dockH slots H (fun _ => 0) = H := by
    funext i
    cases hp : RecoveryFocus.pick slots i with
    | none => simp [dockH, hp]
    | some j =>
      have he := RecoveryFocus.slot_of_pick slots hp
      simp only [dockH, hp]
      rw [← he, hH j]
  rwa [e] at hd

/-! ## The comparison fold into a cell -/

/-- One bit of the comparison, low bit first: a differing bit decides (the later bit is more significant). -/
def cmpStep (a b s : Bool) : Bool := if a == b then s else b

def foldBits (f : Bool → Bool → Bool → Bool) : Bool → List Bool → List Bool → Bool
  | s, a :: u, b :: v => foldBits f (f a b s) u v
  | s, _, _ => s

theorem foldCmp_value (u v : List Bool) (h : u.length = v.length) (s : Bool) :
    foldBits cmpStep s u v = if value u = value v then s else decide (value u < value v) := by
  induction u generalizing v s with
  | nil =>
    cases v with
    | nil => simp [foldBits, value]
    | cons b v => simp at h
  | cons a u ih =>
    cases v with
    | nil => simp at h
    | cons b v =>
      rw [foldBits, ih v (by simpa using h)]
      have hvu : value (a :: u) = a.toNat + 2 * value u := rfl
      have hvv : value (b :: v) = b.toNat + 2 * value v := rfl
      by_cases huv : value u = value v
      · rw [if_pos huv]
        by_cases hab : a = b
        · subst hab
          have he : value (a :: u) = value (a :: v) := by rw [hvu, hvv, huv]
          rw [if_pos he]
          simp [cmpStep]
        · have hne : value (a :: u) ≠ value (b :: v) := by
            rw [hvu, hvv, huv]; cases a <;> cases b <;> simp_all [Bool.toNat]
          rw [if_neg hne]
          have hlt : (value (a :: u) < value (b :: v)) ↔ b = true := by
            rw [hvu, hvv, huv]; cases a <;> cases b <;> simp_all [Bool.toNat]
          have hc : cmpStep a b s = b := by unfold cmpStep; cases a <;> cases b <;> simp_all
          rw [hc]
          apply Bool.eq_iff_iff.mpr
          rw [decide_eq_true_iff]
          exact hlt.symm
      · rw [if_neg huv]
        have hne : value (a :: u) ≠ value (b :: v) := by
          rw [hvu, hvv]; cases a <;> cases b <;> simp [Bool.toNat] <;> omega
        rw [if_neg hne]
        apply decide_eq_decide.mpr
        rw [hvu, hvv]
        cases a <;> cases b <;> simp [Bool.toNat] <;> omega

namespace FoldCell
open Three (act cfg)

/-- A fold of two framed words, the final state written into a cell. States `0`/`1` read a marker with state
`false`/`true`, `2`/`3` read a bit, `4` halts. -/
def machine (f : Bool → Bool → Bool → Bool) (init : Bool) : Machine 3 5 where
  descriptionBits := 0
  start := if init then 1 else 0
  halted := fun q => q.val == 4
  rule := fun q sc =>
    if q.val = 0 then
      some (if sc 0 then act 2 none none none .right .right .stay else act 4 none none (some false) .stay .stay .stay)
    else if q.val = 1 then
      some (if sc 0 then act 3 none none none .right .right .stay else act 4 none none (some true) .stay .stay .stay)
    else if q.val = 2 then
      some (if f (sc 0) (sc 1) false then act 1 none none none .right .right .stay
        else act 0 none none none .right .right .stay)
    else if q.val = 3 then
      some (if f (sc 0) (sc 1) true then act 1 none none none .right .right .stay
        else act 0 none none none .right .right .stay)
    else none

variable (f : Bool → Bool → Bool → Bool) (init : Bool)

def mark (s : Bool) : Fin 5 := if s then 1 else 0
def bitS (s : Bool) : Fin 5 := if s then 3 else 2

theorem mark_step (s : Bool) (X Y F : List Bool) (hx hy : ℕ) (hr : readTapeBit X hx = true) :
    step (machine f init) (cfg (mark s) X Y F hx hy 0) = some (cfg (bitS s) X Y F (hx + 1) (hy + 1) 0) := by
  cases s
  · exact Three.step_cfg (machine f init) 0 2 X Y F hx hy 0 none none none .right .right .stay (by simp [machine, hr])
  · exact Three.step_cfg (machine f init) 1 3 X Y F hx hy 0 none none none .right .right .stay (by simp [machine, hr])

theorem end_step (s c : Bool) (X Y : List Bool) (hx hy : ℕ) (hr : readTapeBit X hx = false) :
    step (machine f init) (cfg (mark s) X Y [c] hx hy 0) = some (cfg 4 X Y [s] hx hy 0) := by
  cases s
  · show step (machine f init) (cfg 0 X Y [c] hx hy 0) = some (cfg 4 X Y [false] hx hy 0)
    rw [Three.step_cfg (machine f init) 0 4 X Y [c] hx hy 0 none none (some false) .stay .stay .stay
      (by simp [machine, hr])]
    simp [Two.wr, HeadMove.apply, writeTapeBit]
  · show step (machine f init) (cfg 1 X Y [c] hx hy 0) = some (cfg 4 X Y [true] hx hy 0)
    rw [Three.step_cfg (machine f init) 1 4 X Y [c] hx hy 0 none none (some true) .stay .stay .stay
      (by simp [machine, hr])]
    simp [Two.wr, HeadMove.apply, writeTapeBit]

theorem bit_step (s a b : Bool) (X Y F : List Bool) (hx hy : ℕ) (ha : readTapeBit X hx = a) (hb : readTapeBit Y hy = b) :
    step (machine f init) (cfg (bitS s) X Y F hx hy 0) = some (cfg (mark (f a b s)) X Y F (hx + 1) (hy + 1) 0) := by
  cases s <;> cases h : f a b _
  · show step (machine f init) (cfg 2 X Y F hx hy 0) = some (cfg 0 X Y F (hx + 1) (hy + 1) 0)
    exact Three.step_cfg (machine f init) 2 0 X Y F hx hy 0 none none none .right .right .stay
      (by simp [machine, ha, hb, h])
  · show step (machine f init) (cfg 2 X Y F hx hy 0) = some (cfg 1 X Y F (hx + 1) (hy + 1) 0)
    exact Three.step_cfg (machine f init) 2 1 X Y F hx hy 0 none none none .right .right .stay
      (by simp [machine, ha, hb, h])
  · show step (machine f init) (cfg 3 X Y F hx hy 0) = some (cfg 0 X Y F (hx + 1) (hy + 1) 0)
    exact Three.step_cfg (machine f init) 3 0 X Y F hx hy 0 none none none .right .right .stay
      (by simp [machine, ha, hb, h])
  · show step (machine f init) (cfg 3 X Y F hx hy 0) = some (cfg 1 X Y F (hx + 1) (hy + 1) 0)
    exact Three.step_cfg (machine f init) 3 1 X Y F hx hy 0 none none none .right .right .stay
      (by simp [machine, ha, hb, h])

theorem timed (c : Bool) (u : List Bool) : ∀ (v : List Bool) (s : Bool), u.length = v.length →
    RecoveryExecution.Timed (machine f init) (2 * u.length + 1)
      (cfg (mark s) (frame u) (frame v) [c] 0 0 0)
      (cfg 4 (frame u) (frame v) [foldBits f s u v] (2 * u.length) (2 * u.length) 0) := by
  suffices key : ∀ (v preX preY : List Bool) (s : Bool), u.length = v.length →
      RecoveryExecution.Timed (machine f init) (2 * u.length + 1)
        (cfg (mark s) (preX ++ frame u) (preY ++ frame v) [c] preX.length preY.length 0)
        (cfg 4 (preX ++ frame u) (preY ++ frame v) [foldBits f s u v] (preX.length + 2 * u.length)
          (preY.length + 2 * u.length) 0) by
    intro v s hl
    simpa using key v [] [] s hl
  induction u with
  | nil =>
    intro v preX preY s _
    have hs := end_step f init s c (preX ++ frame []) (preY ++ frame v) preX.length preY.length
      (by simpa [frame] using Streaming.read_append preX [] false)
    simpa [frame, foldBits] using RecoveryExecution.Timed.single (p := machine f init) (by cases s <;> rfl) hs
  | cons a u ih =>
    intro v preX preY s hl
    obtain ⟨b, v, rfl⟩ : ∃ b v', v = b :: v' := by
      cases v with
      | nil => simp at hl
      | cons b v => exact ⟨b, v, rfl⟩
    have hl' : u.length = v.length := by simpa using hl
    have hr1 : readTapeBit (preX ++ frame (a :: u)) preX.length = true := by
      simpa [frame] using Streaming.read_append preX (a :: frame u) true
    have hra : readTapeBit (preX ++ frame (a :: u)) (preX.length + 1) = a := by
      simpa [frame] using Streaming.read_append (preX ++ [true]) (frame u) a
    have hrb : readTapeBit (preY ++ frame (b :: v)) (preY.length + 1) = b := by
      simpa [frame] using Streaming.read_append (preY ++ [true]) (frame v) b
    have hs1 := mark_step f init s (preX ++ frame (a :: u)) (preY ++ frame (b :: v)) [c] preX.length preY.length hr1
    have hs2 := bit_step f init s a b (preX ++ frame (a :: u)) (preY ++ frame (b :: v)) [c] (preX.length + 1)
      (preY.length + 1) hra hrb
    have t1 := RecoveryExecution.Timed.single (p := machine f init) (by cases s <;> rfl) hs1
    have t2 := RecoveryExecution.Timed.single (p := machine f init) (by cases s <;> rfl) hs2
    have tail := ih v (preX ++ [true, a]) (preY ++ [true, b]) (f a b s) hl'
    have eX : preX ++ [true, a] ++ frame u = preX ++ frame (a :: u) := by simp [frame]
    have eY : preY ++ [true, b] ++ frame v = preY ++ frame (b :: v) := by simp [frame]
    have e3 : (preX ++ [true, a]).length = preX.length + 1 + 1 := by simp
    have e4 : (preY ++ [true, b]).length = preY.length + 1 + 1 := by simp
    have e5 : foldBits f (f a b s) u v = foldBits f s (a :: u) (b :: v) := rfl
    have e7 : preX.length + 1 + 1 + 2 * u.length = preX.length + 2 * (a :: u).length := by simp; omega
    have e8 : preY.length + 1 + 1 + 2 * u.length = preY.length + 2 * (a :: u).length := by simp; omega
    rw [eX, eY, e3, e4, e5, e7, e8] at tail
    have := (t1.trans t2).trans tail
    rwa [show 1 + 1 + (2 * u.length + 1) = 2 * (a :: u).length + 1 by simp; omega] at this

theorem run (u v : List Bool) (c : Bool) (hl : u.length = v.length) :
    Step (machine f init) (2 * u.length + 1) ![0, 0, 0] ![frame u, frame v, [c]]
      ![2 * u.length, 2 * u.length, 0] ![frame u, frame v, [foldBits f init u v]] := by
  obtain ⟨r, hr, hf, hs⟩ := (timed f init c u v init hl).run rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  exacts [r, by cases init <;> exact hr, by rw [hf]; rfl, by rw [hf]; rfl, by omega]

end FoldCell

/-! ## In-place ripple arithmetic `S := ripple g h c₀ S C` (addition, subtraction) -/

/-- A ripple over two words, low bit first: output bit `g a b c`, next carry `h a b c`. -/
def ripple (g h : Bool → Bool → Bool → Bool) : Bool → List Bool → List Bool → List Bool
  | c, a :: u, b :: v => g a b c :: ripple g h (h a b c) u v
  | _, _, _ => []

def sum3 (a b c : Bool) : Bool := xor (xor a b) c
def carry3 (a b c : Bool) : Bool := (a && b) || (c && xor a b)
def borrow3 (a b c : Bool) : Bool := (!a && b) || (!(xor a b) && c)

theorem ripple_add (d x y : ℕ) (c : Bool) :
    ripple sum3 carry3 c (binary d x) (binary d y) = binary d (x + y + c.toNat) := by
  induction d generalizing x y c with
  | zero => rfl
  | succ d ih =>
    have e1 : binary (d + 1) x = (x % 2 == 1) :: binary d (x / 2) := rfl
    have e2 : binary (d + 1) y = (y % 2 == 1) :: binary d (y / 2) := rfl
    have e3 : binary (d + 1) (x + y + c.toNat) =
        ((x + y + c.toNat) % 2 == 1) :: binary d ((x + y + c.toNat) / 2) := rfl
    rw [e1, e2, e3]
    simp only [ripple]
    rw [ih]
    congr 1
    · rcases Nat.mod_two_eq_zero_or_one x with hx | hx <;> rcases Nat.mod_two_eq_zero_or_one y with hy | hy <;>
        cases c <;> simp [sum3, hx, hy, Nat.add_mod]
    · congr 1
      rcases Nat.mod_two_eq_zero_or_one x with hx | hx <;> rcases Nat.mod_two_eq_zero_or_one y with hy | hy <;>
        cases c <;> simp [carry3, hx, hy] <;> omega

theorem ripple_sub (d x y : ℕ) (c : Bool) (hxy : y + c.toNat ≤ x) :
    ripple sum3 borrow3 c (binary d x) (binary d y) = binary d (x - y - c.toNat) := by
  induction d generalizing x y c with
  | zero => rfl
  | succ d ih =>
    have e1 : binary (d + 1) x = (x % 2 == 1) :: binary d (x / 2) := rfl
    have e2 : binary (d + 1) y = (y % 2 == 1) :: binary d (y / 2) := rfl
    have e3 : binary (d + 1) (x - y - c.toNat) =
        ((x - y - c.toNat) % 2 == 1) :: binary d ((x - y - c.toNat) / 2) := rfl
    rw [e1, e2, e3]
    simp only [ripple]
    have hb : y / 2 + (borrow3 (x % 2 == 1) (y % 2 == 1) c).toNat ≤ x / 2 := by
      rcases Nat.mod_two_eq_zero_or_one x with hx | hx <;> rcases Nat.mod_two_eq_zero_or_one y with hy | hy <;>
        cases c <;> simp [borrow3, hx, hy, Bool.toNat] at hxy ⊢ <;> omega
    rw [ih _ _ _ hb]
    congr 1
    · rcases Nat.mod_two_eq_zero_or_one x with hx | hx <;> rcases Nat.mod_two_eq_zero_or_one y with hy | hy <;>
        cases c <;> simp [sum3, hx, hy, Bool.toNat] at hxy ⊢ <;> omega
    · congr 1
      rcases Nat.mod_two_eq_zero_or_one x with hx | hx <;> rcases Nat.mod_two_eq_zero_or_one y with hy | hy <;>
        cases c <;> simp [borrow3, hx, hy, Bool.toNat] at hxy ⊢ <;> omega

namespace RippleIn
open Two (act cfg wr)

/-- Tape 0 the word (in place), tape 1 the operand. States `0`/`1` read a marker with carry `false`/`true`,
`2`/`3` rewrite a bit, `4` halts. -/
def machine (g h : Bool → Bool → Bool → Bool) (c₀ : Bool) : Machine 2 5 where
  descriptionBits := 0
  start := if c₀ then 1 else 0
  halted := fun q => q.val == 4
  rule := fun q sc =>
    if q.val = 0 then some (if sc 0 then act 2 none none .right .right else act 4 none none .stay .stay)
    else if q.val = 1 then some (if sc 0 then act 3 none none .right .right else act 4 none none .stay .stay)
    else if q.val = 2 then
      some (if h (sc 0) (sc 1) false then act 1 (some (g (sc 0) (sc 1) false)) none .right .right
        else act 0 (some (g (sc 0) (sc 1) false)) none .right .right)
    else if q.val = 3 then
      some (if h (sc 0) (sc 1) true then act 1 (some (g (sc 0) (sc 1) true)) none .right .right
        else act 0 (some (g (sc 0) (sc 1) true)) none .right .right)
    else none

variable (g h : Bool → Bool → Bool → Bool) (c₀ : Bool)

def mark (c : Bool) : Fin 5 := if c then 1 else 0
def bitS (c : Bool) : Fin 5 := if c then 3 else 2

theorem mark_step (c : Bool) (S C : List Bool) (hs hc : ℕ) (hr : readTapeBit S hs = true) :
    step (machine g h c₀) (cfg (mark c) S C hs hc) = some (cfg (bitS c) S C (hs + 1) (hc + 1)) := by
  cases c
  · exact Two.step_cfg (machine g h c₀) 0 2 S C hs hc none none .right .right (by simp [machine, hr])
  · exact Two.step_cfg (machine g h c₀) 1 3 S C hs hc none none .right .right (by simp [machine, hr])

theorem end_step (c : Bool) (S C : List Bool) (hs hc : ℕ) (hr : readTapeBit S hs = false) :
    step (machine g h c₀) (cfg (mark c) S C hs hc) = some (cfg 4 S C hs hc) := by
  cases c
  · exact Two.step_cfg (machine g h c₀) 0 4 S C hs hc none none .stay .stay (by simp [machine, hr])
  · exact Two.step_cfg (machine g h c₀) 1 4 S C hs hc none none .stay .stay (by simp [machine, hr])

theorem bit_step (c a b : Bool) (S C : List Bool) (hs hc : ℕ) (ha : readTapeBit S hs = a) (hb : readTapeBit C hc = b) :
    step (machine g h c₀) (cfg (bitS c) S C hs hc) =
      some (cfg (mark (h a b c)) (writeTapeBit S hs (g a b c)) C (hs + 1) (hc + 1)) := by
  cases c <;> cases hh : h a b _
  · show step (machine g h c₀) (cfg 2 S C hs hc) = some (cfg 0 (writeTapeBit S hs (g a b false)) C (hs + 1) (hc + 1))
    exact Two.step_cfg (machine g h c₀) 2 0 S C hs hc (some (g a b false)) none .right .right
      (by simp [machine, ha, hb, hh])
  · show step (machine g h c₀) (cfg 2 S C hs hc) = some (cfg 1 (writeTapeBit S hs (g a b false)) C (hs + 1) (hc + 1))
    exact Two.step_cfg (machine g h c₀) 2 1 S C hs hc (some (g a b false)) none .right .right
      (by simp [machine, ha, hb, hh])
  · show step (machine g h c₀) (cfg 3 S C hs hc) = some (cfg 0 (writeTapeBit S hs (g a b true)) C (hs + 1) (hc + 1))
    exact Two.step_cfg (machine g h c₀) 3 0 S C hs hc (some (g a b true)) none .right .right
      (by simp [machine, ha, hb, hh])
  · show step (machine g h c₀) (cfg 3 S C hs hc) = some (cfg 1 (writeTapeBit S hs (g a b true)) C (hs + 1) (hc + 1))
    exact Two.step_cfg (machine g h c₀) 3 1 S C hs hc (some (g a b true)) none .right .right
      (by simp [machine, ha, hb, hh])

theorem timed (u : List Bool) : ∀ (v preS preC : List Bool) (c : Bool), u.length = v.length →
    RecoveryExecution.Timed (machine g h c₀) (2 * u.length + 1)
      (cfg (mark c) (preS ++ frame u) (preC ++ frame v) preS.length preC.length)
      (cfg 4 (preS ++ frame (ripple g h c u v)) (preC ++ frame v) (preS.length + 2 * u.length)
        (preC.length + 2 * u.length)) := by
  induction u with
  | nil =>
    intro v preS preC c _
    have hs := end_step g h c₀ c (preS ++ frame []) (preC ++ frame v) preS.length preC.length
      (by simpa [frame] using Streaming.read_append preS [] false)
    simpa [frame, ripple] using RecoveryExecution.Timed.single (p := machine g h c₀) (by cases c <;> rfl) hs
  | cons a u ih =>
    intro v preS preC c hl
    obtain ⟨b, v, rfl⟩ : ∃ b v', v = b :: v' := by
      cases v with
      | nil => simp at hl
      | cons b v => exact ⟨b, v, rfl⟩
    have hl' : u.length = v.length := by simpa using hl
    have hr1 : readTapeBit (preS ++ frame (a :: u)) preS.length = true := by
      simpa [frame] using Streaming.read_append preS (a :: frame u) true
    have hra : readTapeBit (preS ++ frame (a :: u)) (preS.length + 1) = a := by
      simpa [frame] using Streaming.read_append (preS ++ [true]) (frame u) a
    have hrb : readTapeBit (preC ++ frame (b :: v)) (preC.length + 1) = b := by
      simpa [frame] using Streaming.read_append (preC ++ [true]) (frame v) b
    have hs1 := mark_step g h c₀ c (preS ++ frame (a :: u)) (preC ++ frame (b :: v)) preS.length preC.length hr1
    have hs2 := bit_step g h c₀ c a b (preS ++ frame (a :: u)) (preC ++ frame (b :: v)) (preS.length + 1)
      (preC.length + 1) hra hrb
    have hw : writeTapeBit (preS ++ frame (a :: u)) (preS.length + 1) (g a b c) = preS ++ [true, g a b c] ++ frame u := by
      simpa [frame] using write_mid (preS ++ [true]) (frame u) a (g a b c)
    rw [hw] at hs2
    have t1 := RecoveryExecution.Timed.single (p := machine g h c₀) (by cases c <;> rfl) hs1
    have t2 := RecoveryExecution.Timed.single (p := machine g h c₀) (by cases c <;> rfl) hs2
    have tail := ih v (preS ++ [true, g a b c]) (preC ++ [true, b]) (h a b c) hl'
    have eC : preC ++ [true, b] ++ frame v = preC ++ frame (b :: v) := by simp [frame]
    have e3 : (preS ++ [true, g a b c]).length = preS.length + 1 + 1 := by simp
    have e4 : (preC ++ [true, b]).length = preC.length + 1 + 1 := by simp
    have e5 : preS ++ [true, g a b c] ++ frame (ripple g h (h a b c) u v) = preS ++ frame (ripple g h c (a :: u) (b :: v)) := by
      simp [frame, ripple]
    have e7 : preS.length + 1 + 1 + 2 * u.length = preS.length + 2 * (a :: u).length := by simp; omega
    have e8 : preC.length + 1 + 1 + 2 * u.length = preC.length + 2 * (a :: u).length := by simp; omega
    rw [eC, e3, e4, e5, e7, e8] at tail
    have := (t1.trans t2).trans tail
    rwa [show 1 + 1 + (2 * u.length + 1) = 2 * (a :: u).length + 1 by simp; omega] at this

theorem run (u v : List Bool) (hl : u.length = v.length) :
    Step (machine g h c₀) (2 * u.length + 1) ![0, 0] ![frame u, frame v]
      ![2 * u.length, 2 * u.length] ![frame (ripple g h c₀ u v), frame v] := by
  obtain ⟨r, hr, hf, hs⟩ := (timed g h c₀ u v [] [] c₀ hl).run rfl
  simp only [List.nil_append, List.length_nil, Nat.zero_add] at hr hf
  refine ⟨r, by cases c₀ <;> exact hr, ?_, ?_, by omega⟩
  · rw [hf]; rfl
  · rw [hf]; rfl

end RippleIn

/-! ## The merge, as pure semantics -/

/-- The register after loading up to record `k` of `L`: the current record, the last one once `L` is exhausted, or
the stale word `r0` if `L` is empty. -/
def reg (L : List (List Bool)) (k : ℕ) (r0 : List Bool) : List Bool := ((L.take (k + 1)).getLast?).getD r0

/-- The stream head after loading up to record `k`. -/
def pos (L : List (List Bool)) (k : ℕ) : ℕ := ((L.take (k + 1)).flatMap frame).length

/-- The merge state: records of `A` counted, records of `B` processed, the accumulated sum, the last test. -/
structure MS where
  i : ℕ
  j : ℕ
  s : ℕ
  t : Bool

/-- One merge step, exactly as the machine takes it. -/
def mstep (A B : List (List Bool)) (init : Bool) (ra0 rb0 : List Bool) (m : MS) : MS :=
  if (foldBits cmpStep init (reg A m.i ra0) (reg B m.j rb0) && decide (m.i < A.length)) then
    ⟨m.i + 1, m.j, m.s, true⟩
  else ⟨m.i, m.j + 1, m.s + m.i, false⟩

def mstate (A B : List (List Bool)) (init : Bool) (ra0 rb0 : List Bool) (t0 : Bool) : ℕ → MS
  | 0 => ⟨0, 0, 0, t0⟩
  | k + 1 => mstep A B init ra0 rb0 (mstate A B init ra0 rb0 t0 k)

theorem reg_lt (L : List (List Bool)) (k : ℕ) (r0 : List Bool) (hk : k < L.length) : reg L k r0 = L[k] := by
  unfold reg
  rw [List.getLast?_eq_getElem?, List.length_take, Nat.min_eq_left (by omega)]
  rw [List.getElem?_take, if_pos (by omega), show k + 1 - 1 = k by omega, List.getElem?_eq_getElem hk]
  rfl

theorem reg_ge (L : List (List Bool)) (k : ℕ) (r0 : List Bool) (hk : L.length ≤ k + 1) :
    reg L (k + 1) r0 = reg L k r0 := by
  unfold reg
  rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)]

/-- The relation the pass counts: `≤` (init `true`) or `<` (init `false`) on values. -/
def rel (init : Bool) (a b : List Bool) : Prop := value a < value b ∨ (init = true ∧ value a = value b)

instance (init : Bool) (a b : List Bool) : Decidable (rel init a b) := by unfold rel; infer_instance

theorem foldCmp_rel (init : Bool) (a b : List Bool) (h : a.length = b.length) :
    foldBits cmpStep init a b = decide (rel init a b) := by
  rw [foldCmp_value a b h]
  unfold rel
  by_cases he : value a = value b
  · rw [if_pos he]; cases init <;> simp [he]
  · rw [if_neg he]; apply decide_eq_decide.mpr; simp [he]

/-- The merge invariant along the path. -/
def Inv (A B : List (List Bool)) (init : Bool) (m : MS) : Prop :=
  m.i ≤ A.length ∧ m.j ≤ B.length ∧
    (∀ i' (hi' : i' < A.length), i' < m.i → ∀ j' (hj' : j' < B.length), m.j ≤ j' → rel init A[i'] B[j']) ∧
    m.s = ((B.take m.j).map (fun b => A.countP (fun a => decide (rel init a b)))).sum

theorem rel_mono_right (init : Bool) (a b b' : List Bool) (hbb : value b ≤ value b') (h : rel init a b) :
    rel init a b' := by
  unfold rel at *
  rcases h with h | ⟨hi, h⟩
  · exact Or.inl (by omega)
  · rcases Nat.lt_or_ge (value a) (value b') with h' | h'
    · exact Or.inl h'
    · exact Or.inr ⟨hi, by omega⟩

theorem not_rel_mono_left (init : Bool) (a a' b : List Bool) (haa : value a ≤ value a') (h : ¬ rel init a b) :
    ¬ rel init a' b := by
  unfold rel at *
  intro h'
  apply h
  rcases h' with h' | ⟨hi, h'⟩
  · exact Or.inl (by omega)
  · rcases Nat.lt_or_ge (value a) (value b) with h'' | h''
    · exact Or.inl h''
    · exact Or.inr ⟨hi, by omega⟩

/-- When the `i` counted records of `A` are exactly those related to `b`, the count is `i`. -/
theorem countP_prefix (A : List (List Bool)) (p : List Bool → Bool) (i : ℕ) (hi : i ≤ A.length)
    (hyes : ∀ i' (h : i' < i), p (A[i']'(by omega)) = true) (hno : ∀ i' (h : i' < A.length), i ≤ i' → p A[i'] = false) :
    A.countP p = i := by
  have hsplit : A = A.take i ++ A.drop i := (List.take_append_drop i A).symm
  rw [hsplit, List.countP_append]
  have h1 : (A.take i).countP p = i := by
    rw [List.countP_eq_length.mpr]
    · simp; omega
    · intro x hx
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
      rw [List.getElem_take]
      exact hyes k (by simp at hk; omega)
  have h2 : (A.drop i).countP p = 0 := by
    rw [List.countP_eq_zero]
    intro x hx
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
    rw [List.getElem_drop]
    have := hno (i + k) (by simp at hk; omega) (by omega)
    simp [this]
  omega

theorem mstep_inv (A B : List (List Bool)) (init : Bool) (ra0 rb0 : List Bool) (W : ℕ)
    (hA : ∀ a ∈ A, a.length = W) (hB : ∀ b ∈ B, b.length = W)
    (sA : A.Pairwise (fun a b => value a ≤ value b)) (sB : B.Pairwise (fun a b => value a ≤ value b))
    (m : MS) (hm : Inv A B init m) (hj : m.j < B.length) : Inv A B init (mstep A B init ra0 rb0 m) := by
  obtain ⟨hi, hjle, hall, hs⟩ := hm
  have hregB : reg B m.j rb0 = B[m.j] := reg_lt B m.j rb0 hj
  unfold mstep
  by_cases hc : (foldBits cmpStep init (reg A m.i ra0) (reg B m.j rb0) && decide (m.i < A.length)) = true
  · rw [if_pos hc]
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨hcmp, hiA⟩ := hc
    have hregA : reg A m.i ra0 = A[m.i] := reg_lt A m.i ra0 hiA
    rw [hregA, hregB, foldCmp_rel init _ _ (by rw [hA _ (List.getElem_mem _), hB _ (List.getElem_mem _)])] at hcmp
    simp only [decide_eq_true_eq] at hcmp
    refine ⟨by simp; omega, hjle, fun i' hi' hi'' j' hj' hjj => ?_, hs⟩
    rcases Nat.lt_or_ge i' m.i with h | h
    · exact hall i' hi' h j' hj' hjj
    · have : i' = m.i := by simp at hi''; omega
      subst this
      rcases Nat.eq_or_lt_of_le hjj with h' | h'
      · subst h'; exact hcmp
      · exact rel_mono_right init _ _ _ ((List.pairwise_iff_getElem.mp sB) m.j j' hj hj' h') hcmp
  · rw [if_neg hc]
    refine ⟨hi, by simp; omega, fun i' hi' hi'' j' hj' hjj => hall i' hi' hi'' j' hj' (by simp at hjj; omega), ?_⟩
    rw [hs, List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some, List.map_append, List.sum_append]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    congr 1
    symm
    apply countP_prefix A _ m.i hi
    · intro i' h
      simp only [decide_eq_true_eq]
      exact hall i' (by omega) h m.j hj le_rfl
    · intro i' h hge
      simp only [decide_eq_false_iff_not]
      have hnot : ¬ rel init A[m.i] B[m.j] ∨ ¬ m.i < A.length := by
        simp only [Bool.and_eq_true, decide_eq_true_eq, not_and_or] at hc
        rcases hc with hc | hc
        · left
          by_cases hiA : m.i < A.length
          · rw [reg_lt A m.i ra0 hiA, hregB, foldCmp_rel init _ _ (by rw [hA _ (List.getElem_mem _),
              hB _ (List.getElem_mem _)])] at hc
            simpa using hc
          · exact absurd (by omega : m.i < A.length) hiA
        · right; exact hc
      rcases hnot with hn | hn
      · rcases Nat.eq_or_lt_of_le hge with h' | h'
        · subst h'; exact hn
        · exact not_rel_mono_left init _ _ _ ((List.pairwise_iff_getElem.mp sA) m.i i' (by omega) h h') hn
      · exact absurd (by omega : m.i < A.length) hn

def jSlotsCMP : Fin 4 → Fin (11 + 1) := ![2, 3, 7, 11]
theorem install_jCMP (A : Fin (11 + 1) → List Bool) (v : Fin 4 → List Bool) :
    RecoveryRootRound.install jSlotsCMP A v = ![A 0, A 1, v 0, v 1, A 4, A 5, A 6, v 2, A 8, A 9, A 10, v 3] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 1
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 2
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 3
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

def jSlotsAND : Fin 3 → Fin (11 + 1) := ![7, 8, 10]
theorem install_jAND (A : Fin (11 + 1) → List Bool) (v : Fin 3 → List Bool) :
    RecoveryRootRound.install jSlotsAND A v = ![A 0, A 1, A 2, A 3, A 4, A 5, A 6, v 0, v 1, A 9, v 2, A 11] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 1
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 2
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

def jSlotsINC : Fin 3 → Fin (11 + 1) := ![4, 7, 11]
theorem install_jINC (A : Fin (11 + 1) → List Bool) (v : Fin 3 → List Bool) :
    RecoveryRootRound.install jSlotsINC A v = ![A 0, A 1, A 2, A 3, v 0, A 5, A 6, v 1, A 8, A 9, A 10, v 2] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 1
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 2
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

def jSlotsADD : Fin 3 → Fin (11 + 1) := ![5, 4, 11]
theorem install_jADD (A : Fin (11 + 1) → List Bool) (v : Fin 3 → List Bool) :
    RecoveryRootRound.install jSlotsADD A v = ![A 0, A 1, A 2, A 3, v 1, v 0, A 6, A 7, A 8, A 9, A 10, v 2] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 1
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 2
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

def jSlotsCLRC : Fin 4 → Fin (11 + 1) := ![4, 5, 10, 11]
theorem install_jCLRC (A : Fin (11 + 1) → List Bool) (v : Fin 4 → List Bool) :
    RecoveryRootRound.install jSlotsCLRC A v = ![A 0, A 1, A 2, A 3, v 0, v 1, A 6, A 7, A 8, A 9, v 2, v 3] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 1
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 2
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 3
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

def jSlotsCLRS : Fin 4 → Fin (11 + 1) := ![5, 4, 10, 11]
theorem install_jCLRS (A : Fin (11 + 1) → List Bool) (v : Fin 4 → List Bool) :
    RecoveryRootRound.install jSlotsCLRS A v = ![A 0, A 1, A 2, A 3, v 1, v 0, A 6, A 7, A 8, A 9, v 2, v 3] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 1
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 2
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 3
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

def jSlotsCPA : Fin 3 → Fin (11 + 1) := ![0, 2, 11]
theorem install_jCPA (A : Fin (11 + 1) → List Bool) (v : Fin 3 → List Bool) :
    RecoveryRootRound.install jSlotsCPA A v = ![v 0, A 1, v 1, A 3, A 4, A 5, A 6, A 7, A 8, A 9, A 10, v 2] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 1
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 2
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)
theorem dockH_jCPA (H : Fin (11 + 1) → ℕ) (v : Fin 3 → ℕ) :
    dockH jSlotsCPA H v = ![v 0, H 1, v 1, H 3, H 4, H 5, H 6, H 7, H 8, H 9, H 10, v 2] := by
  funext i; fin_cases i
  all_goals first
    | exact dockH_slot _ (by decide) _ _ 0
    | exact dockH_slot _ (by decide) _ _ 1
    | exact dockH_slot _ (by decide) _ _ 2
    | exact dockH_other _ _ _ _ (by decide)

def jSlotsCPB : Fin 3 → Fin (11 + 1) := ![1, 3, 11]
theorem install_jCPB (A : Fin (11 + 1) → List Bool) (v : Fin 3 → List Bool) :
    RecoveryRootRound.install jSlotsCPB A v = ![A 0, v 0, A 2, v 1, A 4, A 5, A 6, A 7, A 8, A 9, A 10, v 2] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 1
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 2
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)
theorem dockH_jCPB (H : Fin (11 + 1) → ℕ) (v : Fin 3 → ℕ) :
    dockH jSlotsCPB H v = ![H 0, v 0, H 2, v 1, H 4, H 5, H 6, H 7, H 8, H 9, H 10, v 2] := by
  funext i; fin_cases i
  all_goals first
    | exact dockH_slot _ (by decide) _ _ 0
    | exact dockH_slot _ (by decide) _ _ 1
    | exact dockH_slot _ (by decide) _ _ 2
    | exact dockH_other _ _ _ _ (by decide)

def jSlotsNA : Fin 1 → Fin (11 + 1) := ![0]
theorem install_jNA (A : Fin (11 + 1) → List Bool) (v : Fin 1 → List Bool) :
    RecoveryRootRound.install jSlotsNA A v = ![v 0, A 1, A 2, A 3, A 4, A 5, A 6, A 7, A 8, A 9, A 10, A 11] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)
theorem dockH_jNA (H : Fin (11 + 1) → ℕ) (v : Fin 1 → ℕ) :
    dockH jSlotsNA H v = ![v 0, H 1, H 2, H 3, H 4, H 5, H 6, H 7, H 8, H 9, H 10, H 11] := by
  funext i; fin_cases i
  all_goals first
    | exact dockH_slot _ (by decide) _ _ 0
    | exact dockH_other _ _ _ _ (by decide)

def jSlotsNB : Fin 1 → Fin (11 + 1) := ![1]
theorem install_jNB (A : Fin (11 + 1) → List Bool) (v : Fin 1 → List Bool) :
    RecoveryRootRound.install jSlotsNB A v = ![A 0, v 0, A 2, A 3, A 4, A 5, A 6, A 7, A 8, A 9, A 10, A 11] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)
theorem dockH_jNB (H : Fin (11 + 1) → ℕ) (v : Fin 1 → ℕ) :
    dockH jSlotsNB H v = ![H 0, v 0, H 2, H 3, H 4, H 5, H 6, H 7, H 8, H 9, H 10, H 11] := by
  funext i; fin_cases i
  all_goals first
    | exact dockH_slot _ (by decide) _ _ 0
    | exact dockH_other _ _ _ _ (by decide)

def jSlotsSETA : Fin 3 → Fin (11 + 1) := ![8, 9, 10]
theorem install_jSETA (A : Fin (11 + 1) → List Bool) (v : Fin 3 → List Bool) :
    RecoveryRootRound.install jSlotsSETA A v = ![A 0, A 1, A 2, A 3, A 4, A 5, A 6, A 7, v 0, v 1, v 2, A 11] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 1
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 2
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

def jSlotsSETB : Fin 3 → Fin (11 + 1) := ![9, 8, 10]
theorem install_jSETB (A : Fin (11 + 1) → List Bool) (v : Fin 3 → List Bool) :
    RecoveryRootRound.install jSlotsSETB A v = ![A 0, A 1, A 2, A 3, A 4, A 5, A 6, A 7, v 1, v 0, v 2, A 11] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 1
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 2
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

/-! ## The merge pass machine (12 tapes)

Tapes: 0 `A` and 1 `B` (the streams); 2 `RA` and 3 `RB` (the registers); 4 `CA` (the count); 5 the pass's sum;
6 the other pass's sum (untouched); 7 `T`, 8 `AV`, 9 `BV` (cells); 10 a spare cell; 11 the rewind log. -/

def andOp : Bool → Bool → Bool → Bool := fun t a _ => t && a
def sel2A : Fin 2 → Bool := ![true, false]
def sel2B : Fin 2 → Bool := ![true, true]
def selR : Fin 2 → Bool := ![false, true]

noncomputable def jCmp (init : Bool) :=
  RecoveryFocus.machine jSlotsCMP (MaskedReset.machine (FoldCell.machine cmpStep init) sel3)
noncomputable def jAnd := RecoveryFocus.machine jSlotsAND (CellOp.machine andOp)
noncomputable def jInc := RecoveryFocus.machine jSlotsINC (MaskedReset.machine IncFlag.machine sel2A)
noncomputable def jAdd := RecoveryFocus.machine jSlotsADD (MaskedReset.machine (RippleIn.machine sum3 carry3 false) sel2B)
noncomputable def jClrC := RecoveryFocus.machine jSlotsCLRC (MaskedReset.machine (ZipFlag.machine clearG) sel3)
noncomputable def jClrS := RecoveryFocus.machine jSlotsCLRS (MaskedReset.machine (ZipFlag.machine clearG) sel3)
noncomputable def jCpA := RecoveryFocus.machine jSlotsCPA (MaskedReset.machine CopyO.machine selR)
noncomputable def jCpB := RecoveryFocus.machine jSlotsCPB (MaskedReset.machine CopyO.machine selR)
noncomputable def jNA := RecoveryFocus.machine jSlotsNA nudgeM
noncomputable def jNB := RecoveryFocus.machine jSlotsNB nudgeM
noncomputable def jSetA (b : Bool) := RecoveryFocus.machine jSlotsSETA (CellOp.machine (fun _ _ _ => b))
noncomputable def jSetB (b : Bool) := RecoveryFocus.machine jSlotsSETB (CellOp.machine (fun _ _ _ => b))
/-- Load the next record of `A` into `RA` (and set `AV`), or clear `AV` at the terminator. -/
noncomputable def jLoadA := branchM 0 (Composition.machine (Composition.machine jCpA jNA) (jSetA true)) (jSetA false)
noncomputable def jLoadB := branchM 1 (Composition.machine (Composition.machine jCpB jNB) (jSetB true)) (jSetB false)

section PassStages
variable (cap : ℕ) (h0 h1 : ℕ) (T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 : List Bool)

theorem jCmp_step (init : Bool) (ra rb : List Bool) (t : Bool) (hl : ra.length = rb.length)
    (hcap : 2 * ra.length + 1 ≤ cap) :
    Step (jCmp init) (2 * (2 * ra.length + 1) + 2) ![h0, h1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
      ![T0, T1, frame ra, frame rb, T4, T5, T6, [t], T8, T9, T10, List.replicate cap false]
      ![h0, h1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
      ![T0, T1, frame ra, frame rb, T4, T5, T6, [foldBits cmpStep init ra rb], T8, T9, T10, List.replicate cap false] := by
  have h := FoldCell.run cmpStep init ra rb t hl
  have h1' : Step (FoldCell.machine cmpStep init) (2 * ra.length + 1) (fun _ => 0) ![frame ra, frame rb, [t]]
      ![2 * ra.length, 2 * ra.length, 0] ![frame ra, frame rb, [foldBits cmpStep init ra rb]] :=
    h.congr_in (by funext i; fin_cases i <;> rfl) rfl
  have h2 := maskZero h1' sel3 (by intro j hj; fin_cases j <;> first | rfl | simp [sel3] at hj) hcap
  have h3 : Step (MaskedReset.machine (FoldCell.machine cmpStep init) sel3) (2 * (2 * ra.length + 1) + 2) (fun _ => 0)
      ![frame ra, frame rb, [t], List.replicate cap false] (fun _ => 0)
      ![frame ra, frame rb, [foldBits cmpStep init ra rb], List.replicate cap false] := by
    refine (h2.congr_in rfl ?_).congr rfl ?_ <;> funext i <;> fin_cases i <;> rfl
  have h4 := dockKeep h3 jSlotsCMP (by decide) ![h0, h1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    ![T0, T1, frame ra, frame rb, T4, T5, T6, [t], T8, T9, T10, List.replicate cap false]
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  rw [install_jCMP] at h4
  exact h4.congr rfl (by funext i; fin_cases i <;> rfl)

theorem jCell_step (op : Bool → Bool → Bool → Bool) (slots : Fin 3 → Fin (11 + 1)) (hi : Function.Injective slots)
    (H : Fin (11 + 1) → ℕ) (A : Fin (11 + 1) → List Bool) (t a b : Bool) (hH : ∀ j, H (slots j) = 0)
    (ht : A (slots 0) = [t]) (ha : A (slots 1) = [a]) (hb : A (slots 2) = [b]) :
    Step (RecoveryFocus.machine slots (CellOp.machine op)) 1 H A H
      (RecoveryRootRound.install slots A ![[op t a b], [a], [b]]) := by
  have h0 := CellOp.run op t a b
  have h1 : Step (CellOp.machine op) 1 (fun _ => 0) ![[t], [a], [b]] (fun _ => 0) ![[op t a b], [a], [b]] :=
    (h0.congr_in (by funext i; fin_cases i <;> rfl) rfl).congr (by funext i; fin_cases i <;> rfl) rfl
  exact dockKeep h1 slots hi H A hH (by intro j; fin_cases j <;> assumption)

theorem jAnd_step (t av x : Bool) :
    Step jAnd 1 ![h0, h1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
      ![T0, T1, T2, T3, T4, T5, T6, [t], [av], T9, [x], List.replicate cap false]
      ![h0, h1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
      ![T0, T1, T2, T3, T4, T5, T6, [t && av], [av], T9, [x], List.replicate cap false] := by
  have h := jCell_step andOp jSlotsAND (by decide) ![h0, h1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    ![T0, T1, T2, T3, T4, T5, T6, [t], [av], T9, [x], List.replicate cap false] t av x
    (by intro j; fin_cases j <;> rfl) rfl rfl rfl
  rw [install_jAND] at h
  exact h.congr rfl (by funext i; fin_cases i <;> rfl)

theorem jSetA_step (b av bv x : Bool) :
    Step (jSetA b) 1 ![h0, h1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
      ![T0, T1, T2, T3, T4, T5, T6, T7, [av], [bv], [x], List.replicate cap false]
      ![h0, h1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
      ![T0, T1, T2, T3, T4, T5, T6, T7, [b], [bv], [x], List.replicate cap false] := by
  have h := jCell_step (fun _ _ _ => b) jSlotsSETA (by decide) ![h0, h1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    ![T0, T1, T2, T3, T4, T5, T6, T7, [av], [bv], [x], List.replicate cap false] av bv x
    (by intro j; fin_cases j <;> rfl) rfl rfl rfl
  rw [install_jSETA] at h
  exact h.congr rfl (by funext i; fin_cases i <;> rfl)

theorem jSetB_step (b av bv x : Bool) :
    Step (jSetB b) 1 ![h0, h1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
      ![T0, T1, T2, T3, T4, T5, T6, T7, [av], [bv], [x], List.replicate cap false]
      ![h0, h1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
      ![T0, T1, T2, T3, T4, T5, T6, T7, [av], [b], [x], List.replicate cap false] := by
  have h := jCell_step (fun _ _ _ => b) jSlotsSETB (by decide) ![h0, h1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    ![T0, T1, T2, T3, T4, T5, T6, T7, [av], [bv], [x], List.replicate cap false] bv av x
    (by intro j; fin_cases j <;> rfl) rfl rfl rfl
  rw [install_jSETB] at h
  exact h.congr rfl (by funext i; fin_cases i <;> rfl)

theorem jInc_step (Wc c : ℕ) (f : Bool) (hcap : 2 * Wc + 2 ≤ cap) :
    Step jInc (2 * (2 * Wc + 2) + 2) ![h0, h1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
      ![T0, T1, T2, T3, frame (binary Wc c), T5, T6, [f], T8, T9, T10, List.replicate cap false]
      ![h0, h1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
      ![T0, T1, T2, T3, frame (binary Wc (c + f.toNat)), T5, T6, [f], T8, T9, T10, List.replicate cap false] := by
  have h := IncFlag.run Wc c [f] 0
  rw [read_single] at h
  have h1' : Step IncFlag.machine (2 * Wc + 2) (fun _ => 0) ![frame (binary Wc c), [f]] ![2 * Wc, 0]
      ![frame (binary Wc (c + f.toNat)), [f]] := h.congr_in (by funext i; fin_cases i <;> rfl) rfl
  have h2 := maskZero h1' sel2A (by intro j hj; fin_cases j <;> first | rfl | simp [sel2A] at hj) hcap
  have h3 : Step (MaskedReset.machine IncFlag.machine sel2A) (2 * (2 * Wc + 2) + 2) (fun _ => 0)
      ![frame (binary Wc c), [f], List.replicate cap false] (fun _ => 0)
      ![frame (binary Wc (c + f.toNat)), [f], List.replicate cap false] := by
    refine (h2.congr_in rfl ?_).congr rfl ?_ <;> funext i <;> fin_cases i <;> rfl
  have h4 := dockKeep h3 jSlotsINC (by decide) ![h0, h1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    ![T0, T1, T2, T3, frame (binary Wc c), T5, T6, [f], T8, T9, T10, List.replicate cap false]
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  rw [install_jINC] at h4
  exact h4.congr rfl (by funext i; fin_cases i <;> rfl)

theorem jAdd_step (Wc s c : ℕ) (hcap : 2 * Wc + 1 ≤ cap) :
    Step jAdd (2 * (2 * Wc + 1) + 2) ![h0, h1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
      ![T0, T1, T2, T3, frame (binary Wc c), frame (binary Wc s), T6, T7, T8, T9, T10, List.replicate cap false]
      ![h0, h1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
      ![T0, T1, T2, T3, frame (binary Wc c), frame (binary Wc (s + c)), T6, T7, T8, T9, T10, List.replicate cap false] := by
  have h := RippleIn.run sum3 carry3 false (binary Wc s) (binary Wc c) (by simp)
  rw [ripple_add, binary_length] at h
  simp only [Bool.toNat_false, Nat.add_zero] at h
  have h1' : Step (RippleIn.machine sum3 carry3 false) (2 * Wc + 1) (fun _ => 0) ![frame (binary Wc s), frame (binary Wc c)]
      ![2 * Wc, 2 * Wc] ![frame (binary Wc (s + c)), frame (binary Wc c)] := h.congr_in (by funext i; fin_cases i <;> rfl) rfl
  have h2 := maskZero h1' sel2B (by intro j hj; fin_cases j <;> simp [sel2B] at hj) hcap
  have h3 : Step (MaskedReset.machine (RippleIn.machine sum3 carry3 false) sel2B) (2 * (2 * Wc + 1) + 2) (fun _ => 0)
      ![frame (binary Wc s), frame (binary Wc c), List.replicate cap false] (fun _ => 0)
      ![frame (binary Wc (s + c)), frame (binary Wc c), List.replicate cap false] := by
    refine (h2.congr_in rfl ?_).congr rfl ?_ <;> funext i <;> fin_cases i <;> rfl
  have h4 := dockKeep h3 jSlotsADD (by decide) ![h0, h1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    ![T0, T1, T2, T3, frame (binary Wc c), frame (binary Wc s), T6, T7, T8, T9, T10, List.replicate cap false]
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  rw [install_jADD] at h4
  exact h4.congr rfl (by funext i; fin_cases i <;> rfl)

theorem jClrC_step (Wc c s : ℕ) (x : Bool) (hcap : 2 * Wc + 2 ≤ cap) :
    Step jClrC (2 * (2 * Wc + 2) + 2) ![h0, h1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
      ![T0, T1, T2, T3, frame (binary Wc c), frame (binary Wc s), T6, T7, T8, T9, [x], List.replicate cap false]
      ![h0, h1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
      ![T0, T1, T2, T3, frame (binary Wc 0), frame (binary Wc s), T6, T7, T8, T9, [x], List.replicate cap false] := by
  have h0' := zipStage cap clearG (binary Wc c) (binary Wc s) x (by simp) (by simpa using hcap)
  rw [zipWith_clear _ _ (by simp), binary_length,
    show List.replicate Wc false = binary Wc 0 from (binary_zero Wc).symm] at h0'
  have h4 := dockKeep h0' jSlotsCLRC (by decide) ![h0, h1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    ![T0, T1, T2, T3, frame (binary Wc c), frame (binary Wc s), T6, T7, T8, T9, [x], List.replicate cap false]
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  rw [install_jCLRC] at h4
  exact h4.congr rfl (by funext i; fin_cases i <;> rfl)

theorem jClrS_step (Wc c s : ℕ) (x : Bool) (hcap : 2 * Wc + 2 ≤ cap) :
    Step jClrS (2 * (2 * Wc + 2) + 2) ![h0, h1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
      ![T0, T1, T2, T3, frame (binary Wc c), frame (binary Wc s), T6, T7, T8, T9, [x], List.replicate cap false]
      ![h0, h1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
      ![T0, T1, T2, T3, frame (binary Wc c), frame (binary Wc 0), T6, T7, T8, T9, [x], List.replicate cap false] := by
  have h0' := zipStage cap clearG (binary Wc s) (binary Wc c) x (by simp) (by simpa using hcap)
  rw [zipWith_clear _ _ (by simp), binary_length,
    show List.replicate Wc false = binary Wc 0 from (binary_zero Wc).symm] at h0'
  have h4 := dockKeep h0' jSlotsCLRS (by decide) ![h0, h1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    ![T0, T1, T2, T3, frame (binary Wc c), frame (binary Wc s), T6, T7, T8, T9, [x], List.replicate cap false]
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  rw [install_jCLRS] at h4
  exact h4.congr rfl (by funext i; fin_cases i <;> rfl)

end PassStages

/-! ### Loading the next record -/

/-- A stream: the framed words, then the terminator. -/
def streamOf (L : List (List Bool)) : List Bool := L.flatMap frame ++ [false]

/-- The start of record `k` on the stream. -/
def pre (L : List (List Bool)) (k : ℕ) : ℕ := ((L.take k).flatMap frame).length

/-- The register after an attempt to load record `k` over `r`. -/
def loadReg (L : List (List Bool)) (k : ℕ) (r : List Bool) : List Bool := if h : k < L.length then L[k] else r

theorem streamOf_split (L : List (List Bool)) (k : ℕ) (hk : k < L.length) :
    streamOf L = (L.take k).flatMap frame ++ frame L[k] ++ ((L.drop (k + 1)).flatMap frame ++ [false]) := by
  have e : L = L.take k ++ L[k] :: L.drop (k + 1) := by
    rw [← List.drop_eq_getElem_cons hk, List.take_append_drop]
  calc streamOf L = streamOf (L.take k ++ L[k] :: L.drop (k + 1)) := congrArg streamOf e
    _ = _ := by simp only [streamOf, List.flatMap_append, List.flatMap_cons, List.append_assoc]

theorem pre_succ (L : List (List Bool)) (k : ℕ) (hk : k < L.length) :
    pre L (k + 1) = pre L k + (2 * L[k].length + 1) := by
  unfold pre
  rw [List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some, List.flatMap_append, List.length_append]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, frame_length]

theorem pre_sat (L : List (List Bool)) (k : ℕ) (hk : L.length ≤ k) : pre L (k + 1) = pre L k := by
  unfold pre
  rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)]

theorem read_pre (L : List (List Bool)) (k : ℕ) (hne : ∀ w ∈ L, w ≠ []) :
    readTapeBit (streamOf L) (pre L k) = decide (k < L.length) := by
  by_cases hk : k < L.length
  · rw [streamOf_split L k hk, decide_eq_true hk]
    obtain ⟨b, w, hw⟩ : ∃ b w, L[k] = b :: w := by
      cases h : L[k] with
      | nil => exact absurd h (hne _ (List.getElem_mem hk))
      | cons b w => exact ⟨b, w, rfl⟩
    rw [hw]
    simpa [frame, pre, List.append_assoc] using Streaming.read_append ((L.take k).flatMap frame)
      (b :: frame w ++ ((L.drop (k + 1)).flatMap frame ++ [false])) true
  · rw [decide_eq_false hk]
    unfold pre streamOf
    rw [List.take_of_length_le (by omega)]
    simpa using Streaming.read_append (L.flatMap frame) [] false

def loadCost (W : ℕ) : ℕ := 2 * (2 * W + 1) + 2 + 1 + 1 + 1 + 1 + 2

section Loads
variable (cap : ℕ) (T0 T1 T2 T3 T4 T5 T6 T7 : List Bool)

theorem jLoadA_step (A : List (List Bool)) (W k h1 : ℕ) (hW : ∀ a ∈ A, a.length = W) (hne : ∀ a ∈ A, a ≠ [])
    (r : List Bool) (hr : r.length = W) (av bv x : Bool) (hcap : 2 * W + 1 ≤ cap) :
    Step jLoadA (loadCost W) ![pre A k, h1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
      ![streamOf A, T1, frame r, T3, T4, T5, T6, T7, [av], [bv], [x], List.replicate cap false]
      ![pre A (k + 1), h1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
      ![streamOf A, T1, frame (loadReg A k r), T3, T4, T5, T6, T7, [decide (k < A.length)], [bv], [x],
        List.replicate cap false] := by
  by_cases hk : k < A.length
  · have hwk : A[k].length = W := hW _ (List.getElem_mem hk)
    obtain ⟨c, hc, hcf⟩ := CopyO.copy_run ((A.take k).flatMap frame) A[k]
      ((A.drop (k + 1)).flatMap frame ++ [false]) [] (frame r)
    rw [← streamOf_split A k hk] at hc hcf
    have hcs : Step CopyO.machine (2 * A[k].length + 1) ![pre A k, 0] ![streamOf A, frame r]
        ![pre A k + 2 * A[k].length, 2 * A[k].length + 1] ![streamOf A, frame A[k]] := by
      refine ⟨c, hc, ?_, ?_, runFrom_steps_le _ _ _ _ hc⟩
      · rw [hcf]; funext i; fin_cases i <;> simp [CopyO.config, pre, frame_length]
      · rw [hcf]
        funext i; fin_cases i
        · rfl
        · show overlay ([] ++ frame A[k]) (frame r) = frame A[k]
          exact overlay_exact _ _ (by simp [frame_length, hr, hwk])
    have hm := hcs.mask (cap := cap) selR (by intro i hi; fin_cases i <;> first | rfl | simp [selR] at hi) (by rw [hwk]; exact hcap)
    have hm' : Step (MaskedReset.machine CopyO.machine selR) (2 * (2 * A[k].length + 1) + 2)
        ![pre A k, 0, 0] ![streamOf A, frame r, List.replicate cap false]
        ![pre A k + 2 * A[k].length, 0, 0] ![streamOf A, frame A[k], List.replicate cap false] := by
      refine (hm.congr_in ?_ ?_).congr ?_ ?_ <;> funext i <;> fin_cases i <;> rfl
    have hd := dockRun hm' jSlotsCPA (by decide) ![pre A k, h1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
      ![streamOf A, T1, frame r, T3, T4, T5, T6, T7, [av], [bv], [x], List.replicate cap false]
      (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
    rw [dockH_jCPA, install_jCPA] at hd
    have hn := dockRun (nudge_run (streamOf A) (pre A k + 2 * A[k].length)) jSlotsNA (by decide)
      ![pre A k + 2 * A[k].length, h1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
      ![streamOf A, T1, frame A[k], T3, T4, T5, T6, T7, [av], [bv], [x], List.replicate cap false]
      (by intro j; fin_cases j; rfl) (by intro j; fin_cases j; rfl)
    rw [dockH_jNA, install_jNA] at hn
    have hs := jSetA_step (cap := cap) (h0 := pre A k + 2 * A[k].length + 1) (h1 := h1) (T0 := streamOf A) (T1 := T1)
      (T2 := frame A[k]) (T3 := T3) (T4 := T4) (T5 := T5) (T6 := T6) (T7 := T7) (b := true) (av := av) (bv := bv) (x := x)
    have hyes := ((hd.congr (by funext i; fin_cases i <;> rfl) (by funext i; fin_cases i <;> rfl)).seq
      (hn.congr (by funext i; fin_cases i <;> rfl) (by funext i; fin_cases i <;> rfl))).seq hs
    have hb := branch_true (0 : Fin (11 + 1)) (jSetA false) hyes
      (show readTapeBit (streamOf A) (pre A k) = true by rw [read_pre A k hne, decide_eq_true hk])
    rw [hwk] at hb
    have e1 : pre A k + 2 * W + 1 = pre A (k + 1) := by rw [pre_succ A k hk, hwk]; omega
    have e2 : loadReg A k r = A[k] := by simp [loadReg, hk]
    rw [e2, decide_eq_true hk]
    refine (hb.enlarge (by unfold loadCost; omega)).congr ?_ ?_
    · funext i; fin_cases i
      · show pre A k + 2 * W + 1 = pre A (k + 1); exact e1
      all_goals rfl
    · funext i; fin_cases i <;> rfl
  · have hs := jSetA_step (cap := cap) (h0 := pre A k) (h1 := h1) (T0 := streamOf A) (T1 := T1)
      (T2 := frame r) (T3 := T3) (T4 := T4) (T5 := T5) (T6 := T6) (T7 := T7) (b := false) (av := av) (bv := bv) (x := x)
    have hb := branch_false (0 : Fin (11 + 1)) (Composition.machine (Composition.machine jCpA jNA) (jSetA true)) hs
      (show readTapeBit (streamOf A) (pre A k) = false by rw [read_pre A k hne, decide_eq_false hk])
    have e1 : pre A (k + 1) = pre A k := pre_sat A k (by omega)
    have e2 : loadReg A k r = r := by simp [loadReg, hk]
    rw [e1, e2, decide_eq_false hk]
    exact hb.enlarge (by unfold loadCost; omega)

theorem jLoadB_step (B : List (List Bool)) (W k h0 : ℕ) (hW : ∀ b ∈ B, b.length = W) (hne : ∀ b ∈ B, b ≠ [])
    (r : List Bool) (hr : r.length = W) (av bv x : Bool) (hcap : 2 * W + 1 ≤ cap) :
    Step jLoadB (loadCost W) ![h0, pre B k, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
      ![T0, streamOf B, T2, frame r, T4, T5, T6, T7, [av], [bv], [x], List.replicate cap false]
      ![h0, pre B (k + 1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
      ![T0, streamOf B, T2, frame (loadReg B k r), T4, T5, T6, T7, [av], [decide (k < B.length)], [x],
        List.replicate cap false] := by
  by_cases hk : k < B.length
  · have hwk : B[k].length = W := hW _ (List.getElem_mem hk)
    obtain ⟨c, hc, hcf⟩ := CopyO.copy_run ((B.take k).flatMap frame) B[k]
      ((B.drop (k + 1)).flatMap frame ++ [false]) [] (frame r)
    rw [← streamOf_split B k hk] at hc hcf
    have hcs : Step CopyO.machine (2 * B[k].length + 1) ![pre B k, 0] ![streamOf B, frame r]
        ![pre B k + 2 * B[k].length, 2 * B[k].length + 1] ![streamOf B, frame B[k]] := by
      refine ⟨c, hc, ?_, ?_, runFrom_steps_le _ _ _ _ hc⟩
      · rw [hcf]; funext i; fin_cases i <;> simp [CopyO.config, pre, frame_length]
      · rw [hcf]
        funext i; fin_cases i
        · rfl
        · show overlay ([] ++ frame B[k]) (frame r) = frame B[k]
          exact overlay_exact _ _ (by simp [frame_length, hr, hwk])
    have hm := hcs.mask (cap := cap) selR (by intro i hi; fin_cases i <;> first | rfl | simp [selR] at hi) (by rw [hwk]; exact hcap)
    have hm' : Step (MaskedReset.machine CopyO.machine selR) (2 * (2 * B[k].length + 1) + 2)
        ![pre B k, 0, 0] ![streamOf B, frame r, List.replicate cap false]
        ![pre B k + 2 * B[k].length, 0, 0] ![streamOf B, frame B[k], List.replicate cap false] := by
      refine (hm.congr_in ?_ ?_).congr ?_ ?_ <;> funext i <;> fin_cases i <;> rfl
    have hd := dockRun hm' jSlotsCPB (by decide) ![h0, pre B k, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
      ![T0, streamOf B, T2, frame r, T4, T5, T6, T7, [av], [bv], [x], List.replicate cap false]
      (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
    rw [dockH_jCPB, install_jCPB] at hd
    have hn := dockRun (nudge_run (streamOf B) (pre B k + 2 * B[k].length)) jSlotsNB (by decide)
      ![h0, pre B k + 2 * B[k].length, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
      ![T0, streamOf B, T2, frame B[k], T4, T5, T6, T7, [av], [bv], [x], List.replicate cap false]
      (by intro j; fin_cases j; rfl) (by intro j; fin_cases j; rfl)
    rw [dockH_jNB, install_jNB] at hn
    have hs := jSetB_step (cap := cap) (h0 := h0) (h1 := pre B k + 2 * B[k].length + 1) (T0 := T0) (T1 := streamOf B)
      (T2 := T2) (T3 := frame B[k]) (T4 := T4) (T5 := T5) (T6 := T6) (T7 := T7) (b := true) (av := av) (bv := bv) (x := x)
    have hyes := ((hd.congr (by funext i; fin_cases i <;> rfl) (by funext i; fin_cases i <;> rfl)).seq
      (hn.congr (by funext i; fin_cases i <;> rfl) (by funext i; fin_cases i <;> rfl))).seq hs
    have hb := branch_true (1 : Fin (11 + 1)) (jSetB false) hyes
      (show readTapeBit (streamOf B) (pre B k) = true by rw [read_pre B k hne, decide_eq_true hk])
    rw [hwk] at hb
    have e1 : pre B k + 2 * W + 1 = pre B (k + 1) := by rw [pre_succ B k hk, hwk]; omega
    have e2 : loadReg B k r = B[k] := by simp [loadReg, hk]
    rw [e2, decide_eq_true hk]
    refine (hb.enlarge (by unfold loadCost; omega)).congr ?_ ?_
    · funext i; fin_cases i
      · rfl
      · show pre B k + 2 * W + 1 = pre B (k + 1); exact e1
      all_goals rfl
    · funext i; fin_cases i <;> rfl
  · have hs := jSetB_step (cap := cap) (h0 := h0) (h1 := pre B k) (T0 := T0) (T1 := streamOf B)
      (T2 := T2) (T3 := frame r) (T4 := T4) (T5 := T5) (T6 := T6) (T7 := T7) (b := false) (av := av) (bv := bv) (x := x)
    have hb := branch_false (1 : Fin (11 + 1)) (Composition.machine (Composition.machine jCpB jNB) (jSetB true)) hs
      (show readTapeBit (streamOf B) (pre B k) = false by rw [read_pre B k hne, decide_eq_false hk])
    have e1 : pre B (k + 1) = pre B k := pre_sat B k (by omega)
    have e2 : loadReg B k r = r := by simp [loadReg, hk]
    rw [e1, e2, decide_eq_false hk]
    exact hb.enlarge (by unfold loadCost; omega)

end Loads

/-! ### One merge pass as one `Step` -/

noncomputable def jInit := Composition.machine (Composition.machine (Composition.machine jClrC jClrS) jLoadA) jLoadB
noncomputable def jBody (init : Bool) := Composition.machine (Composition.machine (jCmp init) jAnd)
  (branchM 7 (Composition.machine jInc jLoadA) (Composition.machine jAdd jLoadB))
noncomputable def jLoop (init : Bool) := StreamController.machine (jBody init) 9
/-- **One merge pass**: counting `Σ_b #{a ⋈ b}` (`⋈` is `≤` if `init`, `<` otherwise). -/
noncomputable def jPass (init : Bool) := Composition.machine jInit (jLoop init)

theorem reg_length (L : List (List Bool)) (W k : ℕ) (hL : ∀ a ∈ L, a.length = W) (r0 : List Bool)
    (hr : r0.length = W) : (reg L k r0).length = W := by
  unfold reg
  cases h : (L.take (k + 1)).getLast? with
  | none => simpa using hr
  | some a =>
    have := List.mem_of_getLast? h
    simpa using hL a (List.mem_of_mem_take this)

theorem reg_load (L : List (List Bool)) (k : ℕ) (r0 : List Bool) :
    reg L (k + 1) r0 = loadReg L (k + 1) (reg L k r0) := by
  unfold loadReg
  split
  · next h => exact reg_lt L (k + 1) r0 h
  · next h => exact reg_ge L k r0 (by omega)

theorem reg_zero (L : List (List Bool)) (r0 : List Bool) : reg L 0 r0 = loadReg L 0 r0 := by
  unfold loadReg
  split
  · next h => exact reg_lt L 0 r0 h
  · next h =>
    have : L = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this; rfl

/-- The bank before a merge step. -/
def passH (A B : List (List Bool)) (m : MS) : Fin (11 + 1) → ℕ :=
  ![pre A (m.i + 1), pre B (m.j + 1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def passA (A B : List (List Bool)) (Wc : ℕ) (ra0 rb0 sy : List Bool) (x : Bool) (cap : ℕ) (m : MS) :
    Fin (11 + 1) → List Bool :=
  ![streamOf A, streamOf B, frame (reg A m.i ra0), frame (reg B m.j rb0), frame (binary Wc m.i),
    frame (binary Wc m.s), sy, [m.t], [decide (m.i < A.length)], [decide (m.j < B.length)], [x],
    List.replicate cap false]

/-- The shape assumptions of a pass. -/
structure Shape (A B : List (List Bool)) (W : ℕ) (ra0 rb0 : List Bool) : Prop where
  hA : ∀ a ∈ A, a.length = W
  hB : ∀ b ∈ B, b.length = W
  hW : 1 ≤ W
  hra : ra0.length = W
  hrb : rb0.length = W

theorem Shape.neA {A B : List (List Bool)} {W : ℕ} {ra0 rb0 : List Bool} (S : Shape A B W ra0 rb0) :
    ∀ a ∈ A, a ≠ [] := fun a h e => by have := S.hA a h; rw [e] at this; simp at this; have := S.hW; omega
theorem Shape.neB {A B : List (List Bool)} {W : ℕ} {ra0 rb0 : List Bool} (S : Shape A B W ra0 rb0) :
    ∀ b ∈ B, b ≠ [] := fun b h e => by have := S.hB b h; rw [e] at this; simp at this; have := S.hW; omega

def jInitCost (W Wc : ℕ) : ℕ := (2 * (2 * Wc + 2) + 2) + 1 + (2 * (2 * Wc + 2) + 2) + 1 + loadCost W + 1 + loadCost W

theorem jInit_step (A B : List (List Bool)) (W Wc : ℕ) (ra0 rb0 sy : List Bool) (S : Shape A B W ra0 rb0)
    (c0 s0 : ℕ) (t0 av0 bv0 x : Bool) (cap : ℕ) (hcap : 2 * W + 2 * Wc + 2 ≤ cap) :
    Step jInit (jInitCost W Wc) ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
      ![streamOf A, streamOf B, frame ra0, frame rb0, frame (binary Wc c0), frame (binary Wc s0), sy, [t0], [av0],
        [bv0], [x], List.replicate cap false]
      (passH A B ⟨0, 0, 0, t0⟩) (passA A B Wc ra0 rb0 sy x cap ⟨0, 0, 0, t0⟩) := by
  have h1 := jClrC_step (cap := cap) (h0 := 0) (h1 := 0) (T0 := streamOf A) (T1 := streamOf B) (T2 := frame ra0)
    (T3 := frame rb0) (T6 := sy) (T7 := [t0]) (T8 := [av0]) (T9 := [bv0]) (Wc := Wc) (c := c0) (s := s0) (x := x) (by omega)
  have h2 := jClrS_step (cap := cap) (h0 := 0) (h1 := 0) (T0 := streamOf A) (T1 := streamOf B) (T2 := frame ra0)
    (T3 := frame rb0) (T6 := sy) (T7 := [t0]) (T8 := [av0]) (T9 := [bv0]) (Wc := Wc) (c := 0) (s := s0) (x := x) (by omega)
  have h3 := jLoadA_step (cap := cap) (T1 := streamOf B) (T3 := frame rb0) (T4 := frame (binary Wc 0))
    (T5 := frame (binary Wc 0)) (T6 := sy) (T7 := [t0]) A W 0 0 S.hA S.neA ra0 S.hra av0 bv0 x (by omega)
  have h4 := jLoadB_step (cap := cap) (T0 := streamOf A) (T2 := frame (loadReg A 0 ra0)) (T4 := frame (binary Wc 0))
    (T5 := frame (binary Wc 0)) (T6 := sy) (T7 := [t0]) B W 0 (pre A (0 + 1)) S.hB S.neB rb0 S.hrb
    (decide (0 < A.length)) bv0 x (by omega)
  have h := ((h1.seq h2).seq h3).seq h4
  unfold passH passA
  rw [reg_zero A ra0, reg_zero B rb0]
  exact h

def armCost (W Wc : ℕ) : ℕ := (2 * (2 * Wc + 2) + 2) + 1 + loadCost W
def jBodyCost (W Wc : ℕ) : ℕ := (2 * (2 * W + 1) + 2) + 1 + 1 + 1 + (armCost W Wc + 2)

theorem jBody_step (A B : List (List Bool)) (W Wc : ℕ) (ra0 rb0 sy : List Bool) (S : Shape A B W ra0 rb0)
    (init x : Bool) (cap : ℕ) (hcap : 2 * W + 2 * Wc + 2 ≤ cap) (m : MS) :
    Step (jBody init) (jBodyCost W Wc) (passH A B m) (passA A B Wc ra0 rb0 sy x cap m)
      (passH A B (mstep A B init ra0 rb0 m)) (passA A B Wc ra0 rb0 sy x cap (mstep A B init ra0 rb0 m)) := by
  have hlA := reg_length A W m.i S.hA ra0 S.hra
  have hlB := reg_length B W m.j S.hB rb0 S.hrb
  have hc := jCmp_step (cap := cap) (h0 := pre A (m.i + 1)) (h1 := pre B (m.j + 1)) (T0 := streamOf A)
    (T1 := streamOf B) (T4 := frame (binary Wc m.i)) (T5 := frame (binary Wc m.s)) (T6 := sy)
    (T8 := [decide (m.i < A.length)]) (T9 := [decide (m.j < B.length)]) (T10 := [x]) init (reg A m.i ra0)
    (reg B m.j rb0) m.t (by rw [hlA, hlB]) (by rw [hlA]; omega)
  rw [hlA] at hc
  have ha := jAnd_step (cap := cap) (h0 := pre A (m.i + 1)) (h1 := pre B (m.j + 1)) (T0 := streamOf A)
    (T1 := streamOf B) (T2 := frame (reg A m.i ra0)) (T3 := frame (reg B m.j rb0)) (T4 := frame (binary Wc m.i))
    (T5 := frame (binary Wc m.s)) (T6 := sy) (T9 := [decide (m.j < B.length)])
    (t := foldBits cmpStep init (reg A m.i ra0) (reg B m.j rb0)) (av := decide (m.i < A.length)) (x := x)
  have hc0 := hc.seq ha
  unfold mstep
  by_cases hcond : (foldBits cmpStep init (reg A m.i ra0) (reg B m.j rb0) && decide (m.i < A.length)) = true
  · rw [if_pos hcond]
    have hiA : m.i < A.length := by simp at hcond; exact hcond.2
    have hi := jInc_step (cap := cap) (h0 := pre A (m.i + 1)) (h1 := pre B (m.j + 1)) (T0 := streamOf A)
      (T1 := streamOf B) (T2 := frame (reg A m.i ra0)) (T3 := frame (reg B m.j rb0)) (T5 := frame (binary Wc m.s))
      (T6 := sy) (T8 := [decide (m.i < A.length)]) (T9 := [decide (m.j < B.length)]) (T10 := [x]) Wc m.i
      true (by omega)
    have hl := jLoadA_step (cap := cap) (T1 := streamOf B) (T3 := frame (reg B m.j rb0))
      (T4 := frame (binary Wc (m.i + 1))) (T5 := frame (binary Wc m.s)) (T6 := sy) (T7 := [true]) A W (m.i + 1)
      (pre B (m.j + 1)) S.hA S.neA (reg A m.i ra0) hlA (decide (m.i < A.length)) (decide (m.j < B.length)) x (by omega)
    rw [Bool.toNat_true] at hi
    have harm := hi.seq hl
    have hb := branch_true (7 : Fin (11 + 1)) (Composition.machine jAdd jLoadB) harm rfl
    rw [hcond] at hc0
    have hall := hc0.seq (hb.enlarge (m := armCost W Wc + 2) (by unfold armCost; omega))
    unfold passH passA
    rw [reg_load A m.i ra0]
    exact hall
  · rw [if_neg hcond]
    have hcf : (foldBits cmpStep init (reg A m.i ra0) (reg B m.j rb0) && decide (m.i < A.length)) = false := by
      simpa using hcond
    have hd := jAdd_step (cap := cap) (h0 := pre A (m.i + 1)) (h1 := pre B (m.j + 1)) (T0 := streamOf A)
      (T1 := streamOf B) (T2 := frame (reg A m.i ra0)) (T3 := frame (reg B m.j rb0)) (T6 := sy) (T7 := [false])
      (T8 := [decide (m.i < A.length)]) (T9 := [decide (m.j < B.length)]) (T10 := [x]) Wc m.s m.i (by omega)
    have hl := jLoadB_step (cap := cap) (T0 := streamOf A) (T2 := frame (reg A m.i ra0))
      (T4 := frame (binary Wc m.i)) (T5 := frame (binary Wc (m.s + m.i))) (T6 := sy) (T7 := [false]) B W (m.j + 1)
      (pre A (m.i + 1)) S.hB S.neB (reg B m.j rb0) hlB (decide (m.i < A.length)) (decide (m.j < B.length)) x (by omega)
    have harm := hd.seq hl
    have hb := branch_false (7 : Fin (11 + 1)) (Composition.machine jInc jLoadA) harm rfl
    rw [hcf] at hc0
    have hall := hc0.seq (hb.enlarge (m := armCost W Wc + 2) (by unfold armCost; omega))
    unfold passH passA
    rw [reg_load B m.j rb0]
    exact hall

theorem mstate_sum (A B : List (List Bool)) (init : Bool) (ra0 rb0 : List Bool) (t0 : Bool) (k : ℕ) :
    (mstate A B init ra0 rb0 t0 k).i + (mstate A B init ra0 rb0 t0 k).j = k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    show (mstep A B init ra0 rb0 _).i + (mstep A B init ra0 rb0 _).j = k + 1
    unfold mstep
    split <;> simp <;> omega

theorem mstate_i_le (A B : List (List Bool)) (init : Bool) (ra0 rb0 : List Bool) (t0 : Bool) (k : ℕ) :
    (mstate A B init ra0 rb0 t0 k).i ≤ A.length := by
  induction k with
  | zero => exact Nat.zero_le _
  | succ k ih =>
    show (mstep A B init ra0 rb0 _).i ≤ A.length
    unfold mstep
    split
    · next h => simp at h; simp; omega
    · exact ih

theorem mstate_ends (A B : List (List Bool)) (init : Bool) (ra0 rb0 : List Bool) (t0 : Bool) :
    ∃ k, B.length ≤ (mstate A B init ra0 rb0 t0 k).j :=
  ⟨A.length + B.length, by
    have h1 := mstate_sum A B init ra0 rb0 t0 (A.length + B.length)
    have h2 := mstate_i_le A B init ra0 rb0 t0 (A.length + B.length)
    omega⟩

theorem mstate_inv (A B : List (List Bool)) (init : Bool) (ra0 rb0 : List Bool) (t0 : Bool) (W : ℕ)
    (hA : ∀ a ∈ A, a.length = W) (hB : ∀ b ∈ B, b.length = W)
    (sA : A.Pairwise (fun a b => value a ≤ value b)) (sB : B.Pairwise (fun a b => value a ≤ value b)) (k : ℕ)
    (hk : ∀ k' < k, (mstate A B init ra0 rb0 t0 k').j < B.length) : Inv A B init (mstate A B init ra0 rb0 t0 k) := by
  induction k with
  | zero =>
    refine ⟨Nat.zero_le _, Nat.zero_le _, fun i' _ hi' => absurd hi' (Nat.not_lt_zero _), ?_⟩
    change (0 : ℕ) = ((B.take 0).map (fun b => A.countP (fun a => decide (rel init a b)))).sum
    simp
  | succ k ih =>
    exact mstep_inv A B init ra0 rb0 W hA hB sA sB _ (ih (fun k' hk' => hk k' (by omega))) (hk k (by omega))

theorem jLoop_step (A B : List (List Bool)) (W Wc : ℕ) (ra0 rb0 sy : List Bool) (S : Shape A B W ra0 rb0)
    (init x t0 : Bool) (cap : ℕ) (hcap : 2 * W + 2 * Wc + 2 ≤ cap) :
    Step (jLoop init) (Nat.find (mstate_ends A B init ra0 rb0 t0) * (jBodyCost W Wc + 2) + 1)
      (passH A B ⟨0, 0, 0, t0⟩) (passA A B Wc ra0 rb0 sy x cap ⟨0, 0, 0, t0⟩)
      (passH A B (mstate A B init ra0 rb0 t0 (Nat.find (mstate_ends A B init ra0 rb0 t0))))
      (passA A B Wc ra0 rb0 sy x cap (mstate A B init ra0 rb0 t0 (Nat.find (mstate_ends A B init ra0 rb0 t0)))) := by
  let K := Nat.find (mstate_ends A B init ra0 rb0 t0)
  have hmin : ∀ k < K, (mstate A B init ra0 rb0 t0 k).j < B.length := fun k hk => by
    have := Nat.find_min (mstate_ends A B init ra0 rb0 t0) hk
    omega
  have hend : B.length ≤ (mstate A B init ra0 rb0 t0 K).j := Nat.find_spec (mstate_ends A B init ra0 rb0 t0)
  let W' : WhileBody (11 + 1) _ :=
    { body := jBody init
      tape := 9
      bound := K
      H := fun k => passH A B (mstate A B init ra0 rb0 t0 k)
      A := fun k => passA A B Wc ra0 rb0 sy x cap (mstate A B init ra0 rb0 t0 k)
      cost := fun _ => jBodyCost W Wc
      step := fun k _ => jBody_step A B W Wc ra0 rb0 sy S init x cap hcap (mstate A B init ra0 rb0 t0 k)
      cont := fun k hk => by
        show readTapeBit [decide ((mstate A B init ra0 rb0 t0 k).j < B.length)] 0 = true
        rw [read_single]; simpa using hmin k hk
      halt := by
        show readTapeBit [decide ((mstate A B init ra0 rb0 t0 K).j < B.length)] 0 = false
        rw [read_single]; simp; omega }
  have hW := W'.run
  have hc : W'.rest 0 = W'.bound * (jBodyCost W Wc + 2) + 1 := W'.rest_const _ (fun _ => rfl)
  rw [hc] at hW
  show Step (StreamController.machine (jBody init) 9) (K * (jBodyCost W Wc + 2) + 1)
    (passH A B ⟨0, 0, 0, t0⟩) (passA A B Wc ra0 rb0 sy x cap ⟨0, 0, 0, t0⟩)
    (passH A B (mstate A B init ra0 rb0 t0 K)) (passA A B Wc ra0 rb0 sy x cap (mstate A B init ra0 rb0 t0 K))
  exact hW

def jPassCost (W Wc n : ℕ) : ℕ := jInitCost W Wc + 1 + (n * (jBodyCost W Wc + 2) + 1)

/-- **One merge pass** as one `Step`: the pass's sum ends `Σ_{b ∈ B} #{a ∈ A : a ⋈ b}`. -/
theorem jPass_run (A B : List (List Bool)) (W Wc : ℕ) (ra0 rb0 sy : List Bool) (S : Shape A B W ra0 rb0)
    (sA : A.Pairwise (fun a b => value a ≤ value b)) (sB : B.Pairwise (fun a b => value a ≤ value b))
    (init : Bool) (c0 s0 : ℕ) (t0 av0 bv0 x : Bool) (cap : ℕ) (hcap : 2 * W + 2 * Wc + 2 ≤ cap) :
    ∃ m : MS, m.s = (B.map (fun b => A.countP (fun a => decide (rel init a b)))).sum ∧
      Step (jPass init) (jPassCost W Wc (A.length + B.length)) ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
        ![streamOf A, streamOf B, frame ra0, frame rb0, frame (binary Wc c0), frame (binary Wc s0), sy, [t0], [av0],
          [bv0], [x], List.replicate cap false]
        (passH A B m) (passA A B Wc ra0 rb0 sy x cap m) := by
  let K := Nat.find (mstate_ends A B init ra0 rb0 t0)
  have hmin : ∀ k < K, (mstate A B init ra0 rb0 t0 k).j < B.length := fun k hk => by
    have := Nat.find_min (mstate_ends A B init ra0 rb0 t0) hk
    omega
  have hend : B.length ≤ (mstate A B init ra0 rb0 t0 K).j := Nat.find_spec (mstate_ends A B init ra0 rb0 t0)
  have hinv := mstate_inv A B init ra0 rb0 t0 W S.hA S.hB sA sB K hmin
  have hjK : (mstate A B init ra0 rb0 t0 K).j = B.length := by have := hinv.2.1; omega
  have hK : K ≤ A.length + B.length := by
    have h1 := mstate_sum A B init ra0 rb0 t0 K
    have h2 := mstate_i_le A B init ra0 rb0 t0 K
    omega
  refine ⟨mstate A B init ra0 rb0 t0 K, ?_, ?_⟩
  · rw [hinv.2.2.2, hjK, List.take_length]
  · have h := (jInit_step A B W Wc ra0 rb0 sy S c0 s0 t0 av0 bv0 x cap hcap).seq
      (jLoop_step A B W Wc ra0 rb0 sy S init x t0 cap hcap)
    have hmul := Nat.mul_le_mul_right (jBodyCost W Wc + 2) hK
    exact h.enlarge (by
      unfold jPassCost
      exact Nat.add_le_add_left (Nat.add_le_add_right hmul 1) _)

def jSlotsCP65 : Fin 4 → Fin (11 + 1) := ![6, 5, 10, 11]
theorem install_jCP65 (A : Fin (11 + 1) → List Bool) (v : Fin 4 → List Bool) :
    RecoveryRootRound.install jSlotsCP65 A v = ![A 0, A 1, A 2, A 3, A 4, v 1, v 0, A 7, A 8, A 9, v 2, v 3] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 1
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 2
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 3
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

def jSlotsSB65 : Fin 3 → Fin (11 + 1) := ![6, 5, 11]
theorem install_jSB65 (A : Fin (11 + 1) → List Bool) (v : Fin 3 → List Bool) :
    RecoveryRootRound.install jSlotsSB65 A v = ![A 0, A 1, A 2, A 3, A 4, v 1, v 0, A 7, A 8, A 9, A 10, v 2] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 1
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 2
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

/-! ## The join count: pass `≤`, rewind the streams, pass `<` (sums swapped), subtract -/

def selAB : Fin (11 + 1) → Bool := fun i => decide (i = 0 ∨ i = 1)
/-- Copy the first pass's sum (tape 5) onto tape 6, where the second pass leaves it alone. -/
noncomputable def jCopy := RecoveryFocus.machine jSlotsCP65 (MaskedReset.machine (ZipFlag.machine copyG) sel3)
/-- Subtract the second pass's sum (tape 5) from the first's (tape 6). -/
noncomputable def jSub := RecoveryFocus.machine jSlotsSB65 (MaskedReset.machine (RippleIn.machine sum3 borrow3 false) sel2B)
/-- **The join-count machine** (13 tapes: the pass layout, then the rewind log of the streams). -/
noncomputable def joinM := Composition.machine (Composition.machine (Composition.machine
  (MaskedReset.machine (jPass true) selAB) (TapeEmbedding.machine 1 jCopy)) (TapeEmbedding.machine 1 (jPass false)))
  (TapeEmbedding.machine 1 jSub)

/-- The paper quantity: the number of equal pairs, `Σ_{b ∈ B} #A(b)`. -/
def joinCount (A B : List (List Bool)) : ℕ := (B.map (fun b => A.count b)).sum

theorem value_inj (a b : List Bool) (h : a.length = b.length) (hv : value a = value b) : a = b := by
  induction a generalizing b with
  | nil => cases b with
    | nil => rfl
    | cons y b => simp at h
  | cons x a ih => cases b with
    | nil => simp at h
    | cons y b =>
      simp only [value] at hv
      have hxy : x = y := by cases x <;> cases y <;> simp [Bool.toNat] at hv ⊢ <;> omega
      subst hxy
      rw [ih b (by simpa using h) (by omega)]

theorem countP_le_split (A : List (List Bool)) (b : List Bool) :
    A.countP (fun a => decide (rel true a b)) =
      A.countP (fun a => decide (rel false a b)) + A.countP (fun a => decide (value a = value b)) := by
  induction A with
  | nil => rfl
  | cons a A ih =>
    rw [List.countP_cons, List.countP_cons, List.countP_cons, ih]
    have key : (if decide (rel true a b) = true then 1 else 0) =
        (if decide (rel false a b) = true then 1 else 0) + (if decide (value a = value b) = true then 1 else 0) := by
      unfold rel
      by_cases h1 : value a < value b
      · have h2 : value a ≠ value b := Nat.ne_of_lt h1
        rw [if_pos (decide_eq_true (Or.inl h1)), if_pos (decide_eq_true (Or.inl h1)), if_neg (by simpa using h2)]
      · by_cases h2 : value a = value b
        · rw [if_pos (decide_eq_true (Or.inr ⟨rfl, h2⟩)), if_neg (by simp [h1]), if_pos (decide_eq_true h2)]
        · rw [if_neg (by simp [h1, h2]), if_neg (by simp [h1]), if_neg (by simpa using h2)]
    omega

theorem countP_eq_count (A : List (List Bool)) (b : List Bool) (W : ℕ) (hA : ∀ a ∈ A, a.length = W)
    (hb : b.length = W) : A.countP (fun a => decide (value a = value b)) = A.count b := by
  rw [List.count_eq_countP]
  apply List.countP_congr
  intro a ha
  constructor
  · intro h
    have := value_inj a b (by rw [hA a ha, hb]) (by simpa using h)
    simp [this]
  · intro h
    have : a = b := by simpa using h
    simp [this]

theorem sums_join (A B : List (List Bool)) (W : ℕ) (hA : ∀ a ∈ A, a.length = W) (hB : ∀ b ∈ B, b.length = W) :
    (B.map (fun b => A.countP (fun a => decide (rel true a b)))).sum =
      (B.map (fun b => A.countP (fun a => decide (rel false a b)))).sum + joinCount A B := by
  unfold joinCount
  induction B with
  | nil => rfl
  | cons b B ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [ih (fun c hc => hB c (List.mem_cons_of_mem _ hc)), countP_le_split,
      countP_eq_count A b W hA (hB b List.mem_cons_self)]
    omega

def joinCost (W Wc n : ℕ) : ℕ :=
  (2 * jPassCost W Wc n + 2) + 1 + (2 * (2 * Wc + 2) + 2) + 1 + jPassCost W Wc n + 1 + (2 * (2 * Wc + 1) + 2)

/-- The bank after the first pass (streams rewound). -/
def joinV1 (A B : List (List Bool)) (Wc : ℕ) (ra0 rb0 : List Bool) (s20 : ℕ) (x : Bool) (cap cap' : ℕ) (m1 : MS) :
    Fin (11 + 1 + 1) → List Bool :=
  ![streamOf A, streamOf B, frame (reg A m1.i ra0), frame (reg B m1.j rb0), frame (binary Wc m1.i),
    frame (binary Wc m1.s), frame (binary Wc s20), [m1.t], [decide (m1.i < A.length)], [decide (m1.j < B.length)],
    [x], List.replicate cap false, List.replicate cap' false]

theorem join_pass1 (A B : List (List Bool)) (W Wc : ℕ) (ra0 rb0 : List Bool) (S : Shape A B W ra0 rb0)
    (sA : A.Pairwise (fun a b => value a ≤ value b)) (sB : B.Pairwise (fun a b => value a ≤ value b))
    (c0 s10 s20 : ℕ) (t0 av0 bv0 x : Bool) (cap cap' : ℕ) (hcap : 2 * W + 2 * Wc + 2 ≤ cap)
    (hcap' : jPassCost W Wc (A.length + B.length) ≤ cap') :
    ∃ m1 : MS, m1.s = (B.map (fun b => A.countP (fun a => decide (rel true a b)))).sum ∧
      Step (MaskedReset.machine (jPass true) selAB) (2 * jPassCost W Wc (A.length + B.length) + 2) (fun _ => 0)
        ![streamOf A, streamOf B, frame ra0, frame rb0, frame (binary Wc c0), frame (binary Wc s10),
          frame (binary Wc s20), [t0], [av0], [bv0], [x], List.replicate cap false, List.replicate cap' false]
        (fun _ => 0) (joinV1 A B Wc ra0 rb0 s20 x cap cap' m1) := by
  obtain ⟨m1, hs1, h1⟩ := jPass_run A B W Wc ra0 rb0 (frame (binary Wc s20)) S sA sB true c0 s10 t0 av0 bv0 x cap hcap
  have h1m := h1.mask selAB (by intro i _; fin_cases i <;> rfl) hcap'
  refine ⟨m1, hs1, (h1m.congr_in ?_ ?_).congr ?_ ?_⟩
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl

/-- The first pass's sum is copied onto tape 6. -/
theorem join_copy (Wc s s' : ℕ) (T0 T1 T2 T3 T4 T7 T8 T9 : List Bool) (x : Bool) (cap cap' : ℕ)
    (hcap : 2 * Wc + 2 ≤ cap) :
    Step (TapeEmbedding.machine 1 jCopy) (2 * (2 * Wc + 2) + 2) (fun _ => 0)
      ![T0, T1, T2, T3, T4, frame (binary Wc s), frame (binary Wc s'), T7, T8, T9, [x], List.replicate cap false,
        List.replicate cap' false]
      (fun _ => 0)
      ![T0, T1, T2, T3, T4, frame (binary Wc s), frame (binary Wc s), T7, T8, T9, [x], List.replicate cap false,
        List.replicate cap' false] := by
  have h0 := zipStage cap copyG (binary Wc s') (binary Wc s) x (by simp) (by simpa using hcap)
  rw [zipWith_copy _ _ (by simp), binary_length] at h0
  have h1 := dockKeep h0 jSlotsCP65 (by decide) (fun _ => 0)
    ![T0, T1, T2, T3, T4, frame (binary Wc s), frame (binary Wc s'), T7, T8, T9, [x], List.replicate cap false]
    (fun _ => rfl) (by intro j; fin_cases j <;> rfl)
  rw [install_jCP65] at h1
  have h2 := h1.embed (fun _ : Fin 1 => 0) (fun _ : Fin 1 => List.replicate cap' false)
  refine (h2.congr_in ?_ ?_).congr ?_ ?_
  · funext i; refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp
  · funext i; fin_cases i <;> rfl
  · funext i; refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp
  · funext i; fin_cases i <;> rfl

/-- The bank after the second pass: the first sum on tape 6, the second on tape 5. -/
def joinV2 (A B : List (List Bool)) (Wc : ℕ) (ra rb : List Bool) (s1 : ℕ) (x : Bool) (cap cap' : ℕ) (m2 : MS) :
    Fin (11 + 1 + 1) → List Bool :=
  ![streamOf A, streamOf B, frame (reg A m2.i ra), frame (reg B m2.j rb), frame (binary Wc m2.i),
    frame (binary Wc m2.s), frame (binary Wc s1), [m2.t], [decide (m2.i < A.length)], [decide (m2.j < B.length)],
    [x], List.replicate cap false, List.replicate cap' false]

def joinH2 (A B : List (List Bool)) (m2 : MS) : Fin (11 + 1 + 1) → ℕ :=
  ![pre A (m2.i + 1), pre B (m2.j + 1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

theorem join_pass2 (A B : List (List Bool)) (W Wc : ℕ) (ra rb : List Bool) (S : Shape A B W ra rb)
    (sA : A.Pairwise (fun a b => value a ≤ value b)) (sB : B.Pairwise (fun a b => value a ≤ value b))
    (c1 s1 : ℕ) (t1 av1 bv1 x : Bool) (cap cap' : ℕ) (hcap : 2 * W + 2 * Wc + 2 ≤ cap) :
    ∃ m2 : MS, m2.s = (B.map (fun b => A.countP (fun a => decide (rel false a b)))).sum ∧
      Step (TapeEmbedding.machine 1 (jPass false)) (jPassCost W Wc (A.length + B.length)) (fun _ => 0)
        ![streamOf A, streamOf B, frame ra, frame rb, frame (binary Wc c1), frame (binary Wc s1), frame (binary Wc s1),
          [t1], [av1], [bv1], [x], List.replicate cap false, List.replicate cap' false]
        (joinH2 A B m2) (joinV2 A B Wc ra rb s1 x cap cap' m2) := by
  obtain ⟨m2, hs2, h2⟩ := jPass_run A B W Wc ra rb (frame (binary Wc s1)) S sA sB false c1 s1 t1 av1 bv1 x cap hcap
  have h2' := h2.embed (fun _ : Fin 1 => 0) (fun _ : Fin 1 => List.replicate cap' false)
  refine ⟨m2, hs2, (h2'.congr_in ?_ ?_).congr ?_ ?_⟩
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl

theorem join_sub (A B : List (List Bool)) (Wc : ℕ) (ra rb : List Bool) (s1 : ℕ) (x : Bool) (cap cap' : ℕ)
    (m2 : MS) (hle : m2.s ≤ s1) (hcap : 2 * Wc + 1 ≤ cap) :
    Step (TapeEmbedding.machine 1 jSub) (2 * (2 * Wc + 1) + 2) (joinH2 A B m2) (joinV2 A B Wc ra rb s1 x cap cap' m2)
      (joinH2 A B m2)
      ![streamOf A, streamOf B, frame (reg A m2.i ra), frame (reg B m2.j rb), frame (binary Wc m2.i),
        frame (binary Wc m2.s), frame (binary Wc (s1 - m2.s)), [m2.t], [decide (m2.i < A.length)],
        [decide (m2.j < B.length)], [x], List.replicate cap false, List.replicate cap' false] := by
  have h3 := RippleIn.run sum3 borrow3 false (binary Wc s1) (binary Wc m2.s) (by simp)
  rw [ripple_sub Wc s1 m2.s false (by simpa using hle), binary_length] at h3
  simp only [Bool.toNat_false, Nat.sub_zero] at h3
  have h3' : Step (RippleIn.machine sum3 borrow3 false) (2 * Wc + 1) (fun _ => 0)
      ![frame (binary Wc s1), frame (binary Wc m2.s)] ![2 * Wc, 2 * Wc]
      ![frame (binary Wc (s1 - m2.s)), frame (binary Wc m2.s)] := h3.congr_in (by funext i; fin_cases i <;> rfl) rfl
  have h3m := maskZero h3' sel2B (by intro j hj; fin_cases j <;> simp [sel2B] at hj) (cap := cap) hcap
  have h3m' : Step (MaskedReset.machine (RippleIn.machine sum3 borrow3 false) sel2B) (2 * (2 * Wc + 1) + 2) (fun _ => 0)
      ![frame (binary Wc s1), frame (binary Wc m2.s), List.replicate cap false] (fun _ => 0)
      ![frame (binary Wc (s1 - m2.s)), frame (binary Wc m2.s), List.replicate cap false] := by
    refine (h3m.congr_in rfl ?_).congr rfl ?_ <;> funext i <;> fin_cases i <;> rfl
  have h3d := dockKeep h3m' jSlotsSB65 (by decide) ![pre A (m2.i + 1), pre B (m2.j + 1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    ![streamOf A, streamOf B, frame (reg A m2.i ra), frame (reg B m2.j rb), frame (binary Wc m2.i),
      frame (binary Wc m2.s), frame (binary Wc s1), [m2.t], [decide (m2.i < A.length)], [decide (m2.j < B.length)],
      [x], List.replicate cap false]
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  rw [install_jSB65] at h3d
  have h3e := h3d.embed (fun _ : Fin 1 => 0) (fun _ : Fin 1 => List.replicate cap' false)
  refine (h3e.congr_in ?_ ?_).congr ?_ ?_
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl

theorem join_run (A B : List (List Bool)) (W Wc : ℕ) (ra0 rb0 : List Bool) (S : Shape A B W ra0 rb0)
    (sA : A.Pairwise (fun a b => value a ≤ value b)) (sB : B.Pairwise (fun a b => value a ≤ value b))
    (c0 s10 s20 : ℕ) (t0 av0 bv0 x : Bool) (cap cap' : ℕ) (hcap : 2 * W + 2 * Wc + 2 ≤ cap)
    (hcap' : jPassCost W Wc (A.length + B.length) ≤ cap') :
    ∃ (H' : Fin (11 + 1 + 1) → ℕ) (T' : Fin (11 + 1 + 1) → List Bool),
      Step joinM (joinCost W Wc (A.length + B.length)) (fun _ => 0)
        ![streamOf A, streamOf B, frame ra0, frame rb0, frame (binary Wc c0), frame (binary Wc s10),
          frame (binary Wc s20), [t0], [av0], [bv0], [x], List.replicate cap false, List.replicate cap' false]
        H' T' ∧
      T' 6 = frame (binary Wc (joinCount A B)) ∧ T' 0 = streamOf A ∧ T' 1 = streamOf B := by
  obtain ⟨m1, hs1, h1⟩ := join_pass1 A B W Wc ra0 rb0 S sA sB c0 s10 s20 t0 av0 bv0 x cap cap' hcap hcap'
  have hc := join_copy Wc m1.s s20 (streamOf A) (streamOf B) (frame (reg A m1.i ra0)) (frame (reg B m1.j rb0))
    (frame (binary Wc m1.i)) [m1.t] [decide (m1.i < A.length)] [decide (m1.j < B.length)] x cap cap' (by omega)
  have S' : Shape A B W (reg A m1.i ra0) (reg B m1.j rb0) :=
    ⟨S.hA, S.hB, S.hW, reg_length A W m1.i S.hA ra0 S.hra, reg_length B W m1.j S.hB rb0 S.hrb⟩
  obtain ⟨m2, hs2, h2⟩ := join_pass2 A B W Wc (reg A m1.i ra0) (reg B m1.j rb0) S' sA sB m1.i m1.s m1.t
    (decide (m1.i < A.length)) (decide (m1.j < B.length)) x cap cap' hcap
  have hle : m2.s ≤ m1.s := by rw [hs1, hs2, sums_join A B W S.hA S.hB]; omega
  have h3 := join_sub A B Wc (reg A m1.i ra0) (reg B m1.j rb0) m1.s x cap cap' m2 hle (by omega)
  refine ⟨_, _, ((h1.seq hc).seq h2).seq h3, ?_, rfl, rfl⟩
  show frame (binary Wc (m1.s - m2.s)) = frame (binary Wc (joinCount A B))
  rw [hs1, hs2, sums_join A B W S.hA S.hB]
  congr 2
  omega

/-! ## Cost in a class, the bridge to the kernel reference, twins -/

theorem joinCost_le (W Wc n q e : ℕ) (hq : 1 ≤ q) (hW : W ≤ q) (hWc : Wc ≤ q) (hn : n ≤ 2 ^ e * q) :
    joinCost W Wc n ≤ 400 * (2 ^ e * q ^ 2) := by
  have ha : 1 ≤ 2 ^ e := Nat.one_le_two_pow
  have h1 : jBodyCost W Wc + 2 ≤ 40 * q := by unfold jBodyCost armCost loadCost; omega
  have h2 : n * (jBodyCost W Wc + 2) ≤ (2 ^ e * q) * (40 * q) := Nat.mul_le_mul hn h1
  have e1 : (2 ^ e * q) * (40 * q) = 40 * (2 ^ e * q ^ 2) := by ring
  have hq2 : q ≤ 2 ^ e * q ^ 2 := by
    calc q = 1 * q ^ 1 := by ring
      _ ≤ 2 ^ e * q ^ 2 := Nat.mul_le_mul ha (Nat.pow_le_pow_right hq (by norm_num))
  have h3 : jPassCost W Wc n ≤ 100 * (2 ^ e * q ^ 2) := by
    unfold jPassCost jInitCost loadCost
    omega
  unfold joinCost
  omega

/-- **The join count's cost in a named class**: `≤ 400·2^e·q²` when the streams hold at most `2^e·q` words and
the widths are at most `q`, so within any class of exponent `≥ e` and degree `≥ 2`. -/
theorem join_within {E : Envelope} {cls : BudgetClass} {q k psi W Wc n e : ℕ} (hq : 1 ≤ q) (hW : W ≤ q)
    (hWc : Wc ≤ q) (hn : n ≤ 2 ^ e * q) (he : e ≤ classExp E cls q k psi) (hd : 2 ≤ classDeg E cls) :
    Within E cls 400 q k psi (joinCost W Wc n) :=
  Within.of_scaled hq (joinCost_le W Wc n q e hq hW hWc hn) he hd

/-- Twin: the two merges on a small instance (values `A = {2, 3}`, `B = {1, 2, 2}`) and the count `2`. -/
theorem join_twin :
    (mstate [[false, true], [true, true]] [[true, false], [false, true], [false, true]] true [false, false]
        [false, false] false 4).j = 3 ∧
    (mstate [[false, true], [true, true]] [[true, false], [false, true], [false, true]] false [false, false]
        [false, false] false 3).j = 3 ∧
    (mstate [[false, true], [true, true]] [[true, false], [false, true], [false, true]] true [false, false]
        [false, false] false 4).s -
      (mstate [[false, true], [true, true]] [[true, false], [false, true], [false, true]] false [false, false]
        [false, false] false 3).s =
      joinCount [[false, true], [true, true]] [[true, false], [false, true], [false, true]] := by decide

/-- Executed runs of the new small machines: the comparison (`2 < 3`, `≤` on equal words) and the ripple add. -/
theorem foldCell_twin :
    (runFrom (FoldCell.machine cmpStep false) 20 ⟨(FoldCell.machine cmpStep false).start, ![0, 0, 0],
        ![frame [false, true], frame [true, true], [false]]⟩).map (fun r => r.final.tapes 2) = some [true] ∧
    (runFrom (FoldCell.machine cmpStep true) 20 ⟨(FoldCell.machine cmpStep true).start, ![0, 0, 0],
        ![frame [true, false], frame [true, false], [false]]⟩).map (fun r => r.final.tapes 2) = some [true] := by
  decide

theorem ripple_twin :
    (runFrom (RippleIn.machine sum3 carry3 false) 20 ⟨(RippleIn.machine sum3 carry3 false).start, ![0, 0],
        ![frame (binary 3 3), frame (binary 3 2)]⟩).map (fun r => r.final.tapes 0) = some (frame (binary 3 5)) ∧
    (runFrom (RippleIn.machine sum3 borrow3 false) 20 ⟨(RippleIn.machine sum3 borrow3 false).start, ![0, 0],
        ![frame (binary 3 6), frame (binary 3 2)]⟩).map (fun r => r.final.tapes 0) = some (frame (binary 3 4)) := by
  decide

end NearCubicWires.WireExponent3_5.Block
