import Proof.Wire_3_5.GF2Machines

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.GF2
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.SignedSortKey NearCubicWires.WireExponent3_5.Block
open NearCubicWires.WireExponent3_5.Cost

/-! ## `ZipFlag g`: `H := zipWith (g f) H P` in place -/

namespace ZipFlag
open Three (act cfg)

def machine (g : Bool → Bool → Bool → Bool) : Machine 3 6 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 5
  rule := fun q sc =>
    if q.val = 0 then some (if sc 2 then act 2 none none none .stay .stay .stay else act 1 none none none .stay .stay .stay)
    else if q.val = 1 then
      some (if sc 0 then act 3 none none none .right .right .stay else act 5 none none none .stay .stay .stay)
    else if q.val = 2 then
      some (if sc 0 then act 4 none none none .right .right .stay else act 5 none none none .stay .stay .stay)
    else if q.val = 3 then some (act 1 (some (g false (sc 0) (sc 1))) none none .right .right .stay)
    else if q.val = 4 then some (act 2 (some (g true (sc 0) (sc 1))) none none .right .right .stay)
    else none

variable (g : Bool → Bool → Bool → Bool)

def mark (f : Bool) : Fin 6 := if f then 2 else 1
def bitS (f : Bool) : Fin 6 := if f then 4 else 3

theorem init_step (f : Bool) (H P G : List Bool) (hg : ℕ) (hr : readTapeBit G hg = f) :
    step (machine g) (cfg 0 H P G 0 0 hg) = some (cfg (mark f) H P G 0 0 hg) := by
  cases f
  · exact Three.step_cfg (machine g) 0 1 H P G 0 0 hg none none none .stay .stay .stay (by simp [machine, hr])
  · exact Three.step_cfg (machine g) 0 2 H P G 0 0 hg none none none .stay .stay .stay (by simp [machine, hr])

theorem mark_step (f : Bool) (H P G : List Bool) (hh hp hg : ℕ) (hr : readTapeBit H hh = true) :
    step (machine g) (cfg (mark f) H P G hh hp hg) = some (cfg (bitS f) H P G (hh + 1) (hp + 1) hg) := by
  cases f
  · exact Three.step_cfg (machine g) 1 3 H P G hh hp hg none none none .right .right .stay (by simp [machine, hr])
  · exact Three.step_cfg (machine g) 2 4 H P G hh hp hg none none none .right .right .stay (by simp [machine, hr])

theorem end_step (f : Bool) (H P G : List Bool) (hh hp hg : ℕ) (hr : readTapeBit H hh = false) :
    step (machine g) (cfg (mark f) H P G hh hp hg) = some (cfg 5 H P G hh hp hg) := by
  cases f
  · exact Three.step_cfg (machine g) 1 5 H P G hh hp hg none none none .stay .stay .stay (by simp [machine, hr])
  · exact Three.step_cfg (machine g) 2 5 H P G hh hp hg none none none .stay .stay .stay (by simp [machine, hr])

theorem bit_step (f a b : Bool) (H P G : List Bool) (hh hp hg : ℕ) (ha : readTapeBit H hh = a)
    (hb : readTapeBit P hp = b) :
    step (machine g) (cfg (bitS f) H P G hh hp hg) =
      some (cfg (mark f) (writeTapeBit H hh (g f a b)) P G (hh + 1) (hp + 1) hg) := by
  cases f
  · show step (machine g) (cfg 3 H P G hh hp hg) =
      some (cfg 1 (writeTapeBit H hh (g false a b)) P G (hh + 1) (hp + 1) hg)
    rw [Three.step_cfg (machine g) 3 1 H P G hh hp hg (some (g false a b)) none none .right .right .stay
      (by simp [machine, ha, hb])]
    rfl
  · show step (machine g) (cfg 4 H P G hh hp hg) =
      some (cfg 2 (writeTapeBit H hh (g true a b)) P G (hh + 1) (hp + 1) hg)
    rw [Three.step_cfg (machine g) 4 2 H P G hh hp hg (some (g true a b)) none none .right .right .stay
      (by simp [machine, ha, hb])]
    rfl

theorem timed (f : Bool) (G : List Bool) (hg : ℕ) (u : List Bool) : ∀ (v preH preP postP : List Bool),
    u.length = v.length →
    RecoveryExecution.Timed (machine g) (2 * u.length + 1)
      (cfg (mark f) (preH ++ frame u) (preP ++ frame v ++ postP) G preH.length preP.length hg)
      (cfg 5 (preH ++ frame (List.zipWith (g f) u v)) (preP ++ frame v ++ postP) G
        (preH.length + 2 * u.length) (preP.length + 2 * u.length) hg) := by
  induction u with
  | nil =>
    intro v preH preP postP _
    have hs := end_step g f (preH ++ frame []) (preP ++ frame v ++ postP) G preH.length preP.length hg
      (by simpa [frame] using Streaming.read_append preH [] false)
    simpa [frame] using RecoveryExecution.Timed.single (p := machine g) (by cases f <;> rfl) hs
  | cons a u ih =>
    intro v preH preP postP hl
    obtain ⟨b, v, rfl⟩ : ∃ b v', v = b :: v' := by
      cases v with
      | nil => simp at hl
      | cons b v => exact ⟨b, v, rfl⟩
    have hl' : u.length = v.length := by simpa using hl
    have hr1 : readTapeBit (preH ++ frame (a :: u)) preH.length = true := by
      simpa [frame] using Streaming.read_append preH (a :: frame u) true
    have hra : readTapeBit (preH ++ frame (a :: u)) (preH.length + 1) = a := by
      simpa [frame] using Streaming.read_append (preH ++ [true]) (frame u) a
    have hrb : readTapeBit (preP ++ frame (b :: v) ++ postP) (preP.length + 1) = b := by
      simpa [frame, List.append_assoc] using Streaming.read_append (preP ++ [true]) (frame v ++ postP) b
    have hs1 := mark_step g f (preH ++ frame (a :: u)) (preP ++ frame (b :: v) ++ postP) G preH.length preP.length hg hr1
    have hs2 := bit_step g f a b (preH ++ frame (a :: u)) (preP ++ frame (b :: v) ++ postP) G (preH.length + 1)
      (preP.length + 1) hg hra hrb
    have hw : writeTapeBit (preH ++ frame (a :: u)) (preH.length + 1) (g f a b) = preH ++ [true, g f a b] ++ frame u := by
      simpa [frame] using write_mid (preH ++ [true]) (frame u) a (g f a b)
    rw [hw] at hs2
    have t1 := RecoveryExecution.Timed.single (p := machine g) (by cases f <;> rfl) hs1
    have t2 := RecoveryExecution.Timed.single (p := machine g) (by cases f <;> rfl) hs2
    have tail := ih v (preH ++ [true, g f a b]) (preP ++ [true, b]) postP hl'
    have eP : preP ++ [true, b] ++ frame v ++ postP = preP ++ frame (b :: v) ++ postP := by simp [frame]
    have e3 : (preH ++ [true, g f a b]).length = preH.length + 1 + 1 := by simp
    have e4 : (preP ++ [true, b]).length = preP.length + 1 + 1 := by simp
    have e5 : preH ++ [true, g f a b] ++ frame (List.zipWith (g f) u v) =
        preH ++ frame (List.zipWith (g f) (a :: u) (b :: v)) := by simp [frame]
    have e7 : preH.length + 1 + 1 + 2 * u.length = preH.length + 2 * (a :: u).length := by simp; omega
    have e8 : preP.length + 1 + 1 + 2 * u.length = preP.length + 2 * (a :: u).length := by simp; omega
    rw [eP, e3, e4, e5, e7, e8] at tail
    have := (t1.trans t2).trans tail
    rwa [show 1 + 1 + (2 * u.length + 1) = 2 * (a :: u).length + 1 by simp; omega] at this

theorem run (u v G : List Bool) (hg : ℕ) (hl : u.length = v.length) :
    Step (machine g) (2 * u.length + 2) ![0, 0, hg] ![frame u, frame v, G]
      ![2 * u.length, 2 * u.length, hg] ![frame (List.zipWith (g (readTapeBit G hg)) u v), frame v, G] := by
  have hs := init_step g (readTapeBit G hg) (frame u) (frame v) G hg rfl
  have t0 := RecoveryExecution.Timed.single (p := machine g) rfl hs
  have t1 := timed g (readTapeBit G hg) G hg u v [] [] [] hl
  simp only [List.nil_append, List.append_nil, List.length_nil, Nat.zero_add] at t1
  obtain ⟨r, hr, hf, hsteps⟩ := (t0.trans t1).run rfl
  refine ⟨r, ?_, ?_, ?_, by omega⟩
  · rw [show 2 * u.length + 2 = 1 + (2 * u.length + 1) by omega]; exact hr
  · rw [hf]; rfl
  · rw [hf]; rfl

end ZipFlag

/-! ## `EqCell neg`: the cell becomes `neg ⊕ (u = v)` -/

namespace EqCell
open Three (act cfg)

def machine (neg : Bool) : Machine 3 5 where
  descriptionBits := 0
  start := 1
  halted := fun q => q.val == 4
  rule := fun q sc =>
    if q.val = 0 then
      some (if sc 0 then act 2 none none none .right .right .stay else act 4 none none (some neg) .stay .stay .stay)
    else if q.val = 1 then
      some (if sc 0 then act 3 none none none .right .right .stay else act 4 none none (some (!neg)) .stay .stay .stay)
    else if q.val = 2 then some (act 0 none none none .right .right .stay)
    else if q.val = 3 then some (if sc 0 == sc 1 then act 1 none none none .right .right .stay
      else act 0 none none none .right .right .stay)
    else none

variable (neg : Bool)

def mark (e : Bool) : Fin 5 := if e then 1 else 0
def bitS (e : Bool) : Fin 5 := if e then 3 else 2

theorem mark_step (e : Bool) (X Y F : List Bool) (hx hy : ℕ) (hr : readTapeBit X hx = true) :
    step (machine neg) (cfg (mark e) X Y F hx hy 0) = some (cfg (bitS e) X Y F (hx + 1) (hy + 1) 0) := by
  cases e
  · exact Three.step_cfg (machine neg) 0 2 X Y F hx hy 0 none none none .right .right .stay (by simp [machine, hr])
  · exact Three.step_cfg (machine neg) 1 3 X Y F hx hy 0 none none none .right .right .stay (by simp [machine, hr])

theorem end_step (e c : Bool) (X Y : List Bool) (hx hy : ℕ) (hr : readTapeBit X hx = false) :
    step (machine neg) (cfg (mark e) X Y [c] hx hy 0) = some (cfg 4 X Y [xor neg e] hx hy 0) := by
  cases e
  · show step (machine neg) (cfg 0 X Y [c] hx hy 0) = some (cfg 4 X Y [xor neg false] hx hy 0)
    rw [Three.step_cfg (machine neg) 0 4 X Y [c] hx hy 0 none none (some neg) .stay .stay .stay
      (by simp [machine, hr])]
    simp [Two.wr, HeadMove.apply, writeTapeBit]
  · show step (machine neg) (cfg 1 X Y [c] hx hy 0) = some (cfg 4 X Y [xor neg true] hx hy 0)
    rw [Three.step_cfg (machine neg) 1 4 X Y [c] hx hy 0 none none (some (!neg)) .stay .stay .stay
      (by simp [machine, hr])]
    simp [Two.wr, HeadMove.apply, writeTapeBit]

theorem bit_step (e a b : Bool) (X Y F : List Bool) (hx hy : ℕ) (ha : readTapeBit X hx = a) (hb : readTapeBit Y hy = b) :
    step (machine neg) (cfg (bitS e) X Y F hx hy 0) = some (cfg (mark (e && a == b)) X Y F (hx + 1) (hy + 1) 0) := by
  cases e
  · show step (machine neg) (cfg 2 X Y F hx hy 0) = some (cfg 0 X Y F (hx + 1) (hy + 1) 0)
    exact Three.step_cfg (machine neg) 2 0 X Y F hx hy 0 none none none .right .right .stay (by simp [machine])
  · cases h : (a == b)
    · have h' : ¬ a = b := by simpa using h
      show step (machine neg) (cfg 3 X Y F hx hy 0) = some (cfg 0 X Y F (hx + 1) (hy + 1) 0)
      exact Three.step_cfg (machine neg) 3 0 X Y F hx hy 0 none none none .right .right .stay
        (by simp [machine, ha, hb, h'])
    · have h' : a = b := by simpa using h
      show step (machine neg) (cfg 3 X Y F hx hy 0) = some (cfg 1 X Y F (hx + 1) (hy + 1) 0)
      exact Three.step_cfg (machine neg) 3 1 X Y F hx hy 0 none none none .right .right .stay
        (by simp [machine, ha, hb, h'])

/-- The reference fold: equality of two words of equal length. -/
def eqFold : Bool → List Bool → List Bool → Bool
  | e, a :: u, b :: v => eqFold (e && a == b) u v
  | e, _, _ => e

theorem eqFold_eq (u v : List Bool) (h : u.length = v.length) (e : Bool) : eqFold e u v = (e && decide (u = v)) := by
  induction u generalizing v e with
  | nil =>
    cases v with
    | nil => simp [eqFold]
    | cons b v => simp at h
  | cons a u ih =>
    cases v with
    | nil => simp at h
    | cons b v =>
      rw [eqFold, ih v (by simpa using h)]
      cases e <;> cases a <;> cases b <;> simp

theorem timed (c : Bool) (u : List Bool) : ∀ (v preX preY postY : List Bool) (e : Bool), u.length = v.length →
    RecoveryExecution.Timed (machine neg) (2 * u.length + 1)
      (cfg (mark e) (preX ++ frame u) (preY ++ frame v ++ postY) [c] preX.length preY.length 0)
      (cfg 4 (preX ++ frame u) (preY ++ frame v ++ postY) [xor neg (eqFold e u v)]
        (preX.length + 2 * u.length) (preY.length + 2 * u.length) 0) := by
  induction u with
  | nil =>
    intro v preX preY postY e _
    have hs := end_step neg e c (preX ++ frame []) (preY ++ frame v ++ postY) preX.length preY.length
      (by simpa [frame] using Streaming.read_append preX [] false)
    simpa [frame, eqFold] using RecoveryExecution.Timed.single (p := machine neg) (by cases e <;> rfl) hs
  | cons a u ih =>
    intro v preX preY postY e hl
    obtain ⟨b, v, rfl⟩ : ∃ b v', v = b :: v' := by
      cases v with
      | nil => simp at hl
      | cons b v => exact ⟨b, v, rfl⟩
    have hl' : u.length = v.length := by simpa using hl
    have hr1 : readTapeBit (preX ++ frame (a :: u)) preX.length = true := by
      simpa [frame] using Streaming.read_append preX (a :: frame u) true
    have hra : readTapeBit (preX ++ frame (a :: u)) (preX.length + 1) = a := by
      simpa [frame] using Streaming.read_append (preX ++ [true]) (frame u) a
    have hrb : readTapeBit (preY ++ frame (b :: v) ++ postY) (preY.length + 1) = b := by
      simpa [frame, List.append_assoc] using Streaming.read_append (preY ++ [true]) (frame v ++ postY) b
    have hs1 := mark_step neg e (preX ++ frame (a :: u)) (preY ++ frame (b :: v) ++ postY) [c] preX.length preY.length hr1
    have hs2 := bit_step neg e a b (preX ++ frame (a :: u)) (preY ++ frame (b :: v) ++ postY) [c] (preX.length + 1)
      (preY.length + 1) hra hrb
    have t1 := RecoveryExecution.Timed.single (p := machine neg) (by cases e <;> rfl) hs1
    have t2 := RecoveryExecution.Timed.single (p := machine neg) (by cases e <;> rfl) hs2
    have tail := ih v (preX ++ [true, a]) (preY ++ [true, b]) postY (e && a == b) hl'
    have eX : preX ++ [true, a] ++ frame u = preX ++ frame (a :: u) := by simp [frame]
    have eY : preY ++ [true, b] ++ frame v ++ postY = preY ++ frame (b :: v) ++ postY := by simp [frame]
    have e3 : (preX ++ [true, a]).length = preX.length + 1 + 1 := by simp
    have e4 : (preY ++ [true, b]).length = preY.length + 1 + 1 := by simp
    have e5 : eqFold (e && a == b) u v = eqFold e (a :: u) (b :: v) := rfl
    have e7 : preX.length + 1 + 1 + 2 * u.length = preX.length + 2 * (a :: u).length := by simp; omega
    have e8 : preY.length + 1 + 1 + 2 * u.length = preY.length + 2 * (a :: u).length := by simp; omega
    rw [eX, eY, e3, e4, e5, e7, e8] at tail
    have := (t1.trans t2).trans tail
    rwa [show 1 + 1 + (2 * u.length + 1) = 2 * (a :: u).length + 1 by simp; omega] at this

theorem run (u v : List Bool) (c : Bool) (hl : u.length = v.length) :
    Step (machine neg) (2 * u.length + 1) ![0, 0, 0] ![frame u, frame v, [c]]
      ![2 * u.length, 2 * u.length, 0] ![frame u, frame v, [xor neg (decide (u = v))]] := by
  obtain ⟨r, hr, hf, hs⟩ := (timed neg c u v [] [] [] true hl).run rfl
  simp only [List.nil_append, List.append_nil, List.length_nil, Nat.zero_add] at hr hf
  refine ⟨r, hr, ?_, ?_, by omega⟩
  · rw [hf]; rfl
  · rw [hf, eqFold_eq u v hl]; simp [Three.cfg]

end EqCell

/-! ## `IncFlag`: `H := H + f` in place -/

/-- Add a carry bit to a word, low bit first (the top carry drops). -/
def incBits : Bool → List Bool → List Bool
  | _, [] => []
  | c, a :: w => xor a c :: incBits (a && c) w

@[simp] theorem incBits_length (c : Bool) (w : List Bool) : (incBits c w).length = w.length := by
  induction w generalizing c with
  | nil => rfl
  | cons a w ih => simp [incBits, ih]

theorem incBits_binary (d n : ℕ) (c : Bool) : incBits c (binary d n) = binary d (n + c.toNat) := by
  induction d generalizing n c with
  | zero => rfl
  | succ d ih =>
    have e1 : binary (d + 1) n = (n % 2 == 1) :: binary d (n / 2) := rfl
    have e2 : binary (d + 1) (n + c.toNat) = ((n + c.toNat) % 2 == 1) :: binary d ((n + c.toNat) / 2) := rfl
    rw [e1, e2]
    simp only [incBits]
    rw [ih (n / 2) ((n % 2 == 1) && c)]
    congr 1
    · cases c <;> rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [h, Nat.add_mod]
    · congr 1
      cases c <;> rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [h] <;> omega

namespace IncFlag
open Two (act cfg wr)

def machine : Machine 2 6 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 5
  rule := fun q sc =>
    if q.val = 0 then some (if sc 1 then act 2 none none .stay .stay else act 1 none none .stay .stay)
    else if q.val = 1 then some (if sc 0 then act 3 none none .right .stay else act 5 none none .stay .stay)
    else if q.val = 2 then some (if sc 0 then act 4 none none .right .stay else act 5 none none .stay .stay)
    else if q.val = 3 then some (act 1 (some (sc 0)) none .right .stay)
    else if q.val = 4 then some (if sc 0 then act 2 (some false) none .right .stay else act 1 (some true) none .right .stay)
    else none

def mark (c : Bool) : Fin 6 := if c then 2 else 1
def bitS (c : Bool) : Fin 6 := if c then 4 else 3

theorem init_step (f : Bool) (H G : List Bool) (hg : ℕ) (hr : readTapeBit G hg = f) :
    step machine (cfg 0 H G 0 hg) = some (cfg (mark f) H G 0 hg) := by
  cases f
  · exact Two.step_cfg machine 0 1 H G 0 hg none none .stay .stay (by simp [machine, hr])
  · exact Two.step_cfg machine 0 2 H G 0 hg none none .stay .stay (by simp [machine, hr])

theorem mark_step (c : Bool) (H G : List Bool) (hh hg : ℕ) (hr : readTapeBit H hh = true) :
    step machine (cfg (mark c) H G hh hg) = some (cfg (bitS c) H G (hh + 1) hg) := by
  cases c
  · exact Two.step_cfg machine 1 3 H G hh hg none none .right .stay (by simp [machine, hr])
  · exact Two.step_cfg machine 2 4 H G hh hg none none .right .stay (by simp [machine, hr])

theorem end_step (c : Bool) (H G : List Bool) (hh hg : ℕ) (hr : readTapeBit H hh = false) :
    step machine (cfg (mark c) H G hh hg) = some (cfg 5 H G hh hg) := by
  cases c
  · exact Two.step_cfg machine 1 5 H G hh hg none none .stay .stay (by simp [machine, hr])
  · exact Two.step_cfg machine 2 5 H G hh hg none none .stay .stay (by simp [machine, hr])

theorem bit_step (c a : Bool) (H G : List Bool) (hh hg : ℕ) (hr : readTapeBit H hh = a) :
    step machine (cfg (bitS c) H G hh hg) = some (cfg (mark (a && c)) (writeTapeBit H hh (xor a c)) G (hh + 1) hg) := by
  cases c <;> cases a
  · show step machine (cfg 3 H G hh hg) = some (cfg 1 (writeTapeBit H hh false) G (hh + 1) hg)
    exact Two.step_cfg machine 3 1 H G hh hg (some false) none .right .stay (by simp [machine, hr])
  · show step machine (cfg 3 H G hh hg) = some (cfg 1 (writeTapeBit H hh true) G (hh + 1) hg)
    exact Two.step_cfg machine 3 1 H G hh hg (some true) none .right .stay (by simp [machine, hr])
  · show step machine (cfg 4 H G hh hg) = some (cfg 1 (writeTapeBit H hh true) G (hh + 1) hg)
    exact Two.step_cfg machine 4 1 H G hh hg (some true) none .right .stay (by simp [machine, hr])
  · show step machine (cfg 4 H G hh hg) = some (cfg 2 (writeTapeBit H hh false) G (hh + 1) hg)
    exact Two.step_cfg machine 4 2 H G hh hg (some false) none .right .stay (by simp [machine, hr])

theorem timed (G : List Bool) (hg : ℕ) (w : List Bool) : ∀ (pre : List Bool) (c : Bool),
    RecoveryExecution.Timed machine (2 * w.length + 1) (cfg (mark c) (pre ++ frame w) G pre.length hg)
      (cfg 5 (pre ++ frame (incBits c w)) G (pre.length + 2 * w.length) hg) := by
  induction w with
  | nil =>
    intro pre c
    have hs := end_step c (pre ++ frame []) G pre.length hg (by simpa [frame] using Streaming.read_append pre [] false)
    simpa [frame, incBits] using RecoveryExecution.Timed.single (p := machine) (by cases c <;> rfl) hs
  | cons a w ih =>
    intro pre c
    have hr1 : readTapeBit (pre ++ frame (a :: w)) pre.length = true := by
      simpa [frame] using Streaming.read_append pre (a :: frame w) true
    have hr2 : readTapeBit (pre ++ frame (a :: w)) (pre.length + 1) = a := by
      simpa [frame] using Streaming.read_append (pre ++ [true]) (frame w) a
    have hs1 := mark_step c (pre ++ frame (a :: w)) G pre.length hg hr1
    have hs2 := bit_step c a (pre ++ frame (a :: w)) G (pre.length + 1) hg hr2
    have hw : writeTapeBit (pre ++ frame (a :: w)) (pre.length + 1) (xor a c) = pre ++ [true, xor a c] ++ frame w := by
      simpa [frame] using write_mid (pre ++ [true]) (frame w) a (xor a c)
    rw [hw] at hs2
    have t1 := RecoveryExecution.Timed.single (p := machine) (by cases c <;> rfl) hs1
    have t2 := RecoveryExecution.Timed.single (p := machine) (by cases c <;> rfl) hs2
    have tail := ih (pre ++ [true, xor a c]) (a && c)
    have e3 : (pre ++ [true, xor a c]).length = pre.length + 1 + 1 := by simp
    have e5 : pre ++ [true, xor a c] ++ frame (incBits (a && c) w) = pre ++ frame (incBits c (a :: w)) := by
      simp [frame, incBits]
    have e7 : pre.length + 1 + 1 + 2 * w.length = pre.length + 2 * (a :: w).length := by simp; omega
    rw [e3, e5, e7] at tail
    have := (t1.trans t2).trans tail
    rwa [show 1 + 1 + (2 * w.length + 1) = 2 * (a :: w).length + 1 by simp; omega] at this

theorem run (d n : ℕ) (G : List Bool) (hg : ℕ) :
    Step machine (2 * d + 2) ![0, hg] ![frame (binary d n), G]
      ![2 * d, hg] ![frame (binary d (n + (readTapeBit G hg).toNat)), G] := by
  have hs := init_step (readTapeBit G hg) (frame (binary d n)) G hg rfl
  have t0 := RecoveryExecution.Timed.single (p := machine) rfl hs
  have t1 := timed G hg (binary d n) [] (readTapeBit G hg)
  simp only [List.nil_append, List.length_nil, Nat.zero_add, binary_length, incBits_binary] at t1
  obtain ⟨r, hr, hf, hsteps⟩ := (t0.trans t1).run rfl
  refine ⟨r, ?_, ?_, ?_, by omega⟩
  · rw [show 2 * d + 2 = 1 + (2 * d + 1) by omega]; exact hr
  · rw [hf]; rfl
  · rw [hf]; rfl

end IncFlag

/-! ## `CellOp op`: one step on three cells -/

namespace CellOp
open Three (act cfg)

def machine (op : Bool → Bool → Bool → Bool) : Machine 3 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 1
  rule := fun q sc => if q.val = 0 then some (act 1 (some (op (sc 0) (sc 1) (sc 2))) none none .stay .stay .stay) else none

theorem run (op : Bool → Bool → Bool → Bool) (t a b : Bool) :
    Step (machine op) 1 ![0, 0, 0] ![[t], [a], [b]] ![0, 0, 0] ![[op t a b], [a], [b]] := by
  have hs : step (machine op) (cfg 0 [t] [a] [b] 0 0 0) = some (cfg 1 [op t a b] [a] [b] 0 0 0) := by
    rw [Three.step_cfg (machine op) 0 1 [t] [a] [b] 0 0 0 (some (op t a b)) none none .stay .stay .stay
      (by simp [machine, readTapeBit])]
    simp [Two.wr, HeadMove.apply, writeTapeBit]
  obtain ⟨r, hr, hf, hs'⟩ := (RecoveryExecution.Timed.single (p := machine op) rfl hs).run rfl
  exact ⟨r, hr, by rw [hf]; rfl, by rw [hf]; rfl, by omega⟩

end CellOp

/-! ## Part B: the period test

Tapes: 0 the power `ST`, 1 the counter `I`, 2 the modulus `P`, 3 the word `1`, 4 the word `2^ℓ-1`, 5 the LFSR
flag, 6 `S = [ST = 1]`, 7 `D = [I ≠ 2^ℓ-1]` (the loop's flag), 8 `E` (an early return to `1`), 9 the result
`R`, 10 the rewind log. Every bank has all heads at cell 0. -/

theorem dockH_zero {t u : ℕ} (slots : Fin t → Fin u) (hout : Fin t → ℕ) (sel : Fin u → Bool)
    (hsel : ∀ j, sel (slots j) = false → hout j = 0) :
    (fun i => if sel i then 0 else dockH slots (fun _ => 0) hout i) = fun _ => 0 := by
  funext i
  by_cases hs : sel i = true
  · simp [hs]
  · have hs' : sel i = false := by simpa using hs
    simp only [hs', Bool.false_eq_true, ↓reduceIte]
    cases hp : RecoveryFocus.pick slots i with
    | none => simp [dockH, hp]
    | some j =>
      have he := RecoveryFocus.slot_of_pick slots hp
      simp only [dockH, hp]
      exact hsel j (by rw [he]; exact hs')

theorem dockH_zero' {t u : ℕ} (slots : Fin t → Fin u) : dockH slots (fun _ => 0) (fun _ => 0) = fun _ => 0 := by
  funext i
  cases hp : RecoveryFocus.pick slots i with
  | none => simp [dockH, hp]
  | some j => simp [dockH, hp]

/-- A docked stage whose moved heads are rewound: all heads are at cell 0 before and after. -/
theorem maskedStage {k s n cap : ℕ} {M : Machine k s} {hout : Fin k → ℕ} {tin tout : Fin k → List Bool}
    (h : Step M n (fun _ => 0) tin hout tout) (slots : Fin k → Fin 10) (hi : Function.Injective slots)
    (sel : Fin 10 → Bool) (hsel : ∀ j, sel (slots j) = false → hout j = 0)
    (A : Fin 10 → List Bool) (hA : ∀ j, A (slots j) = tin j) (hcap : n ≤ cap) :
    Step (MaskedReset.machine (RecoveryFocus.machine slots M) sel) (2 * n + 2) (fun _ => 0)
      (Fin.addCases A (fun _ : Fin 1 => List.replicate cap false)) (fun _ => 0)
      (Fin.addCases (RecoveryRootRound.install slots A tout) (fun _ : Fin 1 => List.replicate cap false)) := by
  have hd := dockRun h slots hi (fun _ => 0) A (fun _ => rfl) hA
  have hm := hd.mask sel (fun _ _ => rfl) hcap
  refine (hm.congr_in ?_ rfl).congr ?_ rfl
  · funext i; refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [Fin.addCases_left]; exact congrFun (dockH_zero slots hout sel hsel) j
    · simp

/-- A docked stage that keeps every head at cell 0. -/
theorem plainStage {k s n : ℕ} {M : Machine k s} {tin tout : Fin k → List Bool}
    (h : Step M n (fun _ => 0) tin (fun _ => 0) tout) (slots : Fin k → Fin (10 + 1)) (hi : Function.Injective slots)
    (A : Fin (10 + 1) → List Bool) (hA : ∀ j, A (slots j) = tin j) :
    Step (RecoveryFocus.machine slots M) n (fun _ => 0) A (fun _ => 0) (RecoveryRootRound.install slots A tout) := by
  have hd := dockRun h slots hi (fun _ => 0) A (fun _ => rfl) hA
  rwa [dockH_zero'] at hd

def ptSlotsA : Fin 3 → Fin (10) := ![0, 3, 7]
theorem install_ptA (A : Fin (10) → List Bool) (v : Fin 3 → List Bool) :
    RecoveryRootRound.install ptSlotsA A v = ![v 0, A 1, A 2, v 1, A 4, A 5, A 6, v 2, A 8, A 9] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 1
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 2
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

def ptSlotsB : Fin 3 → Fin (10) := ![1, 3, 7]
theorem install_ptB (A : Fin (10) → List Bool) (v : Fin 3 → List Bool) :
    RecoveryRootRound.install ptSlotsB A v = ![A 0, v 0, A 2, v 1, A 4, A 5, A 6, v 2, A 8, A 9] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 1
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 2
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

def ptSlotsD : Fin 3 → Fin (10) := ![1, 4, 7]
theorem install_ptD (A : Fin (10) → List Bool) (v : Fin 3 → List Bool) :
    RecoveryRootRound.install ptSlotsD A v = ![A 0, v 0, A 2, A 3, v 1, A 5, A 6, v 2, A 8, A 9] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 1
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 2
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

def ptSlotsE : Fin 3 → Fin (10) := ![0, 3, 6]
theorem install_ptE (A : Fin (10) → List Bool) (v : Fin 3 → List Bool) :
    RecoveryRootRound.install ptSlotsE A v = ![v 0, A 1, A 2, v 1, A 4, A 5, v 2, A 7, A 8, A 9] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 1
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 2
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

def ptSlotsH : Fin 2 → Fin (10) := ![1, 7]
theorem install_ptH (A : Fin (10) → List Bool) (v : Fin 2 → List Bool) :
    RecoveryRootRound.install ptSlotsH A v = ![A 0, v 0, A 2, A 3, A 4, A 5, A 6, v 1, A 8, A 9] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 1
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

def ptSlotsC : Fin 3 → Fin (10 + 1) := ![8, 6, 7]
theorem install_ptC (A : Fin (10 + 1) → List Bool) (v : Fin 3 → List Bool) :
    RecoveryRootRound.install ptSlotsC A v = ![A 0, A 1, A 2, A 3, A 4, A 5, v 1, v 2, v 0, A 9, A 10] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 1
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 2
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

def ptSlotsF : Fin 3 → Fin (10 + 1) := ![5, 6, 7]
theorem install_ptF (A : Fin (10 + 1) → List Bool) (v : Fin 3 → List Bool) :
    RecoveryRootRound.install ptSlotsF A v = ![A 0, A 1, A 2, A 3, A 4, v 0, v 1, v 2, A 8, A 9, A 10] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 1
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 2
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

def ptSlotsG : Fin 4 → Fin (10 + 1) := ![0, 2, 5, 10]
theorem install_ptG (A : Fin (10 + 1) → List Bool) (v : Fin 4 → List Bool) :
    RecoveryRootRound.install ptSlotsG A v = ![v 0, A 1, v 1, A 3, A 4, v 2, A 6, A 7, A 8, A 9, v 3] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 1
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 2
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 3
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

def ptSlotsI : Fin 3 → Fin (10 + 1) := ![9, 6, 8]
theorem install_ptI (A : Fin (10 + 1) → List Bool) (v : Fin 3 → List Bool) :
    RecoveryRootRound.install ptSlotsI A v = ![A 0, A 1, A 2, A 3, A 4, A 5, v 1, A 7, v 2, v 0, A 10] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 1
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 2
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

/-! ### The stage machines -/

def copyG : Bool → Bool → Bool → Bool := fun _ _ b => b
def clearG : Bool → Bool → Bool → Bool := fun _ _ _ => false
def earlyOp : Bool → Bool → Bool → Bool := fun e s d => e || (s && d)
def falseOp : Bool → Bool → Bool → Bool := fun _ _ _ => false
def okOp : Bool → Bool → Bool → Bool := fun _ s e => s && !e
def selA : Fin 10 → Bool := fun i => decide (i = 0 ∨ i = 3)
def selB : Fin 10 → Bool := fun i => decide (i = 1 ∨ i = 3)
def selD : Fin 10 → Bool := fun i => decide (i = 1 ∨ i = 4)
def selH : Fin 10 → Bool := fun i => decide (i = 1)

noncomputable def stA := MaskedReset.machine (RecoveryFocus.machine ptSlotsA (ZipFlag.machine copyG)) selA
noncomputable def stB := MaskedReset.machine (RecoveryFocus.machine ptSlotsB (ZipFlag.machine clearG)) selB
noncomputable def stD := MaskedReset.machine (RecoveryFocus.machine ptSlotsD (EqCell.machine true)) selD
noncomputable def stE := MaskedReset.machine (RecoveryFocus.machine ptSlotsE (EqCell.machine false)) selA
noncomputable def stH := MaskedReset.machine (RecoveryFocus.machine ptSlotsH IncFlag.machine) selH
noncomputable def stC := RecoveryFocus.machine ptSlotsC (CellOp.machine earlyOp)
noncomputable def stC0 := RecoveryFocus.machine ptSlotsC (CellOp.machine falseOp)
noncomputable def stF := RecoveryFocus.machine ptSlotsF (CellOp.machine falseOp)
noncomputable def stG := RecoveryFocus.machine ptSlotsG lfsrM
noncomputable def stI := RecoveryFocus.machine ptSlotsI (CellOp.machine okOp)

theorem zipWith_copy (u v : List Bool) (h : u.length = v.length) (f : Bool) : List.zipWith (copyG f) u v = v := by
  induction u generalizing v with
  | nil => cases v with
    | nil => rfl
    | cons b v => simp at h
  | cons a u ih => cases v with
    | nil => simp at h
    | cons b v => simp [List.zipWith, copyG, ih v (by simpa using h)]

theorem zipWith_clear (u v : List Bool) (h : u.length = v.length) (f : Bool) :
    List.zipWith (clearG f) u v = List.replicate u.length false := by
  induction u generalizing v with
  | nil => cases v with
    | nil => rfl
    | cons b v => simp at h
  | cons a u ih => cases v with
    | nil => simp at h
    | cons b v => simp [List.zipWith, clearG, ih v (by simpa using h), List.replicate_succ]

theorem binary_zero (ℓ : ℕ) : binary ℓ 0 = List.replicate ℓ false := by
  induction ℓ with
  | zero => rfl
  | succ ℓ ih => rw [List.replicate_succ, ← ih]; rfl

/-! ### One step per stage, generic in the untouched tapes -/

section Stages
variable (ℓ cap : ℕ) (T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 : List Bool)

theorem stA_step (st : ℕ) (hcap : 2 * ℓ + 2 ≤ cap) :
    Step stA (2 * (2 * ℓ + 2) + 2) (fun _ => 0)
      ![frame (binary ℓ st), T1, T2, frame (binary ℓ 1), T4, T5, T6, T7, T8, T9, List.replicate cap false] (fun _ => 0)
      ![frame (binary ℓ 1), T1, T2, frame (binary ℓ 1), T4, T5, T6, T7, T8, T9, List.replicate cap false] := by
  have h0 := ZipFlag.run copyG (binary ℓ st) (binary ℓ 1) T7 0 (by simp)
  rw [zipWith_copy _ _ (by simp), binary_length] at h0
  have h1 : Step (ZipFlag.machine copyG) (2 * ℓ + 2) (fun _ => 0) ![frame (binary ℓ st), frame (binary ℓ 1), T7]
      ![2 * ℓ, 2 * ℓ, 0] ![frame (binary ℓ 1), frame (binary ℓ 1), T7] :=
    h0.congr_in (by funext i; fin_cases i <;> rfl) rfl
  have h2 := maskedStage h1 ptSlotsA (by decide) selA (by intro j hj; fin_cases j <;> first | rfl | simp [selA, ptSlotsA] at hj)
    ![frame (binary ℓ st), T1, T2, frame (binary ℓ 1), T4, T5, T6, T7, T8, T9] (by intro j; fin_cases j <;> rfl)
    (by omega : 2 * ℓ + 2 ≤ cap)
  rw [install_ptA] at h2
  refine (h2.congr_in rfl ?_).congr rfl ?_ <;> funext i <;> fin_cases i <;> rfl

theorem stB_step (i0 : ℕ) (hcap : 2 * ℓ + 2 ≤ cap) :
    Step stB (2 * (2 * ℓ + 2) + 2) (fun _ => 0)
      ![T0, frame (binary ℓ i0), T2, frame (binary ℓ 1), T4, T5, T6, T7, T8, T9, List.replicate cap false] (fun _ => 0)
      ![T0, frame (binary ℓ 0), T2, frame (binary ℓ 1), T4, T5, T6, T7, T8, T9, List.replicate cap false] := by
  have h0 := ZipFlag.run clearG (binary ℓ i0) (binary ℓ 1) T7 0 (by simp)
  rw [zipWith_clear _ _ (by simp), binary_length, ← binary_zero] at h0
  have h1 : Step (ZipFlag.machine clearG) (2 * ℓ + 2) (fun _ => 0) ![frame (binary ℓ i0), frame (binary ℓ 1), T7]
      ![2 * ℓ, 2 * ℓ, 0] ![frame (binary ℓ 0), frame (binary ℓ 1), T7] :=
    h0.congr_in (by funext i; fin_cases i <;> rfl) rfl
  have h2 := maskedStage h1 ptSlotsB (by decide) selB (by intro j hj; fin_cases j <;> first | rfl | simp [selB, ptSlotsB] at hj)
    ![T0, frame (binary ℓ i0), T2, frame (binary ℓ 1), T4, T5, T6, T7, T8, T9] (by intro j; fin_cases j <;> rfl)
    (by omega : 2 * ℓ + 2 ≤ cap)
  rw [install_ptB] at h2
  refine (h2.congr_in rfl ?_).congr rfl ?_ <;> funext i <;> fin_cases i <;> rfl

theorem stE_step (a : ℕ) (s : Bool) (hcap : 2 * ℓ + 1 ≤ cap) :
    Step stE (2 * (2 * ℓ + 1) + 2) (fun _ => 0)
      ![frame (binary ℓ a), T1, T2, frame (binary ℓ 1), T4, T5, [s], T7, T8, T9, List.replicate cap false] (fun _ => 0)
      ![frame (binary ℓ a), T1, T2, frame (binary ℓ 1), T4, T5, [decide (binary ℓ a = binary ℓ 1)], T7, T8, T9,
        List.replicate cap false] := by
  have h0 := EqCell.run false (binary ℓ a) (binary ℓ 1) s (by simp)
  rw [binary_length, Bool.false_xor] at h0
  have h1 : Step (EqCell.machine false) (2 * ℓ + 1) (fun _ => 0) ![frame (binary ℓ a), frame (binary ℓ 1), [s]]
      ![2 * ℓ, 2 * ℓ, 0] ![frame (binary ℓ a), frame (binary ℓ 1), [decide (binary ℓ a = binary ℓ 1)]] :=
    h0.congr_in (by funext i; fin_cases i <;> rfl) rfl
  have h2 := maskedStage h1 ptSlotsE (by decide) selA (by intro j hj; fin_cases j <;> first | rfl | simp [selA, ptSlotsE] at hj)
    ![frame (binary ℓ a), T1, T2, frame (binary ℓ 1), T4, T5, [s], T7, T8, T9] (by intro j; fin_cases j <;> rfl)
    (by omega : 2 * ℓ + 1 ≤ cap)
  rw [install_ptE] at h2
  refine (h2.congr_in rfl ?_).congr rfl ?_ <;> funext i <;> fin_cases i <;> rfl

theorem stD_step (i : ℕ) (d : Bool) (hcap : 2 * ℓ + 1 ≤ cap) :
    Step stD (2 * (2 * ℓ + 1) + 2) (fun _ => 0)
      ![T0, frame (binary ℓ i), T2, T3, frame (binary ℓ (2 ^ ℓ - 1)), T5, T6, [d], T8, T9, List.replicate cap false]
      (fun _ => 0)
      ![T0, frame (binary ℓ i), T2, T3, frame (binary ℓ (2 ^ ℓ - 1)), T5, T6,
        [!decide (binary ℓ i = binary ℓ (2 ^ ℓ - 1))], T8, T9, List.replicate cap false] := by
  have h0 := EqCell.run true (binary ℓ i) (binary ℓ (2 ^ ℓ - 1)) d (by simp)
  rw [binary_length, Bool.true_xor] at h0
  have h1 : Step (EqCell.machine true) (2 * ℓ + 1) (fun _ => 0) ![frame (binary ℓ i), frame (binary ℓ (2 ^ ℓ - 1)), [d]]
      ![2 * ℓ, 2 * ℓ, 0]
      ![frame (binary ℓ i), frame (binary ℓ (2 ^ ℓ - 1)), [!decide (binary ℓ i = binary ℓ (2 ^ ℓ - 1))]] :=
    h0.congr_in (by funext i; fin_cases i <;> rfl) rfl
  have h2 := maskedStage h1 ptSlotsD (by decide) selD (by intro j hj; fin_cases j <;> first | rfl | simp [selD, ptSlotsD] at hj)
    ![T0, frame (binary ℓ i), T2, T3, frame (binary ℓ (2 ^ ℓ - 1)), T5, T6, [d], T8, T9] (by intro j; fin_cases j <;> rfl)
    (by omega : 2 * ℓ + 1 ≤ cap)
  rw [install_ptD] at h2
  refine (h2.congr_in rfl ?_).congr rfl ?_ <;> funext i <;> fin_cases i <;> rfl

theorem stH_step (i : ℕ) (d : Bool) (hcap : 2 * ℓ + 2 ≤ cap) :
    Step stH (2 * (2 * ℓ + 2) + 2) (fun _ => 0)
      ![T0, frame (binary ℓ i), T2, T3, T4, T5, T6, [d], T8, T9, List.replicate cap false] (fun _ => 0)
      ![T0, frame (binary ℓ (i + d.toNat)), T2, T3, T4, T5, T6, [d], T8, T9, List.replicate cap false] := by
  have h0 := IncFlag.run ℓ i [d] 0
  rw [read_single] at h0
  have h1 : Step IncFlag.machine (2 * ℓ + 2) (fun _ => 0) ![frame (binary ℓ i), [d]] ![2 * ℓ, 0]
      ![frame (binary ℓ (i + d.toNat)), [d]] :=
    h0.congr_in (by funext i; fin_cases i <;> rfl) rfl
  have h2 := maskedStage h1 ptSlotsH (by decide) selH (by intro j hj; fin_cases j <;> first | rfl | simp [selH, ptSlotsH] at hj)
    ![T0, frame (binary ℓ i), T2, T3, T4, T5, T6, [d], T8, T9] (by intro j; fin_cases j <;> rfl)
    (by omega : 2 * ℓ + 2 ≤ cap)
  rw [install_ptH] at h2
  refine (h2.congr_in rfl ?_).congr rfl ?_ <;> funext i <;> fin_cases i <;> rfl

theorem cellStep (op : Bool → Bool → Bool → Bool) (slots : Fin 3 → Fin (10 + 1)) (hi : Function.Injective slots)
    (A : Fin (10 + 1) → List Bool) (t a b : Bool) (ht : A (slots 0) = [t]) (ha : A (slots 1) = [a])
    (hb : A (slots 2) = [b]) :
    Step (RecoveryFocus.machine slots (CellOp.machine op)) 1 (fun _ => 0) A (fun _ => 0)
      (RecoveryRootRound.install slots A ![[op t a b], [a], [b]]) := by
  have h0 := CellOp.run op t a b
  have h1 : Step (CellOp.machine op) 1 (fun _ => 0) ![[t], [a], [b]] (fun _ => 0) ![[op t a b], [a], [b]] :=
    (h0.congr_in (by funext i; fin_cases i <;> rfl) rfl).congr (by funext i; fin_cases i <;> rfl) rfl
  exact plainStage h1 slots hi A (by intro j; fin_cases j <;> assumption)

theorem stC0_step (e s d : Bool) :
    Step stC0 1 (fun _ => 0) ![T0, T1, T2, T3, T4, T5, [s], [d], [e], T9, List.replicate cap false] (fun _ => 0)
      ![T0, T1, T2, T3, T4, T5, [s], [d], [false], T9, List.replicate cap false] := by
  have h := cellStep falseOp ptSlotsC (by decide) ![T0, T1, T2, T3, T4, T5, [s], [d], [e], T9, List.replicate cap false]
    e s d rfl rfl rfl
  rw [install_ptC] at h
  exact h.congr rfl (by funext i; fin_cases i <;> rfl)

theorem stF_step (f s d : Bool) :
    Step stF 1 (fun _ => 0) ![T0, T1, T2, T3, T4, [f], [s], [d], T8, T9, List.replicate cap false] (fun _ => 0)
      ![T0, T1, T2, T3, T4, [false], [s], [d], T8, T9, List.replicate cap false] := by
  have h := cellStep falseOp ptSlotsF (by decide) ![T0, T1, T2, T3, T4, [f], [s], [d], T8, T9, List.replicate cap false]
    f s d rfl rfl rfl
  rw [install_ptF] at h
  exact h.congr rfl (by funext i; fin_cases i <;> rfl)

theorem stC_step (e s d : Bool) :
    Step stC 1 (fun _ => 0) ![T0, T1, T2, T3, T4, T5, [s], [d], [e], T9, List.replicate cap false] (fun _ => 0)
      ![T0, T1, T2, T3, T4, T5, [s], [d], [e || (s && d)], T9, List.replicate cap false] := by
  have h := cellStep earlyOp ptSlotsC (by decide) ![T0, T1, T2, T3, T4, T5, [s], [d], [e], T9, List.replicate cap false]
    e s d rfl rfl rfl
  rw [install_ptC] at h
  exact h.congr rfl (by funext i; fin_cases i <;> rfl)

theorem stI_step (r s e : Bool) :
    Step stI 1 (fun _ => 0) ![T0, T1, T2, T3, T4, T5, [s], T7, [e], [r], List.replicate cap false] (fun _ => 0)
      ![T0, T1, T2, T3, T4, T5, [s], T7, [e], [s && !e], List.replicate cap false] := by
  have h := cellStep okOp ptSlotsI (by decide) ![T0, T1, T2, T3, T4, T5, [s], T7, [e], [r], List.replicate cap false]
    r s e rfl rfl rfl
  rw [install_ptI] at h
  exact h.congr rfl (by funext i; fin_cases i <;> rfl)

theorem stG_step (p a : ℕ) (x : Bool) (hℓ : 1 ≤ ℓ) (hcap : 2 * ℓ + 2 ≤ cap) :
    Step stG (lfsrCost ℓ) (fun _ => 0)
      ![frame (binary ℓ a), T1, frame (binary ℓ p), T3, T4, [x], T6, T7, T8, T9, List.replicate cap false] (fun _ => 0)
      ![frame (binary ℓ (lfsr p ℓ a)), T1, frame (binary ℓ p), T3, T4, [false], T6, T7, T8, T9, List.replicate cap false] := by
  have h0 := lfsr_run p ℓ a hℓ x cap hcap
  have h1 : Step lfsrM (lfsrCost ℓ) (fun _ => 0)
      ![frame (binary ℓ a), frame (binary ℓ p), [x], List.replicate cap false] (fun _ => 0)
      ![frame (binary ℓ (lfsr p ℓ a)), frame (binary ℓ p), [false], List.replicate cap false] :=
    (h0.congr_in (by funext i; fin_cases i <;> rfl) rfl).congr (by funext i; fin_cases i <;> rfl) rfl
  have h2 := plainStage h1 ptSlotsG (by decide)
    ![frame (binary ℓ a), T1, frame (binary ℓ p), T3, T4, [x], T6, T7, T8, T9, List.replicate cap false]
    (by intro j; fin_cases j <;> rfl)
  rw [install_ptG] at h2
  exact h2.congr rfl (by funext i; fin_cases i <;> rfl)

end Stages

/-! ### The period test as one `Step` -/

noncomputable def ptInit := Composition.machine (Composition.machine (Composition.machine (Composition.machine
  (Composition.machine stA stB) stC0) stF) stE) stD
noncomputable def ptBody := Composition.machine (Composition.machine (Composition.machine (Composition.machine
  stG stH) stE) stD) stC
noncomputable def ptLoop := StreamController.machine ptBody 7
/-- **The period test**: init, the loop over the `2^ℓ - 1` powers, the verdict. -/
noncomputable def ptM := Composition.machine (Composition.machine ptInit ptLoop) stI

/-- `S` after `i` steps: the power is `1`. -/
def sOf (p ℓ i : ℕ) : Bool := decide (binary ℓ (lfsrPow p ℓ i) = binary ℓ 1)
/-- `D` after `i` steps: the counter is not yet `2^ℓ - 1`. -/
def dOf (ℓ i : ℕ) : Bool := !decide (binary ℓ i = binary ℓ (2 ^ ℓ - 1))
/-- `E` after `i` steps: some power `x^j`, `0 < j ≤ i`, `j ≠ 2^ℓ - 1`, is `1`. -/
def early (p ℓ : ℕ) : ℕ → Bool
  | 0 => false
  | i + 1 => early p ℓ i || (sOf p ℓ (i + 1) && dOf ℓ (i + 1))

/-- The bank before loop step `i`. -/
def ptA (p ℓ cap i : ℕ) (r : Bool) : Fin (10 + 1) → List Bool :=
  ![frame (binary ℓ (lfsrPow p ℓ i)), frame (binary ℓ i), frame (binary ℓ p), frame (binary ℓ 1),
    frame (binary ℓ (2 ^ ℓ - 1)), [false], [sOf p ℓ i], [dOf ℓ i], [early p ℓ i], [r], List.replicate cap false]

/-- The entry bank: stale power, counter and cells. -/
def ptIn (p ℓ cap st i0 : ℕ) (f s d e r : Bool) : Fin (10 + 1) → List Bool :=
  ![frame (binary ℓ st), frame (binary ℓ i0), frame (binary ℓ p), frame (binary ℓ 1),
    frame (binary ℓ (2 ^ ℓ - 1)), [f], [s], [d], [e], [r], List.replicate cap false]

def ptInitCost (ℓ : ℕ) : ℕ :=
  (2 * (2 * ℓ + 2) + 2) + 1 + (2 * (2 * ℓ + 2) + 2) + 1 + 1 + 1 + 1 + 1 + (2 * (2 * ℓ + 1) + 2) + 1 +
    (2 * (2 * ℓ + 1) + 2)

theorem ptInit_step (p ℓ cap st i0 : ℕ) (f s d e r : Bool) (hcap : 2 * ℓ + 2 ≤ cap) :
    Step ptInit (ptInitCost ℓ) (fun _ => 0) (ptIn p ℓ cap st i0 f s d e r) (fun _ => 0) (ptA p ℓ cap 0 r) := by
  have hA := stA_step (ℓ := ℓ) (cap := cap) (T1 := frame (binary ℓ i0)) (T2 := frame (binary ℓ p))
    (T4 := frame (binary ℓ (2 ^ ℓ - 1))) (T5 := [f]) (T6 := [s]) (T7 := [d]) (T8 := [e]) (T9 := [r]) (st := st) hcap
  have hB := stB_step (ℓ := ℓ) (cap := cap) (T0 := frame (binary ℓ 1)) (T2 := frame (binary ℓ p))
    (T4 := frame (binary ℓ (2 ^ ℓ - 1))) (T5 := [f]) (T6 := [s]) (T7 := [d]) (T8 := [e]) (T9 := [r]) (i0 := i0) hcap
  have hC := stC0_step (cap := cap) (T0 := frame (binary ℓ 1)) (T1 := frame (binary ℓ 0))
    (T2 := frame (binary ℓ p)) (T3 := frame (binary ℓ 1)) (T4 := frame (binary ℓ (2 ^ ℓ - 1))) (T5 := [f])
    (T9 := [r]) (e := e) (s := s) (d := d)
  have hF := stF_step (cap := cap) (T0 := frame (binary ℓ 1)) (T1 := frame (binary ℓ 0))
    (T2 := frame (binary ℓ p)) (T3 := frame (binary ℓ 1)) (T4 := frame (binary ℓ (2 ^ ℓ - 1))) (T8 := [false])
    (T9 := [r]) (f := f) (s := s) (d := d)
  have hE := stE_step (ℓ := ℓ) (cap := cap) (T1 := frame (binary ℓ 0)) (T2 := frame (binary ℓ p))
    (T4 := frame (binary ℓ (2 ^ ℓ - 1))) (T5 := [false]) (T7 := [d]) (T8 := [false]) (T9 := [r]) (a := 1) (s := s)
    (by omega)
  have hD := stD_step (ℓ := ℓ) (cap := cap) (T0 := frame (binary ℓ 1)) (T2 := frame (binary ℓ p))
    (T3 := frame (binary ℓ 1)) (T5 := [false]) (T6 := [decide (binary ℓ 1 = binary ℓ 1)]) (T8 := [false])
    (T9 := [r]) (i := 0) (d := d) (by omega)
  exact (((((hA.seq hB).seq hC).seq hF).seq hE).seq hD)

theorem dOf_lt (ℓ i : ℕ) (hi : i < 2 ^ ℓ - 1) : dOf ℓ i = true := by
  unfold dOf
  have hne : binary ℓ i ≠ binary ℓ (2 ^ ℓ - 1) := by
    intro h
    have h1 := binary_value ℓ i (by omega)
    have h2 := binary_value ℓ (2 ^ ℓ - 1) (by have := Nat.one_le_two_pow (n := ℓ); omega)
    rw [h] at h1
    omega
  simp [hne]

theorem dOf_top (ℓ : ℕ) : dOf ℓ (2 ^ ℓ - 1) = false := by simp [dOf]

def ptBodyCost (ℓ : ℕ) : ℕ :=
  lfsrCost ℓ + 1 + (2 * (2 * ℓ + 2) + 2) + 1 + (2 * (2 * ℓ + 1) + 2) + 1 + (2 * (2 * ℓ + 1) + 2) + 1 + 1

theorem ptBody_step (p ℓ cap i : ℕ) (r : Bool) (hℓ : 1 ≤ ℓ) (hcap : 2 * ℓ + 2 ≤ cap) (hi : i < 2 ^ ℓ - 1) :
    Step ptBody (ptBodyCost ℓ) (fun _ => 0) (ptA p ℓ cap i r) (fun _ => 0) (ptA p ℓ cap (i + 1) r) := by
  have hG := stG_step (ℓ := ℓ) (cap := cap) (T1 := frame (binary ℓ i)) (T3 := frame (binary ℓ 1))
    (T4 := frame (binary ℓ (2 ^ ℓ - 1))) (T6 := [sOf p ℓ i]) (T7 := [dOf ℓ i]) (T8 := [early p ℓ i]) (T9 := [r])
    (p := p) (a := lfsrPow p ℓ i) (x := false) hℓ hcap
  have hH := stH_step (ℓ := ℓ) (cap := cap) (T0 := frame (binary ℓ (lfsrPow p ℓ (i + 1))))
    (T2 := frame (binary ℓ p)) (T3 := frame (binary ℓ 1)) (T4 := frame (binary ℓ (2 ^ ℓ - 1))) (T5 := [false])
    (T6 := [sOf p ℓ i]) (T8 := [early p ℓ i]) (T9 := [r]) (i := i) (d := dOf ℓ i) hcap
  rw [dOf_lt ℓ i hi, Bool.toNat_true] at hH
  have hE := stE_step (ℓ := ℓ) (cap := cap) (T1 := frame (binary ℓ (i + 1))) (T2 := frame (binary ℓ p))
    (T4 := frame (binary ℓ (2 ^ ℓ - 1))) (T5 := [false]) (T7 := [true]) (T8 := [early p ℓ i]) (T9 := [r])
    (a := lfsrPow p ℓ (i + 1)) (s := sOf p ℓ i) (by omega)
  have hD := stD_step (ℓ := ℓ) (cap := cap) (T0 := frame (binary ℓ (lfsrPow p ℓ (i + 1))))
    (T2 := frame (binary ℓ p)) (T3 := frame (binary ℓ 1)) (T5 := [false]) (T6 := [sOf p ℓ (i + 1)])
    (T8 := [early p ℓ i]) (T9 := [r]) (i := i + 1) (d := true) (by omega)
  have hC := stC_step (cap := cap) (T0 := frame (binary ℓ (lfsrPow p ℓ (i + 1))))
    (T1 := frame (binary ℓ (i + 1))) (T2 := frame (binary ℓ p)) (T3 := frame (binary ℓ 1))
    (T4 := frame (binary ℓ (2 ^ ℓ - 1))) (T5 := [false]) (T9 := [r])
    (e := early p ℓ i) (s := sOf p ℓ (i + 1)) (d := dOf ℓ (i + 1))
  have hG' : Step stG (lfsrCost ℓ) (fun _ => 0) (ptA p ℓ cap i r) (fun _ => 0)
      ![frame (binary ℓ (lfsrPow p ℓ (i + 1))), frame (binary ℓ i), frame (binary ℓ p), frame (binary ℓ 1),
        frame (binary ℓ (2 ^ ℓ - 1)), [false], [sOf p ℓ i], [true], [early p ℓ i], [r], List.replicate cap false] := by
    rw [← dOf_lt ℓ i hi]; exact hG
  exact (((hG'.seq hH).seq hE).seq hD).seq hC

/-- The loop over the powers `x^1, …, x^{2^ℓ-1}`. -/
theorem ptLoop_step (p ℓ cap : ℕ) (r : Bool) (hℓ : 1 ≤ ℓ) (hcap : 2 * ℓ + 2 ≤ cap) :
    Step ptLoop ((2 ^ ℓ - 1) * (ptBodyCost ℓ + 2) + 1) (fun _ => 0) (ptA p ℓ cap 0 r) (fun _ => 0)
      (ptA p ℓ cap (2 ^ ℓ - 1) r) := by
  let W : WhileBody (10 + 1) _ :=
    { body := ptBody
      tape := 7
      bound := 2 ^ ℓ - 1
      H := fun _ => fun _ => 0
      A := fun i => ptA p ℓ cap i r
      cost := fun _ => ptBodyCost ℓ
      step := fun i hi => ptBody_step p ℓ cap i r hℓ hcap hi
      cont := fun i hi => by
        show readTapeBit [dOf ℓ i] 0 = true
        rw [read_single, dOf_lt ℓ i hi]
      halt := by
        show readTapeBit [dOf ℓ (2 ^ ℓ - 1)] 0 = false
        rw [read_single, dOf_top] }
  have hW := W.run
  rw [W.rest_const _ (fun _ => rfl)] at hW
  exact hW

def ptCost (ℓ : ℕ) : ℕ := ptInitCost ℓ + 1 + ((2 ^ ℓ - 1) * (ptBodyCost ℓ + 2) + 1) + 1 + 1

/-- **The period test** as one `Step`: the verdict cell ends `S ∧ ¬E` after the `2^ℓ - 1` powers. -/
theorem pt_run (p ℓ cap st i0 : ℕ) (f s d e r : Bool) (hℓ : 1 ≤ ℓ) (hcap : 2 * ℓ + 2 ≤ cap) :
    Step ptM (ptCost ℓ) (fun _ => 0) (ptIn p ℓ cap st i0 f s d e r) (fun _ => 0)
      ![frame (binary ℓ (lfsrPow p ℓ (2 ^ ℓ - 1))), frame (binary ℓ (2 ^ ℓ - 1)), frame (binary ℓ p),
        frame (binary ℓ 1), frame (binary ℓ (2 ^ ℓ - 1)), [false], [sOf p ℓ (2 ^ ℓ - 1)], [dOf ℓ (2 ^ ℓ - 1)],
        [early p ℓ (2 ^ ℓ - 1)], [sOf p ℓ (2 ^ ℓ - 1) && !early p ℓ (2 ^ ℓ - 1)], List.replicate cap false] := by
  have hI := stI_step (cap := cap) (T0 := frame (binary ℓ (lfsrPow p ℓ (2 ^ ℓ - 1))))
    (T1 := frame (binary ℓ (2 ^ ℓ - 1))) (T2 := frame (binary ℓ p)) (T3 := frame (binary ℓ 1))
    (T4 := frame (binary ℓ (2 ^ ℓ - 1))) (T5 := [false]) (T7 := [dOf ℓ (2 ^ ℓ - 1)])
    (r := r) (s := sOf p ℓ (2 ^ ℓ - 1)) (e := early p ℓ (2 ^ ℓ - 1))
  exact ((ptInit_step p ℓ cap st i0 f s d e r hcap).seq (ptLoop_step p ℓ cap r hℓ hcap)).seq hI

/-! ### The verdict is the certificate's period condition -/

theorem lfsr_lt (p ℓ a : ℕ) (hp : GF.ModulusOk p ℓ) (ha : a < 2 ^ ℓ) : lfsr p ℓ a < 2 ^ ℓ := by
  have h2a : 2 * a < 2 ^ (ℓ + 1) := by rw [pow_succ]; omega
  unfold lfsr
  split
  · next hb => exact GF.lt_two_pow_of_testBit_eq _ _ ℓ h2a hp.2 (by rw [hb, hp.1])
  · next hb => exact GF.lt_of_testBit_false _ ℓ h2a (by simpa using hb)

theorem lfsrPow_lt (p ℓ : ℕ) (hp : GF.ModulusOk p ℓ) (hℓ : 1 ≤ ℓ) (i : ℕ) : lfsrPow p ℓ i < 2 ^ ℓ := by
  induction i with
  | zero => exact Nat.one_lt_two_pow (by omega)
  | succ i ih => exact lfsr_lt p ℓ _ hp ih

theorem binary_inj (ℓ x y : ℕ) (hx : x < 2 ^ ℓ) (hy : y < 2 ^ ℓ) : binary ℓ x = binary ℓ y ↔ x = y := by
  constructor
  · intro h
    have h1 := binary_value ℓ x hx
    have h2 := binary_value ℓ y hy
    rw [h] at h1
    omega
  · rintro rfl; rfl

theorem sOf_iff (p ℓ i : ℕ) (hp : GF.ModulusOk p ℓ) (hℓ : 1 ≤ ℓ) : sOf p ℓ i = true ↔ lfsrPow p ℓ i = 1 := by
  unfold sOf
  rw [decide_eq_true_iff]
  exact binary_inj ℓ _ _ (lfsrPow_lt p ℓ hp hℓ i) (Nat.one_lt_two_pow (by omega))

theorem dOf_iff (ℓ j : ℕ) (hj : j < 2 ^ ℓ) : dOf ℓ j = true ↔ j ≠ 2 ^ ℓ - 1 := by
  unfold dOf
  have h := binary_inj ℓ j (2 ^ ℓ - 1) hj (by have := Nat.one_le_two_pow (n := ℓ); omega)
  by_cases hj' : j = 2 ^ ℓ - 1
  · simp [hj']
  · have hne : binary ℓ j ≠ binary ℓ (2 ^ ℓ - 1) := fun e => hj' (h.mp e)
    simp [hne, hj']

theorem early_iff (p ℓ : ℕ) (hp : GF.ModulusOk p ℓ) (hℓ : 1 ≤ ℓ) (i : ℕ) (hi : i < 2 ^ ℓ) :
    early p ℓ i = true ↔ ∃ j, 0 < j ∧ j ≤ i ∧ j ≠ 2 ^ ℓ - 1 ∧ lfsrPow p ℓ j = 1 := by
  induction i with
  | zero =>
    simp only [early, Bool.false_eq_true, false_iff]
    rintro ⟨j, h0, h1, _⟩
    omega
  | succ i ih =>
    rw [early, Bool.or_eq_true, Bool.and_eq_true, ih (by omega), sOf_iff p ℓ (i + 1) hp hℓ, dOf_iff ℓ (i + 1) hi]
    constructor
    · rintro (⟨j, hj0, hji, hjN, hjp⟩ | ⟨hp1, hN⟩)
      · exact ⟨j, hj0, by omega, hjN, hjp⟩
      · exact ⟨i + 1, by omega, le_refl _, hN, hp1⟩
    · rintro ⟨j, hj0, hji, hjN, hjp⟩
      rcases Nat.lt_or_ge j (i + 1) with h | h
      · exact Or.inl ⟨j, hj0, by omega, hjN, hjp⟩
      · have : j = i + 1 := by omega
        subst this
        exact Or.inr ⟨hjp, hjN⟩

theorem period_iff (p ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    period p ℓ = 2 ^ ℓ - 1 ↔ lfsrPow p ℓ (2 ^ ℓ - 1) = 1 ∧ ∀ j, 0 < j → j < 2 ^ ℓ - 1 → lfsrPow p ℓ j ≠ 1 := by
  have h2 : 2 ≤ 2 ^ ℓ := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ ℓ := Nat.pow_le_pow_right (by norm_num) hℓ
  unfold period
  constructor
  · intro h
    cases hf : (List.range (2 ^ ℓ)).find? (fun j => j ≠ 0 && lfsrPow p ℓ j == 1) with
    | none =>
      rw [hf] at h
      simp at h
      omega
    | some m =>
      rw [hf] at h
      simp only [Option.getD_some] at h
      subst h
      rw [List.find?_range_eq_some] at hf
      obtain ⟨hq, _, hlt⟩ := hf
      refine ⟨by simp at hq; exact hq.2, fun j hj0 hjN hj1 => ?_⟩
      have := hlt j hjN
      simp [hj1] at this
      omega
  · rintro ⟨h1, h2'⟩
    have hf : (List.range (2 ^ ℓ)).find? (fun j => j ≠ 0 && lfsrPow p ℓ j == 1) = some (2 ^ ℓ - 1) := by
      rw [List.find?_range_eq_some]
      refine ⟨?_, ?_, fun j hj => ?_⟩
      · simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
        exact ⟨by omega, h1⟩
      · simp only [List.mem_range]; omega
      · by_cases hj0 : j = 0
        · simp [hj0]
        · simp [hj0, h2' j (by omega) hj]
    rw [hf]
    rfl

/-- **The period test decides the certificate's period condition.** -/
theorem verdict (p ℓ : ℕ) (hp : GF.ModulusOk p ℓ) (hℓ : 1 ≤ ℓ) :
    (sOf p ℓ (2 ^ ℓ - 1) && !early p ℓ (2 ^ ℓ - 1)) = decide (period p ℓ = 2 ^ ℓ - 1) := by
  have hN : 2 ^ ℓ - 1 < 2 ^ ℓ := by have := Nat.one_le_two_pow (n := ℓ); omega
  have hs := sOf_iff p ℓ (2 ^ ℓ - 1) hp hℓ
  have he := early_iff p ℓ hp hℓ (2 ^ ℓ - 1) hN
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_iff, period_iff p ℓ hℓ]
  constructor
  · intro h
    have h1 : sOf p ℓ (2 ^ ℓ - 1) = true := by revert h; cases sOf p ℓ (2 ^ ℓ - 1) <;> simp
    have h2 : early p ℓ (2 ^ ℓ - 1) = false := by revert h; cases early p ℓ (2 ^ ℓ - 1) <;> simp
    refine ⟨hs.mp h1, fun j hj0 hjN hj1 => ?_⟩
    have := he.mpr ⟨j, hj0, by omega, by omega, hj1⟩
    rw [h2] at this
    exact Bool.false_ne_true this
  · rintro ⟨h1, h2⟩
    have hsv : sOf p ℓ (2 ^ ℓ - 1) = true := hs.mpr h1
    have hev : early p ℓ (2 ^ ℓ - 1) = false := by
      cases hev : early p ℓ (2 ^ ℓ - 1)
      · rfl
      · obtain ⟨j, hj0, hjle, hjN, hj1⟩ := he.mp hev
        exact absurd hj1 (h2 j hj0 (by omega))
    rw [hsv, hev]
    rfl

/-- A candidate `2^ℓ + c`, `c < 2^ℓ`, is a degree-`ℓ` modulus. -/
theorem candidate_ok (ℓ c : ℕ) (hc : c < 2 ^ ℓ) : GF.ModulusOk (2 ^ ℓ + c) ℓ := by
  refine ⟨?_, by rw [pow_succ]; omega⟩
  rw [Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hc]
  rfl

theorem binary_two_pow_add (ℓ c : ℕ) : binary ℓ (2 ^ ℓ + c) = binary ℓ c := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    rw [binary_getElem, binary_getElem, Nat.testBit_two_pow_add_gt (by simpa using h1)]

/-! ## Part C: the search over the candidates `2^ℓ + c`, `c < 2^ℓ`

Tapes: 0–10 the period test's (tape 2, its modulus, is the candidate `J`; tape 10 is the shared rewind log),
11 the answer `OUT`, 12 `FOUND`, 13 the loop's flag `C = [J ≠ 2^ℓ-1]`, 14 a scratch cell `X`. All 2^ℓ candidates are
tested (no early exit, so the loop is uniform); the first certified one is kept. -/

theorem dockZero {k s n u : ℕ} {M : Machine k s} {tin tout : Fin k → List Bool}
    (h : Step M n (fun _ => 0) tin (fun _ => 0) tout) (slots : Fin k → Fin u) (hi : Function.Injective slots)
    (A : Fin u → List Bool) (hA : ∀ j, A (slots j) = tin j) :
    Step (RecoveryFocus.machine slots M) n (fun _ => 0) A (fun _ => 0) (RecoveryRootRound.install slots A tout) := by
  have hd := dockRun h slots hi (fun _ => 0) A (fun _ => rfl) hA
  rwa [dockH_zero'] at hd

theorem maskZero {k s n cap : ℕ} {M : Machine k s} {hout : Fin k → ℕ} {tin tout : Fin k → List Bool}
    (h : Step M n (fun _ => 0) tin hout tout) (sel : Fin k → Bool) (hsel : ∀ j, sel j = false → hout j = 0)
    (hcap : n ≤ cap) :
    Step (MaskedReset.machine M sel) (2 * n + 2) (fun _ => 0)
      (Fin.addCases tin (fun _ : Fin 1 => List.replicate cap false)) (fun _ => 0)
      (Fin.addCases tout (fun _ : Fin 1 => List.replicate cap false)) := by
  have hm := h.mask sel (fun _ _ => rfl) hcap
  refine (hm.congr_in ?_ rfl).congr ?_ rfl
  · funext i; refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [Fin.addCases_left]
      cases hs : sel j
      · simp [hsel j hs]
      · simp
    · simp

def selG : Bool → Bool → Bool → Bool := fun f a b => if f then b else a
def trueOp : Bool → Bool → Bool → Bool := fun _ _ _ => true
def xOp : Bool → Bool → Bool → Bool := fun _ r f => r && !f
def orOp : Bool → Bool → Bool → Bool := fun f r _ => f || r
def sel3 : Fin 3 → Bool := ![true, true, false]
def sel2 : Fin 2 → Bool := ![true, false]

theorem zipWith_sel (u v : List Bool) (h : u.length = v.length) (f : Bool) :
    List.zipWith (selG f) u v = if f then v else u := by
  induction u generalizing v with
  | nil => cases v with
    | nil => cases f <;> rfl
    | cons b v => simp at h
  | cons a u ih => cases v with
    | nil => simp at h
    | cons b v => cases f <;> simp [List.zipWith, selG, ih v (by simpa using h)]

def srSlotsA : Fin 4 → Fin (10 + 1 + 4) := ![11, 3, 14, 10]
theorem install_srA (A : Fin (10 + 1 + 4) → List Bool) (v : Fin 4 → List Bool) :
    RecoveryRootRound.install srSlotsA A v = ![A 0, A 1, A 2, v 1, A 4, A 5, A 6, A 7, A 8, A 9, v 3, v 0, A 12, A 13, v 2] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 1
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 2
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 3
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

def srSlotsB : Fin 3 → Fin (10 + 1 + 4) := ![12, 13, 14]
theorem install_srB (A : Fin (10 + 1 + 4) → List Bool) (v : Fin 3 → List Bool) :
    RecoveryRootRound.install srSlotsB A v = ![A 0, A 1, A 2, A 3, A 4, A 5, A 6, A 7, A 8, A 9, A 10, A 11, v 0, v 1, v 2] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 1
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 2
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

def srSlotsC : Fin 3 → Fin (10 + 1 + 4) := ![13, 12, 14]
theorem install_srC (A : Fin (10 + 1 + 4) → List Bool) (v : Fin 3 → List Bool) :
    RecoveryRootRound.install srSlotsC A v = ![A 0, A 1, A 2, A 3, A 4, A 5, A 6, A 7, A 8, A 9, A 10, A 11, v 1, v 0, v 2] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 1
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 2
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

def srSlotsD : Fin 4 → Fin (10 + 1 + 4) := ![2, 3, 14, 10]
theorem install_srD (A : Fin (10 + 1 + 4) → List Bool) (v : Fin 4 → List Bool) :
    RecoveryRootRound.install srSlotsD A v = ![A 0, A 1, v 0, v 1, A 4, A 5, A 6, A 7, A 8, A 9, v 3, A 11, A 12, A 13, v 2] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 1
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 2
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 3
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

def srSlotsX : Fin 3 → Fin (10 + 1 + 4) := ![14, 9, 12]
theorem install_srX (A : Fin (10 + 1 + 4) → List Bool) (v : Fin 3 → List Bool) :
    RecoveryRootRound.install srSlotsX A v = ![A 0, A 1, A 2, A 3, A 4, A 5, A 6, A 7, A 8, v 1, A 10, A 11, v 2, A 13, v 0] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 1
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 2
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

def srSlotsS : Fin 4 → Fin (10 + 1 + 4) := ![11, 2, 14, 10]
theorem install_srS (A : Fin (10 + 1 + 4) → List Bool) (v : Fin 4 → List Bool) :
    RecoveryRootRound.install srSlotsS A v = ![A 0, A 1, v 1, A 3, A 4, A 5, A 6, A 7, A 8, A 9, v 3, v 0, A 12, A 13, v 2] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 1
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 2
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 3
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

def srSlotsO : Fin 3 → Fin (10 + 1 + 4) := ![12, 9, 14]
theorem install_srO (A : Fin (10 + 1 + 4) → List Bool) (v : Fin 3 → List Bool) :
    RecoveryRootRound.install srSlotsO A v = ![A 0, A 1, A 2, A 3, A 4, A 5, A 6, A 7, A 8, v 1, A 10, A 11, v 0, A 13, v 2] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 1
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 2
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

def srSlotsE : Fin 4 → Fin (10 + 1 + 4) := ![2, 4, 13, 10]
theorem install_srE (A : Fin (10 + 1 + 4) → List Bool) (v : Fin 4 → List Bool) :
    RecoveryRootRound.install srSlotsE A v = ![A 0, A 1, v 0, A 3, v 1, A 5, A 6, A 7, A 8, A 9, v 3, A 11, A 12, v 2, A 14] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 1
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 2
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 3
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

def srSlotsI : Fin 3 → Fin (10 + 1 + 4) := ![2, 13, 10]
theorem install_srI (A : Fin (10 + 1 + 4) → List Bool) (v : Fin 3 → List Bool) :
    RecoveryRootRound.install srSlotsI A v = ![A 0, A 1, v 0, A 3, A 4, A 5, A 6, A 7, A 8, A 9, v 2, A 11, A 12, v 1, A 14] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 1
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 2
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

noncomputable def srA := RecoveryFocus.machine srSlotsA (MaskedReset.machine (ZipFlag.machine clearG) sel3)
noncomputable def srB := RecoveryFocus.machine srSlotsB (CellOp.machine falseOp)
noncomputable def srC := RecoveryFocus.machine srSlotsC (CellOp.machine trueOp)
noncomputable def srD := RecoveryFocus.machine srSlotsD (MaskedReset.machine (ZipFlag.machine clearG) sel3)
noncomputable def srX := RecoveryFocus.machine srSlotsX (CellOp.machine xOp)
noncomputable def srS := RecoveryFocus.machine srSlotsS (MaskedReset.machine (ZipFlag.machine selG) sel3)
noncomputable def srO := RecoveryFocus.machine srSlotsO (CellOp.machine orOp)
noncomputable def srE := RecoveryFocus.machine srSlotsE (MaskedReset.machine (EqCell.machine true) sel3)
noncomputable def srI := RecoveryFocus.machine srSlotsI (MaskedReset.machine IncFlag.machine sel2)
noncomputable def srPT := TapeEmbedding.machine 4 ptM

section SearchStages
variable (ℓ cap : ℕ) (U0 U1 U2 U3 U4 U5 U6 U7 U8 U9 U11 U12 U13 U14 : List Bool)

/-- A masked three-tape word stage docked on `(a, b, c, log)`. -/
theorem zipStage (g : Bool → Bool → Bool → Bool) (u v : List Bool) (x : Bool) (hl : u.length = v.length)
    (hcap : 2 * u.length + 2 ≤ cap) :
    Step (MaskedReset.machine (ZipFlag.machine g) sel3) (2 * (2 * u.length + 2) + 2) (fun _ => 0)
      ![frame u, frame v, [x], List.replicate cap false] (fun _ => 0)
      ![frame (List.zipWith (g x) u v), frame v, [x], List.replicate cap false] := by
  have h0 := ZipFlag.run g u v [x] 0 hl
  rw [read_single] at h0
  have h1 : Step (ZipFlag.machine g) (2 * u.length + 2) (fun _ => 0) ![frame u, frame v, [x]]
      ![2 * u.length, 2 * u.length, 0] ![frame (List.zipWith (g x) u v), frame v, [x]] :=
    h0.congr_in (by funext i; fin_cases i <;> rfl) rfl
  have h2 := maskZero h1 sel3 (by intro j hj; fin_cases j <;> first | rfl | simp [sel3] at hj) hcap
  refine (h2.congr_in rfl ?_).congr rfl ?_ <;> funext i <;> fin_cases i <;> rfl

theorem srA_step (o : ℕ) (xc : Bool) (hcap : 2 * ℓ + 2 ≤ cap) :
    Step srA (2 * (2 * ℓ + 2) + 2) (fun _ => 0)
      ![U0, U1, U2, frame (binary ℓ 1), U4, U5, U6, U7, U8, U9, List.replicate cap false, frame (binary ℓ o), U12, U13, [xc]]
      (fun _ => 0)
      ![U0, U1, U2, frame (binary ℓ 1), U4, U5, U6, U7, U8, U9, List.replicate cap false, frame (binary ℓ 0), U12, U13, [xc]] := by
  have h0 := zipStage cap clearG (binary ℓ o) (binary ℓ 1) xc (by simp) (by simpa using hcap)
  rw [zipWith_clear _ _ (by simp), binary_length, show List.replicate ℓ false = binary ℓ 0 from (binary_zero ℓ).symm] at h0
  have h1 := dockZero h0 srSlotsA (by decide)
    ![U0, U1, U2, frame (binary ℓ 1), U4, U5, U6, U7, U8, U9, List.replicate cap false, frame (binary ℓ o), U12, U13, [xc]]
    (by intro j; fin_cases j <;> rfl)
  rw [install_srA] at h1
  exact h1.congr rfl (by funext i; fin_cases i <;> rfl)

theorem srD_step (j0 : ℕ) (xc : Bool) (hcap : 2 * ℓ + 2 ≤ cap) :
    Step srD (2 * (2 * ℓ + 2) + 2) (fun _ => 0)
      ![U0, U1, frame (binary ℓ j0), frame (binary ℓ 1), U4, U5, U6, U7, U8, U9, List.replicate cap false, U11, U12, U13, [xc]]
      (fun _ => 0)
      ![U0, U1, frame (binary ℓ 0), frame (binary ℓ 1), U4, U5, U6, U7, U8, U9, List.replicate cap false, U11, U12, U13, [xc]] := by
  have h0 := zipStage cap clearG (binary ℓ j0) (binary ℓ 1) xc (by simp) (by simpa using hcap)
  rw [zipWith_clear _ _ (by simp), binary_length, show List.replicate ℓ false = binary ℓ 0 from (binary_zero ℓ).symm] at h0
  have h1 := dockZero h0 srSlotsD (by decide)
    ![U0, U1, frame (binary ℓ j0), frame (binary ℓ 1), U4, U5, U6, U7, U8, U9, List.replicate cap false, U11, U12, U13, [xc]]
    (by intro j; fin_cases j <;> rfl)
  rw [install_srD] at h1
  exact h1.congr rfl (by funext i; fin_cases i <;> rfl)

theorem srS_step (o j : ℕ) (xc : Bool) (hcap : 2 * ℓ + 2 ≤ cap) :
    Step srS (2 * (2 * ℓ + 2) + 2) (fun _ => 0)
      ![U0, U1, frame (binary ℓ j), U3, U4, U5, U6, U7, U8, U9, List.replicate cap false, frame (binary ℓ o), U12, U13, [xc]]
      (fun _ => 0)
      ![U0, U1, frame (binary ℓ j), U3, U4, U5, U6, U7, U8, U9, List.replicate cap false,
        frame (binary ℓ (if xc then j else o)), U12, U13, [xc]] := by
  have h0 := zipStage cap selG (binary ℓ o) (binary ℓ j) xc (by simp) (by simpa using hcap)
  rw [zipWith_sel _ _ (by simp), binary_length] at h0
  have e : (if xc then binary ℓ j else binary ℓ o) = binary ℓ (if xc then j else o) := by cases xc <;> rfl
  rw [e] at h0
  have h1 := dockZero h0 srSlotsS (by decide)
    ![U0, U1, frame (binary ℓ j), U3, U4, U5, U6, U7, U8, U9, List.replicate cap false, frame (binary ℓ o), U12, U13, [xc]]
    (by intro j; fin_cases j <;> rfl)
  rw [install_srS] at h1
  exact h1.congr rfl (by funext i; fin_cases i <;> rfl)

theorem srE_step (j : ℕ) (c : Bool) (hcap : 2 * ℓ + 1 ≤ cap) :
    Step srE (2 * (2 * ℓ + 1) + 2) (fun _ => 0)
      ![U0, U1, frame (binary ℓ j), U3, frame (binary ℓ (2 ^ ℓ - 1)), U5, U6, U7, U8, U9, List.replicate cap false,
        U11, U12, [c], U14]
      (fun _ => 0)
      ![U0, U1, frame (binary ℓ j), U3, frame (binary ℓ (2 ^ ℓ - 1)), U5, U6, U7, U8, U9, List.replicate cap false,
        U11, U12, [dOf ℓ j], U14] := by
  have h0 := EqCell.run true (binary ℓ j) (binary ℓ (2 ^ ℓ - 1)) c (by simp)
  rw [binary_length, Bool.true_xor] at h0
  have h1 : Step (EqCell.machine true) (2 * ℓ + 1) (fun _ => 0) ![frame (binary ℓ j), frame (binary ℓ (2 ^ ℓ - 1)), [c]]
      ![2 * ℓ, 2 * ℓ, 0] ![frame (binary ℓ j), frame (binary ℓ (2 ^ ℓ - 1)), [dOf ℓ j]] :=
    h0.congr_in (by funext i; fin_cases i <;> rfl) rfl
  have h2 := maskZero h1 sel3 (by intro j hj; fin_cases j <;> first | rfl | simp [sel3] at hj) hcap
  have h3 : Step (MaskedReset.machine (EqCell.machine true) sel3) (2 * (2 * ℓ + 1) + 2) (fun _ => 0)
      ![frame (binary ℓ j), frame (binary ℓ (2 ^ ℓ - 1)), [c], List.replicate cap false] (fun _ => 0)
      ![frame (binary ℓ j), frame (binary ℓ (2 ^ ℓ - 1)), [dOf ℓ j], List.replicate cap false] := by
    refine (h2.congr_in rfl ?_).congr rfl ?_ <;> funext i <;> fin_cases i <;> rfl
  have h4 := dockZero h3 srSlotsE (by decide)
    ![U0, U1, frame (binary ℓ j), U3, frame (binary ℓ (2 ^ ℓ - 1)), U5, U6, U7, U8, U9, List.replicate cap false,
      U11, U12, [c], U14]
    (by intro j; fin_cases j <;> rfl)
  rw [install_srE] at h4
  exact h4.congr rfl (by funext i; fin_cases i <;> rfl)

theorem srI_step (j : ℕ) (c : Bool) (hcap : 2 * ℓ + 2 ≤ cap) :
    Step srI (2 * (2 * ℓ + 2) + 2) (fun _ => 0)
      ![U0, U1, frame (binary ℓ j), U3, U4, U5, U6, U7, U8, U9, List.replicate cap false, U11, U12, [c], U14]
      (fun _ => 0)
      ![U0, U1, frame (binary ℓ (j + c.toNat)), U3, U4, U5, U6, U7, U8, U9, List.replicate cap false, U11, U12, [c], U14] := by
  have h0 := IncFlag.run ℓ j [c] 0
  rw [read_single] at h0
  have h1 : Step IncFlag.machine (2 * ℓ + 2) (fun _ => 0) ![frame (binary ℓ j), [c]] ![2 * ℓ, 0]
      ![frame (binary ℓ (j + c.toNat)), [c]] :=
    h0.congr_in (by funext i; fin_cases i <;> rfl) rfl
  have h2 := maskZero h1 sel2 (by intro j hj; fin_cases j <;> first | rfl | simp [sel2] at hj) hcap
  have h3 : Step (MaskedReset.machine IncFlag.machine sel2) (2 * (2 * ℓ + 2) + 2) (fun _ => 0)
      ![frame (binary ℓ j), [c], List.replicate cap false] (fun _ => 0)
      ![frame (binary ℓ (j + c.toNat)), [c], List.replicate cap false] := by
    refine (h2.congr_in rfl ?_).congr rfl ?_ <;> funext i <;> fin_cases i <;> rfl
  have h4 := dockZero h3 srSlotsI (by decide)
    ![U0, U1, frame (binary ℓ j), U3, U4, U5, U6, U7, U8, U9, List.replicate cap false, U11, U12, [c], U14]
    (by intro j; fin_cases j <;> rfl)
  rw [install_srI] at h4
  exact h4.congr rfl (by funext i; fin_cases i <;> rfl)

theorem cellStage (op : Bool → Bool → Bool → Bool) (slots : Fin 3 → Fin (10 + 1 + 4)) (hi : Function.Injective slots)
    (A : Fin (10 + 1 + 4) → List Bool) (t a b : Bool) (ht : A (slots 0) = [t]) (ha : A (slots 1) = [a])
    (hb : A (slots 2) = [b]) :
    Step (RecoveryFocus.machine slots (CellOp.machine op)) 1 (fun _ => 0) A (fun _ => 0)
      (RecoveryRootRound.install slots A ![[op t a b], [a], [b]]) := by
  have h0 := CellOp.run op t a b
  have h1 : Step (CellOp.machine op) 1 (fun _ => 0) ![[t], [a], [b]] (fun _ => 0) ![[op t a b], [a], [b]] :=
    (h0.congr_in (by funext i; fin_cases i <;> rfl) rfl).congr (by funext i; fin_cases i <;> rfl) rfl
  exact dockZero h1 slots hi A (by intro j; fin_cases j <;> assumption)

theorem srB_step (fd c xc : Bool) :
    Step srB 1 (fun _ => 0)
      ![U0, U1, U2, U3, U4, U5, U6, U7, U8, U9, List.replicate cap false, U11, [fd], [c], [xc]] (fun _ => 0)
      ![U0, U1, U2, U3, U4, U5, U6, U7, U8, U9, List.replicate cap false, U11, [false], [c], [xc]] := by
  have h := cellStage falseOp srSlotsB (by decide)
    ![U0, U1, U2, U3, U4, U5, U6, U7, U8, U9, List.replicate cap false, U11, [fd], [c], [xc]] fd c xc rfl rfl rfl
  rw [install_srB] at h
  exact h.congr rfl (by funext i; fin_cases i <;> rfl)

theorem srC_step (fd c xc : Bool) :
    Step srC 1 (fun _ => 0)
      ![U0, U1, U2, U3, U4, U5, U6, U7, U8, U9, List.replicate cap false, U11, [fd], [c], [xc]] (fun _ => 0)
      ![U0, U1, U2, U3, U4, U5, U6, U7, U8, U9, List.replicate cap false, U11, [fd], [true], [xc]] := by
  have h := cellStage trueOp srSlotsC (by decide)
    ![U0, U1, U2, U3, U4, U5, U6, U7, U8, U9, List.replicate cap false, U11, [fd], [c], [xc]] c fd xc rfl rfl rfl
  rw [install_srC] at h
  exact h.congr rfl (by funext i; fin_cases i <;> rfl)

theorem srX_step (r fd xc : Bool) :
    Step srX 1 (fun _ => 0)
      ![U0, U1, U2, U3, U4, U5, U6, U7, U8, [r], List.replicate cap false, U11, [fd], U13, [xc]] (fun _ => 0)
      ![U0, U1, U2, U3, U4, U5, U6, U7, U8, [r], List.replicate cap false, U11, [fd], U13, [r && !fd]] := by
  have h := cellStage xOp srSlotsX (by decide)
    ![U0, U1, U2, U3, U4, U5, U6, U7, U8, [r], List.replicate cap false, U11, [fd], U13, [xc]] xc r fd rfl rfl rfl
  rw [install_srX] at h
  exact h.congr rfl (by funext i; fin_cases i <;> rfl)

theorem srO_step (r fd xc : Bool) :
    Step srO 1 (fun _ => 0)
      ![U0, U1, U2, U3, U4, U5, U6, U7, U8, [r], List.replicate cap false, U11, [fd], U13, [xc]] (fun _ => 0)
      ![U0, U1, U2, U3, U4, U5, U6, U7, U8, [r], List.replicate cap false, U11, [fd || r], U13, [xc]] := by
  have h := cellStage orOp srSlotsO (by decide)
    ![U0, U1, U2, U3, U4, U5, U6, U7, U8, [r], List.replicate cap false, U11, [fd], U13, [xc]] fd r xc rfl rfl rfl
  rw [install_srO] at h
  exact h.congr rfl (by funext i; fin_cases i <;> rfl)

end SearchStages

/-! ### The search semantics -/

/-- The first certified candidate among the first `j`. -/
def firstUpTo (ℓ j : ℕ) : Option ℕ := (List.range j).find? (fun c => decide (GF.PrimitiveCert (2 ^ ℓ + c) ℓ))
def outOf (ℓ j : ℕ) : ℕ := (firstUpTo ℓ j).getD 0
def foundOf (ℓ j : ℕ) : Bool := (firstUpTo ℓ j).isSome
/-- The period test's verdict on candidate `c`. -/
def okOf (ℓ c : ℕ) : Bool := sOf (2 ^ ℓ + c) ℓ (2 ^ ℓ - 1) && !early (2 ^ ℓ + c) ℓ (2 ^ ℓ - 1)

theorem okOf_eq (ℓ c : ℕ) (hℓ : 1 ≤ ℓ) (hc : c < 2 ^ ℓ) : okOf ℓ c = decide (GF.PrimitiveCert (2 ^ ℓ + c) ℓ) := by
  unfold okOf
  rw [verdict (2 ^ ℓ + c) ℓ (candidate_ok ℓ c hc) hℓ]
  apply decide_eq_decide.mpr
  unfold GF.PrimitiveCert
  exact ⟨fun h => ⟨hℓ, candidate_ok ℓ c hc, h⟩, fun h => h.2.2⟩

theorem firstUpTo_succ (ℓ j : ℕ) :
    firstUpTo ℓ (j + 1) = (firstUpTo ℓ j).or (if decide (GF.PrimitiveCert (2 ^ ℓ + j) ℓ) then some j else none) := by
  unfold firstUpTo
  rw [List.range_succ, List.find?_append]
  congr 1
  simp only [List.find?_cons, List.find?_nil]
  split <;> simp_all

theorem outOf_succ (ℓ j : ℕ) (hℓ : 1 ≤ ℓ) (hj : j < 2 ^ ℓ) :
    outOf ℓ (j + 1) = (if (okOf ℓ j && !foundOf ℓ j) then j else outOf ℓ j) := by
  unfold outOf foundOf
  rw [firstUpTo_succ, okOf_eq ℓ j hℓ hj]
  cases h : firstUpTo ℓ j with
  | some c => simp
  | none =>
    by_cases hc : GF.PrimitiveCert (2 ^ ℓ + j) ℓ <;> simp [hc]

theorem foundOf_succ (ℓ j : ℕ) (hℓ : 1 ≤ ℓ) (hj : j < 2 ^ ℓ) :
    foundOf ℓ (j + 1) = (foundOf ℓ j || okOf ℓ j) := by
  unfold foundOf
  rw [firstUpTo_succ, okOf_eq ℓ j hℓ hj]
  cases h : firstUpTo ℓ j with
  | some c => simp
  | none =>
    by_cases hc : GF.PrimitiveCert (2 ^ ℓ + j) ℓ <;> simp [hc]

theorem outOf_top (ℓ : ℕ) : binary ℓ (GF.firstPrimitive ℓ) = binary ℓ (outOf ℓ (2 ^ ℓ)) := by
  unfold GF.firstPrimitive outOf firstUpTo
  rw [binary_two_pow_add]

/-- The stale period-test tapes. -/
structure Junk where
  st : ℕ
  i0 : ℕ
  f : Bool
  s : Bool
  d : Bool
  e : Bool
  r : Bool

/-- The period test's tapes after candidate `c`. -/
def junkAfter (ℓ c : ℕ) : Junk :=
  ⟨lfsrPow (2 ^ ℓ + c) ℓ (2 ^ ℓ - 1), 2 ^ ℓ - 1, false, sOf (2 ^ ℓ + c) ℓ (2 ^ ℓ - 1), dOf ℓ (2 ^ ℓ - 1),
    early (2 ^ ℓ + c) ℓ (2 ^ ℓ - 1), okOf ℓ c⟩

def junkOf (ℓ : ℕ) (J0 : Junk) : ℕ → Junk
  | 0 => J0
  | c + 1 => junkAfter ℓ c

def cOf (ℓ : ℕ) : ℕ → Bool
  | 0 => true
  | j + 1 => dOf ℓ j

def xOf (ℓ : ℕ) (x0 : Bool) : ℕ → Bool
  | 0 => x0
  | j + 1 => okOf ℓ j && !foundOf ℓ j

def jOf (ℓ j : ℕ) : ℕ := min j (2 ^ ℓ - 1)

/-- The search bank before candidate `j`. -/
def srBank (ℓ cap : ℕ) (J0 : Junk) (x0 : Bool) (j : ℕ) : Fin (10 + 1 + 4) → List Bool :=
  ![frame (binary ℓ (junkOf ℓ J0 j).st), frame (binary ℓ (junkOf ℓ J0 j).i0), frame (binary ℓ (jOf ℓ j)),
    frame (binary ℓ 1), frame (binary ℓ (2 ^ ℓ - 1)), [(junkOf ℓ J0 j).f], [(junkOf ℓ J0 j).s], [(junkOf ℓ J0 j).d],
    [(junkOf ℓ J0 j).e], [(junkOf ℓ J0 j).r], List.replicate cap false, frame (binary ℓ (outOf ℓ j)), [foundOf ℓ j],
    [cOf ℓ j], [xOf ℓ x0 j]]

/-! ### The search as one `Step` -/

noncomputable def srBody := Composition.machine (Composition.machine (Composition.machine (Composition.machine
  (Composition.machine srPT srX) srS) srO) srE) srI
noncomputable def srLoop := StreamController.machine srBody 13
noncomputable def srInit := Composition.machine (Composition.machine (Composition.machine srA srB) srC) srD
/-- **The primitive-modulus search**: every candidate `2^ℓ + c` is tested, the first certified one is kept. -/
noncomputable def searchM := Composition.machine srInit srLoop

theorem srPT_step (p ℓ cap st i0 : ℕ) (f s d e r : Bool) (U11 U12 U13 U14 : List Bool) (hℓ : 1 ≤ ℓ)
    (hcap : 2 * ℓ + 2 ≤ cap) :
    Step srPT (ptCost ℓ) (fun _ => 0)
      ![frame (binary ℓ st), frame (binary ℓ i0), frame (binary ℓ p), frame (binary ℓ 1), frame (binary ℓ (2 ^ ℓ - 1)),
        [f], [s], [d], [e], [r], List.replicate cap false, U11, U12, U13, U14] (fun _ => 0)
      ![frame (binary ℓ (lfsrPow p ℓ (2 ^ ℓ - 1))), frame (binary ℓ (2 ^ ℓ - 1)), frame (binary ℓ p),
        frame (binary ℓ 1), frame (binary ℓ (2 ^ ℓ - 1)), [false], [sOf p ℓ (2 ^ ℓ - 1)], [dOf ℓ (2 ^ ℓ - 1)],
        [early p ℓ (2 ^ ℓ - 1)], [sOf p ℓ (2 ^ ℓ - 1) && !early p ℓ (2 ^ ℓ - 1)], List.replicate cap false,
        U11, U12, U13, U14] := by
  have h := (pt_run p ℓ cap st i0 f s d e r hℓ hcap).embed (fun _ : Fin 4 => 0) ![U11, U12, U13, U14]
  refine (h.congr_in ?_ ?_).congr ?_ ?_
  · funext i; refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp
  · funext i; fin_cases i <;> rfl
  · funext i; refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp
  · funext i; fin_cases i <;> rfl

def srBodyCost (ℓ : ℕ) : ℕ :=
  ptCost ℓ + 1 + 1 + 1 + (2 * (2 * ℓ + 2) + 2) + 1 + 1 + 1 + (2 * (2 * ℓ + 1) + 2) + 1 + (2 * (2 * ℓ + 2) + 2)

theorem srBody_step (ℓ cap : ℕ) (J0 : Junk) (x0 : Bool) (j : ℕ) (hℓ : 1 ≤ ℓ) (hcap : 2 * ℓ + 2 ≤ cap)
    (hj : j < 2 ^ ℓ) :
    Step srBody (srBodyCost ℓ) (fun _ => 0) (srBank ℓ cap J0 x0 j) (fun _ => 0) (srBank ℓ cap J0 x0 (j + 1)) := by
  have hjJ : jOf ℓ j = j := by unfold jOf; omega
  have e3 : jOf ℓ (j + 1) = j + (dOf ℓ j).toNat := by
    unfold jOf
    by_cases h : j < 2 ^ ℓ - 1
    · rw [dOf_lt ℓ j h, Bool.toNat_true]; omega
    · have hjN : j = 2 ^ ℓ - 1 := by omega
      rw [hjN, dOf_top, Bool.toNat_false]; omega
  unfold srBank
  rw [hjJ, e3, outOf_succ ℓ j hℓ hj, foundOf_succ ℓ j hℓ hj]
  have h1 := srPT_step (2 ^ ℓ + j) ℓ cap (junkOf ℓ J0 j).st (junkOf ℓ J0 j).i0 (junkOf ℓ J0 j).f (junkOf ℓ J0 j).s
    (junkOf ℓ J0 j).d (junkOf ℓ J0 j).e (junkOf ℓ J0 j).r (frame (binary ℓ (outOf ℓ j))) [foundOf ℓ j] [cOf ℓ j]
    [xOf ℓ x0 j] hℓ hcap
  rw [binary_two_pow_add] at h1
  have h2 := srX_step (cap := cap) (U0 := frame (binary ℓ (lfsrPow (2 ^ ℓ + j) ℓ (2 ^ ℓ - 1))))
    (U1 := frame (binary ℓ (2 ^ ℓ - 1))) (U2 := frame (binary ℓ j)) (U3 := frame (binary ℓ 1))
    (U4 := frame (binary ℓ (2 ^ ℓ - 1))) (U5 := [false]) (U6 := [sOf (2 ^ ℓ + j) ℓ (2 ^ ℓ - 1)])
    (U7 := [dOf ℓ (2 ^ ℓ - 1)]) (U8 := [early (2 ^ ℓ + j) ℓ (2 ^ ℓ - 1)]) (U11 := frame (binary ℓ (outOf ℓ j)))
    (U13 := [cOf ℓ j]) (r := okOf ℓ j) (fd := foundOf ℓ j) (xc := xOf ℓ x0 j)
  have h3 := srS_step (ℓ := ℓ) (cap := cap) (U0 := frame (binary ℓ (lfsrPow (2 ^ ℓ + j) ℓ (2 ^ ℓ - 1))))
    (U1 := frame (binary ℓ (2 ^ ℓ - 1))) (U3 := frame (binary ℓ 1))
    (U4 := frame (binary ℓ (2 ^ ℓ - 1))) (U5 := [false]) (U6 := [sOf (2 ^ ℓ + j) ℓ (2 ^ ℓ - 1)])
    (U7 := [dOf ℓ (2 ^ ℓ - 1)]) (U8 := [early (2 ^ ℓ + j) ℓ (2 ^ ℓ - 1)]) (U9 := [okOf ℓ j])
    (U12 := [foundOf ℓ j]) (U13 := [cOf ℓ j]) (o := outOf ℓ j) (j := j) (xc := okOf ℓ j && !foundOf ℓ j) hcap
  have h4 := srO_step (cap := cap) (U0 := frame (binary ℓ (lfsrPow (2 ^ ℓ + j) ℓ (2 ^ ℓ - 1))))
    (U1 := frame (binary ℓ (2 ^ ℓ - 1))) (U2 := frame (binary ℓ j)) (U3 := frame (binary ℓ 1))
    (U4 := frame (binary ℓ (2 ^ ℓ - 1))) (U5 := [false]) (U6 := [sOf (2 ^ ℓ + j) ℓ (2 ^ ℓ - 1)])
    (U7 := [dOf ℓ (2 ^ ℓ - 1)]) (U8 := [early (2 ^ ℓ + j) ℓ (2 ^ ℓ - 1)])
    (U11 := frame (binary ℓ (if (okOf ℓ j && !foundOf ℓ j) then j else outOf ℓ j)))
    (U13 := [cOf ℓ j]) (r := okOf ℓ j) (fd := foundOf ℓ j) (xc := okOf ℓ j && !foundOf ℓ j)
  have h5 := srE_step (ℓ := ℓ) (cap := cap) (U0 := frame (binary ℓ (lfsrPow (2 ^ ℓ + j) ℓ (2 ^ ℓ - 1))))
    (U1 := frame (binary ℓ (2 ^ ℓ - 1))) (U3 := frame (binary ℓ 1)) (U5 := [false])
    (U6 := [sOf (2 ^ ℓ + j) ℓ (2 ^ ℓ - 1)]) (U7 := [dOf ℓ (2 ^ ℓ - 1)]) (U8 := [early (2 ^ ℓ + j) ℓ (2 ^ ℓ - 1)])
    (U9 := [okOf ℓ j]) (U11 := frame (binary ℓ (if (okOf ℓ j && !foundOf ℓ j) then j else outOf ℓ j)))
    (U12 := [foundOf ℓ j || okOf ℓ j]) (U14 := [okOf ℓ j && !foundOf ℓ j]) (j := j) (c := cOf ℓ j) (by omega)
  have h6 := srI_step (ℓ := ℓ) (cap := cap) (U0 := frame (binary ℓ (lfsrPow (2 ^ ℓ + j) ℓ (2 ^ ℓ - 1))))
    (U1 := frame (binary ℓ (2 ^ ℓ - 1))) (U3 := frame (binary ℓ 1)) (U4 := frame (binary ℓ (2 ^ ℓ - 1)))
    (U5 := [false]) (U6 := [sOf (2 ^ ℓ + j) ℓ (2 ^ ℓ - 1)]) (U7 := [dOf ℓ (2 ^ ℓ - 1)])
    (U8 := [early (2 ^ ℓ + j) ℓ (2 ^ ℓ - 1)]) (U9 := [okOf ℓ j])
    (U11 := frame (binary ℓ (if (okOf ℓ j && !foundOf ℓ j) then j else outOf ℓ j)))
    (U12 := [foundOf ℓ j || okOf ℓ j]) (U14 := [okOf ℓ j && !foundOf ℓ j]) (j := j) (c := dOf ℓ j) hcap
  exact (((((h1.seq h2).seq h3).seq h4).seq h5).seq h6)

/-- The entry bank of the search: any stale words and cells. -/
def srIn (ℓ cap : ℕ) (J0 : Junk) (j0 o0 : ℕ) (fd0 c0 x0 : Bool) : Fin (10 + 1 + 4) → List Bool :=
  ![frame (binary ℓ J0.st), frame (binary ℓ J0.i0), frame (binary ℓ j0), frame (binary ℓ 1), frame (binary ℓ (2 ^ ℓ - 1)),
    [J0.f], [J0.s], [J0.d], [J0.e], [J0.r], List.replicate cap false, frame (binary ℓ o0), [fd0], [c0], [x0]]

def srInitCost (ℓ : ℕ) : ℕ := (2 * (2 * ℓ + 2) + 2) + 1 + 1 + 1 + 1 + 1 + (2 * (2 * ℓ + 2) + 2)

theorem jOf_zero (ℓ : ℕ) : jOf ℓ 0 = 0 := by simp [jOf]

theorem srInit_step (ℓ cap : ℕ) (J0 : Junk) (j0 o0 : ℕ) (fd0 c0 x0 : Bool) (hcap : 2 * ℓ + 2 ≤ cap) :
    Step srInit (srInitCost ℓ) (fun _ => 0) (srIn ℓ cap J0 j0 o0 fd0 c0 x0) (fun _ => 0) (srBank ℓ cap J0 x0 0) := by
  have hA := srA_step (ℓ := ℓ) (cap := cap) (U0 := frame (binary ℓ J0.st)) (U1 := frame (binary ℓ J0.i0))
    (U2 := frame (binary ℓ j0)) (U4 := frame (binary ℓ (2 ^ ℓ - 1))) (U5 := [J0.f]) (U6 := [J0.s]) (U7 := [J0.d])
    (U8 := [J0.e]) (U9 := [J0.r]) (U12 := [fd0]) (U13 := [c0]) (o := o0) (xc := x0) hcap
  have hB := srB_step (cap := cap) (U0 := frame (binary ℓ J0.st)) (U1 := frame (binary ℓ J0.i0))
    (U2 := frame (binary ℓ j0)) (U3 := frame (binary ℓ 1)) (U4 := frame (binary ℓ (2 ^ ℓ - 1))) (U5 := [J0.f])
    (U6 := [J0.s]) (U7 := [J0.d]) (U8 := [J0.e]) (U9 := [J0.r]) (U11 := frame (binary ℓ 0)) (fd := fd0) (c := c0)
    (xc := x0)
  have hC := srC_step (cap := cap) (U0 := frame (binary ℓ J0.st)) (U1 := frame (binary ℓ J0.i0))
    (U2 := frame (binary ℓ j0)) (U3 := frame (binary ℓ 1)) (U4 := frame (binary ℓ (2 ^ ℓ - 1))) (U5 := [J0.f])
    (U6 := [J0.s]) (U7 := [J0.d]) (U8 := [J0.e]) (U9 := [J0.r]) (U11 := frame (binary ℓ 0)) (fd := false) (c := c0)
    (xc := x0)
  have hD := srD_step (ℓ := ℓ) (cap := cap) (U0 := frame (binary ℓ J0.st)) (U1 := frame (binary ℓ J0.i0))
    (U4 := frame (binary ℓ (2 ^ ℓ - 1))) (U5 := [J0.f]) (U6 := [J0.s]) (U7 := [J0.d]) (U8 := [J0.e]) (U9 := [J0.r])
    (U11 := frame (binary ℓ 0)) (U12 := [false]) (U13 := [true]) (j0 := j0) (xc := x0) hcap
  have h := ((hA.seq hB).seq hC).seq hD
  unfold srBank
  rw [jOf_zero]
  exact h

theorem cOf_cont (ℓ j : ℕ) (hj : j < 2 ^ ℓ) : cOf ℓ j = true := by
  cases j with
  | zero => rfl
  | succ i => exact dOf_lt ℓ i (by omega)

theorem cOf_top (ℓ : ℕ) : cOf ℓ (2 ^ ℓ) = false := by
  have h : 2 ^ ℓ = (2 ^ ℓ - 1) + 1 := by have := Nat.one_le_two_pow (n := ℓ); omega
  rw [h]
  exact dOf_top ℓ

theorem srLoop_step (ℓ cap : ℕ) (J0 : Junk) (x0 : Bool) (hℓ : 1 ≤ ℓ) (hcap : 2 * ℓ + 2 ≤ cap) :
    Step srLoop (2 ^ ℓ * (srBodyCost ℓ + 2) + 1) (fun _ => 0) (srBank ℓ cap J0 x0 0) (fun _ => 0)
      (srBank ℓ cap J0 x0 (2 ^ ℓ)) := by
  let W : WhileBody (10 + 1 + 4) _ :=
    { body := srBody
      tape := 13
      bound := 2 ^ ℓ
      H := fun _ => fun _ => 0
      A := fun j => srBank ℓ cap J0 x0 j
      cost := fun _ => srBodyCost ℓ
      step := fun j hj => srBody_step ℓ cap J0 x0 j hℓ hcap hj
      cont := fun j hj => by
        show readTapeBit [cOf ℓ j] 0 = true
        rw [read_single, cOf_cont ℓ j hj]
      halt := by
        show readTapeBit [cOf ℓ (2 ^ ℓ)] 0 = false
        rw [read_single, cOf_top] }
  have hW := W.run
  have hc : W.rest 0 = W.bound * (srBodyCost ℓ + 2) + 1 := W.rest_const _ (fun _ => rfl)
  rw [hc] at hW
  show Step (StreamController.machine srBody 13) (2 ^ ℓ * (srBodyCost ℓ + 2) + 1) (fun _ => 0) (srBank ℓ cap J0 x0 0)
    (fun _ => 0) (srBank ℓ cap J0 x0 (2 ^ ℓ))
  exact hW

def searchCost (ℓ : ℕ) : ℕ := srInitCost ℓ + 1 + (2 ^ ℓ * (srBodyCost ℓ + 2) + 1)

theorem search_run (ℓ cap : ℕ) (J0 : Junk) (j0 o0 : ℕ) (fd0 c0 x0 : Bool) (hℓ : 1 ≤ ℓ) (hcap : 2 * ℓ + 2 ≤ cap) :
    Step searchM (searchCost ℓ) (fun _ => 0) (srIn ℓ cap J0 j0 o0 fd0 c0 x0) (fun _ => 0)
      (srBank ℓ cap J0 x0 (2 ^ ℓ)) :=
  (srInit_step ℓ cap J0 j0 o0 fd0 c0 x0 hcap).seq (srLoop_step ℓ cap J0 x0 hℓ hcap)

/-- The answer tape of the final bank is the seed's modulus. -/
theorem srBank_out (ℓ cap : ℕ) (J0 : Junk) (x0 : Bool) :
    srBank ℓ cap J0 x0 (2 ^ ℓ) 11 = frame (binary ℓ (GF.firstPrimitive ℓ)) := by
  rw [outOf_top]
  rfl

/-! ## Cost in the PREPROCESSING class, and twins -/

theorem searchCost_le (ℓ q : ℕ) (hq : 1 ≤ q) (hl : ℓ ≤ q) : searchCost ℓ ≤ 200 * (2 ^ (2 * ℓ) * q ^ 1) := by
  have ha : 1 ≤ 2 ^ ℓ := Nat.one_le_two_pow
  have e2 : 2 ^ (2 * ℓ) = 2 ^ ℓ * 2 ^ ℓ := by rw [show 2 * ℓ = ℓ + ℓ by ring, pow_add]
  rw [e2, pow_one]
  have haq : q ≤ 2 ^ ℓ * q := Nat.le_mul_of_pos_left q ha
  have haaq : 2 ^ ℓ * q ≤ 2 ^ ℓ * 2 ^ ℓ * q := by
    rw [Nat.mul_assoc]; exact Nat.le_mul_of_pos_left _ ha
  have h1 : ptBodyCost ℓ ≤ 52 * q := by unfold ptBodyCost lfsrCost; omega
  have h2 : ptCost ℓ ≤ 110 * (2 ^ ℓ * q) := by
    have hsub : (2 ^ ℓ - 1) * (ptBodyCost ℓ + 2) ≤ 2 ^ ℓ * (54 * q) := Nat.mul_le_mul (Nat.sub_le _ _) (by omega)
    have e : 2 ^ ℓ * (54 * q) = 54 * (2 ^ ℓ * q) := by ring
    unfold ptCost ptInitCost
    omega
  have h3 : srBodyCost ℓ ≤ 145 * (2 ^ ℓ * q) := by unfold srBodyCost; omega
  have h4 : 2 ^ ℓ * (srBodyCost ℓ + 2) ≤ 147 * (2 ^ ℓ * 2 ^ ℓ * q) := by
    have := Nat.mul_le_mul_left (2 ^ ℓ) (show srBodyCost ℓ + 2 ≤ 147 * (2 ^ ℓ * q) by omega)
    have e : 2 ^ ℓ * (147 * (2 ^ ℓ * q)) = 147 * (2 ^ ℓ * 2 ^ ℓ * q) := by ring
    omega
  unfold searchCost srInitCost
  omega

theorem search_within {E : Envelope} {cls : BudgetClass} {q k psi ℓ : ℕ} (hq : 1 ≤ q) (hl : ℓ ≤ q)
    (he : 2 * ℓ ≤ classExp E cls q k psi) (hd : 1 ≤ classDeg E cls) : Within E cls 200 q k psi (searchCost ℓ) :=
  Within.of_scaled hq (searchCost_le ℓ q hq hl) he hd

theorem search_within_preprocessing {E : Envelope} {q k psi ℓ : ℕ} (hq : 1 ≤ q) (hl : ℓ ≤ q)
    (he : 2 * ℓ ≤ E.cpsi * psi) (hd : 1 ≤ E.Apre) : Within E .preprocessing 200 q k psi (searchCost ℓ) :=
  search_within hq hl he hd

/-- Twin: the verdict on two moduli of degree 4 (`x⁴+x+1` is primitive; `x⁴+x³+x²+x+1` has period 5). -/
theorem okOf_twin : okOf 4 3 = true ∧ okOf 4 15 = false := by decide

/-- Twin: the search's iteration (the bank semantics of `srBody_step`) finds `x⁴+x+1`, i.e. `firstPrimitive 4`. -/
theorem search_twin :
    ((List.range 16).foldl (fun (st : ℕ × Bool) j => (if okOf 4 j && !st.2 then j else st.1, st.2 || okOf 4 j))
      (0, false)) = (3, true) ∧ GF.firstPrimitive 4 = 16 + 3 := by decide

/-- Executed runs of the small machines. -/
theorem eqCell_twin :
    (runFrom (EqCell.machine false) 20 ⟨(EqCell.machine false).start, ![0, 0, 0],
        ![frame (binary 3 5), frame (binary 3 5), [false]]⟩).map (fun r => r.final.tapes 2) = some [true] ∧
    (runFrom (EqCell.machine true) 20 ⟨(EqCell.machine true).start, ![0, 0, 0],
        ![frame (binary 3 5), frame (binary 3 4), [false]]⟩).map (fun r => r.final.tapes 2) = some [true] := by
  decide

theorem incFlag_twin :
    (runFrom IncFlag.machine 20 ⟨IncFlag.machine.start, ![0, 0], ![frame (binary 3 5), [true]]⟩).map
      (fun r => r.final.tapes 0) = some (frame (binary 3 6)) := by decide

theorem zipFlag_twin :
    (runFrom (ZipFlag.machine selG) 20 ⟨(ZipFlag.machine selG).start, ![0, 0, 0],
        ![frame (binary 3 5), frame (binary 3 2), [true]]⟩).map (fun r => r.final.tapes 0) = some (frame (binary 3 2)) := by
  decide

end NearCubicWires.WireExponent3_5.GF2
