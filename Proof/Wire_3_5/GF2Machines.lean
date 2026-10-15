import Proof.Wire_3_5.GF2Refs
import Proof.Wire_3_5.BlockWhile
import Proof.Wire_3_5.BlockZip
import Proof.MachineModel.OrdinarySignedSortKey

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.GF2
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.SignedSortKey NearCubicWires.WireExponent3_5.Block
open NearCubicWires.WireExponent3_5.Cost

/-! ## Bits of the references -/

theorem binary_getElem (w n i : ℕ) (h : i < (binary w n).length) : (binary w n)[i] = n.testBit i := by
  induction w generalizing n i with
  | zero => simp at h
  | succ w ih =>
    cases i with
    | zero =>
      show (n % 2 == 1) = n.testBit 0
      rw [Nat.testBit_zero]
      cases Nat.mod_two_eq_zero_or_one n with
      | inl h0 => simp [h0]
      | inr h1 => simp [h1]
    | succ i =>
      show (binary w (n / 2))[i]'(by simpa using h) = n.testBit (i + 1)
      rw [ih (n / 2) i (by simpa using h), Nat.testBit_succ]

theorem binary_xor (w a b : ℕ) : binary w (a ^^^ b) = List.zipWith xor (binary w a) (binary w b) := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    rw [List.getElem_zipWith, binary_getElem, binary_getElem, binary_getElem, Nat.testBit_xor]

/-- Shift up by one bit with carry-in `c` (the top bit drops). -/
def shiftIn : Bool → List Bool → List Bool
  | _, [] => []
  | c, a :: w => c :: shiftIn a w

/-- The bit shifted out: the last bit (or the carry-in of an empty word). -/
def carryOut : Bool → List Bool → Bool
  | c, [] => c
  | _, a :: w => carryOut a w

@[simp] theorem shiftIn_length (c : Bool) (w : List Bool) : (shiftIn c w).length = w.length := by
  induction w generalizing c with
  | nil => rfl
  | cons a w ih => simp [shiftIn, ih]

theorem shiftIn_binary (d m : ℕ) (c : Bool) : shiftIn c (binary d m) = binary d (2 * m + c.toNat) := by
  induction d generalizing m c with
  | zero => rfl
  | succ d ih =>
    have e1 : binary (d + 1) m = (m % 2 == 1) :: binary d (m / 2) := rfl
    have e2 : binary (d + 1) (2 * m + c.toNat) =
        ((2 * m + c.toNat) % 2 == 1) :: binary d ((2 * m + c.toNat) / 2) := rfl
    rw [e1, e2]
    simp only [shiftIn]
    rw [ih (m / 2) (m % 2 == 1)]
    congr 1
    · cases c <;> simp
    · congr 1
      cases c <;> cases h : m % 2 == 1 <;> simp_all [Bool.toNat] <;> omega

theorem carryOut_binary (w m : ℕ) (c : Bool) : carryOut c (binary (w + 1) m) = m.testBit w := by
  induction w generalizing m c with
  | zero =>
    show (m % 2 == 1) = m.testBit 0
    rw [Nat.testBit_zero]
    cases Nat.mod_two_eq_zero_or_one m with
    | inl h0 => simp [h0]
    | inr h1 => simp [h1]
  | succ w ih =>
    show carryOut (m % 2 == 1) (binary (w + 1) (m / 2)) = m.testBit (w + 1)
    rw [ih (m / 2), Nat.testBit_succ]

/-- The masked XOR of the second pass: `x ⊕ (f ∧ q)`. -/
def mx (f : Bool) (x q : Bool) : Bool := xor x (f && q)

theorem zipWith_mx_false (u v : List Bool) (h : u.length = v.length) : List.zipWith (mx false) u v = u := by
  induction u generalizing v with
  | nil => rfl
  | cons a u ih =>
    cases v with
    | nil => simp at h
    | cons b v => simp [List.zipWith, mx, ih v (by simpa using h)]

theorem zipWith_mx_true (u v : List Bool) : List.zipWith (mx true) u v = List.zipWith xor u v := by
  induction u generalizing v with
  | nil => rfl
  | cons a u ih =>
    cases v with
    | nil => rfl
    | cons b v => simp [List.zipWith, mx, ih v]

/-- **One LFSR step, bitwise**: shift in `false`, then XOR the modulus iff the shifted-out bit is set. -/
theorem lfsr_bits (p ℓ a : ℕ) (hℓ : 1 ≤ ℓ) :
    binary ℓ (lfsr p ℓ a) =
      List.zipWith (mx (carryOut false (binary ℓ a))) (shiftIn false (binary ℓ a)) (binary ℓ p) := by
  obtain ⟨w, rfl⟩ : ∃ w, ℓ = w + 1 := ⟨ℓ - 1, by omega⟩
  rw [carryOut_binary, shiftIn_binary]
  have htop : (2 * a).testBit (w + 1) = a.testBit w := by
    rw [Nat.testBit_succ]; congr 1; omega
  unfold lfsr
  simp only [Bool.toNat_false, Nat.add_zero]
  rw [htop]
  cases h : a.testBit w
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [zipWith_mx_false _ _ (by simp)]
  · simp only [↓reduceIte]
    rw [zipWith_mx_true, binary_xor]

/-! ## Two- and three-tape actions -/

namespace Two

def act {s : ℕ} (next : Fin s) (w0 w1 : Option Bool) (m0 m1 : HeadMove) : Action 2 s :=
  ⟨next, ![w0, w1], ![m0, m1]⟩

def cfg {s : ℕ} (q : Fin s) (A B : List Bool) (ha hb : ℕ) : Configuration 2 s := ⟨q, ![ha, hb], ![A, B]⟩

def wr (tape : List Bool) (head : ℕ) : Option Bool → List Bool
  | none => tape
  | some b => writeTapeBit tape head b

theorem step_cfg {s : ℕ} (p : Machine 2 s) (q next : Fin s) (A B : List Bool) (ha hb : ℕ)
    (w0 w1 : Option Bool) (m0 m1 : HeadMove)
    (hr : p.rule q ![readTapeBit A ha, readTapeBit B hb] = some (act next w0 w1 m0 m1)) :
    step p (cfg q A B ha hb) = some (cfg next (wr A ha w0) (wr B hb w1) (m0.apply ha) (m1.apply hb)) := by
  have hs : (cfg q A B ha hb).scanned = ![readTapeBit A ha, readTapeBit B hb] := by
    funext i; fin_cases i <;> rfl
  unfold step
  rw [hs]
  change (p.rule q _).map _ = _
  rw [hr]
  simp only [Option.map_some, Option.some.injEq]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> rfl
  · funext i
    fin_cases i
    · cases w0 <;> rfl
    · cases w1 <;> rfl

end Two

namespace Three

def act {s : ℕ} (next : Fin s) (w0 w1 w2 : Option Bool) (m0 m1 m2 : HeadMove) : Action 3 s :=
  ⟨next, ![w0, w1, w2], ![m0, m1, m2]⟩

def cfg {s : ℕ} (q : Fin s) (A B C : List Bool) (ha hb hc : ℕ) : Configuration 3 s :=
  ⟨q, ![ha, hb, hc], ![A, B, C]⟩

theorem step_cfg {s : ℕ} (p : Machine 3 s) (q next : Fin s) (A B C : List Bool) (ha hb hc : ℕ)
    (w0 w1 w2 : Option Bool) (m0 m1 m2 : HeadMove)
    (hr : p.rule q ![readTapeBit A ha, readTapeBit B hb, readTapeBit C hc] = some (act next w0 w1 w2 m0 m1 m2)) :
    step p (cfg q A B C ha hb hc) =
      some (cfg next (Two.wr A ha w0) (Two.wr B hb w1) (Two.wr C hc w2) (m0.apply ha) (m1.apply hb) (m2.apply hc)) := by
  have hs : (cfg q A B C ha hb hc).scanned = ![readTapeBit A ha, readTapeBit B hb, readTapeBit C hc] := by
    funext i; fin_cases i <;> rfl
  unfold step
  rw [hs]
  change (p.rule q _).map _ = _
  rw [hr]
  simp only [Option.map_some, Option.some.injEq]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> rfl
  · funext i
    fin_cases i
    · cases w0 <;> rfl
    · cases w1 <;> rfl
    · cases w2 <;> rfl

end Three

theorem write_mid (pre tail : List Bool) (old v : Bool) :
    writeTapeBit (pre ++ old :: tail) pre.length v = pre ++ v :: tail := by
  induction pre with
  | nil => rfl
  | cons b pre ih => simpa [writeTapeBit] using congrArg (List.cons b) ih

/-! ## The shift pass: in place, carry-out onto a flag cell -/

namespace ShiftOut
open Two (act cfg wr)

/-- Tape 0 is the word (in place), tape 1 the flag cell. States `0`/`1` read a marker with carry
`false`/`true`, `2`/`3` rewrite a bit, `4` halts; at the end marker the carry is written onto the flag. -/
def machine : Machine 2 5 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 4
  rule := fun q sc =>
    if q.val = 0 then some (if sc 0 then act 2 none none .right .stay else act 4 none (some false) .stay .stay)
    else if q.val = 1 then some (if sc 0 then act 3 none none .right .stay else act 4 none (some true) .stay .stay)
    else if q.val = 2 then
      some (if sc 0 then act 1 (some false) none .right .stay else act 0 (some false) none .right .stay)
    else if q.val = 3 then
      some (if sc 0 then act 1 (some true) none .right .stay else act 0 (some true) none .right .stay)
    else none

def mark (c : Bool) : Fin 5 := if c then 1 else 0
def bitS (c : Bool) : Fin 5 := if c then 3 else 2

theorem mark_step (c : Bool) (H F : List Bool) (hh : ℕ) (hr : readTapeBit H hh = true) :
    step machine (cfg (mark c) H F hh 0) = some (cfg (bitS c) H F (hh + 1) 0) := by
  cases c
  · exact Two.step_cfg machine 0 2 H F hh 0 none none .right .stay (by simp [machine, hr])
  · exact Two.step_cfg machine 1 3 H F hh 0 none none .right .stay (by simp [machine, hr])

theorem bit_step (c a : Bool) (H F : List Bool) (hh : ℕ) (hr : readTapeBit H hh = a) :
    step machine (cfg (bitS c) H F hh 0) = some (cfg (mark a) (writeTapeBit H hh c) F (hh + 1) 0) := by
  cases c <;> cases a
  · exact Two.step_cfg machine 2 0 H F hh 0 (some false) none .right .stay (by simp [machine, hr])
  · exact Two.step_cfg machine 2 1 H F hh 0 (some false) none .right .stay (by simp [machine, hr])
  · exact Two.step_cfg machine 3 0 H F hh 0 (some true) none .right .stay (by simp [machine, hr])
  · exact Two.step_cfg machine 3 1 H F hh 0 (some true) none .right .stay (by simp [machine, hr])

theorem end_step (c x : Bool) (H : List Bool) (hh : ℕ) (hr : readTapeBit H hh = false) :
    step machine (cfg (mark c) H [x] hh 0) = some (cfg 4 H [c] hh 0) := by
  cases c
  · exact Two.step_cfg machine 0 4 H [x] hh 0 none (some false) .stay .stay (by simp [machine, hr])
  · exact Two.step_cfg machine 1 4 H [x] hh 0 none (some true) .stay .stay (by simp [machine, hr])

theorem timed (x : Bool) (w : List Bool) : ∀ (pre : List Bool) (c : Bool),
    RecoveryExecution.Timed machine (2 * w.length + 1) (cfg (mark c) (pre ++ frame w) [x] pre.length 0)
      (cfg 4 (pre ++ frame (shiftIn c w)) [carryOut c w] (pre.length + 2 * w.length) 0) := by
  induction w with
  | nil =>
    intro pre c
    have hs := end_step c x (pre ++ frame []) pre.length (by simpa [frame] using Streaming.read_append pre [] false)
    simpa [frame, shiftIn, carryOut] using RecoveryExecution.Timed.single (p := machine) (by cases c <;> rfl) hs
  | cons a w ih =>
    intro pre c
    have hr1 : readTapeBit (pre ++ frame (a :: w)) pre.length = true := by
      simpa [frame] using Streaming.read_append pre (a :: frame w) true
    have hr2 : readTapeBit (pre ++ frame (a :: w)) (pre.length + 1) = a := by
      simpa [frame] using Streaming.read_append (pre ++ [true]) (frame w) a
    have hs1 := mark_step c (pre ++ frame (a :: w)) [x] pre.length hr1
    have hs2 := bit_step c a (pre ++ frame (a :: w)) [x] (pre.length + 1) hr2
    have hw : writeTapeBit (pre ++ frame (a :: w)) (pre.length + 1) c = pre ++ [true, c] ++ frame w := by
      simpa [frame] using write_mid (pre ++ [true]) (frame w) a c
    rw [hw] at hs2
    have t1 := RecoveryExecution.Timed.single (p := machine) (by cases c <;> rfl) hs1
    have t2 := RecoveryExecution.Timed.single (p := machine) (by cases c <;> rfl) hs2
    have tail := ih (pre ++ [true, c]) a
    have e3 : (pre ++ [true, c]).length = pre.length + 1 + 1 := by simp
    have e5 : pre ++ [true, c] ++ frame (shiftIn a w) = pre ++ frame (shiftIn c (a :: w)) := by
      simp [frame, shiftIn]
    have e6 : carryOut a w = carryOut c (a :: w) := rfl
    have e7 : pre.length + 1 + 1 + 2 * w.length = pre.length + 2 * (a :: w).length := by simp; omega
    rw [e3, e5, e6, e7] at tail
    have := (t1.trans t2).trans tail
    rwa [show 1 + 1 + (2 * w.length + 1) = 2 * (a :: w).length + 1 by simp; omega] at this

theorem run (w : List Bool) (x : Bool) :
    Step machine (2 * w.length + 1) ![0, 0] ![frame w, [x]]
      ![2 * w.length, 0] ![frame (shiftIn false w), [carryOut false w]] := by
  obtain ⟨r, hr, hf, hs⟩ := (timed x w [] false).run rfl
  refine ⟨r, hr, ?_, ?_, by omega⟩
  · rw [hf]; simp [cfg]
  · rw [hf]; simp [cfg]

end ShiftOut

/-! ## The masked XOR pass: `H := H ⊕ (f ∧ P)` in place, with `f` read once from a flag cell -/

namespace MaskXor
open Three (act cfg)

/-- Tape 0 the word (in place), tape 1 the operand, tape 2 the flag. State `0` reads the flag, `1`/`2` read a
marker (flag clear/set), `3`/`4` rewrite a bit, `5` halts. -/
def machine : Machine 3 6 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 5
  rule := fun q sc =>
    if q.val = 0 then some (if sc 2 then act 2 none none none .stay .stay .stay else act 1 none none none .stay .stay .stay)
    else if q.val = 1 then
      some (if sc 0 then act 3 none none none .right .right .stay else act 5 none none none .stay .stay .stay)
    else if q.val = 2 then
      some (if sc 0 then act 4 none none none .right .right .stay else act 5 none none none .stay .stay .stay)
    else if q.val = 3 then some (act 1 (some (sc 0)) none none .right .right .stay)
    else if q.val = 4 then some (act 2 (some (xor (sc 0) (sc 1))) none none .right .right .stay)
    else none

def mark (f : Bool) : Fin 6 := if f then 2 else 1
def bitS (f : Bool) : Fin 6 := if f then 4 else 3

theorem init_step (f : Bool) (H P G : List Bool) (hg : ℕ) (hr : readTapeBit G hg = f) :
    step machine (cfg 0 H P G 0 0 hg) = some (cfg (mark f) H P G 0 0 hg) := by
  cases f
  · exact Three.step_cfg machine 0 1 H P G 0 0 hg none none none .stay .stay .stay (by simp [machine, hr])
  · exact Three.step_cfg machine 0 2 H P G 0 0 hg none none none .stay .stay .stay (by simp [machine, hr])

theorem mark_step (f : Bool) (H P G : List Bool) (hh hp hg : ℕ) (hr : readTapeBit H hh = true) :
    step machine (cfg (mark f) H P G hh hp hg) = some (cfg (bitS f) H P G (hh + 1) (hp + 1) hg) := by
  cases f
  · exact Three.step_cfg machine 1 3 H P G hh hp hg none none none .right .right .stay (by simp [machine, hr])
  · exact Three.step_cfg machine 2 4 H P G hh hp hg none none none .right .right .stay (by simp [machine, hr])

theorem end_step (f : Bool) (H P G : List Bool) (hh hp hg : ℕ) (hr : readTapeBit H hh = false) :
    step machine (cfg (mark f) H P G hh hp hg) = some (cfg 5 H P G hh hp hg) := by
  cases f
  · exact Three.step_cfg machine 1 5 H P G hh hp hg none none none .stay .stay .stay (by simp [machine, hr])
  · exact Three.step_cfg machine 2 5 H P G hh hp hg none none none .stay .stay .stay (by simp [machine, hr])

theorem bit_step (f a b : Bool) (H P G : List Bool) (hh hp hg : ℕ) (ha : readTapeBit H hh = a)
    (hb : readTapeBit P hp = b) :
    step machine (cfg (bitS f) H P G hh hp hg) =
      some (cfg (mark f) (writeTapeBit H hh (mx f a b)) P G (hh + 1) (hp + 1) hg) := by
  cases f
  · show step machine (cfg 3 H P G hh hp hg) =
      some (cfg 1 (writeTapeBit H hh (mx false a b)) P G (hh + 1) (hp + 1) hg)
    rw [Three.step_cfg machine 3 1 H P G hh hp hg (some a) none none .right .right .stay (by simp [machine, ha])]
    simp [Two.wr, mx, HeadMove.apply]
  · show step machine (cfg 4 H P G hh hp hg) =
      some (cfg 2 (writeTapeBit H hh (mx true a b)) P G (hh + 1) (hp + 1) hg)
    rw [Three.step_cfg machine 4 2 H P G hh hp hg (some (xor a b)) none none .right .right .stay
      (by simp [machine, ha, hb])]
    simp [Two.wr, mx, HeadMove.apply]

theorem timed (f : Bool) (G : List Bool) (hg : ℕ) (u : List Bool) : ∀ (v preH preP postP : List Bool),
    u.length = v.length →
    RecoveryExecution.Timed machine (2 * u.length + 1)
      (cfg (mark f) (preH ++ frame u) (preP ++ frame v ++ postP) G preH.length preP.length hg)
      (cfg 5 (preH ++ frame (List.zipWith (mx f) u v)) (preP ++ frame v ++ postP) G
        (preH.length + 2 * u.length) (preP.length + 2 * u.length) hg) := by
  induction u with
  | nil =>
    intro v preH preP postP _
    have hs := end_step f (preH ++ frame []) (preP ++ frame v ++ postP) G preH.length preP.length hg
      (by simpa [frame] using Streaming.read_append preH [] false)
    simpa [frame] using RecoveryExecution.Timed.single (p := machine) (by cases f <;> rfl) hs
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
    have hs1 := mark_step f (preH ++ frame (a :: u)) (preP ++ frame (b :: v) ++ postP) G preH.length preP.length hg hr1
    have hs2 := bit_step f a b (preH ++ frame (a :: u)) (preP ++ frame (b :: v) ++ postP) G (preH.length + 1)
      (preP.length + 1) hg hra hrb
    have hw : writeTapeBit (preH ++ frame (a :: u)) (preH.length + 1) (mx f a b) = preH ++ [true, mx f a b] ++ frame u := by
      simpa [frame] using write_mid (preH ++ [true]) (frame u) a (mx f a b)
    rw [hw] at hs2
    have t1 := RecoveryExecution.Timed.single (p := machine) (by cases f <;> rfl) hs1
    have t2 := RecoveryExecution.Timed.single (p := machine) (by cases f <;> rfl) hs2
    have tail := ih v (preH ++ [true, mx f a b]) (preP ++ [true, b]) postP hl'
    have eP : preP ++ [true, b] ++ frame v ++ postP = preP ++ frame (b :: v) ++ postP := by simp [frame]
    have e3 : (preH ++ [true, mx f a b]).length = preH.length + 1 + 1 := by simp
    have e4 : (preP ++ [true, b]).length = preP.length + 1 + 1 := by simp
    have e5 : preH ++ [true, mx f a b] ++ frame (List.zipWith (mx f) u v) =
        preH ++ frame (List.zipWith (mx f) (a :: u) (b :: v)) := by simp [frame]
    have e7 : preH.length + 1 + 1 + 2 * u.length = preH.length + 2 * (a :: u).length := by simp; omega
    have e8 : preP.length + 1 + 1 + 2 * u.length = preP.length + 2 * (a :: u).length := by simp; omega
    rw [eP, e3, e4, e5, e7, e8] at tail
    have := (t1.trans t2).trans tail
    rwa [show 1 + 1 + (2 * u.length + 1) = 2 * (a :: u).length + 1 by simp; omega] at this

/-- **The masked XOR** as one `Step`: the flag is read from tape 2 at its head, which does not move. -/
theorem run (u v G : List Bool) (hg : ℕ) (hl : u.length = v.length) :
    Step machine (2 * u.length + 2) ![0, 0, hg] ![frame u, frame v, G]
      ![2 * u.length, 2 * u.length, hg] ![frame (List.zipWith (mx (readTapeBit G hg)) u v), frame v, G] := by
  have hs := init_step (readTapeBit G hg) (frame u) (frame v) G hg rfl
  have t0 := RecoveryExecution.Timed.single (p := machine) rfl hs
  have t1 := timed (readTapeBit G hg) G hg u v [] [] [] hl
  simp only [List.nil_append, List.append_nil, List.length_nil, Nat.zero_add] at t1
  obtain ⟨r, hr, hf, hsteps⟩ := (t0.trans t1).run rfl
  refine ⟨r, ?_, ?_, ?_, by omega⟩
  · rw [show 2 * u.length + 2 = 1 + (2 * u.length + 1) by omega]; exact hr
  · rw [hf]; rfl
  · rw [hf]; rfl

end MaskXor

/-! ## Assembly helpers -/

theorem dockRun {t u s n : ℕ} {p : Machine t s} {hin hout : Fin t → ℕ} {tin tout : Fin t → List Bool}
    (h : Step p n hin tin hout tout) (slots : Fin t → Fin u) (hi : Function.Injective slots)
    (H : Fin u → ℕ) (A : Fin u → List Bool) (hH : ∀ j, H (slots j) = hin j) (hA : ∀ j, A (slots j) = tin j) :
    Step (RecoveryFocus.machine slots p) n H A (dockH slots H hout) (RecoveryRootRound.install slots A tout) := by
  have hf := h.focus slots hi H A
  have e1 : dockH slots H hin = H := by
    funext i
    cases hp : RecoveryFocus.pick slots i with
    | none => simp [dockH, hp]
    | some j =>
      have he := RecoveryFocus.slot_of_pick slots hp
      simp only [dockH, hp]
      rw [← he]
      exact (hH j).symm
  rwa [e1, RecoveryRootRound.install_existing slots A tin hA] at hf

/-- Write `false` under the head, without moving. -/
def clearM : Machine 1 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 1
  rule := fun q _ => if q.val = 0 then some ⟨1, fun _ => some false, fun _ => .stay⟩ else none

theorem clear_run (c : Bool) : Step clearM 1 ![0] ![[c]] ![0] ![[false]] := by
  have hs : step clearM ⟨clearM.start, ![0], ![[c]]⟩ = some ⟨1, ![0], ![[false]]⟩ := by
    simp [step, clearM]
    apply configuration_ext
    · rfl
    · funext i; fin_cases i; simp [applyAction, HeadMove.apply]
    · funext i; fin_cases i; simp [applyAction, writeTapeBit]
  obtain ⟨r, hr, hf, hs'⟩ := (RecoveryExecution.Timed.single (p := clearM) rfl hs).run rfl
  exact ⟨r, hr, by rw [hf], by rw [hf], by omega⟩

/-- Step the head one cell right. -/
def nudgeM : Machine 1 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 1
  rule := fun q _ => if q.val = 0 then some ⟨1, fun _ => none, fun _ => .right⟩ else none

theorem nudge_run (tape : List Bool) (h : ℕ) : Step nudgeM 1 ![h] ![tape] ![h + 1] ![tape] := by
  have hs : step nudgeM ⟨nudgeM.start, ![h], ![tape]⟩ = some ⟨1, ![h + 1], ![tape]⟩ := by
    simp [step, nudgeM]
    apply configuration_ext
    · rfl
    · funext i; fin_cases i; simp [applyAction, HeadMove.apply]
    · funext i; fin_cases i; simp [applyAction]
  obtain ⟨r, hr, hf, hs'⟩ := (RecoveryExecution.Timed.single (p := nudgeM) rfl hs).run rfl
  exact ⟨r, hr, by rw [hf], by rw [hf], by omega⟩

theorem read_single (c : Bool) : readTapeBit [c] 0 = c := by cases c <;> rfl

theorem read_frame_mark (w : List Bool) (i : ℕ) (hi : i < w.length) : readTapeBit (frame w) (2 * i) = true := by
  induction w generalizing i with
  | nil => simp at hi
  | cons a w ih =>
    cases i with
    | zero => rfl
    | succ i =>
      have := ih i (by simpa using hi)
      simpa [frame, readTapeBit, Nat.mul_succ] using this

theorem read_frame_bit (w : List Bool) (i : ℕ) (hi : i < w.length) : readTapeBit (frame w) (2 * i + 1) = w[i] := by
  induction w generalizing i with
  | nil => simp at hi
  | cons a w ih =>
    cases i with
    | zero => rfl
    | succ i =>
      have := ih i (by simpa using hi)
      simpa [frame, readTapeBit, Nat.mul_succ] using this

theorem read_frame_end (w : List Bool) : readTapeBit (frame w) (2 * w.length) = false := by
  induction w with
  | nil => rfl
  | cons a w ih => simpa [frame, readTapeBit, Nat.mul_succ] using ih

/-! ## One LFSR step: tapes 0 the word, 1 the modulus, 2 the flag cell, 3 the rewind log -/

def slotsS : Fin 2 → Fin 3 := ![0, 2]
def sel0 : Fin 3 → Bool := fun i => decide (i = 0)
def sel01 : Fin 3 → Bool := fun i => decide (i = 0 ∨ i = 1)
def slotF : Fin 1 → Fin (3 + 1) := ![2]

noncomputable def lfsrM :=
  Composition.machine (Composition.machine (MaskedReset.machine (RecoveryFocus.machine slotsS ShiftOut.machine) sel0)
    (MaskedReset.machine MaskXor.machine sel01)) (RecoveryFocus.machine slotF clearM)

def lfsrCost (ℓ : ℕ) : ℕ := 2 * (2 * ℓ + 1) + 2 + 1 + (2 * (2 * ℓ + 2) + 2) + 1 + 1

theorem dockH_S (H : Fin 3 → ℕ) (v : Fin 2 → ℕ) : dockH slotsS H v = ![v 0, H 1, v 1] := by
  funext i; fin_cases i
  · exact dockH_slot _ (by decide) _ _ 0
  · exact dockH_other _ _ _ _ (by decide)
  · exact dockH_slot _ (by decide) _ _ 1

theorem install_S (A : Fin 3 → List Bool) (v : Fin 2 → List Bool) :
    RecoveryRootRound.install slotsS A v = ![v 0, A 1, v 1] := by
  funext i; fin_cases i
  · exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
  · exact RecoveryRootRound.install_other _ _ _ _ (by decide)
  · exact RecoveryRootRound.install_slot _ (by decide) _ _ 1

theorem dockH_F (H : Fin (3 + 1) → ℕ) (v : Fin 1 → ℕ) : dockH slotF H v = ![H 0, H 1, v 0, H 3] := by
  funext i; fin_cases i
  · exact dockH_other _ _ _ _ (by decide)
  · exact dockH_other _ _ _ _ (by decide)
  · exact dockH_slot _ (by decide) _ _ 0
  · exact dockH_other _ _ _ _ (by decide)

theorem install_F (A : Fin (3 + 1) → List Bool) (v : Fin 1 → List Bool) :
    RecoveryRootRound.install slotF A v = ![A 0, A 1, v 0, A 3] := by
  funext i; fin_cases i
  · exact RecoveryRootRound.install_other _ _ _ _ (by decide)
  · exact RecoveryRootRound.install_other _ _ _ _ (by decide)
  · exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
  · exact RecoveryRootRound.install_other _ _ _ _ (by decide)

/-- **One LFSR step** (multiplication by `x` modulo `p`) as one `Step`: the word becomes
`frame (binary ℓ (lfsr p ℓ a))`, the flag cell is cleared, every head ends at cell 0. -/
theorem lfsr_run (p ℓ a : ℕ) (hℓ : 1 ≤ ℓ) (x : Bool) (cap : ℕ) (hcap : 2 * ℓ + 2 ≤ cap) :
    Step lfsrM (lfsrCost ℓ) ![0, 0, 0, 0]
      ![frame (binary ℓ a), frame (binary ℓ p), [x], List.replicate cap false] ![0, 0, 0, 0]
      ![frame (binary ℓ (lfsr p ℓ a)), frame (binary ℓ p), [false], List.replicate cap false] := by
  have h1 := ShiftOut.run (binary ℓ a) x
  rw [binary_length] at h1
  have h1d := dockRun h1 slotsS (by decide) ![0, 0, 0] ![frame (binary ℓ a), frame (binary ℓ p), [x]]
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  rw [dockH_S, install_S] at h1d
  have h1m := h1d.mask sel0 (by intro i _; fin_cases i <;> rfl) (by omega : 2 * ℓ + 1 ≤ cap)
  have h2 := MaskXor.run (shiftIn false (binary ℓ a)) (binary ℓ p) [carryOut false (binary ℓ a)] 0 (by simp)
  rw [read_single, shiftIn_length, binary_length] at h2
  have h2m := h2.mask sel01 (by intro i _; fin_cases i <;> rfl) (by omega : 2 * ℓ + 2 ≤ cap)
  have h3 := dockRun (clear_run (carryOut false (binary ℓ a))) slotF (by decide) ![0, 0, 0, 0]
    ![frame (List.zipWith (mx (carryOut false (binary ℓ a))) (shiftIn false (binary ℓ a)) (binary ℓ p)),
      frame (binary ℓ p), [carryOut false (binary ℓ a)], List.replicate cap false]
    (by intro j; fin_cases j; rfl) (by intro j; fin_cases j; rfl)
  rw [dockH_F, install_F] at h3
  have A1 : Step (MaskedReset.machine (RecoveryFocus.machine slotsS ShiftOut.machine) sel0) (2 * (2 * ℓ + 1) + 2)
      ![0, 0, 0, 0] ![frame (binary ℓ a), frame (binary ℓ p), [x], List.replicate cap false] ![0, 0, 0, 0]
      ![frame (shiftIn false (binary ℓ a)), frame (binary ℓ p), [carryOut false (binary ℓ a)], List.replicate cap false] := by
    refine (h1m.congr_in ?_ ?_).congr ?_ ?_ <;> funext i <;> fin_cases i <;> rfl
  have A2 : Step (MaskedReset.machine MaskXor.machine sel01) (2 * (2 * ℓ + 2) + 2)
      ![0, 0, 0, 0] ![frame (shiftIn false (binary ℓ a)), frame (binary ℓ p), [carryOut false (binary ℓ a)],
        List.replicate cap false] ![0, 0, 0, 0]
      ![frame (List.zipWith (mx (carryOut false (binary ℓ a))) (shiftIn false (binary ℓ a)) (binary ℓ p)),
        frame (binary ℓ p), [carryOut false (binary ℓ a)], List.replicate cap false] := by
    refine (h2m.congr_in ?_ ?_).congr ?_ ?_ <;> funext i <;> fin_cases i <;> rfl
  have A3 := (A1.seq A2).seq h3
  rw [← lfsr_bits p ℓ a hℓ] at A3
  refine A3.congr ?_ ?_ <;> funext i <;> fin_cases i <;> rfl

/-! ## The product: tapes 0 the multiplier `y`, 1 the accumulator, 2 the shifted multiplicand, 3 the modulus,
4 the flag cell, 5 the rewind log -/

/-- The state of `fmulShift`'s fold after `i` bits of `y`. -/
def mulState (p ℓ x y i : ℕ) : ℕ × ℕ :=
  (List.range i).foldl (fun (st : ℕ × ℕ) j => (if y.testBit j then st.1 ^^^ st.2 else st.1, lfsr p ℓ st.2)) (0, x)

theorem mulState_succ (p ℓ x y i : ℕ) :
    mulState p ℓ x y (i + 1) =
      (if y.testBit i then (mulState p ℓ x y i).1 ^^^ (mulState p ℓ x y i).2 else (mulState p ℓ x y i).1,
        lfsr p ℓ (mulState p ℓ x y i).2) := by
  unfold mulState
  rw [List.range_succ, List.foldl_append]
  rfl

theorem fmulShift_eq_state (p ℓ x y : ℕ) : fmulShift p ℓ x y = (mulState p ℓ x y ℓ).1 := rfl

theorem mx_binary (ℓ acc st : ℕ) (f : Bool) :
    List.zipWith (mx f) (binary ℓ acc) (binary ℓ st) = binary ℓ (if f then acc ^^^ st else acc) := by
  cases f
  · simp only [Bool.false_eq_true, ↓reduceIte]; exact zipWith_mx_false _ _ (by simp)
  · simp only [↓reduceIte]; rw [zipWith_mx_true, binary_xor]

def slotY : Fin 1 → Fin (5 + 1) := ![0]
def slotsX : Fin 3 → Fin 5 := ![1, 2, 0]
def selAS : Fin 5 → Bool := fun i => decide (i = 1 ∨ i = 2)
def slotsL : Fin (3 + 1) → Fin (5 + 1) := ![2, 3, 4, 5]

noncomputable def mulBody :=
  Composition.machine (Composition.machine (Composition.machine (RecoveryFocus.machine slotY nudgeM)
    (MaskedReset.machine (RecoveryFocus.machine slotsX MaskXor.machine) selAS))
    (RecoveryFocus.machine slotsL lfsrM)) (RecoveryFocus.machine slotY nudgeM)

/-- **The product machine**: the stream loop over the multiplier's markers. -/
noncomputable def fmulM := StreamController.machine mulBody 0

theorem dockH_Y (H : Fin (5 + 1) → ℕ) (v : Fin 1 → ℕ) : dockH slotY H v = ![v 0, H 1, H 2, H 3, H 4, H 5] := by
  funext i; fin_cases i
  all_goals first
    | exact dockH_slot _ (by decide) _ _ 0
    | exact dockH_other _ _ _ _ (by decide)

theorem install_Y (A : Fin (5 + 1) → List Bool) (v : Fin 1 → List Bool) :
    RecoveryRootRound.install slotY A v = ![v 0, A 1, A 2, A 3, A 4, A 5] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

theorem dockH_X (H : Fin 5 → ℕ) (v : Fin 3 → ℕ) : dockH slotsX H v = ![v 2, v 0, v 1, H 3, H 4] := by
  funext i; fin_cases i
  all_goals first
    | exact dockH_slot _ (by decide) _ _ 0
    | exact dockH_slot _ (by decide) _ _ 1
    | exact dockH_slot _ (by decide) _ _ 2
    | exact dockH_other _ _ _ _ (by decide)

theorem install_X (A : Fin 5 → List Bool) (v : Fin 3 → List Bool) :
    RecoveryRootRound.install slotsX A v = ![v 2, v 0, v 1, A 3, A 4] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 1
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 2
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

theorem dockH_L (H : Fin (5 + 1) → ℕ) (v : Fin (3 + 1) → ℕ) : dockH slotsL H v = ![H 0, H 1, v 0, v 1, v 2, v 3] := by
  funext i; fin_cases i
  all_goals first
    | exact dockH_slot _ (by decide) _ _ 0
    | exact dockH_slot _ (by decide) _ _ 1
    | exact dockH_slot _ (by decide) _ _ 2
    | exact dockH_slot _ (by decide) _ _ 3
    | exact dockH_other _ _ _ _ (by decide)

theorem install_L (A : Fin (5 + 1) → List Bool) (v : Fin (3 + 1) → List Bool) :
    RecoveryRootRound.install slotsL A v = ![A 0, A 1, v 0, v 1, v 2, v 3] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 1
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 2
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 3
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

/-- The bank before bit `i` of the multiplier. -/
def mulH (i : ℕ) : Fin (5 + 1) → ℕ := ![2 * i, 0, 0, 0, 0, 0]
def mulA (p ℓ x y cap i : ℕ) : Fin (5 + 1) → List Bool :=
  ![frame (binary ℓ y), frame (binary ℓ (mulState p ℓ x y i).1), frame (binary ℓ (mulState p ℓ x y i).2),
    frame (binary ℓ p), [false], List.replicate cap false]

def mulIterCost (ℓ : ℕ) : ℕ := 1 + 1 + (2 * (2 * ℓ + 2) + 2) + 1 + lfsrCost ℓ + 1 + 1

theorem mul_step (p ℓ x y cap i : ℕ) (hℓ : 1 ≤ ℓ) (hi : i < ℓ) (hcap : 2 * ℓ + 2 ≤ cap) :
    Step mulBody (mulIterCost ℓ) (mulH i) (mulA p ℓ x y cap i) (mulH (i + 1)) (mulA p ℓ x y cap (i + 1)) := by
  -- a: onto the bit
  have ha := dockRun (nudge_run (frame (binary ℓ y)) (2 * i)) slotY (by decide) (mulH i) (mulA p ℓ x y cap i)
    (by intro j; fin_cases j; rfl) (by intro j; fin_cases j; rfl)
  rw [dockH_Y, install_Y] at ha
  -- b: the masked XOR of the accumulator with the multiplicand, flag = the bit of `y`
  have hb0 := MaskXor.run (binary ℓ (mulState p ℓ x y i).1) (binary ℓ (mulState p ℓ x y i).2)
    (frame (binary ℓ y)) (2 * i + 1) (by simp)
  have hbit : readTapeBit (frame (binary ℓ y)) (2 * i + 1) = y.testBit i := by
    rw [read_frame_bit (binary ℓ y) i (by simpa using hi), binary_getElem]
  rw [hbit, mx_binary, binary_length] at hb0
  have hbd := dockRun hb0 slotsX (by decide) ![2 * i + 1, 0, 0, 0, 0]
    ![frame (binary ℓ y), frame (binary ℓ (mulState p ℓ x y i).1), frame (binary ℓ (mulState p ℓ x y i).2),
      frame (binary ℓ p), [false]]
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  rw [dockH_X, install_X] at hbd
  have hbm := hbd.mask selAS (by intro i hi; fin_cases i <;> first | rfl | simp [selAS] at hi) (by omega : 2 * ℓ + 2 ≤ cap)
  -- c: one LFSR step of the multiplicand
  have hc := dockRun (lfsr_run p ℓ (mulState p ℓ x y i).2 hℓ false cap hcap) slotsL (by decide)
    ![2 * i + 1, 0, 0, 0, 0, 0]
    ![frame (binary ℓ y),
      frame (binary ℓ (if y.testBit i then (mulState p ℓ x y i).1 ^^^ (mulState p ℓ x y i).2 else (mulState p ℓ x y i).1)),
      frame (binary ℓ (mulState p ℓ x y i).2), frame (binary ℓ p), [false], List.replicate cap false]
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  rw [dockH_L, install_L] at hc
  -- d: onto the next marker
  have hd := dockRun (nudge_run (frame (binary ℓ y)) (2 * i + 1)) slotY (by decide) ![2 * i + 1, 0, 0, 0, 0, 0]
    ![frame (binary ℓ y),
      frame (binary ℓ (if y.testBit i then (mulState p ℓ x y i).1 ^^^ (mulState p ℓ x y i).2 else (mulState p ℓ x y i).1)),
      frame (binary ℓ (lfsr p ℓ (mulState p ℓ x y i).2)), frame (binary ℓ p), [false], List.replicate cap false]
    (by intro j; fin_cases j; rfl) (by intro j; fin_cases j; rfl)
  rw [dockH_Y, install_Y] at hd
  have hB : Step (MaskedReset.machine (RecoveryFocus.machine slotsX MaskXor.machine) selAS) (2 * (2 * ℓ + 2) + 2)
      ![2 * i + 1, 0, 0, 0, 0, 0]
      ![frame (binary ℓ y), frame (binary ℓ (mulState p ℓ x y i).1), frame (binary ℓ (mulState p ℓ x y i).2),
        frame (binary ℓ p), [false], List.replicate cap false]
      ![2 * i + 1, 0, 0, 0, 0, 0]
      ![frame (binary ℓ y),
        frame (binary ℓ (if y.testBit i then (mulState p ℓ x y i).1 ^^^ (mulState p ℓ x y i).2 else (mulState p ℓ x y i).1)),
        frame (binary ℓ (mulState p ℓ x y i).2), frame (binary ℓ p), [false], List.replicate cap false] := by
    refine (hbm.congr_in ?_ ?_).congr ?_ ?_ <;> funext j <;> fin_cases j <;> rfl
  have hall := ((ha.seq hB).seq hc).seq hd
  have hA1 : mulA p ℓ x y cap (i + 1) =
      ![frame (binary ℓ y),
        frame (binary ℓ (if y.testBit i then (mulState p ℓ x y i).1 ^^^ (mulState p ℓ x y i).2 else (mulState p ℓ x y i).1)),
        frame (binary ℓ (lfsr p ℓ (mulState p ℓ x y i).2)), frame (binary ℓ p), [false], List.replicate cap false] := by
    unfold mulA; rw [mulState_succ]
  rw [hA1]
  refine hall.congr ?_ ?_
  · funext j
    fin_cases j
    · show 2 * i + 1 + 1 = 2 * (i + 1)
      omega
    all_goals rfl
  · funext j; fin_cases j <;> rfl

/-- **The product** `fmulShift p ℓ x y` as one `Step`: the stream loop over the `ℓ` bits of `y`. -/
theorem fmul_run (p ℓ x y cap : ℕ) (hℓ : 1 ≤ ℓ) (hcap : 2 * ℓ + 2 ≤ cap) :
    Step fmulM (ℓ * (mulIterCost ℓ + 2) + 1)
      ![0, 0, 0, 0, 0, 0]
      ![frame (binary ℓ y), frame (binary ℓ 0), frame (binary ℓ x), frame (binary ℓ p), [false], List.replicate cap false]
      ![2 * ℓ, 0, 0, 0, 0, 0]
      ![frame (binary ℓ y), frame (binary ℓ (fmulShift p ℓ x y)), frame (binary ℓ (mulState p ℓ x y ℓ).2),
        frame (binary ℓ p), [false], List.replicate cap false] := by
  let W : WhileBody (5 + 1) _ :=
    { body := mulBody
      tape := 0
      bound := ℓ
      H := mulH
      A := mulA p ℓ x y cap
      cost := fun _ => mulIterCost ℓ
      step := fun i hi => mul_step p ℓ x y cap i hℓ hi hcap
      cont := fun i hi => by
        show readTapeBit (frame (binary ℓ y)) (2 * i) = true
        exact read_frame_mark (binary ℓ y) i (by simpa using hi)
      halt := by
        show readTapeBit (frame (binary ℓ y)) (2 * ℓ) = false
        simpa using read_frame_end (binary ℓ y) }
  have hW := W.run
  rw [W.rest_const _ (fun _ => rfl)] at hW
  exact hW

theorem foldl_xor (L : List Bool) (old : Bool) :
    L.foldl xor old = xor old (decide ((L.filter (fun b => b)).length % 2 = 1)) := by
  induction L generalizing old with
  | nil => simp
  | cons x L ih =>
    rw [List.foldl_cons, ih]
    have key : ∀ n : ℕ, decide ((n + 1) % 2 = 1) = !decide (n % 2 = 1) := by
      intro n
      rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [Nat.add_mod, h]
    cases x
    · simp
    · have e : (List.filter (fun b : Bool => b) (true :: L)).length = (List.filter (fun b : Bool => b) L).length + 1 := by
        simp
      rw [e, key]
      cases old <;> simp

theorem zipWith_and_binary (ℓ m a : ℕ) :
    List.zipWith (· && ·) (binary ℓ m) (binary ℓ a) = (List.range ℓ).map (fun b => m.testBit b && a.testBit b) := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    rw [List.getElem_zipWith, binary_getElem, binary_getElem, List.getElem_map, List.getElem_range]

/-- The machine's fold is the reference's masked parity. -/
theorem parity_bit (ℓ m a : ℕ) :
    ZipFold.fold parityStep (binary ℓ m) (binary ℓ a) false = decide (parityMasked m a ℓ = 1) := by
  rw [fold_parity, zipWith_and_binary, foldl_xor]
  unfold parityMasked
  simp [List.filter_map, Function.comp_def]

/-- **The trace bit** as one `Step` of the fold machine: `decide (parityMasked m a ℓ = 1)` is appended. -/
theorem trace_run (ℓ m a : ℕ) (output : List Bool) :
    Step (ZipFold.machine parityStep false) (2 * ℓ + 1) ![0, 0, output.length]
      ![frame (binary ℓ m), frame (binary ℓ a), output] ![2 * ℓ, 2 * ℓ, output.length + 1]
      ![frame (binary ℓ m), frame (binary ℓ a), output ++ [decide (parityMasked m a ℓ = 1)]] := by
  obtain ⟨r, hr, hf⟩ := ZipFold.scan_run parityStep false [] [] (binary ℓ m) (binary ℓ a) [] [] output (by simp)
  simp only [List.nil_append, List.append_nil, List.length_nil, binary_length, Nat.zero_add] at hr hf
  refine ⟨r, hr, ?_, ?_, runFrom_steps_le _ _ _ _ hr⟩
  · rw [hf]; simp [ZipFold.config]
  · rw [hf, parity_bit]; rfl

/-! ## Cost in a class (per call: polynomial in `ℓ`) -/

theorem lfsrCost_le (ℓ q : ℕ) (hq : 1 ≤ q) (hl : ℓ ≤ q) : lfsrCost ℓ ≤ 25 * q := by
  unfold lfsrCost; omega

theorem fmulCost_le (ℓ q : ℕ) (hq : 1 ≤ q) (hl : ℓ ≤ q) : ℓ * (mulIterCost ℓ + 2) + 1 ≤ 40 * q ^ 2 := by
  unfold mulIterCost lfsrCost
  have h1 : ℓ * ℓ ≤ q * q := Nat.mul_le_mul hl hl
  have h2 : ℓ ≤ q * q := hl.trans (Nat.le_mul_of_pos_left q hq)
  rw [sq]
  nlinarith

theorem lfsr_within {E : Envelope} {cls : BudgetClass} {q k psi ℓ : ℕ} (hq : 1 ≤ q) (hl : ℓ ≤ q)
    (hd : 1 ≤ classDeg E cls) : Within E cls 25 q k psi (lfsrCost ℓ) :=
  Within.of_poly hq (a := 1) (by rw [pow_one]; exact lfsrCost_le ℓ q hq hl) hd

theorem fmul_within {E : Envelope} {cls : BudgetClass} {q k psi ℓ : ℕ} (hq : 1 ≤ q) (hl : ℓ ≤ q)
    (hd : 2 ≤ classDeg E cls) : Within E cls 40 q k psi (ℓ * (mulIterCost ℓ + 2) + 1) :=
  Within.of_poly hq (fmulCost_le ℓ q hq hl) hd

/-! ## Twins -/

/-- The bitwise LFSR step is the reference on every 4-bit word (modulus `x^4 + x + 1`). -/
theorem lfsr_bits_twin : ∀ a < 16, binary 4 (lfsr 19 4 a) =
    List.zipWith (mx (carryOut false (binary 4 a))) (shiftIn false (binary 4 a)) (binary 4 19) := by decide

/-- The product's state machine is the reference product on every pair of 4-bit words. -/
theorem mulState_twin : ∀ x < 16, ∀ y < 16, (mulState 19 4 x y 4).1 = fmul 19 4 x y := by decide

/-- Executed runs of the two passes of an LFSR step on `a = 0b1001`. -/
theorem shiftOut_twin :
    (runFrom ShiftOut.machine 20 ⟨ShiftOut.machine.start, ![0, 0], ![frame (binary 4 9), [false]]⟩).map
      (fun r => (r.final.tapes 0, r.final.tapes 1)) = some (frame (binary 4 2), [true]) := by decide

theorem maskXor_twin :
    (runFrom MaskXor.machine 20 ⟨MaskXor.machine.start, ![0, 0, 0], ![frame (binary 4 2), frame (binary 4 19), [true]]⟩).map
      (fun r => r.final.tapes 0) = some (frame (binary 4 (lfsr 19 4 9))) := by decide

end NearCubicWires.WireExponent3_5.GF2
