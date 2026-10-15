import Proof.Gates.Expand.MobVal

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicGates.Close.Expand

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length binary_value)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (NumOn)

variable {ns nr : ℕ}

/-! ## Value level -/

/-- The position after the last `1` among the first `i` bits. -/
def szI (v i : ℕ) : ℕ := Nat.size (v % 2 ^ i)

theorem szI_zero (v : ℕ) : szI v 0 = 0 := by simp [szI, Nat.mod_one]

theorem szI_succ (v i : ℕ) : szI v (i + 1) = if v.testBit i then i + 1 else szI v i := by
  unfold szI
  rw [mod_two_pow_succ']
  split_ifs with h
  · exact size_add_two_pow _ _ (Nat.mod_lt _ (Nat.two_pow_pos i))
  · rw [Nat.add_zero]

theorem szI_le (v i : ℕ) : szI v i ≤ i := Nat.size_le.mpr (Nat.mod_lt _ (Nat.two_pow_pos i))

/-- The length of the payload: `natBitLength v`. -/
def lenF (v : ℕ) : ℕ := if Nat.size v = 0 then 1 else Nat.size v

theorem lenF_eq (v : ℕ) : lenF v = natBitLength v := by
  unfold lenF
  split_ifs with h
  · rw [Nat.size_eq_zero] at h; subst h; rfl
  · exact size_eq_of_ne v (fun e => h (by rw [e]; rfl))

theorem lenF_le (v Wb : ℕ) (hv : v < 2 ^ Wb) (hW : 1 ≤ Wb) : lenF v ≤ Wb := by
  unfold lenF; split_ifs
  · exact hW
  · exact Nat.size_le.mpr hv

theorem ofFn_testBit (v n : ℕ) : (List.ofFn fun j : Fin n => v.testBit j.val) = (List.range n).map v.testBit := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.ofFn_succ_last, List.range_succ, List.map_append, ← ih]; rfl

theorem natWord_eq_lenF (v : ℕ) :
    natWord v = List.replicate (lenF v) true ++ false :: (List.range (lenF v)).map v.testBit := by
  rw [lenF_eq, ← ofFn_testBit]; rfl

theorem natWord_length (v : ℕ) : (natWord v).length = 2 * lenF v + 1 := by
  rw [natWord_eq_lenF]; simp; ring

theorem frame_testBit (Wb v i : ℕ) (hi : i < Wb) :
    readTapeBit (frame (binary Wb v)) (2 * i + 1) = v.testBit i := by
  rw [NearCubicWires.WireExponent3_5.UnionMachine.RegRat.frame_bit Wb v i hi, Nat.testBit_eq_decide_div_mod_eq]
  cases h : v / 2 ^ i % 2 == 1 <;> simp_all

theorem frame_end_gen : ∀ bs : List Bool, readTapeBit (frame bs) (2 * bs.length) = false
  | [] => rfl
  | b :: bs => by
      have := frame_end_gen bs
      unfold readTapeBit at *
      rw [List.length_cons, show 2 * (bs.length + 1) = 2 * bs.length + 1 + 1 by ring]
      simpa [frame] using this

theorem frame_end (Wb v : ℕ) : readTapeBit (frame (binary Wb v)) (2 * Wb) = false := by
  have := frame_end_gen (binary Wb v); rwa [binary_length] at this

/-! ## The program -/

section Prog
variable (X O : Fin (ns + 1)) (OP : Fin nr) (PR : Fin 4 ↪ Fin nr)

def moveZ (Z L : Fin nr) : WMX ns nr := .whr Z (.seq (WMX.dec Z) (WMX.inc L))

def scanBody : WMX ns nr :=
  .seq (WMX.fwd X) (.seq (WMX.inc (PR 2)) (.seq (.ifs X (.seq (moveZ (PR 1) (PR 0)) (WMX.inc (PR 0)))
    (WMX.inc (PR 1))) (.seq (WMX.fwd X) (WMX.inc (PR 2)))))

def rewX (P : Fin nr) : WMX ns nr := .whr P (.seq (WMX.dec P) (WMX.bwd X))

def clrR (r : Fin nr) : WMX ns nr := .whr r (WMX.dec r)

def onesW : WMX ns nr := .whr (PR 0) (.seq (WMX.dec (PR 0)) (.seq (WMX.inc (PR 3)) (.wm (emitC O OP true))))

def bitsW : WMX ns nr :=
  .whr (PR 3) (.seq (WMX.dec (PR 3)) (.seq (WMX.fwd X) (.seq (WMX.inc (PR 2))
    (.seq (.ifs X (.wm (emitC O OP true)) (.wm (emitC O OP false))) (.seq (WMX.fwd X) (WMX.inc (PR 2)))))))

/-- **The raw `natWord` writer.** -/
def natW : WMX ns nr :=
  .seq (.whs X (scanBody X PR)) (.seq (rewX X (PR 2)) (.seq (clrR (PR 1))
    (.seq (.ifr (PR 0) WMX.skip (WMX.inc (PR 0))) (.seq (onesW O OP PR) (.seq (.wm (emitC O OP false))
      (.seq (bitsW X O OP PR) (rewX X (PR 2))))))))

end Prog

def natWCost (Wb : ℕ) : ℕ := 7 * Wb ^ 2 + 100 * Wb + 30

/-! ## The writer's states -/

section States
variable {X O : Fin (ns + 1)} {OP : Fin nr} {PR : Fin 4 ↪ Fin nr} {cap : ℕ}

/-- The writer's state: `u` appended to `O`, head of `X` at `h`, scratch registers `r`. -/
def WD (X O : Fin (ns + 1)) (OP : Fin nr) (PR : Fin 4 ↪ Fin nr) (σ τ : WState ns nr) (u : List Bool) (h : ℕ)
    (r : Fin 4 → ℕ) : Prop :=
  SameExcept σ τ [X, O] [OP, PR 0, PR 1, PR 2, PR 3] ∧ τ.st X = σ.st X ∧ τ.st O = σ.st O ++ u ∧
    τ.sh O = σ.sh O + u.length ∧ τ.val OP = σ.val OP + u.length ∧ τ.sh X = h ∧ ∀ i, τ.val (PR i) = r i

theorem prN {i j : Fin 4} (h : i ≠ j) : PR i ≠ PR j := fun e => h (PR.injective e)

theorem WD.r_eq {σ τ : WState ns nr} {u : List Bool} {h : ℕ} {r r' : Fin 4 → ℕ}
    (hd : WD X O OP PR σ τ u h r) (e : r = r') : WD X O OP PR σ τ u h r' := e ▸ hd

theorem WD.inc (hOP : ∀ i, PR i ≠ OP) {σ τ : WState ns nr} {u : List Bool} {h : ℕ} {r : Fin 4 → ℕ}
    (hd : WD X O OP PR σ τ u h r) (i : Fin 4) (hc : r i < cap) :
    Runs cap (WMX.inc (PR i)) τ 3 (fun ρ => WD X O OP PR σ ρ u h (Function.update r i (r i + 1))) := by
  obtain ⟨hs, hX, hO, hOh, hOP', hh, hr⟩ := hd
  refine Runs.of (WXExec.inc cap (PR i) τ (by rw [hr]; exact hc)) ⟨⟨fun x hx => ?_, fun q hq => ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using hs.1 x hx
  · have : q ≠ PR i := by intro e; subst e; fin_cases i <;> simp at hq
    simp [Function.update_of_ne this]; exact hs.2.1 q hq
  · simpa using hs.2.2
  · simpa using hX
  · simpa using hO
  · simpa using hOh
  · simp [Function.update_of_ne (hOP i).symm]; exact hOP'
  · simpa using hh
  · intro j
    by_cases e : j = i
    · subst e; simp [hr]
    · simp [Function.update_of_ne e, Function.update_of_ne (prN (PR := PR) e), hr]

theorem WD.dec {σ τ : WState ns nr} {u : List Bool} {h : ℕ} {r : Fin 4 → ℕ}
    (hOP : ∀ i, PR i ≠ OP) (hd : WD X O OP PR σ τ u h r) (i : Fin 4) (hc : r i ≤ cap) :
    Runs cap (WMX.dec (PR i)) τ 1 (fun ρ => WD X O OP PR σ ρ u h (Function.update r i (r i - 1))) := by
  obtain ⟨hs, hX, hO, hOh, hOP', hh, hr⟩ := hd
  refine Runs.of (WXExec.dec cap (PR i) τ (by rw [hr]; exact hc)) ⟨⟨fun x hx => ?_, fun q hq => ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using hs.1 x hx
  · have : q ≠ PR i := by intro e; subst e; fin_cases i <;> simp at hq
    simp [Function.update_of_ne this]; exact hs.2.1 q hq
  · simpa using hs.2.2
  · simpa using hX
  · simpa using hO
  · simpa using hOh
  · simp [Function.update_of_ne (hOP i).symm]; exact hOP'
  · simpa using hh
  · intro j
    by_cases e : j = i
    · subst e; simp [hr]
    · simp [Function.update_of_ne e, Function.update_of_ne (prN (PR := PR) e), hr]

theorem WD.fwd (hXO : X ≠ O) {σ τ : WState ns nr} {u : List Bool} {h : ℕ} {r : Fin 4 → ℕ}
    (hd : WD X O OP PR σ τ u h r) : Runs cap (WMX.fwd X) τ 1 (fun ρ => WD X O OP PR σ ρ u (h + 1) r) := by
  obtain ⟨hs, hX, hO, hOh, hOP', hh, hr⟩ := hd
  refine Runs.of (WXExec.fwd cap X τ) ⟨⟨fun x hx => ?_, fun q hq => ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have : x ≠ X := fun e => hx (by simp [e])
    simp [Function.update_of_ne this]; exact hs.1 x hx
  · simpa using hs.2.1 q hq
  · simpa using hs.2.2
  · simpa using hX
  · simpa using hO
  · simp [Function.update_of_ne hXO.symm]; exact hOh
  · simpa using hOP'
  · simp [hh]
  · simpa using hr

theorem WD.bwd (hXO : X ≠ O) {σ τ : WState ns nr} {u : List Bool} {h : ℕ} {r : Fin 4 → ℕ}
    (hd : WD X O OP PR σ τ u h r) : Runs cap (WMX.bwd X) τ 1 (fun ρ => WD X O OP PR σ ρ u (h - 1) r) := by
  obtain ⟨hs, hX, hO, hOh, hOP', hh, hr⟩ := hd
  refine Runs.of (WXExec.bwd cap X τ) ⟨⟨fun x hx => ?_, fun q hq => ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have : x ≠ X := fun e => hx (by simp [e])
    simp [Function.update_of_ne this]; exact hs.1 x hx
  · simpa using hs.2.1 q hq
  · simpa using hs.2.2
  · simpa using hX
  · simpa using hO
  · simp [Function.update_of_ne hXO.symm]; exact hOh
  · simpa using hOP'
  · simp [hh]
  · simpa using hr

theorem WD.emit (hXO : X ≠ O) (hOP : ∀ i, PR i ≠ OP) {σ τ : WState ns nr} {u : List Bool} {h : ℕ}
    {r : Fin 4 → ℕ} (hd : WD X O OP PR σ τ u h r) (hO0 : σ.sh O = (σ.st O).length) (b : Bool)
    (hc : σ.val OP + u.length < cap) :
    Runs cap (.wm (emitC O OP b)) τ 7 (fun ρ => WD X O OP PR σ ρ (u ++ [b]) h r) := by
  obtain ⟨hs, hX, hO, hOh, hOP', hh, hr⟩ := hd
  have hτO : τ.sh O = (τ.st O).length := by rw [hOh, hO, List.length_append, hO0]
  refine Runs.of (WXExec.wm (emitC_spec cap O OP b τ hτO (by rw [hOP']; exact hc)))
    ⟨⟨fun x hx => ?_, fun q hq => ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have : x ≠ O := fun e => hx (by simp [e])
    simp [Function.update_of_ne this]; exact hs.1 x hx
  · have : q ≠ OP := fun e => hq (by simp [e])
    simp [Function.update_of_ne this]; exact hs.2.1 q hq
  · simpa using hs.2.2
  · simp [Function.update_of_ne hXO]; exact hX
  · simp [hO]
  · simp [hOh]; omega
  · simp [hOP']; omega
  · simp [Function.update_of_ne hXO, hh]
  · intro j; simp [Function.update_of_ne (hOP j), hr]

theorem WD.bit {σ τ : WState ns nr} {u : List Bool} {h : ℕ} {r : Fin 4 → ℕ}
    (hd : WD X O OP PR σ τ u h r) : wbit τ X = readTapeBit (σ.st X) h := by
  obtain ⟨_, hX, _, _, _, hh, _⟩ := hd
  simp [wbit, hX, hh]

theorem upd4 (a b c d : ℕ) (i : Fin 4) (x : ℕ) :
    Function.update ![a, b, c, d] i x = ![if i = 0 then x else a, if i = 1 then x else b, if i = 2 then x else c,
      if i = 3 then x else d] := by
  funext j; fin_cases i <;> fin_cases j <;> rfl

end States

end NearCubicGates.Close.Expand
