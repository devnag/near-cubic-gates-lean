import Proof.Gates.Expand.Print2

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

/-- The set bits of `s`, increasing. -/
def bitsOf (s : ℕ) : List ℕ := (List.range (Nat.size s)).filter fun j => s.testBit j

/-- The words a record prints. -/
def recOut (V W x : ℕ) : List Bool :=
  natWord (x / (2 ^ V * 2 ^ W)) ++ (bitsOf (x % (2 ^ V * 2 ^ W) / 2 ^ W)).flatMap natWord ++
    (if x % (2 ^ V * 2 ^ W) % 2 ^ W < 2 ^ (W - 1) then natWord 0 ++ natWord (x % (2 ^ V * 2 ^ W) % 2 ^ W)
     else natWord 1 ++ natWord (2 ^ W - x % (2 ^ V * 2 ^ W) % 2 ^ W))

/-- The bits emitted after `j` steps of the bit loop. -/
def bitsUpTo (s j : ℕ) : List Bool := ((List.range j).filter fun i => s.testBit i).flatMap natWord

theorem bitsUpTo_succ (s j : ℕ) :
    bitsUpTo s (j + 1) = bitsUpTo s j ++ (if s.testBit j then natWord j else []) := by
  unfold bitsUpTo
  rw [List.range_succ, List.filter_append, List.flatMap_append]
  split_ifs with h <;> simp [h]

theorem div_pos_iff_lt_size (s j : ℕ) : 0 < s / 2 ^ j ↔ j < Nat.size s := by
  rw [Nat.div_pos_iff, Nat.lt_size]; simp [Nat.two_pow_pos]

theorem and_one_testBit (s j : ℕ) : 0 < (s / 2 ^ j) &&& 1 ↔ s.testBit j = true := by
  rw [Nat.and_one_is_mod, Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (s / 2 ^ j) with h | h <;> simp [h]

/-! ## The program -/

section Prog
variable (PB : Fin 14 ↪ Fin (ns + 1)) (PG : Fin 5 ↪ Fin nr) (PR : Fin 4 ↪ Fin nr) (O : Fin (ns + 1)) (OP : Fin nr)

/-- `GL := [0 < S]`. -/
def setFlag : WMX ns nr :=
  .seq (BinW.lt (PB 13) (PB 4) (PG 0) (PG 1)) (.ifr (PG 0) (.seq (WMX.dec (PG 0)) (WMX.inc (PG 4))) WMX.skip)

def bitBody : WMX ns nr :=
  .seq (WMX.dec (PG 4)) (.seq (BinW.copy (PB 7) (PB 4) (PG 0) (PG 1)) (.seq (andX (PB 7) (PB 11) (PG 0) (PG 1))
    (.seq (BinW.lt (PB 13) (PB 7) (PG 0) (PG 1)) (.seq (.ifr (PG 0) (.seq (WMX.dec (PG 0)) (natW (PB 6) O OP PR))
      WMX.skip) (.seq (BinW.half (PB 4) (PG 1)) (.seq (BinW.inc (PB 6) (PB 11) (PG 0) (PG 1)) (setFlag PB PG)))))))

def signPart : WMX ns nr :=
  .seq (BinW.lt (PB 5) (PB 12) (PG 0) (PG 1))
    (.ifr (PG 0) (.seq (WMX.dec (PG 0)) (.seq (natW (PB 13) O OP PR) (natW (PB 5) O OP PR)))
      (.seq (BinW.copy (PB 8) (PB 10) (PG 0) (PG 1)) (.seq (BinW.sub (PB 8) (PB 5) (PG 0) (PG 1))
        (.seq (natW (PB 11) O OP PR) (natW (PB 8) O OP PR)))))

/-- **One monomial.** -/
def prRec : WMX ns nr :=
  .seq (BinW.divmod (PB 0) (PB 9) (PB 1) (PB 2) (PB 3) (PG 0) (PG 1) (PG 2) (PG 3)) (.seq (natW (PB 1) O OP PR)
    (.seq (BinW.divmod (PB 2) (PB 10) (PB 4) (PB 5) (PB 3) (PG 0) (PG 1) (PG 2) (PG 3))
      (.seq (BinW.zero (PB 6) (PB 0) (PG 0) (PG 1)) (.seq (setFlag PB PG)
        (.seq (.whr (PG 4) (bitBody PB PG PR O OP)) (signPart PB PG PR O OP))))))

end Prog

/-! ## The record state -/

section State
variable {PB : Fin 14 ↪ Fin (ns + 1)} {PG : Fin 5 ↪ Fin nr} {PR : Fin 4 ↪ Fin nr} {O : Fin (ns + 1)} {OP : Fin nr}
  {cap Wb : ℕ}

/-- The streams a record may change. -/
def bl (PB : Fin 14 ↪ Fin (ns + 1)) (O : Fin (ns + 1)) : List (Fin (ns + 1)) :=
  [O, PB 0, PB 1, PB 2, PB 3, PB 4, PB 5, PB 6, PB 7, PB 8]

/-- The record state: block values `w`, `u` appended to `O`, flag `F = f`, loop flag `GL = g`, other scratch `0`. -/
def RS (PB : Fin 14 ↪ Fin (ns + 1)) (PG : Fin 5 ↪ Fin nr) (O : Fin (ns + 1)) (OP : Fin nr)
    (Wb : ℕ) (σ0 τ : WState ns nr) (w : Fin 14 → ℕ) (u : List Bool) (f g : ℕ) : Prop :=
  MV PB Wb w τ ∧ τ.st O = σ0.st O ++ u ∧ τ.sh O = σ0.sh O + u.length ∧ τ.val OP = σ0.val OP + u.length ∧
    τ.val (PG 0) = f ∧ τ.val (PG 4) = g ∧ SameExcept σ0 τ (bl PB O) [OP, PG 0, PG 4]

theorem pgN {i j : Fin 5} (h : i ≠ j) : PG i ≠ PG j := fun e => h (PG.injective e)

/-- The scratch registers that the state keeps at their start values. -/
structure Regs0 (PG : Fin 5 ↪ Fin nr) (PR : Fin 4 ↪ Fin nr) (σ0 : WState ns nr) : Prop where
  r : σ0.val (PG 1) = 0
  k : σ0.val (PG 2) = 0
  t : σ0.val (PG 3) = 0
  pr : ∀ i, σ0.val (PR i) = 0

/-- Distinctness of the layout. -/
structure PLay (PB : Fin 14 ↪ Fin (ns + 1)) (PG : Fin 5 ↪ Fin nr) (PR : Fin 4 ↪ Fin nr) (O : Fin (ns + 1))
    (OP : Fin nr) : Prop where
  bo : ∀ i, PB i ≠ O
  gp : ∀ i j, PG i ≠ PR j
  go : ∀ i, PG i ≠ OP
  po : ∀ i, PR i ≠ OP

theorem RS.reg {σ0 τ : WState ns nr} {w : Fin 14 → ℕ} {u : List Bool} {f g : ℕ}
    (h : RS PB PG O OP Wb σ0 τ w u f g) (r : Fin nr) (h1 : r ≠ OP) (h2 : r ≠ PG 0)
    (h3 : r ≠ PG 4) : τ.val r = σ0.val r :=
  h.2.2.2.2.2.2.val (by simp [h1, h2, h3])

theorem RS.r0 {σ0 τ : WState ns nr} {w : Fin 14 → ℕ} {u : List Bool} {f g : ℕ}
    (h : RS PB PG O OP Wb σ0 τ w u f g) (hl : PLay PB PG PR O OP) (z : Regs0 PG PR σ0) :
    τ.val (PG 1) = 0 ∧ τ.val (PG 2) = 0 ∧ τ.val (PG 3) = 0 ∧ ∀ i, τ.val (PR i) = 0 := by
  refine ⟨?_, ?_, ?_, fun i => ?_⟩
  · rw [h.reg _ (hl.go 1) (pgN (by decide)) (pgN (by decide)), z.r]
  · rw [h.reg _ (hl.go 2) (pgN (by decide)) (pgN (by decide)), z.k]
  · rw [h.reg _ (hl.go 3) (pgN (by decide)) (pgN (by decide)), z.t]
  · rw [h.reg _ (hl.po i) (hl.gp 0 i).symm (hl.gp 4 i).symm, z.pr i]

/-- After a block op on stream `a` (registers kept). -/
theorem RS.op {σ0 τ τ' : WState ns nr} {w w' : Fin 14 → ℕ} {u : List Bool} {f g : ℕ}
    (h : RS PB PG O OP Wb σ0 τ w u f g) (hl : PLay PB PG PR O OP) (a : Fin 14) (ha : PB a ∈ bl PB O)
    (hw : MV PB Wb w' τ') (fr : SameExcept τ τ' [PB a] []) : RS PB PG O OP Wb σ0 τ' w' u f g := by
  obtain ⟨_, hO, hOh, hOP, hf, hg, s⟩ := h
  refine ⟨hw, by rw [fr.st (by simp [hl.bo a |>.symm]), hO], by rw [fr.sh (by simp [hl.bo a |>.symm]), hOh],
    by rw [fr.val (by simp), hOP], by rw [fr.val (by simp), hf], by rw [fr.val (by simp), hg], ?_⟩
  exact s.trans (se_sub fr (by simpa using ha) (by simp))

/-- After a register change. -/
theorem RS.regs {σ0 τ τ' : WState ns nr} {w : Fin 14 → ℕ} {u : List Bool} {f g f' g' : ℕ}
    (h : RS PB PG O OP Wb σ0 τ w u f g) (hl : PLay PB PG PR O OP) (fr : SameExcept τ τ' [] [PG 0, PG 4])
    (hf : τ'.val (PG 0) = f') (hg : τ'.val (PG 4) = g') : RS PB PG O OP Wb σ0 τ' w u f' g' := by
  obtain ⟨hw, hO, hOh, hOP, _, _, s⟩ := h
  refine ⟨hw.frame' fr (by simp), by rw [fr.st (by simp), hO], by rw [fr.sh (by simp), hOh], ?_, hf, hg,
    s.trans (se_sub fr (by simp) (by simp [List.cons_subset]))⟩
  rw [fr.val (by simp [(hl.go 0).symm, (hl.go 4).symm]), hOP]

end State

end NearCubicGates.Close.Expand
