import Proof.Gates.TabMachine.Layout

/-! # The cut machine's state at rest

`GRest`: every scratch word exists at its width (`W + 1` for gate data, `Lc = (s+1)(W+1)` for fields), the
constants hold their values, the work streams are rewound, the closed output streams are rewound with counter `0`,
every scratch register is `0`, the loop constants hold `s`, `s + 1`, `k`. `grest_frame` re-establishes it after
a component machine from its frame and the facts it returns. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicGates.Close.TabMachine
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length binary_value)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (NumOn)
open NearCubicGates.Close.WordPrograms.SInt (encS sval SNumOn)

variable {ns nr : ℕ}

/-- Scratch words of width `W + 1`. -/
def w1List : List (Fin 64) := [1, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 22, 23, 48, 49, 50, 51, 52]
/-- Scratch words of width `Lc`. -/
def wcList : List (Fin 64) := [25, 27, 28, 29, 35, 36, 37, 38, 39, 40, 41, 42]
/-- Registers `0` at rest. -/
def zList : List (Fin 112) :=
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31,
    33, 34, 35, 36, 37, 38, 39, 40, 42, 43, 45, 46, 48, 49, 50, 51, 52, 53, 54, 55, 57, 58, 59, 60, 61, 62, 63, 64, 65,
    67, 68, 69, 70, 71, 72, 73, 75, 76, 78, 79, 80, 81, 82, 83, 85, 86, 87, 88, 90, 91, 92, 93, 95, 96, 97]

section Rest
variable (Z : Fin 64 ↪ Fin (ns + 1)) (Y : Fin 112 ↪ Fin nr)

/-- The cut machine at rest (`Lc = (s + 1)(W + 1)`). -/
structure GRest (cap W s k : ℕ) (σ : WState ns nr) : Prop where
  w1 : ∀ i ∈ w1List, ∃ v, NumOn σ (Z i) (W + 1) v
  wc : ∀ i ∈ wcList, ∃ v, NumOn σ (Z i) ((s + 1) * (W + 1)) v
  c20 : NumOn σ (Z 20) (W + 1) 0
  c21 : NumOn σ (Z 21) (W + 1) 2
  c53 : NumOn σ (Z 53) (W + 1) 2
  c26 : NumOn σ (Z 26) ((s + 1) * (W + 1)) (2 ^ (W + 1))
  c44 : NumOn σ (Z 44) ((s + 1) * (W + 1)) 0
  c45 : NumOn σ (Z 45) ((s + 1) * (W + 1)) 2
  c55 : NumOn σ (Z 55) (W + 1) 1
  work1 : ∀ i ∈ [(3 : Fin 64), 47], σ.sh (Z i) = 0 ∧ (σ.st (Z i)).length ≤ 2 * (W + 1) + 1
  workc : ∀ i ∈ [(24 : Fin 64), 33], σ.sh (Z i) = 0 ∧ (σ.st (Z i)).length ≤ 2 * ((s + 1) * (W + 1)) + 1
  closed : ∀ i ∈ [(0 : Fin 64), 2, 30, 31, 32], σ.sh (Z i) = 0
  zero : ∀ r ∈ zList, σ.val (Y r) = 0
  r13 : σ.val (Y 13) = s
  r32 : σ.val (Y 32) = s + 1
  r41 : σ.val (Y 41) = s + 1
  r66 : σ.val (Y 66) = s + 1
  r84 : σ.val (Y 84) = k
  r89 : σ.val (Y 89) = s
  cap : 2 * ((s + 1) * (W + 1)) + 1 ≤ cap

theorem GRest.compPre {cap W s k : ℕ} {σ : WState ns nr} (h : GRest Z Y cap W s k σ) :
    CompPre (zS Z) (yR Y) cap W σ where
  words j hj := by
    have : ixS j ∈ w1List := by
      revert j; decide
    exact h.w1 _ this
  wkh := (h.work1 3 (by simp)).1
  wkl := (h.work1 3 (by simp)).2
  zr := h.c20
  tw := h.c21
  regs j h13 h14 := by
    have : ixR j ∈ zList := by
      revert j; decide
    exact h.zero _ this
  cap := by have := h.cap; nlinarith

theorem GRest.s1 {cap W s k : ℕ} {σ : WState ns nr} (h : GRest Z Y cap W s k σ) :
    ∃ v, NumOn σ (zS Z 1) (W + 1) v := h.w1 1 (by decide)

theorem grest_frame {cap W s k : ℕ} {σ τ : WState ns nr} {Ls : List (Fin (ns + 1))} {Rs : List (Fin nr)}
    (h : GRest Z Y cap W s k σ) (hfr : SameExcept σ τ Ls Rs)
    (hw1 : ∀ i ∈ w1List, Z i ∈ Ls → ∃ v, NumOn τ (Z i) (W + 1) v)
    (hwc : ∀ i ∈ wcList, Z i ∈ Ls → ∃ v, NumOn τ (Z i) ((s + 1) * (W + 1)) v)
    (hconst : ∀ i ∈ [(20 : Fin 64), 21, 53, 26, 44, 45, 55], Z i ∉ Ls)
    (hwork1 : ∀ i ∈ [(3 : Fin 64), 47], Z i ∈ Ls → τ.sh (Z i) = 0 ∧ (τ.st (Z i)).length ≤ 2 * (W + 1) + 1)
    (hworkc : ∀ i ∈ [(24 : Fin 64), 33], Z i ∈ Ls →
      τ.sh (Z i) = 0 ∧ (τ.st (Z i)).length ≤ 2 * ((s + 1) * (W + 1)) + 1)
    (hclosed : ∀ i ∈ [(0 : Fin 64), 2, 30, 31, 32], Z i ∈ Ls → τ.sh (Z i) = 0)
    (hzero : ∀ r ∈ zList, Y r ∈ Rs → τ.val (Y r) = 0)
    (hconstR : ∀ r ∈ [(13 : Fin 112), 32, 41, 66, 84, 89], Y r ∉ Rs) : GRest Z Y cap W s k τ where
  w1 i hi := by
    by_cases hm : Z i ∈ Ls
    · exact hw1 i hi hm
    · obtain ⟨v, hv⟩ := h.w1 i hi; exact ⟨v, hfr.numOn hm hv⟩
  wc i hi := by
    by_cases hm : Z i ∈ Ls
    · exact hwc i hi hm
    · obtain ⟨v, hv⟩ := h.wc i hi; exact ⟨v, hfr.numOn hm hv⟩
  c20 := hfr.numOn (hconst 20 (by simp)) h.c20
  c21 := hfr.numOn (hconst 21 (by simp)) h.c21
  c53 := hfr.numOn (hconst 53 (by simp)) h.c53
  c26 := hfr.numOn (hconst 26 (by simp)) h.c26
  c44 := hfr.numOn (hconst 44 (by simp)) h.c44
  c45 := hfr.numOn (hconst 45 (by simp)) h.c45
  c55 := hfr.numOn (hconst 55 (by simp)) h.c55
  work1 i hi := by
    by_cases hm : Z i ∈ Ls
    · exact hwork1 i hi hm
    · rw [hfr.sh hm, hfr.st hm]; exact h.work1 i hi
  workc i hi := by
    by_cases hm : Z i ∈ Ls
    · exact hworkc i hi hm
    · rw [hfr.sh hm, hfr.st hm]; exact h.workc i hi
  closed i hi := by
    by_cases hm : Z i ∈ Ls
    · exact hclosed i hi hm
    · rw [hfr.sh hm]; exact h.closed i hi
  zero r hr := by
    by_cases hm : Y r ∈ Rs
    · exact hzero r hr hm
    · rw [hfr.val hm]; exact h.zero r hr
  r13 := by rw [hfr.val (hconstR 13 (by simp))]; exact h.r13
  r32 := by rw [hfr.val (hconstR 32 (by simp))]; exact h.r32
  r41 := by rw [hfr.val (hconstR 41 (by simp))]; exact h.r41
  r66 := by rw [hfr.val (hconstR 66 (by simp))]; exact h.r66
  r84 := by rw [hfr.val (hconstR 84 (by simp))]; exact h.r84
  r89 := by rw [hfr.val (hconstR 89 (by simp))]; exact h.r89
  cap := h.cap

theorem GRest.exWords {cap W s k : ℕ} {σ : WState ns nr} (h : GRest Z Y cap W s k σ) :
    ExWords (zE Z) ((s + 1) * (W + 1)) σ :=
  ⟨h.wc 27 (by decide), h.wc 28 (by decide), h.wc 29 (by decide)⟩

theorem GRest.rPre {cap W s k : ℕ} {σ : WState ns nr} (h : GRest Z Y cap W s k σ) (xs : List ℕ)
    (hpg : ∃ junk, σ.st (Z 46) = recStream (xs.map (binary (W + 1))) ++ junk) (hpgh : σ.sh (Z 46) = 0) :
    RPre (zA Z) (yB Y) W xs σ where
  pg := hpg
  pgh := hpgh
  wh := (h.work1 47 (by simp)).1
  wl := (h.work1 47 (by simp)).2
  words j hj := by
    have : ixA j ∈ w1List := by revert j; decide
    exact h.w1 _ this
  one := h.c53
  zero j hj := by
    have : ixB j ∈ zList := by revert j; decide
    exact h.zero _ this

theorem GRest.tPre {cap W s k : ℕ} {σ : WState ns nr} (h : GRest Z Y cap W s k σ) (M : ℕ) (kf tf : List (List ℤ))
    (hkf : ∃ junk, σ.st (Z 30) = recStream ((fieldNums kf).map (binary ((s + 1) * (W + 1)))) ++ junk)
    (htf : ∃ junk, σ.st (Z 31) = recStream ((fieldNums tf).map (binary ((s + 1) * (W + 1)))) ++ junk)
    (hM : σ.val (Y 44) = M) : TPre (zP Z) (yQ Y) ((s + 1) * (W + 1)) (s + 1) M kf tf σ where
  kf := hkf
  kfh := h.closed 30 (by simp)
  tf := htf
  tfh := h.closed 31 (by simp)
  wh := (h.workc 33 (by simp)).1
  wl := (h.workc 33 (by simp)).2
  r0 := h.zero 35 (by decide)
  r1 := h.zero 36 (by decide)
  r3 := h.zero 38 (by decide)
  r4 := h.zero 39 (by decide)
  r7 := h.zero 42 (by decide)
  r10 := h.zero 45 (by decide)
  r16 := h.zero 50 (by decide)
  ks := h.r41
  mc := hM

end Rest

end NearCubicGates.Close.TabMachine
