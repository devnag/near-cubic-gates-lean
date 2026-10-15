import Proof.Gates.CounterMachine.FormulaRole

/-! # RG machine, part 14: the formula printer's state

The data a request's formula is printed from (`FData`: per role the gate count, the stage coefficient lists and the
top coefficients; the rates `a_j`; the residues; `J`, `q`, `e`, `k`, `M₁`, `A`) and its layout (`FState`): the
streams `Y` (`Y 0` the token stream `S`, `Y 1`/`Y 3` the stage lists of roles 0/1, `Y 2`/`Y 4` their top
coefficients, `Y 5` the rates followed by `M₁, A`, `Y 6` the residues; `Y 7` unused), the registers `X` (values and
bounds; `X 2, X 3, X 4` zero at rest; `X 9, X 10, X 12, X 13, X 23` free for the callers) beside the printer file `F`. Every printer of the
following parts ends in `emitT σ ts` from a state in `FState`, and `FState` survives `emitT` (**`FState.emitT`**). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.CounterMachine

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Codec
open NearCubicGates.Close.Interfaces.Formats (Tok tokWord toks)

variable {ns nr : ℕ}

/-- The values a formula is printed from. -/
structure FData where
  pair : Bool
  J : ℕ
  q : ℕ
  e : ℕ
  k : ℕ
  G0 : ℕ
  G1 : ℕ
  B0 : List (List ℤ)
  B1 : List (List ℤ)
  C0 : List ℤ
  C1 : List ℤ
  L : List ℕ
  ρs : List ℕ
  M1 : ℕ
  A : ℕ

/-- Number of roles. -/
def FData.rc (d : FData) : ℕ := if d.pair then 2 else 1

/-- Its layout. -/
structure FState (Y : Fin 8 ↪ Fin (ns + 1)) (X : Fin 24 ↪ Fin nr) (F : Fin 24 ↪ Fin nr) (σ : WState ns nr)
    (d : FData) : Prop where
  rest : TRest (Y 0) F σ
  disj : ∀ i j, F i ≠ X j
  stB0 : ∃ r, σ.st (Y 1) = encI d.B0.flatten ++ r
  stC0 : ∃ r, σ.st (Y 2) = encI d.C0 ++ r
  stB1 : ∃ r, σ.st (Y 3) = encI d.B1.flatten ++ r
  stC1 : ∃ r, σ.st (Y 4) = encI d.C1 ++ r
  stL : ∃ r, σ.st (Y 5) = encN d.L ++ r
  stK : ∃ r, σ.st (Y 6) = encN d.ρs ++ r
  sh : ∀ i : Fin 8, i ≠ 0 → σ.sh (Y i) = 0
  vPr : σ.val (X 0) = if d.pair then 1 else 0
  vJ : σ.val (X 1) = d.J
  vQ : σ.val (X 5) = d.q - 1
  vLF : (encN d.L).length ≤ σ.val (X 6)
  vLK : (encN d.ρs).length ≤ σ.val (X 7)
  vE : σ.val (X 8) = d.e
  vR : σ.val (X 11) = d.rc * (d.J + 1)
  vG0 : σ.val (X 14) = d.G0
  vo0 : σ.val (X 15) = 0
  vL0 : (encI d.B0.flatten).length ≤ σ.val (X 16)
  vS0 : (encI d.C0).length ≤ σ.val (X 17)
  vG1 : σ.val (X 18) = d.G1
  vo1 : σ.val (X 19) = d.G0
  vL1 : (encI d.B1.flatten).length ≤ σ.val (X 20)
  vS1 : (encI d.C1).length ≤ σ.val (X 21)
  vK : σ.val (X 22) = 2 * d.k
  zero : ∀ i : Fin 24, i ∈ ([2, 3, 4] : List (Fin 24)) → σ.val (X i) = 0

/-- The shapes and the size bound `Λ` of the data. -/
structure FBound (d : FData) (Λ : ℕ) : Prop where
  b0 : ∀ b ∈ d.B0, b.length = d.G0
  b1 : ∀ b ∈ d.B1, b.length = d.G1
  c0 : d.C0.length = d.G0
  c1 : d.C1.length = d.G1
  lB0 : d.B0.length = d.J
  lB1 : d.B1.length = d.J
  lL : d.J ≤ d.L.length + 1
  J : d.J ≤ Λ
  q : d.q - 1 ≤ Λ
  e : d.e ≤ Λ
  k : 2 * d.k ≤ Λ
  G : d.G0 + d.G1 ≤ Λ
  zB : ∀ b ∈ d.B0 ++ d.B1, ∀ z ∈ b, natBitLength z.natAbs ≤ Λ
  zC : ∀ z ∈ d.C0 ++ d.C1, natBitLength z.natAbs ≤ Λ
  zL : ∀ x ∈ d.L, natBitLength x ≤ Λ
  zρ : ∀ x ∈ d.ρs, natBitLength x ≤ Λ
  zM : natBitLength d.M1 ≤ Λ ∧ natBitLength d.A ≤ Λ

/-- The bounds held in registers are within `Λ`. -/
def FBoundR (X : Fin 24 ↪ Fin nr) (σ : WState ns nr) (Λ : ℕ) : Prop :=
  ∀ i : Fin 24, i ∈ ([6, 7, 16, 17, 20, 21] : List (Fin 24)) → σ.val (X i) ≤ Λ

section
variable (Y : Fin 8 ↪ Fin (ns + 1)) (X : Fin 24 ↪ Fin nr) (F : Fin 24 ↪ Fin nr)

theorem FState.emitT {σ : WState ns nr} {d : FData} (h : FState Y X F σ d) (ts : List Tok) :
    FState Y X F (CounterMachine.emitT (Y 0) F σ ts) d := by
  have hY : ∀ i : Fin 8, i ≠ 0 → Y i ≠ Y 0 := fun i hi => Y.injective.ne hi
  have hX : ∀ j, (CounterMachine.emitT (Y 0) F σ ts).val (X j) = σ.val (X j) := fun j =>
    emitT_val_ne (Y 0) F (X j) (h.disj 7 j).symm (h.disj 16 j).symm σ ts
  have hs : ∀ i : Fin 8, i ≠ 0 → (CounterMachine.emitT (Y 0) F σ ts).st (Y i) = σ.st (Y i) := fun i hi =>
    emitT_st_ne (Y 0) F (Y i) (hY i hi) σ ts
  exact {
    rest := h.rest.emitT (Y 0) F ts
    disj := h.disj
    stB0 := by rw [hs 1 (by decide)]; exact h.stB0
    stC0 := by rw [hs 2 (by decide)]; exact h.stC0
    stB1 := by rw [hs 3 (by decide)]; exact h.stB1
    stC1 := by rw [hs 4 (by decide)]; exact h.stC1
    stL := by rw [hs 5 (by decide)]; exact h.stL
    stK := by rw [hs 6 (by decide)]; exact h.stK
    sh := fun i hi => by rw [emitT_sh_ne (Y 0) F (Y i) (hY i hi)]; exact h.sh i hi
    vPr := by rw [hX]; exact h.vPr
    vJ := by rw [hX]; exact h.vJ
    vQ := by rw [hX]; exact h.vQ
    vLF := by rw [hX]; exact h.vLF
    vLK := by rw [hX]; exact h.vLK
    vE := by rw [hX]; exact h.vE
    vR := by rw [hX]; exact h.vR
    vG0 := by rw [hX]; exact h.vG0
    vo0 := by rw [hX]; exact h.vo0
    vL0 := by rw [hX]; exact h.vL0
    vS0 := by rw [hX]; exact h.vS0
    vG1 := by rw [hX]; exact h.vG1
    vo1 := by rw [hX]; exact h.vo1
    vL1 := by rw [hX]; exact h.vL1
    vS1 := by rw [hX]; exact h.vS1
    vK := by rw [hX]; exact h.vK
    zero := fun i hi => by rw [hX]; exact h.zero i hi }

theorem FBoundR.emitT {σ : WState ns nr} {Λ : ℕ} (hF : ∀ i j, F i ≠ X j) (h : FBoundR X σ Λ) (S : Fin (ns + 1))
    (ts : List Tok) : FBoundR X (CounterMachine.emitT S F σ ts) Λ := fun i hi => by
  rw [emitT_val_ne S F (X i) (hF 7 i).symm (hF 16 i).symm]; exact h i hi

theorem FState.setv_free {σ : WState ns nr} {d : FData} (h : FState Y X F σ d) (j : Fin 24)
    (hj : j ∈ ([9, 10, 12, 13, 23] : List (Fin 24))) (v : ℕ) : FState Y X F (σ.setv (X j) v) d := by
  have hX : ∀ i : Fin 24, i ∉ ([9, 10, 12, 13, 23] : List (Fin 24)) → (σ.setv (X j) v).val (X i) = σ.val (X i) :=
    fun i hi => by
      have : i ≠ j := fun e => hi (e ▸ hj)
      simp [Function.update_of_ne (X.injective.ne this)]
  exact {
    rest := h.rest.setv (Y 0) F (X j) (fun i => h.disj i j) v
    disj := h.disj
    stB0 := h.stB0
    stC0 := h.stC0
    stB1 := h.stB1
    stC1 := h.stC1
    stL := h.stL
    stK := h.stK
    sh := h.sh
    vPr := by rw [hX 0 (by decide)]; exact h.vPr
    vJ := by rw [hX 1 (by decide)]; exact h.vJ
    vQ := by rw [hX 5 (by decide)]; exact h.vQ
    vLF := by rw [hX 6 (by decide)]; exact h.vLF
    vLK := by rw [hX 7 (by decide)]; exact h.vLK
    vE := by rw [hX 8 (by decide)]; exact h.vE
    vR := by rw [hX 11 (by decide)]; exact h.vR
    vG0 := by rw [hX 14 (by decide)]; exact h.vG0
    vo0 := by rw [hX 15 (by decide)]; exact h.vo0
    vL0 := by rw [hX 16 (by decide)]; exact h.vL0
    vS0 := by rw [hX 17 (by decide)]; exact h.vS0
    vG1 := by rw [hX 18 (by decide)]; exact h.vG1
    vo1 := by rw [hX 19 (by decide)]; exact h.vo1
    vL1 := by rw [hX 20 (by decide)]; exact h.vL1
    vS1 := by rw [hX 21 (by decide)]; exact h.vS1
    vK := by rw [hX 22 (by decide)]; exact h.vK
    zero := fun i hi => by
      rw [hX i (by revert i; decide)]; exact h.zero i hi }

theorem FBoundR.setv_free {σ : WState ns nr} {Λ : ℕ} (h : FBoundR X σ Λ) (j : Fin 24)
    (hj : j ∈ ([9, 10, 12, 13, 23] : List (Fin 24))) (v : ℕ) : FBoundR X (σ.setv (X j) v) Λ := fun i hi => by
  have : i ≠ j := by revert i; revert j; decide
  simp [Function.update_of_ne (X.injective.ne this)]; exact h i hi

end

end NearCubicGates.Close.CounterMachine
