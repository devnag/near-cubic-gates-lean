import Proof.Wire_3_5.FinalPassSeamsHalves
import Proof.Wire_3_5.UnionMachineRegRatOps

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.Out
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (NumOn)

/-! ## The layout -/

/-- Streams `0 … 11`. -/
abbrev nsO : ℕ := 11
/-- Registers `0 … 9`. -/
abbrev nrO : ℕ := 10
/-- The out machine's word states. -/
abbrev St : Type := WState nsO nrO

/-- The output stream (tape `o`). -/
def sO : Fin (nsO + 1) := 0
/-- The numerator stream (tape `tN`). -/
def sN : Fin (nsO + 1) := 1
/-- The denominator stream (tape `tD`). -/
def sD : Fin (nsO + 1) := 2
/-- The gcd pair. -/
def sU : Fin (nsO + 1) := 3
def sV : Fin (nsO + 1) := 4
/-- The swap temporary. -/
def sT : Fin (nsO + 1) := 5
/-- The six words of P4 and P5. -/
def sX (j : Fin 6) : Fin (nsO + 1) := ⟨6 + j.val, by have := j.isLt; show 6 + j.val < 12; omega⟩

/-- A pass's flag and counter (`RegRat`'s `F`, `R`). -/
def rF : Fin nrO := 0
def rR : Fin nrO := 1
/-- The width `W`, kept from P1 to P6. -/
def rW : Fin nrO := 2
/-- A loop counter. -/
def rK : Fin nrO := 3
/-- Scratch registers. -/
def rg (j : Fin 6) : Fin nrO := ⟨4 + j.val, by have := j.isLt; show 4 + j.val < 10; omega⟩

/-- The register bound of every phase. -/
def capO (W : ℕ) : ℕ := 8 * W + 8

/-- **The room**: the compiled program's `nsO + 2 + nrO + 1 = 24` tapes but `O`, `N`, `D`. -/
def mOut : ℕ := 21

theorem mOut_eq : mOut + 3 = nsO + 2 + nrO + 1 := rfl

/-! ## The boundary predicates -/

/-- Heads at `0`, the cell `false`, every register `0` but `rW = W`. -/
structure Bd (σ : St) (W : ℕ) : Prop where
  heads : ∀ i, σ.sh i = 0
  cell : σ.cell = false
  hw : σ.val rW = W
  regs : ∀ r, r ≠ rW → σ.val r = 0

/-- **The machine's entry** (P1's): `Num`, `Den` framed on `N`, `D`, every other stream blank, every head and register
`0`. -/
structure Entry (σ : St) (W num den : ℕ) : Prop where
  bd : Bd σ 0
  hn : σ.st sN = frame (binary W num)
  hd : σ.st sD = frame (binary W den)
  blank : ∀ i, i ≠ sN → i ≠ sD → σ.st i = []

/-- **P1–P4's word state**: `a, b, u, v` on `N, D, U, V`, a word on `T`, the six room words `0`, `O` blank. -/
structure Words (σ : St) (W a b u v : ℕ) : Prop where
  bd : Bd σ W
  ho : σ.st sO = []
  hn : NumOn σ sN W a
  hd : NumOn σ sD W b
  hu : NumOn σ sU W u
  hv : NumOn σ sV W v
  ht : ∃ x, NumOn σ sT W x
  hx : ∀ j, NumOn σ (sX j) W 0

/-- **P4 → P5**: the reduced pair `n'`, `d'` on `X 0`, `X 1`, words on `X 2 … X 5`, `O` blank. -/
structure Quot (σ : St) (W n' d' : ℕ) : Prop where
  bd : Bd σ W
  ho : σ.st sO = []
  hq : NumOn σ (sX 0) W n'
  hr : NumOn σ (sX 1) W d'
  hx : ∀ j : Fin 6, 2 ≤ j.val → ∃ y, NumOn σ (sX j) W y

/-- **P5 → P6**: the printed rational on `O`, the cell `false`, every register `0` but `rW = W` (heads free). -/
structure Printed (σ : St) (W : ℕ) (q : ℚ) : Prop where
  cell : σ.cell = false
  hw : σ.val rW = W
  regs : ∀ r, r ≠ rW → σ.val r = 0
  ho : σ.st sO = ratWord q

/-! ## The values -/

/-- One step of stripping the common factors `2`. -/
def stripStep (p : ℕ × ℕ) : ℕ × ℕ := if p.1 % 2 = 0 ∧ p.2 % 2 = 0 then (p.1 / 2, p.2 / 2) else p

/-- `W` steps of stripping the common factors `2` (P1's values). -/
def strip (W num den : ℕ) : ℕ × ℕ := stripStep^[W] (num, den)

/-- One step towards the odd part. -/
def oddStep (u : ℕ) : ℕ := if u % 2 = 0 then u / 2 else u

/-- `W` steps towards the odd part (P2's value). -/
def oddPart (W u : ℕ) : ℕ := oddStep^[W] u

/-- **P5's print encoding**: the reduced rational `n/d` is printed as `false :: natWord n ++ natWord d`. -/
theorem ratWord_coprime (n d : ℕ) (hd : 0 < d) (h : Nat.Coprime n d) :
    ratWord ((n : ℚ) / d) = false :: (natWord n ++ natWord d) := by
  have hb : (0 : ℤ) < (d : ℤ) := by exact_mod_cast hd
  have hc : Nat.Coprime (n : ℤ).natAbs (d : ℤ).natAbs := by simpa using h
  have e1 := Rat.num_div_eq_of_coprime hb hc
  have e2 := Rat.den_div_eq_of_coprime hb hc
  simp only [Int.cast_natCast] at e1 e2
  have e3 : ((n : ℚ) / d).den = d := by exact_mod_cast e2
  have e4 : decide ((n : ℤ) < 0) = false := by simp
  simp only [ratWord, intWord, e1, e3, e4, Int.natAbs_natCast, List.cons_append]

/-! ## The phases -/

/-- **P1**: count `W` into `rW`, make the room words `0` (and `U`, `V`, `T`), strip the common factors `2`. -/
structure Ph1 where
  P : WM nsO nrO
  cost : ℕ → ℕ
  C : ℕ
  cost_le : ∀ W, cost W ≤ C * (W + 1) ^ 2
  run : ∀ (W num den : ℕ) (σ : St), Entry σ W num den → num < 2 ^ W → den < 2 ^ W →
    ∃ τ, WExec (capO W) P σ τ (cost W) ∧ Words τ W (strip W num den).1 (strip W num den).2 0 0

/-- **P2**: `U := oddPart W b`, `V := a`. -/
structure Ph2 where
  P : WM nsO nrO
  cost : ℕ → ℕ
  C : ℕ
  cost_le : ∀ W, cost W ≤ C * (W + 1) ^ 2
  run : ∀ (W a b u v : ℕ) (σ : St), Words σ W a b u v → a < 2 ^ W → b < 2 ^ W →
    ∃ τ, WExec (capO W) P σ τ (cost W) ∧ Words τ W a b (oddPart W b) a

/-- **P3**: the constant-time Stein gcd (`2W` rounds) of an odd `u` and `v`: `U := gcd u v`, `V := 0`. -/
structure Ph3 where
  P : WM nsO nrO
  cost : ℕ → ℕ
  C : ℕ
  cost_le : ∀ W, cost W ≤ C * (W + 1) ^ 2
  run : ∀ (W a b u v : ℕ) (σ : St), Words σ W a b u v → u % 2 = 1 → u < 2 ^ W → v < 2 ^ W →
    ∃ τ, WExec (capO W) P σ τ (cost W) ∧ Words τ W a b (Nat.gcd u v) 0

/-- **P4**: the exact divisions by the odd `g = gcd a b`: `X 0 := a / g`, `X 1 := b / g`. -/
structure Ph4 where
  P : WM nsO nrO
  cost : ℕ → ℕ
  C : ℕ
  cost_le : ∀ W, cost W ≤ C * (W + 1) ^ 2
  run : ∀ (W a b v : ℕ) (σ : St), Words σ W a b (Nat.gcd a b) v → Nat.gcd a b % 2 = 1 → a < 2 ^ W → b < 2 ^ W →
    0 < b → ∃ τ, WExec (capO W) P σ τ (cost W) ∧ Quot τ W (a / Nat.gcd a b) (b / Nat.gcd a b)

/-- **P5**: print the reduced rational `n'/d'` on `O`. -/
structure Ph5 where
  P : WM nsO nrO
  cost : ℕ → ℕ
  C : ℕ
  cost_le : ∀ W, cost W ≤ C * (W + 1) ^ 2
  run : ∀ (W n' d' : ℕ) (σ : St), Quot σ W n' d' → Nat.Coprime n' d' → 0 < d' → n' < 2 ^ W → d' < 2 ^ W →
    ∃ τ, WExec (capO W) P σ τ (cost W) ∧ Printed τ W ((n' : ℚ) / d')

/-- **P6**: clear `rW` (every register `0`, the masked reset's exit condition). -/
structure Ph6 where
  P : WM nsO nrO
  cost : ℕ → ℕ
  C : ℕ
  cost_le : ∀ W, cost W ≤ C * (W + 1) ^ 2
  run : ∀ (W : ℕ) (q : ℚ) (σ : St), Printed σ W q →
    ∃ τ, WExec (capO W) P σ τ (cost W) ∧ τ.cell = false ∧ (∀ r, τ.val r = 0) ∧ τ.st sO = ratWord q

/-- **P6, proved**: `WM.clear rW`, `3W + 1` steps. -/
def ph6 : Ph6 where
  P := WM.clear rW
  cost := fun W => 3 * W + 1
  C := 4
  cost_le := fun W => by nlinarith [Nat.zero_le W]
  run := fun W q σ h => by
    refine ⟨σ.setv rW 0, wclear_spec (capO W) rW W σ h.hw (by rw [h.hw]; unfold capO; omega), h.cell, fun r => ?_,
      h.ho⟩
    by_cases hr : r = rW
    · subst hr; simp
    · simp [Function.update_of_ne hr, h.regs r hr]

/-! ## The assembly's statement -/

abbrev OutOfPhases : Type := Ph1 → Ph2 → Ph3 → Ph4 → Ph5 → Ph6 → Bank.OutGen mOut

end NearCubicWires.WireExponent3_5.FinalPass.Out
