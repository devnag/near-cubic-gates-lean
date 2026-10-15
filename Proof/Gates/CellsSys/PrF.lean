import Proof.Gates.CellsSys.PrE
import Proof.Gates.CellsSys.Asm

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace NearCubicGates.Close.Cells.SystemsPhase

open NearCubicGates.Close.Cells
open NearCubicWires NearCubicGates NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Counter
open NearCubicGates.Close.CounterMachine (cellN callN paramsN witN)

theorem cellN_len {B1 B2 cT : ℕ} (c : Call) (p : Params) (wt : Wit c.n) (w : List Bool)
    (hadm : c.Admitted B1 B2) (hs : Spec cT (header c) p) (hw : decodeWitness c p w = some wt) :
    (cellN c p wt).length ≤ 100 * (c.n + 1) ^ 5 := by
  have h1 := call_len c hadm
  have h2 := params_len c p hadm hs
  have h3 := wit_len c p hadm hs wt w hw
  have hJ : p.J ≤ c.n + 1 := (J_le_Jmax c p hs).trans (Jmax_le c p hadm hs)
  have hW : c.W ≤ 2 * c.n ^ 4 := hadm.2.2.2.2.2.2.1
  have hlen : (cellN c p wt).length = (callN c).length + (paramsN p).length + (witN c p wt).length := by
    simp [CounterMachine.cellN, Nat.add_assoc]
  set N := c.n + 1 with hN
  have hN1 : 1 ≤ N := by omega
  have hn4 : c.n ^ 4 ≤ N ^ 4 := Nat.pow_le_pow_left (by omega) 4
  have hp45 : N ^ 4 ≤ N ^ 5 := Nat.pow_le_pow_right hN1 (by norm_num)
  have hp15 : N ≤ N ^ 5 := by
    calc N = N ^ 1 := (pow_one N).symm
      _ ≤ N ^ 5 := Nat.pow_le_pow_right hN1 (by norm_num)
  have hp5 : 1 ≤ N ^ 5 := Nat.one_le_pow _ _ (by omega)
  have e1 : 4 * N ^ 4 * (2 * N + 7) ≤ 36 * N ^ 5 := by
    have : N ^ 4 * N = N ^ 5 := by ring
    nlinarith
  have e2 : p.J * 2 * (1 + 2 * c.W) ≤ 2 * N + 8 * N ^ 5 := by
    have a1 : 1 + 2 * c.W ≤ 1 + 4 * N ^ 4 := by omega
    have a2 : p.J * 2 * (1 + 2 * c.W) ≤ N * 2 * (1 + 4 * N ^ 4) :=
      Nat.mul_le_mul (Nat.mul_le_mul_right _ hJ) a1
    have a3 : N * 2 * (1 + 4 * N ^ 4) = 2 * N + 8 * (N ^ 4 * N) := by ring
    have a4 : N ^ 4 * N = N ^ 5 := by ring
    omega
  omega

/-- The primes in `sN`: from `SysPre.IPr`. -/
theorem drop_getD {l A B : List ℕ} {k : ℕ} (h : l.drop k = A ++ B) (i : ℕ) (hi : i < A.length) :
    l.getD (k + i) 0 = A.getD i 0 ∧ k + i < l.length := by
  have hl := congrArg List.length h
  simp only [List.length_drop, List.length_append] at hl
  have hk : k + i < l.length := by omega
  refine ⟨?_, hk⟩
  have := congrArg (fun m => m.getD i 0) h
  simp only [List.getD_eq_getElem?_getD, List.getElem?_drop, List.getElem?_append_left hi] at this
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  exact this

theorem nbl_lt {v k : ℕ} (h : v < 2 ^ k) (hk : 1 ≤ k) : natBitLength v ≤ k := nbl_le_of_lt h hk

theorem trueBit_le (n : ℕ) : n < 2 ^ n := Nat.lt_two_pow_self

theorem jointCount_le (c : Call) (p : Params) (wt : Wit c.n) (y : Cells wt.I) (q : ℕ) (part : Option Bool)
    (κ : Role c × Fin p.J → ℤ) (σ : Role c → ℤ) : jointCount c p wt q part y κ σ ≤ 2 ^ c.n := by
  unfold jointCount
  have h1 := Finset.card_filter_le (Finset.univ : Finset (Points wt.I)) (fun x => inPart c wt part x = true ∧
    (∀ rj : Role c × Fin p.J, digit c p wt rj.1.val rj.2.val (extend wt.I y x) ≡ κ rj [ZMOD (q : ℤ)]) ∧
    ∀ r : Role c, scoreForm c r.val (extend wt.I y x) ≡ σ r [ZMOD (q : ℤ)])
  have h2 : (Finset.univ : Finset (Points wt.I)).card = 2 ^ wt.I.card := by
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_coe]
  have h3 : wt.I.card ≤ c.n := (Finset.card_le_univ _).trans (by simp)
  have h4 : 2 ^ wt.I.card ≤ 2 ^ c.n := Nat.pow_le_pow_right (by norm_num) h3
  omega

theorem qq_sum {cT : ℕ} (c : Call) (p : Params) (hs : Spec cT (header c) p) :
    ((p.primes.sort (· ≤ ·)).map fun q => q * qBn q (roleCount c.kind)).sum ≤ c.n ^ 3 := by
  have h := rows_n3 c p hs
  have e : ((p.primes.sort (· ≤ ·)).map fun q => q * qBn q (roleCount c.kind)) =
      ((p.primes.sort (· ≤ ·)).map fun q => q ^ roleCount c.kind) := by
    apply List.map_congr_left; intro q _
    unfold qBn
    rcases rc12 c with h1 | h1 <;> rw [h1] <;> simp [pow_two]
  rw [e]; exact h

/-- The printer's bit bound. -/
abbrev BwP (c : Call) : ℕ := 8 * c.n + 8

theorem n4p (n : ℕ) : 4 * n ^ 4 + 1 ≤ 2 ^ (4 * n + 3) := by
  have h : n ^ 4 ≤ 2 ^ (4 * n) := by
    calc n ^ 4 ≤ (2 ^ n) ^ 4 := Nat.pow_le_pow_left Nat.lt_two_pow_self.le 4
      _ = 2 ^ (4 * n) := by rw [← pow_mul, mul_comm]
  have : 2 ^ (4 * n + 3) = 8 * 2 ^ (4 * n) := by rw [pow_add]; ring
  have : 1 ≤ 2 ^ (4 * n) := Nat.one_le_two_pow
  omega

theorem n3p (n : ℕ) : n ^ 3 < 2 ^ (3 * n + 1) := by
  have h : n ^ 3 ≤ 2 ^ (3 * n) := by
    calc n ^ 3 ≤ (2 ^ n) ^ 3 := Nat.pow_le_pow_left Nat.lt_two_pow_self.le 3
      _ = 2 ^ (3 * n) := by rw [← pow_mul, mul_comm]
  have : 2 ^ (3 * n + 1) = 2 * 2 ^ (3 * n) := by rw [pow_add]; ring
  have : 1 ≤ 2 ^ (3 * n) := Nat.one_le_two_pow
  omega

end NearCubicGates.Close.Cells.SystemsPhase
