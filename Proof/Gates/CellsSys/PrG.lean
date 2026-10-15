import Proof.Gates.CellsSys.PrF

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace NearCubicGates.Close.Cells.SystemsPhase

open NearCubicGates.Close.Cells
open NearCubicWires NearCubicGates NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Counter

variable {C : Ctx}

section
variable (c : Call) (p : Params) (wt : Wit c.n) (y : Cells wt.I) (κ : Role c × Fin p.J → ℤ)

theorem coord_abs (r : ℕ) (hr : r < roleCount c.kind) (a : ℕ) (ha : a < lenR c p wt y κ r) :
    (loR c p wt y κ r + a).natAbs ≤ c.W := by
  unfold lenR at ha; unfold loR
  rw [dif_pos hr] at ha ⊢
  have h1 := boxLo_ge c p wt y κ ⟨r, hr⟩
  have h2 := boxHi_le c p wt y κ ⟨r, hr⟩
  have h3 : ((circ c r).topWeight : ℤ) ≤ c.W := by exact_mod_cast topWeight_le_W c r
  simp only at h1 h2
  omega

theorem lenR_le (r : ℕ) : lenR c p wt y κ r ≤ 2 * c.W + 1 := by
  unfold lenR
  split_ifs with hr
  · have h1 := boxLo_ge c p wt y κ ⟨r, hr⟩
    have h2 := boxHi_le c p wt y κ ⟨r, hr⟩
    have h3 : ((circ c r).topWeight : ℤ) ≤ c.W := by exact_mod_cast topWeight_le_W c r
    simp only at h1 h2
    omega
  · omega

theorem loR_pos (r : ℕ) (hn : 0 < lenR c p wt y κ r) : (loR c p wt y κ r).toNat ≤ c.W := by
  unfold lenR at hn; unfold loR
  split_ifs at hn ⊢ with hr
  · have h2 := boxHi_le c p wt y κ ⟨r, hr⟩
    have h3 : ((circ c r).topWeight : ℤ) ≤ c.W := by exact_mod_cast topWeight_le_W c r
    simp only at h2
    omega
  · simp

end

theorem wd_n {S : SolveMachine} {c : Call} {p : Params} {wt : Wit c.n} {y : Cells wt.I} {Big : ℕ}
    (G : Glob S C c p wt y Big) (k : ℕ) (hk : k ≤ 8 * c.n + 64) : 2 ^ k ≤ 2 ^ C.Wd := by
  apply Nat.pow_le_pow_right (by norm_num)
  have := G.wd
  nlinarith

theorem boxN_of {S : SolveMachine} {c : Call} {p : Params} {wt : Wit c.n} {y : Cells wt.I} {Big : ℕ}
    {a0 a : DS VV MM} {κ : Role c × Fin p.J → ℤ} (G : Glob S C c p wt y Big) (h0 : SysPre S C c p wt y a0)
    (hK : Keep a0 a) (hB : BoxV c p wt y κ a) :
    BoxN a (roleCount c.kind) (loR c p wt y κ 0).toNat (-loR c p wt y κ 0).toNat (loR c p wt y κ 1).toNat
      (-loR c p wt y κ 1).toNat (lenR c p wt y κ 0) (lenR c p wt y κ 1) (BwP c) C := by
  have hW := W_le c p wt y G
  have h4 := n4p c.n
  have hp := wd_n G (4 * c.n + 4) (by omega)
  have hp2 : 2 ^ (4 * c.n + 4) = 2 * 2 ^ (4 * c.n + 3) := by rw [pow_succ]; ring
  have hbw : BwP c + 2 < 2 ^ C.Wd := by
    have := wd_n G (8 * c.n + 11) (by omega)
    have := Nat.lt_two_pow_self (n := 8 * c.n + 11)
    unfold BwP; omega
  have hrc := rc12 c
  have hcoord : ∀ r < roleCount c.kind, ∀ a' < lenR c p wt y κ r,
      natBitLength (zOf ((loR c p wt y κ r).toNat + a') (-loR c p wt y κ r).toNat).natAbs ≤ BwP c := by
    intro r hr a' ha'
    have h1 := coord_abs c p wt y κ r hr a' ha'
    have e : zOf ((loR c p wt y κ r).toNat + a') (-loR c p wt y κ r).toNat = loR c p wt y κ r + a' := by
      unfold zOf; omega
    rw [e]
    refine (nbl_lt (k := 4 * c.n + 3) (by omega) (by omega)).trans (by unfold BwP; omega)
  refine ⟨(hK.ev (x := vRC) (by decide) (by decide)).trans h0.rc, hB.l0p, hB.l0n, hB.l1p, hB.l1n, hB.n0e, hB.n1e,
    by omega, ?_, fun a' ha' => hcoord 0 (by omega) a' ha', fun h1 b hb => hcoord 1 h1 b hb, by unfold BwP; omega,
    hbw, ?_, ?_, ?_, fun hn => ?_, fun hn => ?_⟩
  · exact (nbl_le_self _).trans (by unfold BwP; omega)
  · have := G.wd; nlinarith
  · have := lenR_le c p wt y κ 0; omega
  · have := lenR_le c p wt y κ 1; omega
  · have := lenR_le c p wt y κ 0; have := loR_pos c p wt y κ 0 hn; omega
  · have := lenR_le c p wt y κ 1; have := loR_pos c p wt y κ 1 hn; omega

theorem n5p (n : ℕ) : (n + 1) ^ 5 ≤ 2 ^ (5 * n + 5) := by
  calc (n + 1) ^ 5 ≤ (2 ^ (n + 1)) ^ 5 := Nat.pow_le_pow_left Nat.lt_two_pow_self.le 5
    _ = 2 ^ (5 * n + 5) := by rw [← pow_mul]; congr 1; ring

theorem rowN_of {S : SolveMachine} {c : Call} {p : Params} {wt : Wit c.n} {y : Cells wt.I} {Big : ℕ}
    {a0 a : DS VV MM} (κ : Role c × Fin p.J → ℤ) (part : Option Bool) (G : Glob S C c p wt y Big)
    (h0 : SysPre S C c p wt y a0) (hK : Keep a0 a) :
    RowN a (roleCount c.kind) (a.env vIPr) (p.primes.sort (· ≤ ·)) (Jf c p wt y κ part) c.n (BwP c) C := by
  obtain ⟨cT, hs⟩ := G.spec
  obtain ⟨w, hw⟩ := G.dec
  obtain ⟨B1, B2, hadm⟩ := G.adm
  have hram : a.ram sN = CounterMachine.cellN c p wt := by rw [hK.ram]; exact h0.cellN
  have hIP : a.env vIPr = a0.env vIPr := hK.ev (x := vIPr) (by decide) (by decide)
  have hN : ∀ i < (p.primes.sort (· ≤ ·)).length, (a.ram sN).getD (a.env vIPr + i) 0 =
      (p.primes.sort (· ≤ ·)).getD i 0 ∧ a.env vIPr + i < (a.ram sN).length := by
    intro i hi; rw [hram, hIP]; exact drop_getD h0.IPr i hi
  have hmem : ∀ q ∈ p.primes.sort (· ≤ ·), q ∈ p.primes := fun q hq => (Finset.mem_sort _).mp hq
  have hqn : ∀ q ∈ p.primes.sort (· ≤ ·), q ≤ c.n := fun q hq =>
    (primes_le hs q (hmem q hq)).trans (P_le_n c p hs)
  have hbw : BwP c + 2 < 2 ^ C.Wd := by
    have := wd_n G (8 * c.n + 11) (by omega)
    have := Nat.lt_two_pow_self (n := 8 * c.n + 11)
    unfold BwP; omega
  have hPs : (p.primes.sort (· ≤ ·)).length ≤ c.n := by
    rw [Finset.length_sort]; exact (primes_card_le c p hs).trans (P_le_n c p hs)
  have hne : 0 < (p.primes.sort (· ≤ ·)).length := by
    rw [Finset.length_sort]; exact Finset.card_pos.mpr hs.primes_nonempty
  have hlenN : (a.ram sN).length ≤ 100 * (c.n + 1) ^ 5 := by rw [hram]; exact cellN_len c p wt w hadm hs hw
  have hIPr := (hN 0 hne).2
  have hsum := qq_sum c p hs
  have hn3 : c.n ^ 3 ≤ (c.n + 1) ^ 5 :=
    (Nat.pow_le_pow_left (by omega) 3).trans (Nat.pow_le_pow_right (by omega) (by norm_num))
  have hn2 : c.n * c.n ≤ (c.n + 1) ^ 5 := by
    have : c.n * c.n ≤ (c.n + 1) ^ 2 := by nlinarith
    exact this.trans (Nat.pow_le_pow_right (by omega) (by norm_num))
  have hn1 : c.n ≤ (c.n + 1) ^ 5 :=
    (show c.n ≤ (c.n + 1) ^ 1 by simp).trans (Nat.pow_le_pow_right (by omega) (by norm_num))
  have h5 := n5p c.n
  have hp14 := wd_n G (5 * c.n + 14) (by omega)
  have hp14' : 2 ^ (5 * c.n + 14) = 512 * 2 ^ (5 * c.n + 5) := by
    rw [show 5 * c.n + 14 = 5 * c.n + 5 + 9 by omega, pow_add]; ring
  refine ⟨(hK.ev (x := vRC) (by decide) (by decide)).trans h0.rc, rfl,
    (hK.ev (x := vNP) (by decide) (by decide)).trans h0.NP, hN, rc12 c |>.elim (fun h => by omega) (fun h => by omega),
    hqn, fun q hq => (primes_prime hs q (hmem q hq)).one_lt.le,
    fun q hq => (nbl_le_self q).trans (by have := hqn q hq; unfold BwP; omega),
    (nbl_le_self _).trans (by have := roleCount_le_two c; unfold BwP; omega),
    fun q _ s0 _ s1 _ => ?_, ?_, by unfold BwP; omega, hbw, ?_, ?_⟩
  · have := jointCount_le c p wt y q part κ (fun r => ((([s0, s1].take (roleCount c.kind)).getD r.val 0 : ℕ) : ℤ))
    refine (nbl_lt (k := c.n + 1) (lt_of_le_of_lt this (Nat.pow_lt_pow_right (by norm_num) (by omega))) (by omega)).trans
      (by unfold BwP; omega)
  · exact (nbl_lt (k := 3 * c.n + 1) (lt_of_le_of_lt hsum (n3p c.n)) (by omega)).trans (by unfold BwP; omega)
  · have := G.wd; nlinarith
  · omega

end NearCubicGates.Close.Cells.SystemsPhase
