import Proof.Gates.CellsSys.Asm

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000

namespace NearCubicGates.Close.Cells.SystemsPhase

open NearCubicGates.Close.Cells
open NearCubicWires NearCubicGates NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Counter

variable {C : Ctx}

def stepCostN (pr : PrFrag) (cf : CallFrag) (S : SolveMachine) (C : Ctx) (c : Call) (p : Params) (Big : ℕ) : ℕ :=
  boxesCost (c.n + 1) + (pr.cost S C c p Big + cf.cost S C c p Big + 1) + 1

def tCostN (pr : PrFrag) (cf : CallFrag) (S : SolveMachine) (C : Ctx) (c : Call) (p : Params) (Big : ℕ) : ℕ :=
  BN c p * (stepCostN pr cf S C c p Big + 4) + 4

/-- **The cost of the systems phase.** -/
def sysCostOf (pr : PrFrag) (cf : CallFrag) (S : SolveMachine) (C : Ctx) (c : Call) (p : Params) (Big : ℕ) : ℕ :=
  2 * (BN c p * c.n ^ 3) + 12 + (2 * (tCostN pr cf S C c p Big + 4) + 4) + 1

theorem boxesCost_mono {J J' : ℕ} (h : J ≤ J') : boxesCost J ≤ boxesCost J' := by
  unfold boxesCost boxCost accCost digCost
  gcongr

theorem room_ok {S : SolveMachine} {c : Call} {p : Params} {wt : Wit c.n} {y : Cells wt.I} {Big : ℕ}
    (G : Glob S C c p wt y Big) {v : ℕ} (hv : v ≤ 2 ^ c.n) :
    v + (2 * BN c p + 1) * (PT c * 2 ^ c.n) < 2 ^ C.Wd := by
  have hw := wWin_lt c p wt y G
  have hrc2 := roleCount_le_two c
  have hnD2 : nDig c p ≤ 2 * p.J := by unfold nDig; exact Nat.mul_le_mul_right _ hrc2
  have hw1 : 1 ≤ wWin p := by have := hE_ge c p wt y G; unfold wWin; omega
  set X := 2 ^ ((Big + 1) * (2 * p.J)) with hX
  have h1 : BN c p ≤ X := by
    calc wWin p ^ nDig c p ≤ (2 ^ (Big + 1)) ^ nDig c p := Nat.pow_le_pow_left hw.le _
      _ ≤ (2 ^ (Big + 1)) ^ (2 * p.J) := Nat.pow_le_pow_right (by positivity) hnD2
      _ = X := by rw [hX, ← pow_mul]
  have hX1 : 1 ≤ X := Nat.one_le_two_pow
  have h2 : 2 * BN c p + 1 ≤ 2 ^ ((Big + 1) * (2 * p.J) + 2) := by rw [pow_add]; omega
  have hW := W_le_pow c p wt y G
  have h3 : 2 * c.W + 1 ≤ 2 ^ (4 * c.n + 3) := by
    have : 2 ^ (4 * c.n + 3) = 4 * 2 ^ (4 * c.n + 1) := by rw [show 4 * c.n + 3 = 4 * c.n + 1 + 2 by omega, pow_add]; ring
    have : 1 ≤ 2 ^ (4 * c.n + 1) := Nat.one_le_two_pow
    omega
  have h4 : PT c ≤ 2 ^ (8 * c.n + 6) := by
    calc PT c = (2 * c.W + 1) ^ 2 := rfl
      _ ≤ (2 ^ (4 * c.n + 3)) ^ 2 := Nat.pow_le_pow_left h3 2
      _ = 2 ^ (8 * c.n + 6) := by rw [← pow_mul]; congr 1; ring
  set E := (Big + 1) * (2 * p.J) + 2 + (8 * c.n + 6) + c.n with hE
  have h5 : (2 * BN c p + 1) * (PT c * 2 ^ c.n) ≤ 2 ^ E := by
    calc (2 * BN c p + 1) * (PT c * 2 ^ c.n) ≤ 2 ^ ((Big + 1) * (2 * p.J) + 2) * (2 ^ (8 * c.n + 6) * 2 ^ c.n) :=
          Nat.mul_le_mul h2 (Nat.mul_le_mul_right _ h4)
      _ = 2 ^ E := by rw [hE, ← pow_add, ← pow_add]; ring_nf
  have h6 : 2 ^ c.n ≤ 2 ^ E := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h7 : 2 ^ (E + 2) ≤ 2 ^ C.Wd := by
    apply Nat.pow_le_pow_right (by norm_num)
    have := G.wd
    rw [hE]; nlinarith
  have h8 : 2 ^ (E + 2) = 4 * 2 ^ E := by rw [pow_add]; ring
  have h9 : 1 ≤ 2 ^ E := Nat.one_le_two_pow
  clear_value X E
  omega

theorem scr_range (x : Fin VV) (h3 : x ≠ vJ) (h4 : x ≠ t0) (h5 : x ≠ t1) (h6 : x ≠ t2) (h7 : x ≠ t3) (h8 : x ≠ t4)
    (h9 : x ≠ t5) (h10 : x ≠ t6) (h11 : x ≠ t7) (h12 : x ≠ t8) (h13 : x ≠ t9) (h14 : x ≠ c0) (h15 : x ≠ c1)
    (h16 : x ≠ c2) (h17 : x ≠ c3) (h18 : x ≠ c4) (h19 : x ≠ c5) : x.val < 3 ∨ 19 < x.val := by
  rcases x with ⟨v, hv⟩
  simp only
  rcases Nat.lt_or_ge v 3 with h | ha
  · exact Or.inl h
  rcases Nat.lt_or_ge 19 v with h | hb
  · exact Or.inr h
  interval_cases v <;> simp_all [Fin.ext_iff, vJ, t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, c0, c1, c2, c3, c4, c5]

theorem sysPOf_run (pr : PrFrag) (cf : CallFrag) (S : SolveMachine) (C : Ctx) {cT : ℕ} (c : Call) (p : Params)
    (wt : Wit c.n) (y : Cells wt.I) (a : DS VV MM) (Big : ℕ) (hs : Spec cT (header c) p)
    (hdec : ∃ w, decodeWitness c p w = some wt) (hadm : ∃ B1 B2 : ℕ, c.Admitted B1 B2) (ht : CellTests c p wt y)
    (h0 : SysPre S C c p wt y a) (hbits : ∀ x ∈ CounterMachine.cellN c p wt, natBitLength x ≤ Big)
    (hwd : 64 * (p.J + 4) * (Big + c.n + 16) ≤ C.Wd)
    (hcall : ∀ part κ, κ ∈ digitVectors c p wt y → (sysWord (sysOf c p wt y κ part)).length ≤ C.Lk ∧
      S.budget (sysOf c p wt y κ part) ≤ C.Bk)
    (hcnt : a.env vCnt ≤ 2 ^ c.n) :
    ∃ b n, Ex C (sysPOf pr cf) a b n ∧ n ≤ sysCostOf pr cf S C c p Big ∧
      ((b.env vCnt : ℚ) = a.env vCnt + cellCount c p wt y) ∧
      b.ram = a.ram ∧ b.ip = a.ip ∧ b.out = a.out ∧ b.kin = [] ∧
      (∀ x : Fin VV, (x.val < 50 ∨ 99 < x.val) → x ≠ t0 → x ≠ t1 → x ≠ t2 → x ≠ t3 → x ≠ t4 → x ≠ t5 → x ≠ t6 →
        x ≠ t7 → x ≠ t8 → x ≠ t9 → x ≠ c0 → x ≠ c1 → x ≠ c2 → x ≠ c3 → x ≠ c4 → x ≠ c5 → x ≠ vCnt → x ≠ vJ →
        b.env x = a.env x) := by
  have G : Glob S C c p wt y Big := ⟨⟨cT, hs⟩, hdec, hadm, ht, hbits, hwd, hcall⟩
  obtain ⟨a2, n1, hx1, hn1, hK2, hkin2, hw2, hnD2, hnP2, hA2, hfr2⟩ := setup_spec G h0
  have e2 : a2.env vCnt = a.env vCnt := hfr2 vCnt (by decide) (by decide) (by decide)
  have hroom : a2.env vCnt + (2 * BN c p + 1) * (PT c * 2 ^ c.n) < 2 ^ C.Wd := by rw [e2]; exact room_ok G hcnt
  obtain ⟨b, n2, hx2, hn2, hb1, hb2, hb3, hb4⟩ := pLoop_spec pr cf G h0 hK2 hw2 hnD2 hkin2 hnP2 hA2 hroom
  refine ⟨b, n1 + n2 + 1, Ex.seq hx1 hx2, ?_, ?_, hb3.ram, hb3.ip, hb3.out, hb2, ?_⟩
  · have hJ := J_le_n c p wt y G
    have hm : stepCost pr cf S C c p Big ≤ stepCostN pr cf S C c p Big := by
      unfold stepCost stepCostN; have := boxesCost_mono hJ; omega
    have ht' : tCost pr cf S C c p Big ≤ tCostN pr cf S C c p Big := by
      unfold tCost tCostN; have := Nat.mul_le_mul_left (BN c p) (show stepCost pr cf S C c p Big + 4 ≤
        stepCostN pr cf S C c p Big + 4 by omega); omega
    have hpl := parts_length_le c
    have : (parts c).length * (tCost pr cf S C c p Big + 4) ≤ 2 * (tCostN pr cf S C c p Big + 4) :=
      Nat.mul_le_mul hpl (by omega)
    unfold sysCostOf; omega
  · rw [hb1, e2, cellCount_eq c p wt y hs ht]; rfl
  · intro x hx h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 hc hJ
    have hr := scr_range x hJ h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19
    clear h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 hJ
    have hP : ¬ PVar x := by
      rintro ((hf | hm | he) | he | he)
      · unfold FragVar at hf; omega
      · have := boxesT_range x hm; omega
      · exact hc he
      · subst he; revert hx; decide
      · subst he; revert hx; decide
    rw [hb4 x hP]
    exact hfr2 x (fun e => by subst e; revert hx; decide) (fun e => by subst e; revert hx; decide)
      (fun e => by subst e; revert hx; decide)

end NearCubicGates.Close.Cells.SystemsPhase
