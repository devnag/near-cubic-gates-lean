import Proof.Gates.CounterMachine.TabCallFacts

/-! # RK, part 17: the numbers (`Λf`, `capf`) and the discharge of stage A's and stage B's side conditions

`Λf x = 4L + 40(n+1)⁴ + 4^e(2e+2) + 20` (`L = |tabCallInput x|`) dominates every bit length, count and binomial constant
RG reads; `capf` (a semantic register capacity only, it never enters a cost) is the sum of every capacity demand. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace NearCubicGates.Close.CounterMachine.TabCallProg

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.CounterMachine
open NearCubicGates.Close.Counter

variable {B1 B2 cT : ℕ}

/-- RK's bit-length bound. -/
def Λf (x : TabCallReq B1 B2 cT) : ℕ :=
  4 * (tabCallInput x).length + 40 * (x.r.c.n + 1) ^ 4 + 4 ^ x.r.p.e * (2 * x.r.p.e + 2) + 20

/-- RK's register capacity. -/
noncomputable def capf (x : TabCallReq B1 B2 cT) (Cl El : ℕ) : ℕ :=
  40 * (Λf x + 1) ^ 2 + 50 * (tabCallInput x).length + 10 * Λf x + 10 * x.r.c.n +
    4 * (lcap Cl El x.r.c.n x.r.p.k * (x.r.c.n + 1)) + 2 * (x.r.p.J + 1) + 2 * x.r.p.k +
    x.r.c.first.gates.length + dF1 x.id + dF2 x.id + kindTag x.r.c.kind + (prefixesWord x.r).length +
    20 * ((pfxOf x).length + ((formulaToks x).flatMap tokWord).length + (formulaToks x).length + 1) +
    2 * ((formulaToks x).flatMap tokWord).length + (formulaToks x).length + costA x (Λf x) Cl El + 1000

theorem n4_ge (n : ℕ) : n + 1 ≤ (n + 1) ^ 4 := by
  calc n + 1 = (n + 1) ^ 1 := (pow_one _).symm
    _ ≤ (n + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)

theorem pow4_ge (n : ℕ) : n ^ 4 ≤ (n + 1) ^ 4 := Nat.pow_le_pow_left (by omega) 4

theorem e_le_pow (e : ℕ) : e + 1 ≤ 4 ^ e := by
  induction e with
  | zero => simp
  | succ e ih => rw [pow_succ]; omega

/-- A count of at most `8(n+1)⁴` fits. -/
theorem fitV (x : TabCallReq B1 B2 cT) (v : ℕ) (hv : v ≤ 8 * (x.r.c.n + 1) ^ 4) : 2 ^ (natBitLength v + 1) ≤ Λf x := by
  have := pow_nbl_le v
  unfold Λf; omega

theorem nbl_fit (x : TabCallReq B1 B2 cT) (v : ℕ) (hv : v ∈ allN x) : natBitLength v + 2 ≤ Λf x := by
  have := nbl_le_L x v hv
  unfold Λf; omega

theorem dF_mem (x : TabCallReq B1 B2 cT) : dF1 x.id ∈ descN x.id ∧ dF2 x.id ∈ descN x.id := by
  rw [descN_split]; simp

theorem dF_le (x : TabCallReq B1 B2 cT) : dF1 x.id ≤ 2 * x.r.c.n + 4 ∧ dF2 x.id ≤ 2 * x.r.c.n + 4 :=
  ⟨desc_le x _ (dF_mem x).1, desc_le x _ (dF_mem x).2⟩

theorem qOf_le (x : TabCallReq B1 B2 cT) : qOf x.id ≤ 2 * x.r.c.n + 4 := by
  unfold qOf; split_ifs
  · exact (dF_le x).2
  · omega

/-- **Stage A's side conditions.** -/
theorem ahyp_of (x : TabCallReq B1 B2 cT) (Cl El : ℕ) : AHyp x (Λf x) (capf x Cl El) Cl El := by
  have hn4 := n4_ge x.r.c.n
  have hp4 := pow4_ge x.r.c.n
  have hc := circ_counts x
  have hk := k_le x
  have hJ := J_le x
  have hP := P_le x
  have he := e_le_k x
  have hs := cellReq_spec x.r
  have hlenE := len_eq x
  have hsl := streams_le x
  simp only [allN] at hsl
  have hcap1 : 40 * (Λf x + 1) ^ 2 + 50 * (tabCallInput x).length + 10 * Λf x ≤ capf x Cl El := by
    unfold capf; omega
  refine ⟨fun v hv => ⟨nbl_fit x v (by simp [allN, hv]), fitV x v (by have := desc_le x v hv; omega)⟩,
    fun y hy => nbl_fit x y hy, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, k_le x⟩
  · have := allN_len_le x; simp only [allN] at this; unfold Λf; omega
  · intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    apply fitV
    have hkt : kindTag x.r.c.kind ≤ 2 := by cases x.r.c.kind <;> decide
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  · unfold Λf; omega
  · intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    apply fitV
    have hpc := primes_card_le x.r.c x.r.p hs
    have hfl := factors_length hs
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
    · omega
    · omega
    · omega
    · omega
    · rw [Finset.length_sort]; omega
    · omega
  · refine ⟨fitV x _ ?_, fun s hs' => ⟨fitV x _ ?_, fitV x _ ?_⟩⟩
    · rw [coordsOf_length, cellReq_hk]; omega
    · have := coef_count x s 0 hs' (by omega); omega
    · have := coef_count x s 1 hs' le_rfl; omega
  · have h20 : 20 ≤ Λf x := by unfold Λf; omega
    rw [← hlenE]; have := hsl.2.2.2.2.2.1; rw [← hlenE] at this; omega
  · have := dF_le x; have hkt : kindTag x.r.c.kind ≤ 2 := by cases x.r.c.kind <;> decide
    unfold capf; omega
  · unfold capf; omega
  · unfold capf; omega

theorem bcond_of (x : TabCallReq B1 B2 cT) (Cl El : ℕ) :
    BCond x (Λf x) (capf x Cl El) (costA x (Λf x) Cl El) := by
  have hn4 := n4_ge x.r.c.n
  have hp4 := pow4_ge x.r.c.n
  have hc := circ_counts x
  have hk := k_le x
  have hJ := J_le x
  have he := e_le_k x
  have hep := e_le_pow x.r.p.e
  have hcap : capf x Cl El = capf x Cl El := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine fbound_of x (Λf x) (fun v hv => by have := nbl_fit x v hv; omega) ?_ ?_ ?_ ?_ ?_
    · unfold Λf; omega
    · have := qOf_le x; unfold Λf; omega
    · unfold Λf
      have : x.r.p.e ≤ 4 ^ x.r.p.e * (2 * x.r.p.e + 2) := by nlinarith
      omega
    · unfold Λf; omega
    · unfold Λf; omega
  · unfold Λf; omega
  · intro j hj
    have h1 : binom x.r.p.e j ≤ 4 ^ x.r.p.e := by
      unfold binom
      calc (x.r.p.e - 1 + j).choose j ≤ 2 ^ (x.r.p.e - 1 + j) := Nat.choose_le_two_pow _ _
        _ ≤ 2 ^ (2 * x.r.p.e) := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = 4 ^ x.r.p.e := by rw [pow_mul]; norm_num
    have h2 : binom x.r.p.e j * (x.r.p.e + j) ≤ 4 ^ x.r.p.e * (2 * x.r.p.e + 2) :=
      Nat.mul_le_mul h1 (by omega)
    unfold Λf; omega
  · unfold Λf
    have : x.r.p.e ≤ 4 ^ x.r.p.e * (2 * x.r.p.e + 2) := by nlinarith
    omega
  · unfold Λf; omega
  · unfold capf; omega
  · unfold capf; omega
  · unfold capf; omega
  · unfold capf; omega
  · unfold capf; omega

end NearCubicGates.Close.CounterMachine.TabCallProg
