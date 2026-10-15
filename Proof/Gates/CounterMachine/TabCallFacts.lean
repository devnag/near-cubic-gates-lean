import Proof.Gates.CounterMachine.TabCallRun
import Proof.Gates.CounterMachine.TabCallSize

/-! # RK, part 16: the request's sizes (values, counts, bit lengths) against `n` and `L = |tabCallInput|`

Every count stage A reads into a register is at most `8(n+1)⁴` (`count_le`: gates ≤ topWeight ≤ 2n⁴ by admission,
tables `2·topWeight + 1`, `k, P ≤ n`, `e ≤ 2k + 2`, `J ≤ n + 1`); every descriptor value is at most `2n + 4`
(`desc_le`); every natural of the input has at most `L` bits (`nbl_le_L`) and there are at most `L` of them
(`allN_len_le`). Also the exponential facts `100(k+2) ≤ n − k + 1` (eq:print-condition at degree 0) and
`e ≤ 2k + 2` (`liftExp`). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace NearCubicGates.Close.CounterMachine.TabCallProg

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.CounterMachine
open NearCubicGates.Close.Counter

variable {B1 B2 cT : ℕ}

theorem pow_nbl_le (v : ℕ) : 2 ^ (natBitLength v + 1) ≤ 4 * v + 4 := by
  unfold natBitLength
  rcases Nat.eq_zero_or_pos v with rfl | hv
  · simp
  · have := Nat.pow_log_le_self 2 hv.ne'
    rw [pow_succ, pow_succ]; omega

theorem tabCallInput_eq (x : TabCallReq B1 B2 cT) : tabCallInput x = (allN x).flatMap natWord := by
  rw [tabCallInput, cellInput, allN, List.flatMap_append, cellN_word]

theorem nbl_le_L (x : TabCallReq B1 B2 cT) : ∀ v ∈ allN x, natBitLength v ≤ (tabCallInput x).length := by
  intro v hv
  have h1 := TabCallSizes.len_le_flatMap natWord _ v hv
  rw [← tabCallInput_eq] at h1
  have := TabCallSizes.natWord_len v
  omega

theorem flatMap_len_ge {α : Type} (f : α → List Bool) (hf : ∀ a, 1 ≤ (f a).length) :
    ∀ L : List α, L.length ≤ (L.flatMap f).length
  | [] => by simp
  | a :: L => by
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    have := flatMap_len_ge f hf L; have := hf a; omega

theorem allN_len_le (x : TabCallReq B1 B2 cT) : (allN x).length ≤ (tabCallInput x).length := by
  rw [tabCallInput_eq]
  exact flatMap_len_ge natWord (fun a => by rw [TabCallSizes.natWord_len]; omega) _

theorem cellInput_le_L (x : TabCallReq B1 B2 cT) : (cellInput x.r).length ≤ (tabCallInput x).length := by
  rw [tabCallInput]; simp

section Spec
variable (x : TabCallReq B1 B2 cT)

theorem e_le_k (x : TabCallReq B1 B2 cT) : x.r.p.e ≤ 2 * (x.r.p.k + 1) := by
  have h := (cellReq_spec x.r).e_eq
  unfold liftExp at h
  exact (leastUpTo_spec _ _ _ h).2.1

/-- eq:print-condition at degree 0: `100(k+2) ≤ s + s % 2`. -/
theorem k_small (x : TabCallReq B1 B2 cT) : 100 * (x.r.p.k + 2) ≤ x.r.c.n - x.r.p.k + 1 := by
  have h := printCond_of x.r.c x.r.p (cellReq_spec x.r) 0 0 (Nat.zero_le _) (Nat.zero_le _)
  unfold Tabulator.PrintCondition at h
  simp only [pow_zero, mul_one, ← pow_mul] at h
  have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 h
  have : (x.r.c.n - x.r.p.k) % 2 ≤ 1 := Nat.le_of_lt_succ (Nat.mod_lt _ (by norm_num))
  omega

theorem k_le (x : TabCallReq B1 B2 cT) : x.r.p.k ≤ x.r.c.n := k_le_n x.r.c x.r.p (cellReq_spec x.r)

theorem J_le (x : TabCallReq B1 B2 cT) : x.r.p.J ≤ x.r.c.n + 1 :=
  (J_le_Jmax x.r.c x.r.p (cellReq_spec x.r)).trans (Cells.Jmax_le x.r.c x.r.p x.r.adm (cellReq_spec x.r))

theorem P_le (x : TabCallReq B1 B2 cT) : x.r.p.P ≤ x.r.c.n := P_le_n x.r.c x.r.p (cellReq_spec x.r)

/-- The circuit counts. -/
theorem circ_counts (x : TabCallReq B1 B2 cT) :
    x.r.c.first.gates.length ≤ 2 * x.r.c.n ^ 4 ∧ x.r.c.second.gates.length ≤ 2 * x.r.c.n ^ 4 ∧
    x.r.c.first.coeffs.length ≤ 2 * x.r.c.n ^ 4 ∧ x.r.c.second.coeffs.length ≤ 2 * x.r.c.n ^ 4 ∧
    x.r.c.first.table.length ≤ 4 * x.r.c.n ^ 4 + 1 ∧ x.r.c.second.table.length ≤ 4 * x.r.c.n ^ 4 + 1 ∧
    x.r.c.first.gates.length + x.r.c.second.gates.length ≤ 2 * x.r.c.n ^ 4 ∧ x.r.c.parity.length ≤ x.r.c.n := by
  obtain ⟨-, hf, hsec, -, -, -, hW, -, -, -, hpl⟩ := x.r.adm
  have a := gates_le_topWeight x.r.c.first _ hf
  have b := gates_le_topWeight x.r.c.second _ hsec
  have hW' : x.r.c.first.topWeight + x.r.c.second.topWeight ≤ 2 * x.r.c.n ^ 4 := hW
  obtain ⟨e1, -, t1, -⟩ := hf
  obtain ⟨e2, -, t2, -⟩ := hsec
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, hpl⟩

/-- The witness coefficient counts. -/
theorem coef_count (x : TabCallReq B1 B2 cT) (s r : ℕ) (hs : s < x.r.p.J) (hr : r ≤ 1) :
    (x.r.wt.coef s r).length ≤ 2 * x.r.c.n ^ 4 := by
  obtain ⟨w, hw⟩ := x.r.hw
  have hc := circ_counts x
  by_cases hrc : r < roleCount x.r.c.kind
  · rw [coef_length_of_decode _ _ w _ hw s r hs hrc]
    unfold circ; split_ifs <;> omega
  · have hr1 : r = 1 := by have := roleCount_pos x.r.c.kind; omega
    have hp : x.r.c.kind ≠ .pair := fun h => by subst hr1; simp [roleCount, h] at hrc
    rw [hr1, cellReq_coef1 x.r hp]; simp

/-- Every descriptor value is at most `2n + 4`. -/
theorem desc_le (x : TabCallReq B1 B2 cT) : ∀ v ∈ descN x.id, v ≤ 2 * x.r.c.n + 4 := by
  have hmem := x.mem
  have hJ := J_le x
  have hP := P_le x
  have hrc := TabCallSizes.roleCount_le x.r.c.kind
  cases hid : x.id with
  | residue part q κ σ =>
    rw [hid] at hmem
    obtain ⟨hq, hκ, hσ⟩ := TabCallSizes.mem_residue hmem
    have hqP := primes_le (cellReq_spec x.r) q hq
    rw [Cells.mem_vecs_iff] at hκ hσ
    have hlt : ∀ v ∈ κ ++ σ, v < q := by
      intro v hv
      rcases List.mem_append.1 hv with hv | hv
      · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hv
        have := hκ.2 i hi; rwa [List.getD_eq_getElem] at this
      · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hv
        have := hσ.2 i hi; rwa [List.getD_eq_getElem] at this
    have hlen : (κ ++ σ).length ≤ 2 * x.r.c.n + 4 := by
      rw [List.length_append, hκ.1, hσ.1]
      have : roleCount x.r.c.kind * x.r.p.J ≤ 2 * (x.r.c.n + 1) := Nat.mul_le_mul hrc hJ
      omega
    intro v hv
    simp only [descN, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with (((rfl | rfl | rfl | rfl) | hv) | hv)
    · omega
    · cases part with
      | none => simp [partCode]
      | some b => cases b <;> simp [partCode]
    · omega
    · exact hlen
    · have := hlt v (List.mem_append_left _ hv); omega
    · have := hlt v (List.mem_append_right _ hv); omega
  | digitMoment r j =>
    rw [hid] at hmem
    obtain ⟨hr, hj⟩ := TabCallSizes.mem_digit hmem
    intro v hv
    simp only [descN, List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl <;> omega
  | phiMoment r =>
    rw [hid] at hmem
    have hr := TabCallSizes.mem_phi hmem
    intro v hv
    simp only [descN, List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl <;> omega

end Spec

end NearCubicGates.Close.CounterMachine.TabCallProg
