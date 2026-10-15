import Proof.Gates.CounterMachine.ReqMom

/-! # RG, value level 5: the requests are legal lem:print instances (paper v2 lines 1668–1679)

"These operations are legal applications of lem:print … The residue polynomials have degree at most the left side of
eq:prime-budget; moments have degree at most `2k ≤ D_max`. At most twice the original number of gate variables is
needed … and eq:degree-budget supplies the printing condition." **`printCond_of`**: every formula of degree at most
`D_max` over at most `2G₀` variables meets the printing condition of `TabReq` (from `DegreePass` at `D_max`, the
selected `m = n − k` rounded up, and `m_T` of lem:print below the counter's `m_T`). **`resFormula_degree_le_Dmax`**:
the residue polynomials (eq:prime-budget through `PrimeCandidate` at `P`). Bit bounds `hB` from admission. -/

set_option autoImplicit false

namespace NearCubicGates.Close.CounterMachine

open NearCubicWires NearCubicGates NearCubicGates.Close.Counter NearCubicGates.Close.Tabulator
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats

section Cond
variable {cT : ℕ} (c : Call) (p : Params) (hs : Spec cT (header c) p)
include hs

theorem degreePass_Dmax : DegreePass c.n p.k p.m p.Dmax := by
  rw [hs.Dmax_eq, hs.m_eq, hs.k_eq]
  have h0 := hs.zero_pass
  rw [hs.m_eq, hs.k_eq] at h0
  exact Nat.findGreatest_spec (Nat.zero_le _) h0

theorem m_eq_s : p.m = (c.n - p.k) + (c.n - p.k) % 2 := by
  rw [hs.m_eq]; rfl

/-- **The printing condition** of every request of degree at most `D_max` over at most `2G₀` variables. -/
theorem printCond_of (D V : ℕ) (hD : D ≤ p.Dmax) (hV : V ≤ 2 * G0 c.n) :
    PrintCondition p.k (c.n - p.k) D V (Tabulator.mT (c.n - p.k) (Call.B0 c.n + Nat.clog 2 (c.n + 1))) := by
  have hdp := degreePass_Dmax c p hs
  have hm := m_eq_s c p hs
  unfold DegreePass at hdp
  unfold PrintCondition
  rw [hm] at hdp
  set s := c.n - p.k with hsdef
  set mm := s + s % 2 with hmm
  -- m_T of lem:print is below the counter's m_T
  have hss : s ≤ mm := by omega
  have hclog : Nat.clog 2 (s + 1) ≤ Nat.clog 2 (mm + 1) := Nat.clog_mono_right 2 (by omega)
  have hbb : blockBits s (Call.B0 c.n + Nat.clog 2 (c.n + 1)) ≤ Bb c.n mm := by
    unfold blockBits Bb; simp only [Call.B0, Counter.B0]; omega
  have hhalf : (s + 1) / 2 ≤ (mm + 1) / 2 := Nat.div_le_div_right (by omega)
  have hmt : Tabulator.mT s (Call.B0 c.n + Nat.clog 2 (c.n + 1)) ≤ Counter.mT c.n mm := by
    unfold Tabulator.mT Counter.mT
    have := Nat.mul_le_mul (Nat.mul_le_mul hbb hss) hhalf
    omega
  have hbase : 1 + V * Tabulator.mT s (Call.B0 c.n + Nat.clog 2 (c.n + 1)) ≤ Ubase c.n mm := by
    unfold Ubase
    have := Nat.mul_le_mul hV hmt
    nlinarith
  have hU1 : 1 ≤ Ubase c.n mm := by unfold Ubase; omega
  calc (2 ^ (p.k + 2) * (1 + V * Tabulator.mT s (Call.B0 c.n + Nat.clog 2 (c.n + 1))) ^ D) ^ 100
      = 2 ^ (100 * (p.k + 2)) * (1 + V * Tabulator.mT s (Call.B0 c.n + Nat.clog 2 (c.n + 1))) ^ (100 * D) := by
        rw [mul_pow, ← pow_mul, ← pow_mul]; ring_nf
    _ ≤ 2 ^ (100 * (p.k + 2)) * Ubase c.n mm ^ (100 * p.Dmax) := by
        apply Nat.mul_le_mul_left
        calc (1 + V * Tabulator.mT s (Call.B0 c.n + Nat.clog 2 (c.n + 1))) ^ (100 * D)
            ≤ Ubase c.n mm ^ (100 * D) := Nat.pow_le_pow_left hbase _
          _ ≤ Ubase c.n mm ^ (100 * p.Dmax) := Nat.pow_le_pow_right hU1 (by omega)
    _ ≤ 2 ^ mm := hdp

/-- `P` passes eq:prime-budget with the selected `e`. -/
theorem prime_budget : (2 * p.e - 1) * (2 * Jmax c.n + 2) * (p.P - 1) ≤ p.Dmax := by
  have hP := hs.P_eq
  have hne : p.P ≠ 0 := by have := hs.P_three; omega
  have hc := Nat.findGreatest_of_ne_zero hP.symm hne
  obtain ⟨-, -, e, he, hle⟩ := hc
  have heq : liftExp p.k p.P = some p.e := by rw [hs.e_eq]
  rw [hs.k_eq] at heq
  have : e = p.e := by
    rw [hs.k_eq] at he
    rw [he] at heq; exact Option.some.inj heq
  rw [← this]; exact hle

/-- The residue polynomials stay within `D_max`. -/
theorem resFormula_degree_le_Dmax (wt : Wit c.n) (q : ℕ) (hq : q ∈ p.primes) (κ σ : List ℕ) :
    (resFormula c p wt q κ σ).degree ≤ p.Dmax := by
  refine (resF_degree_le q p.e _ _ (fun i => resForm_degree c p wt i.val)).trans ?_
  refine le_trans ?_ (prime_budget c p hs)
  have hR : roleCount c.kind ≤ 2 := roleCount_le_two c
  have hJ := J_le_Jmax c p hs
  have hq' : q - 1 ≤ p.P - 1 := Nat.sub_le_sub_right (primes_le hs q hq) 1
  have h1 : roleCount c.kind * p.J + roleCount c.kind ≤ 2 * Jmax c.n + 2 := by nlinarith
  calc (2 * p.e - 1) * (roleCount c.kind * p.J + roleCount c.kind) * (q - 1)
      ≤ (2 * p.e - 1) * (2 * Jmax c.n + 2) * (p.P - 1) := by gcongr

/-- Moments have degree at most `2k ≤ D_max`. -/
theorem momF_degree_le_Dmax (wt : Wit c.n) (r : ℕ) (j : Option ℕ) {V : ℕ} :
    (momF (V := V) c p wt r j).degree ≤ p.Dmax :=
  (momF_degree c p wt r j).trans hs.moment_degree

end Cond

/-! ## Gate counts and bit bounds from admission -/

theorem gates_le_topWeight {n : ℕ} (C : NCircuit n) (B : ℕ) (hC : C.WellFormed B) : C.gates.length ≤ C.topWeight := by
  obtain ⟨hlen, hnz, -, -⟩ := hC
  rw [hlen]
  unfold NCircuit.topWeight
  have : ∀ l : List ℤ, (∀ a ∈ l, a ≠ 0) → l.length ≤ (l.map Int.natAbs).sum := by
    intro l hl
    induction l with
    | nil => simp
    | cons a l ih =>
      simp only [List.length_cons, List.map_cons, List.sum_cons]
      have h1 : 1 ≤ a.natAbs := Int.natAbs_pos.mpr (hl a (by simp))
      have := ih (fun b hb => hl b (by simp [hb]))
      omega
  exact this _ hnz

section Adm
variable {B1 B2 : ℕ} (c : Call) (hadm : c.Admitted B1 B2)
include hadm

omit hadm in
theorem circ_wf (r : ℕ) (h1 : c.first.WellFormed (Call.B0 c.n)) (h2 : c.second.WellFormed (Call.B0 c.n)) :
    (circ c r).WellFormed (Call.B0 c.n) := by
  unfold circ; split <;> assumption

theorem resGates_le : (resGates c).length ≤ 2 * G0 c.n := by
  obtain ⟨-, h1, h2, -, -, -, hW, -⟩ := hadm
  have a := gates_le_topWeight c.first _ h1
  have b := gates_le_topWeight c.second _ h2
  have hW' : c.first.topWeight + c.second.topWeight ≤ 2 * c.n ^ 4 := hW
  unfold resGates G0
  split <;> simp <;> omega

theorem circ_gates_le (r : ℕ) : 2 * (circ c r).gates.length ≤ 2 * G0 c.n := by
  obtain ⟨-, h1, h2, -, -, -, hW, -⟩ := hadm
  have a := gates_le_topWeight c.first _ h1
  have b := gates_le_topWeight c.second _ h2
  have hW' : c.first.topWeight + c.second.topWeight ≤ 2 * c.n ^ 4 := hW
  unfold circ G0
  split <;> omega

theorem gateBits_of (g : NormalizedThresholdGate c.n) (hg : g ∈ c.first.gates ∨ g ∈ c.second.gates) :
    GateBits (Call.B0 c.n) g := by
  obtain ⟨-, h1, h2, -⟩ := hadm
  rcases hg with hg | hg
  · exact h1.2.2.2 g hg
  · exact h2.2.2.2 g hg

theorem resGates_bits : ∀ i : Fin (resGates c).length, GateBits (Call.B0 c.n) ((resGates c)[i]) := by
  have hmem : ∀ g ∈ resGates c, g ∈ c.first.gates ∨ g ∈ c.second.gates := by
    intro g hg; unfold resGates at hg
    split at hg
    · exact List.mem_append.mp hg
    · exact Or.inl hg
  intro i
  exact gateBits_of c hadm _ (hmem _ (List.getElem_mem _))

theorem circ_bits (r : ℕ) : ∀ t : Fin (circ c r).gates.length, GateBits (Call.B0 c.n) ((circ c r).gates[t]) := by
  have hmem : ∀ g ∈ (circ c r).gates, g ∈ c.first.gates ∨ g ∈ c.second.gates := by
    intro g hg; unfold circ at hg
    split at hg
    · exact Or.inl hg
    · exact Or.inr hg
  intro t
  exact gateBits_of c hadm _ (hmem _ (List.getElem_mem _))

end Adm

end NearCubicGates.Close.CounterMachine
