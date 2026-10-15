import Proof.Gates.Expand.Main1
import Proof.Gates.Interfaces.WordFn

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicGates.Close.Expand.Layout

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length binary_value)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (NumOn)
open NearCubicGates.Close.Tabulator NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Expand

theorem two_pow_lt_wb1 (r : FormulaReq) : 2 ^ (Lw r + 1) + 1 < 2 ^ Wb1 r := by
  unfold Wb1
  have h1 : 2 ^ (Lw r + 2) ≤ 2 ^ ((Lw r + 2) * (Lw r + 2)) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  have h2 : 2 ^ (Lw r + 2) = 2 * 2 ^ (Lw r + 1) := by ring
  have h3 : 1 ≤ 2 ^ (Lw r + 1) := Nat.one_le_two_pow
  omega

theorem deg_lt (r : FormulaReq) : r.2.degree < 2 ^ (Lw r + 1) :=
  lt_of_lt_of_le (degree_weight_lt r.2).1 (Nat.pow_le_pow_right (by norm_num) (by have := tokBits_le r; unfold Lw; omega))

theorem wt_lt (r : FormulaReq) : r.2.weight < 2 ^ (Lw r + 1) :=
  lt_of_lt_of_le (degree_weight_lt r.2).2 (Nat.pow_le_pow_right (by norm_num) (by have := tokBits_le r; unfold Lw; omega))

theorem depthA (r : FormulaReq) : (KA r + 1) ^ ((toks r.2).length + 2) ≤ 2 ^ Wb1 r := by
  have hN := toks_le_word r
  have h1 : KA r + 1 ≤ 2 ^ (Lw r + 2) := by unfold KA; rw [pow_succ 2 (Lw r + 1)]; have := @Nat.one_le_two_pow (Lw r + 1); omega
  calc (KA r + 1) ^ ((toks r.2).length + 2) ≤ (2 ^ (Lw r + 2)) ^ ((toks r.2).length + 2) := Nat.pow_le_pow_left h1 _
    _ = 2 ^ ((Lw r + 2) * ((toks r.2).length + 2)) := by rw [← pow_mul]
    _ ≤ 2 ^ Wb1 r := Nat.pow_le_pow_right (by norm_num) (by unfold Wb1 Lw at *; nlinarith)

theorem wb1_le_wb2 (r : FormulaReq) : Wb1 r ≤ Wb2 r := by
  unfold Wb1 Wb2 wb2 Wt; nlinarith

theorem degA_eq (r : FormulaReq) : (degAlg (KA r)).eval r.2 = r.2.degree := degAlg_exact r
theorem wtA_eq (r : FormulaReq) : (wtAlg (KA r)).eval r.2 = r.2.weight := wtAlg_exact r

theorem nb_val_ne0 (j : Fin 53) : (NB j).val ≠ 0 := by
  have := j.isLt; simp only [NB_val, nbv]; split_ifs <;> omega

theorem rR_KeepA (j : Fin 12) : R j ∉ KeepA := by have := j.isLt; unfold KeepA; lay_ne

theorem stageA_spec (r : FormulaReq) (cap : ℕ) (hcap : CapA r cap) :
    Runs cap stageA (Interfaces.startState NS NR (formulaWord r)) (stageACost r) (AState r) := by
  set S0 := Interfaces.startState NS NR (formulaWord r) with hS0
  have s0st : ∀ x, S0.st x = if x.val = 0 then frame (formulaWord r) else [] := fun _ => rfl
  have s0sh : ∀ x, S0.sh x = 0 := fun _ => rfl
  have s0v : ∀ q, S0.val q = 0 := fun _ => rfl
  unfold CapA at hcap
  have hL := toks_le_word r
  have hD := deg_lt r
  have hwt := wt_lt r
  have hKW := two_pow_lt_wb1 r
  have h12 := wb1_le_wb2 r
  have hTB := tokBits_le r
  have hWb2a : (r.2.weight + 2 + Lw r + 2) * (Lw r + 2) ≤ Wb2 r := by unfold Wb2 wb2 Wt; omega
  have eW2 : Wb2 r = wb2 (r.2.weight + 2) (Lw r) r.1 r.2.degree := rfl
  have eWt : Wt r = r.2.weight + 2 := rfl
  have hLWb : Lw r + 2 ≤ Wb1 r := by unfold Wb1; nlinarith
  have hpowL : Lw r + 4 < 2 ^ (Lw r + 4) := Nat.lt_two_pow_self
  have hp1 : 2 ^ (Lw r + 1) ≤ 2 ^ (Lw r + 4) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hp2 : 2 ^ (tokBits r.2 + 2) ≤ 2 ^ (Lw r + 4) := Nat.pow_le_pow_right (by norm_num) (by unfold Lw; omega)
  have eL : Lw r = (formulaWord r).length := rfl
  have eW1 : Wb1 r = (Lw r + 2) * (Lw r + 2) := rfl
  have eK : KA r = 2 ^ (Lw r + 1) := rfl
  have pb1 := Nat.two_pow_pos (natBitLength r.1)
  have pb2 := Nat.two_pow_pos (natBitLength r.1 + 1)
  have pb3 := Nat.two_pow_pos (Lw r + 4)
  have pb4 := Nat.two_pow_pos (Lw r + 1)
  have pb5 := Nat.two_pow_pos (Lw r)
  -- 1. the input length
  refine Runs.seq (meas_spec cap (formulaWord r) S0 (by rw [s0st]; simp) (s0sh _) (s0v _) (s0v _) (s0v _)
    (by omega)) (fun τ1 ⟨f1, g01, y01⟩ => ?_)
  -- 2. the first width
  refine Runs.seq (regA_spec cap (Lw r) τ1 g01 (by rw [f1.val (by lay_ne)]; rfl) (by rw [f1.val (by lay_ne)]; rfl)
    (by rw [f1.val (by lay_ne)]; rfl) (by rw [f1.val (by lay_ne)]; rfl) (by rw [f1.val (by lay_ne)]; rfl)
    (by omega)) (fun τ2 ⟨f2, g22, g23, g24⟩ => ?_)
  -- 3. the number block at Wb1
  refine Runs.seq (stageA1_spec cap (Lw r) τ2 (fun j => ⟨by rw [f2.st (by simp), f1.st (by simp), s0st,
      if_neg (nb_val_ne0 j)], by rw [f2.sh (by simp), f1.sh (by simp)]; rfl⟩) g22 g23
    (by rw [f2.val (by lay_ne), f1.val (by lay_ne)]; rfl) (by rw [f2.val (by lay_ne), f1.val (by lay_ne)]; rfl)
    (by rw [f2.val (by lay_ne), f1.val (by lay_ne)]; rfl) (by omega))
    (fun τ3 ⟨m3, g33, f3⟩ => ?_)
  have v3 : ∀ q, q ∉ [GR 0, Y 0, GR 2, GR 3, GR 4] → τ3.val q = 0 := fun q hq => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
    rw [f3.val (by simp [hq.2.2.2.1]), f2.val (by simp [hq.2.2.1, hq.2.2.2.1, hq.2.2.2.2]),
      f1.val (by simp [hq.1, hq.2.1])]; rfl
  have st3 : ∀ x, x ∉ nbList → τ3.st x = S0.st x ∧ τ3.sh x = S0.sh x := fun x hx =>
    ⟨by rw [f3.st hx, f2.st (by simp), f1.st (by simp)], by rw [f3.sh hx, f2.sh (by simp), f1.sh (by simp)]⟩
  have hU0n : U 0 ∉ nbList := by
    intro hm; obtain ⟨j, hj⟩ := List.mem_ofFn.mp hm; exact NB_ne_0 j hj
  have y03 : τ3.val (Y 0) = 2 * Lw r + 1 := by
    rw [f3.val (by lay_ne), f2.val (by lay_ne)]; exact y01
  -- 4. the degree pass
  have hFtok := toks_ok r.2
  refine Runs.seq ((passA_spec cap (Wb1 r) (KA r + 1) (KA r) (hcost (Wb1 r) (tokBits r.2) (maxExp r.2) r.1)
    (degAlg (KA r)) (degAlg_closed (KA r)) (by rw [eK]; have := @Nat.one_le_two_pow (Lw r + 1); omega)
    (degH U R) rfl r (fun tok htok => degHs U R cap (Wb1 r) (KA r) 0 (tokBits r.2) (maxExp r.2) r.1
      (Nat.one_le_two_pow) (by omega) (by omega) tok (hFtok tok htok))
    (RF 8) (fun j => rne (by have := j.isLt; simp; omega)) (rne (by simp [GLr])) (rne (by simp [F0]))
    (rne (by simp [R0])) τ3 (wA (Lw r)) m3 (by simp [wA]) (by simp [wA, KA]) (by simp [wA, KA]) (by simp [wA])
    (by simp [wA]) (by rw [(st3 _ hU0n).1, s0st]; simp) (by rw [(st3 _ hU0n).2]; rfl)
    (fun j => v3 _ (by have := j.isLt; lay_ne)) y03 (v3 _ (by lay_ne)) (v3 _ (by simp [F0]; lay_ne))
    (v3 _ (by simp [R0]; lay_ne)) (v3 _ (by simp [GLr]; lay_ne)) (v3 _ (by lay_ne))
    (by rw [degA_eq]; omega) (depthA r) (by omega) (by rw [← eL]; omega)
    (by rw [degA_eq]; omega)).cost (le_of_eq (by rw [degA_eq]; rfl)))
    (fun τ4 ⟨⟨w4, m4, w4j, w40, w41⟩, d4, inp4, hd4, R4, regs4, strs4⟩ => ?_)
  rw [degA_eq] at d4
  have gq4 : ∀ q, q ∉ RF 8 :: (evR R ++ [R 11]) → q ∉ [GR 0, Y 0, GR 2, GR 3, GR 4] → τ4.val q = 0 :=
    fun q h1 h2 => by rw [regs4 q h1, v3 q h2]
  -- 5. the weight pass
  refine Runs.seq ((passA_spec cap (Wb1 r) (KA r + 1) (KA r) (hcost (Wb1 r) (tokBits r.2) (maxExp r.2) r.1)
    (wtAlg (KA r)) (wtAlg_closed (KA r)) (by rw [eK]; have := @Nat.one_le_two_pow (Lw r + 1); omega)
    (wtH U R) rfl r (fun tok htok => wtHs U R cap (Wb1 r) (KA r) 0 (tokBits r.2) (maxExp r.2) r.1
      (Nat.one_le_two_pow) (by omega) (by have := @Nat.lt_two_pow_self (Wb1 r); omega) (by omega) (by omega) tok
      (hFtok tok htok))
    (GR 1) (fun j => rne (by have := j.isLt; simp; omega)) (rne (by simp [GLr])) (rne (by simp [F0]))
    (rne (by simp [R0])) τ4 w4 m4 w40 (by rw [w4j 5 (by decide)]; simp [wA, KA]) (by rw [w4j 6 (by decide)]; simp [wA, KA])
    (by rw [w4j 7 (by decide)]; simp [wA]) (by rw [w4j 8 (by decide)]; simp [wA]) inp4 hd4 R4
    (by rw [regs4 _ (by lay_ne)]; exact y03) (gq4 _ (by lay_ne) (by lay_ne)) (gq4 _ (by simp [F0]; lay_ne) (by simp [F0]; lay_ne))
    (gq4 _ (by simp [R0]; lay_ne) (by simp [R0]; lay_ne)) (gq4 _ (by simp [GLr]; lay_ne) (by simp [GLr]; lay_ne))
    (gq4 _ (by lay_ne) (by lay_ne))
    (by rw [wtA_eq]; omega) (depthA r) (by omega) (by rw [← eL]; omega)
    (by rw [wtA_eq]; omega)).cost (le_of_eq (by rw [wtA_eq]; rfl)))
    (fun τ5 ⟨⟨w5, m5, w5j, w50, w51⟩, g15, inp5, hd5, R5, regs5, strs5⟩ => ?_)
  rw [wtA_eq] at g15
  have gq5 : ∀ q, q ∉ GR 1 :: (evR R ++ [R 11]) → q ∉ RF 8 :: (evR R ++ [R 11]) →
      q ∉ [GR 0, Y 0, GR 2, GR 3, GR 4] → τ5.val q = 0 := fun q h1 h2 h3 => by rw [regs5 q h1, gq4 q h2 h3]
  -- 6. V
  refine Runs.seq (readV_spec cap r τ5 inp5 hd5 R5 (gq5 _ (by lay_ne) (by lay_ne) (by lay_ne))
    (by rw [regs5 _ (by lay_ne), regs4 _ (by lay_ne)]; exact y03) (gq5 _ (by lay_ne) (by lay_ne) (by lay_ne))
    (by rw [← eL]; omega)) (fun τ6 ⟨f6, v6⟩ => ?_)
  -- 7. the second width
  have u62 : τ6.val (GR 2) = (Lw r + 2) * (Lw r + 2) := by
    rw [f6.val (by lay_ne), regs5 _ (by lay_ne), regs4 _ (by lay_ne), f3.val (by lay_ne)]; exact g22
  have u63 : τ6.val (GR 3) = Lw r + 1 := by
    rw [f6.val (by lay_ne), regs5 _ (by lay_ne), regs4 _ (by lay_ne)]; exact g33
  have u64 : τ6.val (GR 4) = Lw r + 2 := by
    rw [f6.val (by lay_ne), regs5 _ (by lay_ne), regs4 _ (by lay_ne), f3.val (by lay_ne)]; exact g24
  refine Runs.seq (regB1_spec cap r.2.weight (Lw r) τ6 (by rw [f6.val (by lay_ne)]; exact g15) u62 u63 u64
    (by rw [f6.val (by lay_ne)]; exact gq5 _ (by lay_ne) (by lay_ne) (by lay_ne))
    (by rw [f6.val (by lay_ne)]; exact gq5 _ (by lay_ne) (by lay_ne) (by lay_ne)) (by omega))
    (fun τ7 ⟨f7, g71, g72, g73⟩ => ?_)
  have u7D : τ7.val (RF 8) = r.2.degree := by
    rw [f7.val (by lay_ne), f6.val (by lay_ne), regs5 _ (by lay_ne)]; exact d4
  have u7V : τ7.val (RF 10) = r.1 := by rw [f7.val (by lay_ne)]; exact v6
  refine (regB2_spec cap r.2.weight (Lw r) r.1 r.2.degree τ7 g72 g73
    (by rw [f7.val (by lay_ne), f6.val (by lay_ne)]; exact gq5 _ (by lay_ne) (by lay_ne) (by lay_ne))
    (by rw [f7.val (by lay_ne), f6.val (by lay_ne)]; exact gq5 _ (by lay_ne) (by lay_ne) (by lay_ne))
    u7D u7V (by rw [← eW2]; omega)).post (fun τ8 ⟨f8, g82, g83⟩ => ?_)
  have hS : ∀ x, τ8.st x = τ5.st x ∧ τ8.sh x = τ5.sh x := fun x =>
    ⟨by rw [f8.st (by simp), f7.st (by simp), f6.st (by simp)], by rw [f8.sh (by simp), f7.sh (by simp), f6.sh (by simp)]⟩
  refine ⟨⟨w5, fun j => ⟨by rw [(hS _).1]; exact (m5 j).1, by rw [(hS _).2]; exact (m5 j).2⟩⟩, by rw [(hS _).1]; exact inp5,
    fun x hx h0 => ?_, by rw [(hS _).2]; exact hd5, fun q hq => ?_, ?_, ?_, g83, ?_, ?_, ?_, ?_, ?_⟩
  · rw [(hS x).1, (hS x).2, (strs5 x hx h0).1, (strs5 x hx h0).2, (strs4 x hx h0).1, (strs4 x hx h0).2,
      (st3 x hx).1, (st3 x hx).2, s0st, s0sh]
    have : x.val ≠ 0 := fun e => h0 (Fin.ext (by simpa using e))
    simp [this]
  · simp only [KeepA, List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
    obtain ⟨q0, q1, q2, q3, q4, q8, q10, qy⟩ := hq
    rw [f8.val (by simp [q2, q3]), f7.val (by simp [q1, q2, q3]), f6.val (by simp [q10])]
    by_cases hR : ∃ j, q = R j
    · obtain ⟨j, rfl⟩ := hR; exact R5 j
    · push Not at hR
      have hRl : q ∉ evR R ++ [R 11] := by
        simp only [evR, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨⟨hR 0, hR 1, hR 2, hR 3, hR 4, hR 5, hR 6, hR 7, hR 8, hR 9, hR 10⟩, hR 11⟩
      exact gq5 q (by simp [q1, hRl]) (by simp [q8, hRl]) (by simp [q0, qy, q2, q3, q4])
  · rw [f8.val (by lay_ne), g71]; rfl
  · rw [g82]; rfl
  · rw [f8.val (by lay_ne)]; exact u7D
  · rw [f8.val (by lay_ne)]; exact u7V
  · rw [f8.val (by lay_ne), f7.val (by lay_ne), f6.val (by lay_ne), regs5 _ (by lay_ne), regs4 _ (by lay_ne)]
    exact y03
  · rw [f8.val (by lay_ne), f7.val (by lay_ne), f6.val (by lay_ne), regs5 _ (by lay_ne), regs4 _ (by lay_ne),
      f3.val (by lay_ne), f2.val (by lay_ne)]; exact g01
  · rw [f8.val (by lay_ne), f7.val (by lay_ne), f6.val (by lay_ne), regs5 _ (by lay_ne), regs4 _ (by lay_ne),
      f3.val (by lay_ne)]; exact g24

end NearCubicGates.Close.Expand.Layout
