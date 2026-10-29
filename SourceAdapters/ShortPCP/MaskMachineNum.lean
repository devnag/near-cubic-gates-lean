import SourceAdapters.ShortPCP.MaskMachineEmit

/-!
# The mask machine: `N = r0²·n·K1·f^{b1}` and `m` by comparisons

 (Step 3 of `thm:short-pcp-ours`): "Choose the least nonnegative integer `m` such that
`2^{2m} ≥ r0² n K1 f^{b1}`"; Step 3: "Choosing `m` uses only integer comparisons". `numS` computes
`N = r0²·n·K1·f^{b1}` (the constants `K1`, `b1` of Step 3 are built into the program), `mdegS` compares `N` with
`4^0, 4^1, …` (`MasksSpec.mDeg_spec`), keeping `2^m` and `4^m`.
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.ShortPCP.MaskMachine

open NearCubicGates.Close.Cells NearCubicWires.WireExponent3_5 NearCubicWires
open NearCubicGates.Adapters.Joins NearCubicGates.Adapters.Joins.SingleRun
open NearCubicGates.Adapters.ShortPCP.OracleCircuitPCP

def vN : Var := ⟨61, by decide⟩
def vNN : Var := ⟨63, by decide⟩
def vQ4 : Var := ⟨64, by decide⟩
def nA : Var := ⟨65, by decide⟩
def nB : Var := ⟨66, by decide⟩
def nC : Var := ⟨67, by decide⟩
def nI : Var := ⟨68, by decide⟩

/-! ## A constant -/

/-- `x := k` by `k` increments. -/
def constS (x : Var) : ℕ → Sc
  | 0 => .op (.zero x)
  | k + 1 => .seq (constS x k) (.op (.inc x))

theorem constS_spec (C : Ctx) (x : Var) (a : Ds) : ∀ k : ℕ, k < 2 ^ C.Wd →
    Runs C (constS x k) a (2 * k + 1) [x] [] (fun b => b.env x = k)
  | 0, _ => Runs.last (r_zero C [x] a x (by simp)) (fun _ => by norm_env) le_rfl
  | k + 1, hk => by
    refine Runs.call0 (constS_spec C x a k (by omega)) (fun b _ hb => ?_) (by omega)
    exact Runs.last (r_inc C [x] b x (by simp) (by rw [hb]; omega)) (fun _ => by norm_env; rw [hb]) (by omega)

/-! ## `N` -/

def numS (K1 b1 : ℕ) : Sc :=
  .seq (.op (.copy nB vR)) (.seq (.op (.mul vR nB nA)) (.seq (.op (.mul nA vN nB)) (.seq (constS nC K1)
  (.seq (.op (.mul nB nC nA)) (.seq (constS nC b1) (.seq (.op (.zero nI))
  (.seq (.loop (.lt nI nC) (.seq (.op (.mul nA vF nB)) (.seq (.op (.copy nA nB)) (.op (.inc nI)))))
  (.op (.copy vNN nA)))))))))

def numSet : List Var := [vNN, nA, nB, nC, nI]

def numCost (K1 b1 : ℕ) : ℕ := 2 * K1 + 9 * b1 + 40

/-- `N` and the bound it is computed under. -/
def nBig (r n K1 b1 f : ℕ) : ℕ := (r + 1) ^ 2 * (n + 1) * (K1 + 1) * (f + 1) ^ b1

theorem part_le (r n K1 f i b1 : ℕ) (hi : i ≤ b1) : r ^ 2 * n * K1 * f ^ i ≤ nBig r n K1 b1 f := by
  unfold nBig
  have h1 : f ^ i ≤ (f + 1) ^ b1 :=
    (Nat.pow_le_pow_left (by omega) i).trans (Nat.pow_le_pow_right (by omega) hi)
  have h2 : r ^ 2 ≤ (r + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have : r ^ 2 * n ≤ (r + 1) ^ 2 * (n + 1) := Nat.mul_le_mul h2 (by omega)
  have : r ^ 2 * n * K1 ≤ (r + 1) ^ 2 * (n + 1) * (K1 + 1) := Nat.mul_le_mul this (by omega)
  exact Nat.mul_le_mul this h1

theorem numS_spec (C : Ctx) (a : Ds) (K1 b1 r n f : ℕ) (hR : a.env vR = r) (hN : a.env vN = n) (hF : a.env vF = f)
    (hbig : nBig r n K1 b1 f + K1 + b1 < 2 ^ C.Wd) :
    Runs C (numS K1 b1) a (numCost K1 b1) numSet [] (fun b => b.env vNN = r ^ 2 * n * K1 * f ^ b1) := by
  have hb0 := part_le r n K1 f 0 b1 (by omega)
  have hb1 : r ^ 2 * n ≤ nBig r n K1 b1 f := by
    unfold nBig
    have h2 : r ^ 2 ≤ (r + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have : r ^ 2 * n ≤ (r + 1) ^ 2 * (n + 1) := Nat.mul_le_mul h2 (by omega)
    have h3 : 1 ≤ (K1 + 1) * (f + 1) ^ b1 := Nat.one_le_iff_ne_zero.2 (by positivity)
    calc r ^ 2 * n ≤ (r + 1) ^ 2 * (n + 1) * 1 := by omega
      _ ≤ (r + 1) ^ 2 * (n + 1) * ((K1 + 1) * (f + 1) ^ b1) := Nat.mul_le_mul_left _ h3
      _ = _ := by ring
  have hb2 : r ^ 2 ≤ nBig r n K1 b1 f := by
    unfold nBig
    have h2 : r ^ 2 ≤ (r + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have h3 : 1 ≤ (n + 1) * (K1 + 1) * (f + 1) ^ b1 := Nat.one_le_iff_ne_zero.2 (by positivity)
    calc r ^ 2 ≤ (r + 1) ^ 2 * 1 := by omega
      _ ≤ (r + 1) ^ 2 * ((n + 1) * (K1 + 1) * (f + 1) ^ b1) := Nat.mul_le_mul_left _ h3
      _ = _ := by ring
  simp only [pow_zero, mul_one] at hb0
  unfold numS
  have f0 := Fx.refl numSet a
  refine Runs.op1B f0 (r_copy C numSet a nB vR (by decide) (by decide)) (fun f0 => ?_) (by unfold numCost; omega)
  refine Runs.op1B f0 (r_mul C numSet _ vR nB nA (by decide) (by decide) (by decide) (by decide)
    (by norm_env; rw [hR, ← pow_two]; omega)) (fun f0 => ?_) (by unfold numCost; omega)
  refine Runs.op1B f0 (r_mul C numSet _ nA vN nB (by decide) (by decide) (by decide) (by decide)
    (by norm_env; rw [hR, hN, ← pow_two]; omega)) (fun f0 => ?_) (by unfold numCost; omega)
  refine Runs.callS0B f0 (constS_spec C nC _ K1 (by omega)) (by decide) (fun c cl f1 hc => ?_)
    (by unfold numCost; omega)
  have cB : c.env nB = r ^ 2 * n := by rw [cl.env nB (by decide)]; norm_env; rw [hR, hN, ← pow_two]
  refine Runs.op1B f1 (r_mul C numSet _ nB nC nA (by decide) (by decide) (by decide) (by decide)
    (by rw [cB, hc]; omega)) (fun f1 => ?_) (by unfold numCost; omega)
  refine Runs.callS0B f1 (constS_spec C nC _ b1 (by omega)) (by decide) (fun d dl f2 hd => ?_)
    (by unfold numCost; omega)
  have dA : d.env nA = r ^ 2 * n * K1 := by rw [dl.env nA (by decide)]; norm_env; rw [cB, hc]
  have dF : d.env vF = f := by rw [f2.env vF (by decide), hF]
  refine Runs.op1B f2 (r_zero C numSet _ nI (by decide)) (fun f2 => ?_) (by unfold numCost; omega)
  let Inv : ℕ → Ds → Prop := fun j e => e.env nA = r ^ 2 * n * K1 * f ^ j ∧ e.env nI = j ∧ e.env nC = b1
  refine Runs.callS0B f2 (Runs.loopN0F (wf_lt (by decide)) b1 5 Inv _ (fun j hj e hfe ⟨e1, e2, e3⟩ => ?_)
    (fun e _ ⟨_, e2, e3⟩ => by simp [e2, e3]) ⟨by norm_env; rw [dA]; ring, by norm_env, by norm_env; exact hd⟩)
    (List.Subset.refl _) (fun e _ f3 ⟨e1, _, _⟩ => ?_) (by unfold numCost; omega)
  · have eF : e.env vF = f := by rw [hfe.env vF (by decide)]; norm_env; exact dF
    refine ⟨by simp [e2, e3, hj], ?_⟩
    have hp := part_le r n K1 f (j + 1) b1 hj
    refine Runs.op1 (r_mul C numSet e nA vF nB (by decide) (by decide) (by decide) (by decide)
      (by rw [e1, eF, mul_assoc (r ^ 2 * n * K1), ← pow_succ]; omega)) ?_ (by norm_num)
    refine Runs.op1 (r_copy C numSet _ nA nB (by decide) (by decide)) ?_ (by norm_num)
    refine Runs.last (r_inc C numSet _ nI (by decide) (by norm_env; rw [e2]; omega)) (fun _ => ?_) le_rfl
    refine ⟨?_, ?_, ?_⟩ <;> norm_env
    · rw [e1, eF, pow_succ]; ring
    · rw [e2]
    · exact e3
  · exact Runs.last (r_copy C numSet e vNN nA (by decide) (by decide)) (fun _ => by norm_env; exact e1)
      (by unfold numCost; omega)

/-! ## `m`, `2^m`, `4^m` -/

def mdegS : Sc :=
  .seq (.op (.zero vM)) (.seq (.op (.copy vQ4 v1)) (.seq (.op (.copy vT v1))
    (.loop (.lt vQ4 vNN) (.seq (.op (.shl vQ4)) (.seq (.op (.shl vQ4)) (.seq (.op (.shl vT)) (.op (.inc vM))))))))

def mdegSet : List Var := [vM, vQ4, vT]

def mdegCost (m : ℕ) : ℕ := m * 9 + 10

theorem four_pow_mDeg_le (N : ℕ) : 4 ^ Amplified.mDeg N ≤ 4 * N + 1 := by
  rcases Nat.eq_zero_or_pos (Amplified.mDeg N) with h | h
  · rw [h]; omega
  · have := (mDeg_spec N).2 (Amplified.mDeg N - 1) (by omega)
    have e : 4 ^ Amplified.mDeg N = 4 * 4 ^ (Amplified.mDeg N - 1) := by
      rw [← pow_succ']; congr 1; omega
    omega

theorem mdegS_spec (C : Ctx) (a : Ds) (N : ℕ) (hNN : a.env vNN = N) (h1 : a.env v1 = 1)
    (hbig : 8 * N + 8 < 2 ^ C.Wd) :
    Runs C mdegS a (mdegCost (Amplified.mDeg N)) mdegSet [] (fun b => b.env vM = Amplified.mDeg N ∧
      b.env vQ4 = 4 ^ Amplified.mDeg N ∧ b.env vT = 2 ^ Amplified.mDeg N) := by
  set m := Amplified.mDeg N with hm
  have h4 := four_pow_mDeg_le N
  rw [← hm] at h4
  have h24 : ∀ j ≤ m, 2 ^ j ≤ 4 ^ m := fun j hj =>
    (Nat.pow_le_pow_right (by norm_num) hj).trans (Nat.pow_le_pow_left (by norm_num) m)
  have hmlt : m < 4 ^ m := (Nat.lt_two_pow_self).trans_le (h24 m le_rfl)
  unfold mdegS
  have f0 := Fx.refl mdegSet a
  refine Runs.op1B f0 (r_zero C mdegSet a vM (by decide)) (fun f0 => ?_) (by unfold mdegCost; omega)
  refine Runs.op1B f0 (r_copy C mdegSet _ vQ4 v1 (by decide) (by decide)) (fun f0 => ?_) (by unfold mdegCost; omega)
  refine Runs.op1B f0 (r_copy C mdegSet _ vT v1 (by decide) (by decide)) (fun f0 => ?_) (by unfold mdegCost; omega)
  let Inv : ℕ → Ds → Prop := fun j e => e.env vM = j ∧ e.env vQ4 = 4 ^ j ∧ e.env vT = 2 ^ j
  refine (Runs.loopN0F (wf_lt (by decide)) m 7 Inv _ (fun j hj e hfe ⟨e1, e2, e3⟩ => ?_)
    (fun e hfe ⟨_, e2, _⟩ => ?_) ⟨by norm_env, by norm_env; rw [h1]; rfl, by norm_env; rw [h1]; rfl⟩).mono
    (by unfold mdegCost; omega) (List.Subset.refl _) (fun e _ h => h)
  · have eN : e.env vNN = N := by rw [hfe.env vNN (by decide)]; norm_env; exact hNN
    have hjm : 4 ^ (j + 1) ≤ 4 ^ m := Nat.pow_le_pow_right (by norm_num) hj
    have h2j := h24 (j + 1) hj
    refine ⟨by simp [e2, eN, (mDeg_spec N).2 j hj], ?_⟩
    refine Runs.op1 (r_shl C mdegSet e vQ4 (by decide) (by rw [e2, pow_succ] at *; omega)) ?_ (by norm_num)
    refine Runs.op1 (r_shl C mdegSet _ vQ4 (by decide) (by norm_env; rw [e2, pow_succ] at *; omega)) ?_
      (by norm_num)
    refine Runs.op1 (r_shl C mdegSet _ vT (by decide) (by norm_env; rw [e3, pow_succ] at *; omega)) ?_ (by norm_num)
    refine Runs.last (r_inc C mdegSet _ vM (by decide) (by norm_env; rw [e1]; omega)) (fun _ => ?_) le_rfl
    refine ⟨?_, ?_, ?_⟩ <;> norm_env
    · rw [e1]
    · rw [e2, pow_succ]; ring
    · rw [e3, pow_succ]; ring
  · have eN : e.env vNN = N := by rw [hfe.env vNN (by decide)]; norm_env; exact hNN
    simp only [eval_lt, e2, eN, decide_eq_false_iff_not, not_lt]
    exact (mDeg_spec N).1

end NearCubicGates.Adapters.ShortPCP.MaskMachine
