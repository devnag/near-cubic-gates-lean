import SourceAdapters.ShortPCP.MaskMachineNum

/-!
# The mask machine: the whole cell-language program

 (Step 3 of `thm:short-pcp-ours`), in order: `r0` (`tableS`), `N = r0²·n·K1·f^{b1}` (`numS`), the
least `m` with `2^{2m} ≥ N` (`mdegS`), the field `𝔽_{2^m}` by exhaustive search (`srchS`, proof of `lem:small-bias`), and the
listing of the multiset `S` (`emitNatO` for `|S| = 4^m`, then `allS`), as the word `listWord frame S`.
The input is `1^s 0 ++ natWord f ++ natWord n` (the unary prefix fixes the cell width, `Cells/Run.lean:84`).
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.ShortPCP.MaskMachine

open NearCubicGates.Close.Cells NearCubicWires.WireExponent3_5 NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Adapters.Joins NearCubicGates.Adapters.Joins.SingleRun
open NearCubicGates.Adapters.ShortPCP.OracleCircuitPCP

/-! ## `natWord` printing as a framed run -/

theorem r_emitNat (C : Ctx) (a : Ds) (hc : Cst a) (hW : 2 ≤ C.Wd)
    (hv : natBitLength (a.env t3) + 2 < 2 ^ C.Wd) :
    Runs C emitNatO a (40 * natBitLength (a.env t3) + 40) emitNatT (natWord (a.env t3)) (fun _ => True) := by
  obtain ⟨b, n, hex, hn, h1, h2, -, h4⟩ := emitNatO_spec (C := C) a hc hW hv
  simp only [Prod.mk.injEq] at h2
  exact ⟨b, hex.mono hn, ⟨fun x hx => h4 x hx, h2.1, h1, h2.2.2.2.1, h2.2.2.2.2.1, h2.2.2.2.2.2⟩, trivial⟩

/-! ## Phase B: from `(f, n)` in variables to the printed multiset -/

/-- `vP := firstPrimitive m` for `m ≥ 1`, `vP := 1` for `m = 0`. -/
def fieldS : Sc := .ite (.lt vZ vM) srchS (.op (.copy vP v1))

def phaseB (K1 b1 : ℕ) : Sc :=
  .seq tableS (.seq (numS K1 b1) (.seq mdegS (.seq (.op (.copy xT vT)) (.seq (.op (.shl xT))
  (.seq fieldS (.seq (.op (.copy t3 vQ4)) (.seq emitNatO allS)))))))

def phaseBSet : List Var := tableSet ++ numSet ++ mdegSet ++ [xT] ++ srchSet ++ [t3] ++ emitNatT ++ allSet

/-- The parameters of Step 3 as functions of `(f, n)`. -/
def rOf (f : ℕ) : ℕ := r0f f
def nOf (K1 b1 f n : ℕ) : ℕ := rOf f ^ 2 * n * K1 * f ^ b1
def mOf (K1 b1 f n : ℕ) : ℕ := Amplified.mDeg (nOf K1 b1 f n)

def phaseBCost (K1 b1 f n : ℕ) : ℕ :=
  tableCost f + numCost K1 b1 + mdegCost (mOf K1 b1 f n) + srchCost (mOf K1 b1 f n) +
    40 * natBitLength (4 ^ mOf K1 b1 f n) + allCost (mOf K1 b1 f n) (rOf f) + 60

theorem firstPrimitive_zero : GF.firstPrimitive 0 = 1 := by decide

/-- The width every value of phase B fits in. -/
def wBig (K1 b1 f n : ℕ) : ℕ := 64 * (nBig (rOf f) n K1 b1 f + K1 + b1 + f + n + 8)

theorem phaseB_spec (C : Ctx) (a : Ds) (K1 b1 f n : ℕ) (hF : a.env vF = f) (hN : a.env vN = n) (hc : Cst a)
    (hram : a.ram sT = []) (hrc : a.rc sT = 0) (hW : 2 ≤ C.Wd) (hbig : wBig K1 b1 f n < 2 ^ C.Wd) :
    Runs C (phaseB K1 b1) a (phaseBCost K1 b1 f n) phaseBSet
      (natWord (4 ^ mOf K1 b1 f n) ++ allBits (Amplified.modulus (mOf K1 b1 f n)) (mOf K1 b1 f n) (rOf f))
      (fun _ => True) := by
  unfold phaseBCost
  set r := rOf f with hr
  set N := nOf K1 b1 f n with hNdef
  set m := mOf K1 b1 f n with hm
  have hrf : r ≤ 4 * f := r0f_le f
  have hNb : N ≤ nBig r n K1 b1 f := by
    have := part_le r n K1 f b1 b1 le_rfl; simpa [hNdef, nOf] using this
  have h4m : 4 ^ m ≤ 4 * N + 1 := four_pow_mDeg_le N
  have h2m : 2 ^ (m + 1) ≤ 2 * 4 ^ m := by
    rw [pow_succ, mul_comm]
    exact Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left (by norm_num) m)
  have hwb : 64 * (nBig r n K1 b1 f + K1 + b1 + f + n + 8) < 2 ^ C.Wd := hbig
  have hm1W : m + 1 < C.Wd := by
    have : 2 ^ (m + 1) < 2 ^ C.Wd := by omega
    exact (Nat.pow_lt_pow_iff_right (by norm_num)).1 this
  unfold phaseB
  have f0 := Fx.refl phaseBSet a
  -- r0
  refine Runs.callS0B f0 (tableS_spec C a f hF hc.two hram hrc (by omega)) (by decide)
    (fun a1 _ f1 h1 => ?_) (by omega)
  -- N
  refine Runs.callS0B f1 (numS_spec C a1 K1 b1 r n f h1 (by rw [f1.env vN (by decide), hN])
    (by rw [f1.env vF (by decide), hF]) (by omega)) (by decide) (fun a2 l2 f2 h2 => ?_)
    (by omega)
  -- m
  have hmd : mdegCost (Amplified.mDeg N) = mdegCost m := rfl
  refine Runs.callS0B f2 (mdegS_spec C a2 N h2 (by rw [f2.env v1 (by decide), hc.one]) (by omega)) (by decide)
    (fun a3 l3 f3 ⟨h3M, h3Q, h3T⟩ => ?_) (by omega)
  have hmN : Amplified.mDeg N = m := rfl
  rw [hmN] at h3M h3Q h3T
  have hpw : 2 * 2 ^ m < 2 ^ C.Wd := by rw [← pow_succ']; omega
  refine Runs.op1B f3 (r_copy C phaseBSet a3 xT vT (by decide) (by decide)) (fun f3 => ?_)
    (by omega)
  refine Runs.op1B f3 (r_shl C phaseBSet _ xT (by decide) (by norm_env; rw [h3T]; omega)) (fun f3 => ?_)
    (by omega)
  have hb4 : FBase ((a3.set xT (a3.env vT)).set xT (2 * (a3.set xT (a3.env vT)).env xT)) m :=
    ⟨by rw [f3.env v1 (by decide), hc.one], by rw [f3.env v2 (by decide), hc.two],
      by norm_env; exact h3M, by norm_env; exact h3T, by norm_env; rw [h3T, pow_succ]; ring⟩
  -- the field
  refine Runs.callS0B f3 (n := srchCost m + 1) (S0 := srchSet) (Q1 := fun b => FCtx b m (Amplified.modulus m)) ?_
    (by decide)
    (fun a5 l5 f5 h5 => ?_) (by omega)
  · unfold fieldS
    rcases Nat.eq_zero_or_pos m with hm0 | hm0
    · have hz : ((a3.set xT (a3.env vT)).set xT (2 * (a3.set xT (a3.env vT)).env xT)).env vZ = 0 := by
        rw [f3.env vZ (by decide), hc.z]
      refine Runs.iteF (wf_lt (by decide)) (by simp only [eval_lt, hz, hb4.M, hm0]; decide) ?_ (by omega)
      refine Runs.last (r_copy C srchSet _ vP v1 (by decide) (by decide)) (fun hf => ?_)
        (by unfold srchCost; omega)
      refine (hb4.of_fx hf (by decide)).withP ?_
      have h1' := hb4.one
      norm_env at h1' ⊢
      rw [h1', Amplified.modulus, hm0, firstPrimitive_zero]
    · have hz : ((a3.set xT (a3.env vT)).set xT (2 * (a3.set xT (a3.env vT)).env xT)).env vZ = 0 := by
        rw [f3.env vZ (by decide), hc.z]
      refine Runs.iteT (wf_lt (by decide)) (by simp only [eval_lt, hz, hb4.M]; simpa using hm0) ?_ (by omega)
      exact (srchS_spec C _ m hb4 hm0 hm1W hW).mono (by omega) (List.Subset.refl _)
        (fun b hf hb => (hb4.of_fx hf (by decide)).withP hb)
  -- |S| = 4^m
  have hQ : a5.env vQ4 = 4 ^ m := by rw [l5.env vQ4 (by decide)]; norm_env; exact h3Q
  refine Runs.op1B f5 (r_copy C phaseBSet a5 t3 vQ4 (by decide) (by decide)) (fun f6 => ?_)
    (by omega)
  have hcst : Cst (a5.set t3 (a5.env vQ4)) :=
    ⟨by norm_env; rw [f5.env vZ (by decide), hc.z], by norm_env; exact h5.one, by norm_env; exact h5.two⟩
  have hnbl : natBitLength (4 ^ m) + 2 < 2 ^ C.Wd := by
    have := natBitLength_le_self (4 ^ m); omega
  have hem := r_emitNat C (a5.set t3 (a5.env vQ4)) hcst hW (by norm_env; rw [hQ]; exact hnbl)
  have e3 : (a5.set t3 (a5.env vQ4)).env t3 = 4 ^ m := by norm_env; exact hQ
  rw [e3] at hem
  refine Runs.callSB (n := 40 * natBitLength (4 ^ m) + 40) f6 hem (by decide) (fun a7 l7 f7 _ => ?_)
    (by omega)
  -- the masks
  have h7 : FCtx a7 m (Amplified.modulus m) := by
    have := h5.set t3 (a5.env vQ4) (by decide)
    exact this.of_fx l7 (by decide)
  have hR7 : a7.env vR = r := by
    rw [l7.env vR (by decide)]; norm_env; rw [l5.env vR (by decide)]; norm_env
    rw [l3.env vR (by decide), l2.env vR (by decide), h1]; rfl
  refine (allS_spec C a7 m (Amplified.modulus m) r h7 (fun h => firstPrimitive_ok h) hR7 hm1W hW (by omega)).mono
    (by omega) (by decide) (fun _ _ h => h)

end NearCubicGates.Adapters.ShortPCP.MaskMachine
