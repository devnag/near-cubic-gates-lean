import SourceAdapters.ShortPCP.MaskMachineKit
import Proof.Wire_3_5.GFRef

/-!
# The mask machine: field arithmetic on words in the cell language

 (proof of `lem:small-bias`): "identify `𝔽_{2^m}` with `𝔽₂^m`": "`σ_{a,b}` has
coordinates `a^j · b`" with `·` the inner product of masks (proof of `lem:small-bias`). A field element is an `m`-bit word; the
modulus `p` has bit `m` set (`Joins/BinaryFieldArithmetic.lean`). The routines (fixed variables, fixed scratch):
- `xorS`: `xZ := (xX ⊕ xY) mod 2^k` for the bound `xT = 2^k` (the field sum `GF.rep_xor`);
- `lfsrS`: `lA := lfsr p m lA` (multiplication by `x`, L `Shared/GF.lean:11`);
- `fmulS`: `mZ := fmulShift p m mX mY` (the released shift-and-xor product, `GF.fmulShift_spec`);
- `dotS`: `dB := wordDot m dX dY` (the inner product of masks, `MasksSpec.bdot_rep`).
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.ShortPCP.MaskMachine

open NearCubicGates.Close.Cells NearCubicWires.WireExponent3_5

/-! ## Variables -/

def xX : Var := ⟨20, by decide⟩
def xY : Var := ⟨21, by decide⟩
def xZ : Var := ⟨22, by decide⟩
def xT : Var := ⟨23, by decide⟩
def xU : Var := ⟨24, by decide⟩
def xV : Var := ⟨25, by decide⟩
def xW : Var := ⟨26, by decide⟩
def xBu : Var := ⟨27, by decide⟩
def xBv : Var := ⟨28, by decide⟩
def xQ : Var := ⟨29, by decide⟩

/-! ## The sum: `xZ := (xX ⊕ xY) mod 2^k` -/

theorem xor_mod_succ (x y j : ℕ) : (x ^^^ y) % 2 ^ (j + 1) =
    (x ^^^ y) % 2 ^ j + (if (x / 2 ^ j) % 2 = (y / 2 ^ j) % 2 then 0 else 2 ^ j) := by
  rw [Nat.mod_pow_succ, Nat.xor_div_two_pow]
  congr 1
  have key := Nat.xor_mod_two_eq_one (a := x / 2 ^ j) (b := y / 2 ^ j)
  rcases Nat.mod_two_eq_zero_or_one (x / 2 ^ j) with h1 | h1 <;>
    rcases Nat.mod_two_eq_zero_or_one (y / 2 ^ j) with h2 | h2 <;>
    rcases Nat.mod_two_eq_zero_or_one (x / 2 ^ j ^^^ y / 2 ^ j) with h3 | h3 <;>
    simp_all

/-- One pass: the low bits of `u`, `v`; add the place value `w` to `z` when they differ; `w := 2w`. -/
def xorBody : Sc :=
  .seq (.op (.dm xU v2 xQ xBu)) (.seq (.op (.copy xU xQ))
  (.seq (.op (.dm xV v2 xQ xBv)) (.seq (.op (.copy xV xQ))
  (.seq (.ite (.eq xBu xBv) (.op (.zero xQ)) (.op (.add xZ xW)))
  (.op (.shl xW))))))

/-- **Sum.** `xZ := (xX ⊕ xY) mod xT` for `xT = 2^k`. -/
def xorS : Sc :=
  .seq (.op (.copy xU xX)) (.seq (.op (.copy xV xY)) (.seq (.op (.zero xZ)) (.seq (.op (.zero xW))
  (.seq (.op (.inc xW)) (.loop (.lt xW xT) xorBody)))))

/-- The variables the sum changes. -/
def xorSet : List Var := [xZ, xU, xV, xW, xBu, xBv, xQ]

def xorCost (k : ℕ) : ℕ := 14 * k + 20

theorem xorTail (C : Ctx) (c : Ds) (x y j : ℕ) (hU : c.env xBu = (x / 2 ^ j) % 2)
    (hV : c.env xBv = (y / 2 ^ j) % 2) (hZ : c.env xZ = (x ^^^ y) % 2 ^ j) (hW : c.env xW = 2 ^ j)
    (hj : 2 ^ (j + 1) < 2 ^ C.Wd) :
    Runs C (.seq (.ite (.eq xBu xBv) (.op (.zero xQ)) (.op (.add xZ xW))) (.op (.shl xW))) c 4 [xZ, xW, xQ] []
      (fun d => d.env xZ = (x ^^^ y) % 2 ^ (j + 1) ∧ d.env xW = 2 ^ (j + 1)) := by
  have hzlt : (x ^^^ y) % 2 ^ j < 2 ^ j := Nat.mod_lt _ (by positivity)
  have hp : 2 ^ (j + 1) = 2 * 2 ^ j := by rw [pow_succ]; ring
  by_cases hb : (x / 2 ^ j) % 2 = (y / 2 ^ j) % 2
  · refine Runs.call0 (Runs.iteT (m := 2) (wf_eq (by decide))
      (by simp only [Cnd.eval, hU, hV, hb, decide_true]) (r_zero C [xZ, xW, xQ] c xQ (by decide)) (by norm_num))
      ?_ (by norm_num)
    rintro d - rfl
    refine Runs.last (r_shl C _ _ xW (by decide) (by norm_env; omega)) (fun _ => ?_) (by norm_num)
    norm_env
    rw [xor_mod_succ, if_pos hb, hZ, hW, hp]; simp
  · refine Runs.call0 (Runs.iteF (m := 2) (wf_eq (by decide))
      (by simp only [Cnd.eval, hU, hV, hb, decide_false]) (r_add C [xZ, xW, xQ] c xZ xW (by decide) (by decide)
        (by rw [hZ, hW]; omega)) (by norm_num)) ?_ (by norm_num)
    rintro d - rfl
    refine Runs.last (r_shl C _ _ xW (by decide) (by norm_env; omega)) (fun _ => ?_) (by norm_num)
    norm_env
    rw [xor_mod_succ, if_neg hb, hZ, hW, hp]
    exact ⟨rfl, rfl⟩

theorem xorS_spec (C : Ctx) (a : Ds) (k : ℕ) (h2 : a.env v2 = 2) (hT : a.env xT = 2 ^ k) (hk : k < C.Wd)
    (hW : 2 ≤ C.Wd) :
    Runs C xorS a (xorCost k) xorSet [] (fun b => b.env xZ = (a.env xX ^^^ a.env xY) % 2 ^ k) := by
  set x := a.env xX with hx
  set y := a.env xY with hy
  have hpk : 2 ^ k < 2 ^ C.Wd := Nat.pow_lt_pow_right (by norm_num) hk
  have h4 : 4 ≤ 2 ^ C.Wd := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ C.Wd := Nat.pow_le_pow_right (by norm_num) hW
  let Inv : ℕ → Ds → Prop := fun j b => b.env xU = x / 2 ^ j ∧ b.env xV = y / 2 ^ j ∧ b.env xW = 2 ^ j ∧
    b.env xZ = (x ^^^ y) % 2 ^ j ∧ b.env xT = 2 ^ k ∧ b.env v2 = 2
  have hloop : ∀ b, Inv 0 b → Runs C (.loop (.lt xW xT) xorBody) b (k * (12 + 2) + 2) xorSet [] (Inv k) := by
    refine Runs.loopN0 (wf_lt (by decide)) k 12 Inv ?_ ?_
    · intro j hj b ⟨b1, b2, b3, b4, b5, b6⟩
      have hjk : 2 ^ j < 2 ^ k := Nat.pow_lt_pow_right (by norm_num) hj
      have hj1 : 2 ^ (j + 1) ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hj
      refine ⟨by simp only [Cnd.eval, b3, b5, decide_eq_true_eq]; exact hjk, ?_⟩
      refine Runs.op1 (r_dm C xorSet b xU v2 xQ xBu (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by rw [b6]; norm_num) (by rw [b6]; omega)) ?_ (by norm_num)
      refine Runs.op1 (r_copy C xorSet _ xU xQ (by decide) (by decide)) ?_ (by norm_num)
      refine Runs.op1 (r_dm C xorSet _ xV v2 xQ xBv (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by norm_env; rw [b6]; norm_num)
        (by norm_env; rw [b6]; omega)) ?_ (by norm_num)
      refine Runs.op1 (r_copy C xorSet _ xV xQ (by decide) (by decide)) ?_ (by norm_num)
      refine Runs.lastS (xorTail C _ x y j (by norm_env; rw [b1, b6]) (by norm_env; rw [b2, b6])
        (by norm_env; rw [b4]) (by norm_env; rw [b3]) (by omega)) (by decide) (fun d hf hq => ?_) (by norm_num)
      refine ⟨?_, ?_, hq.2, hq.1, ?_, ?_⟩
      · rw [hf.env xU (by decide)]; norm_env; rw [b1, b6, Nat.div_div_eq_div_mul, ← pow_succ]
      · rw [hf.env xV (by decide)]; norm_env; rw [b2, b6, Nat.div_div_eq_div_mul, ← pow_succ]
      · rw [hf.env xT (by decide)]; norm_env; exact b5
      · rw [hf.env v2 (by decide)]; norm_env; exact b6
    · intro b ⟨_, _, b3, _, b5, _⟩
      simp only [Cnd.eval, b3, b5, lt_self_iff_false, decide_false]
  unfold xorS
  refine Runs.op1 (r_copy C xorSet a xU xX (by decide) (by decide)) ?_ (by unfold xorCost; omega)
  refine Runs.op1 (r_copy C xorSet _ xV xY (by decide) (by decide)) ?_ (by unfold xorCost; omega)
  refine Runs.op1 (r_zero C xorSet _ xZ (by decide)) ?_ (by unfold xorCost; omega)
  refine Runs.op1 (r_zero C xorSet _ xW (by decide)) ?_ (by unfold xorCost; omega)
  refine Runs.op1 (r_inc C xorSet _ xW (by decide) (by norm_env; omega)) ?_ (by unfold xorCost; omega)
  refine (hloop _ ?_).mono (by unfold xorCost; omega) (List.Subset.refl _) (fun b _ hb => hb.2.2.2.1.trans ?_)
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_env <;> simp [hT, h2, x, y, Nat.mod_one]
  · simp

/-! ## The field context -/

def lA : Var := ⟨30, by decide⟩
def vT : Var := ⟨31, by decide⟩
def vP : Var := ⟨32, by decide⟩
def mX : Var := ⟨33, by decide⟩
def mY : Var := ⟨34, by decide⟩
def mZ : Var := ⟨35, by decide⟩
def mAcc : Var := ⟨36, by decide⟩
def mYY : Var := ⟨37, by decide⟩
def mI : Var := ⟨38, by decide⟩
def mB : Var := ⟨39, by decide⟩
def mQ : Var := ⟨40, by decide⟩
def vM : Var := ⟨41, by decide⟩
def dX : Var := ⟨42, by decide⟩
def dY : Var := ⟨43, by decide⟩
def dB : Var := ⟨44, by decide⟩
def dU : Var := ⟨45, by decide⟩
def dV : Var := ⟨46, by decide⟩
def dI : Var := ⟨47, by decide⟩
def dQ : Var := ⟨48, by decide⟩
def dBu : Var := ⟨49, by decide⟩
def dBv : Var := ⟨50, by decide⟩
def dR : Var := ⟨51, by decide⟩

/-- The field `𝔽₂[X]/(p)` of degree `m` as the machine holds it: `vM = m`, `vT = 2^m`, `xT = 2^{m+1}` (the bound
of the sums), `vP = p`, and the constants `1`, `2`. -/
structure FCtx (a : Ds) (m p : ℕ) : Prop where
  one : a.env v1 = 1
  two : a.env v2 = 2
  M : a.env vM = m
  T : a.env vT = 2 ^ m
  T2 : a.env xT = 2 ^ (m + 1)
  P : a.env vP = p

/-- The variables of the field context. -/
def fctxVars : List Var := [v1, v2, vM, vT, xT, vP]

theorem FCtx.of_fx {a b : Ds} {m p : ℕ} {S : List Var} {w : List Bool} (h : FCtx a m p) (hf : Fx S w a b)
    (hS : ∀ x ∈ fctxVars, x ∉ S) : FCtx b m p :=
  ⟨by rw [hf.env _ (hS _ (by decide))]; exact h.one, by rw [hf.env _ (hS _ (by decide))]; exact h.two,
    by rw [hf.env _ (hS _ (by decide))]; exact h.M, by rw [hf.env _ (hS _ (by decide))]; exact h.T,
    by rw [hf.env _ (hS _ (by decide))]; exact h.T2, by rw [hf.env _ (hS _ (by decide))]; exact h.P⟩

theorem FCtx.set {a : Ds} {m p : ℕ} (h : FCtx a m p) (x : Var) (v : ℕ) (hx : x ∉ fctxVars) :
    FCtx (a.set x v) m p :=
  h.of_fx (Fx.set [x] a x v (by simp)) (fun y hy h' => hx (by simp at h'; exact h' ▸ hy))

theorem FCtx.emit {a : Ds} {m p : ℕ} (h : FCtx a m p) (bit : Bool) :
    FCtx { a with out := a.out ++ [bit] } m p := ⟨h.one, h.two, h.M, h.T, h.T2, h.P⟩

/-! ## One LFSR step: `lA := lfsr p m lA` -/

theorem testBit_two_mul {a m : ℕ} (ha : a < 2 ^ m) : (2 * a).testBit m = decide (2 ^ m ≤ 2 * a) := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  have h2 : 2 * a < 2 * 2 ^ m := by omega
  have hq : 2 * a / 2 ^ m < 2 := (Nat.div_lt_iff_lt_mul (by positivity)).2 h2
  by_cases h : 2 ^ m ≤ 2 * a
  · have : 1 ≤ 2 * a / 2 ^ m := (Nat.le_div_iff_mul_le (by positivity)).2 (by simpa using h)
    simp only [h, decide_true, decide_eq_true_eq]
    omega
  · have : 2 * a / 2 ^ m = 0 := Nat.div_eq_of_lt (by omega)
    simp [this, h]

theorem lfsr_eq {p m a : ℕ} (ha : a < 2 ^ m) (hp : p < 2 ^ (m + 1)) :
    GF2.lfsr p m a = if 2 * a < 2 ^ m then 2 * a else (2 * a ^^^ p) % 2 ^ (m + 1) := by
  unfold GF2.lfsr
  rw [testBit_two_mul ha]
  have h2 : 2 * a < 2 ^ (m + 1) := by rw [pow_succ]; omega
  by_cases h : 2 * a < 2 ^ m
  · simp [h]
  · simp only [show 2 ^ m ≤ 2 * a by omega, decide_true, if_true, h, if_false]
    rw [Nat.mod_eq_of_lt (Nat.xor_lt_two_pow h2 hp)]

/-- **One LFSR step.** -/
def lfsrS : Sc :=
  .seq (.op (.shl lA)) (.ite (.lt lA vT) (.op (.zero xQ))
    (.seq (.op (.copy xX lA)) (.seq (.op (.copy xY vP)) (.seq xorS (.op (.copy lA xZ))))))

def lfsrSet : List Var := [lA, xX, xY, xZ, xU, xV, xW, xBu, xBv, xQ]

def lfsrCost (m : ℕ) : ℕ := xorCost (m + 1) + 10

theorem lfsrS_spec (C : Ctx) (a : Ds) (m p : ℕ) (hc : FCtx a m p) (ha : a.env lA < 2 ^ m)
    (hp : p < 2 ^ (m + 1)) (hm : m + 1 < C.Wd) (hW : 2 ≤ C.Wd) :
    Runs C lfsrS a (lfsrCost m) lfsrSet [] (fun b => b.env lA = GF2.lfsr p m (a.env lA)) := by
  have hpw : 2 ^ (m + 1) < 2 ^ C.Wd := Nat.pow_lt_pow_right (by norm_num) hm
  have h2a : 2 * a.env lA < 2 ^ (m + 1) := by rw [pow_succ]; omega
  unfold lfsrS
  refine Runs.op1 (r_shl C lfsrSet a lA (by decide) (by omega)) ?_ (by unfold lfsrCost xorCost; omega)
  rw [lfsr_eq ha hp]
  by_cases h : 2 * a.env lA < 2 ^ m
  · refine Runs.iteT (wf_lt (by decide)) (by norm_env; rw [hc.T]; simpa using h) ?_ (by unfold lfsrCost xorCost; omega)
    refine Runs.last (r_zero C lfsrSet _ xQ (by decide)) (fun _ => ?_) (by unfold lfsrCost xorCost; omega)
    norm_env; simp [h]
  · refine Runs.iteF (wf_lt (by decide)) (by norm_env; rw [hc.T]; simpa using h) ?_ (by unfold lfsrCost xorCost; omega)
    refine Runs.op1 (r_copy C lfsrSet _ xX lA (by decide) (by decide)) ?_ (by unfold lfsrCost xorCost; omega)
    refine Runs.op1 (r_copy C lfsrSet _ xY vP (by decide) (by decide)) ?_ (by unfold lfsrCost xorCost; omega)
    refine Runs.callS0 (xorS_spec C _ (m + 1) (by norm_env; exact hc.two) (by norm_env; exact hc.T2) hm hW)
      (by decide) (fun b hf hb => ?_) (by unfold lfsrCost; omega)
    refine Runs.last (r_copy C lfsrSet _ lA xZ (by decide) (by decide)) (fun _ => ?_) (by unfold lfsrCost; omega)
    norm_env
    rw [hb]; norm_env; rw [hc.P]; simp [h]

/-! ## The product: `mZ := fmulShift p m mX mY` -/

theorem div_two_pow_mod_two (n j : ℕ) : n / 2 ^ j % 2 = (n.testBit j).toNat := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (n / 2 ^ j) with h | h <;> simp [h]

/-- One pass of the product (`GF.mulStep`): bit `j` of `y` adds the shifted `x` to the accumulator; `x := x·X`. -/
def mulBody : Sc :=
  .seq (.op (.dm mYY v2 mQ mB)) (.seq (.op (.copy mYY mQ))
  (.seq (.ite (.eq mB v1) (.seq (.op (.copy xX mAcc)) (.seq (.op (.copy xY lA)) (.seq xorS (.op (.copy mAcc xZ)))))
      (.op (.zero mQ)))
  (.seq lfsrS (.op (.inc mI)))))

/-- **Product.** `mZ := fmulShift p m mX mY` (`vM = m`). -/
def fmulS : Sc :=
  .seq (.op (.zero mAcc)) (.seq (.op (.copy lA mX)) (.seq (.op (.copy mYY mY)) (.seq (.op (.zero mI))
  (.seq (.loop (.lt mI vM) mulBody) (.op (.copy mZ mAcc))))))

def fmulSet : List Var := [mZ, mAcc, mYY, mI, mB, mQ, lA, xX, xY, xZ, xU, xV, xW, xBu, xBv, xQ]

def mulPass (m : ℕ) : ℕ := xorCost (m + 1) + lfsrCost m + 20

def fmulCost (m : ℕ) : ℕ := m * (mulPass m + 2) + 20

theorem fmulS_spec (C : Ctx) (a : Ds) (m p : ℕ) (hc : FCtx a m p) (hp : 1 ≤ m → GF.ModulusOk p m)
    (hx : 1 ≤ m → a.env mX < 2 ^ m) (hm : m + 1 < C.Wd) (hW : 2 ≤ C.Wd) :
    Runs C fmulS a (fmulCost m) fmulSet []
      (fun b => b.env mZ = GF2.fmulShift p m (a.env mX) (a.env mY)) := by
  set x := a.env mX with hxdef
  set y := a.env mY with hydef
  have hpw : 2 ^ (m + 1) < 2 ^ C.Wd := Nat.pow_lt_pow_right (by norm_num) hm
  have h4 : 4 ≤ 2 ^ C.Wd := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ C.Wd := Nat.pow_le_pow_right (by norm_num) hW
  have hm2 : 2 ^ m < 2 ^ (m + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  let st : ℕ → ℕ × ℕ := fun j => (List.range j).foldl (GF.mulStep p m y) (0, x)
  let Inv : ℕ → Ds → Prop := fun j b => FCtx b m p ∧ b.env mAcc = (st j).1 ∧ b.env lA = (st j).2 ∧
    b.env mYY = y / 2 ^ j ∧ b.env mI = j
  have hloop : ∀ b, Inv 0 b →
      Runs C (.loop (.lt mI vM) mulBody) b (m * (mulPass m + 2) + 2) fmulSet [] (Inv m) := by
    refine Runs.loopN0 (wf_lt (by decide)) m (mulPass m) Inv ?_ ?_
    · intro j hj b ⟨b0, b1, b2, b3, b4⟩
      obtain ⟨f1, f2, -, -⟩ := GF.mulStep_fold p m x y (hp (by omega)) (hx (by omega)) j
      refine ⟨by simp only [eval_lt, b4, b0.M, decide_eq_true_eq]; exact hj, ?_⟩
      unfold mulBody
      refine Runs.op1 (r_dm C fmulSet b mYY v2 mQ mB (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by rw [b0.two]; norm_num) (by rw [b0.two]; omega)) ?_
        (by unfold mulPass; omega)
      refine Runs.op1 (r_copy C fmulSet _ mYY mQ (by decide) (by decide)) ?_ (by unfold mulPass; omega)
      have hbit : (y.testBit j) = decide (y / 2 ^ j % 2 = 1) := Nat.testBit_eq_decide_div_mod_eq
      -- the conditional sum, then the shift
      refine Runs.call0 (n := xorCost (m + 1) + 7) (Q1 := fun c => FCtx c m p ∧ c.env mAcc = (st (j + 1)).1 ∧
        c.env lA = (st j).2 ∧ c.env mYY = y / 2 ^ (j + 1) ∧ c.env mI = j) ?_ (fun c _ ⟨c0, c1, c2, c3, c4⟩ => ?_)
        (by unfold mulPass lfsrCost; omega)
      · by_cases hb : y.testBit j
        · refine Runs.iteT (wf_eq (by decide)) (by norm_env; rw [b0.one, b3, b0.two]; simpa [hbit] using hb) ?_
            (by omega)
          refine Runs.op1 (r_copy C fmulSet _ xX mAcc (by decide) (by decide)) ?_ (by omega)
          refine Runs.op1 (r_copy C fmulSet _ xY lA (by decide) (by decide)) ?_ (by omega)
          refine Runs.callS0 (xorS_spec C _ (m + 1) (by norm_env; exact b0.two) (by norm_env; exact b0.T2) hm hW)
            (by decide) (fun d hf hd => ?_) (by omega)
          refine Runs.last (r_copy C fmulSet _ mAcc xZ (by decide) (by decide)) (fun _ => ?_) (by omega)
          refine ⟨?_, ?_, ?_, ?_, ?_⟩
          · exact ((b0.set _ _ (by decide)).set _ _ (by decide) |>.set _ _ (by decide) |>.set _ _ (by decide)
              |>.set _ _ (by decide) |>.of_fx hf (by decide)).set _ _ (by decide)
          · norm_env; rw [hd]; norm_env
            rw [b1, b2, Nat.mod_eq_of_lt (Nat.xor_lt_two_pow (f1.trans hm2) (f2.trans hm2))]
            simp only [st, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
              GF.mulStep_fst, hb, if_true]
          · norm_env; rw [hf.env lA (by decide)]; norm_env; exact b2
          · norm_env; rw [hf.env mYY (by decide)]; norm_env
            rw [b3, b0.two, Nat.div_div_eq_div_mul, ← pow_succ]
          · norm_env; rw [hf.env mI (by decide)]; norm_env; exact b4
        · refine Runs.iteF (wf_eq (by decide)) (by norm_env; rw [b0.one, b3, b0.two]; simpa [hbit] using hb) ?_
            (by omega)
          refine Runs.last (r_zero C fmulSet _ mQ (by decide)) (fun _ => ?_) (by omega)
          refine ⟨((b0.set _ _ (by decide)).set _ _ (by decide) |>.set _ _ (by decide)).set _ _ (by decide),
            ?_, ?_, ?_, ?_⟩
          · norm_env; rw [b1]
            simp only [st, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
              GF.mulStep_fst, hb]
            simp
          · norm_env; exact b2
          · norm_env; rw [b3, b0.two, Nat.div_div_eq_div_mul, ← pow_succ]
          · norm_env; exact b4
      · refine Runs.callS0 (lfsrS_spec C c m p c0 (by rw [c2]; exact f2) (by
            have := (hp (by omega)).2; exact this) hm hW) (by decide) (fun d hf hd => ?_) (by unfold mulPass; omega)
        refine Runs.last (r_inc C fmulSet _ mI (by decide) (by
            rw [hf.env mI (by decide), c4]
            have : j + 1 < 2 ^ (m + 1) := by
              have := Nat.lt_two_pow_self (n := m); rw [pow_succ]; omega
            omega)) (fun _ => ?_) (by unfold mulPass; omega)
        refine ⟨(c0.of_fx hf (by decide)).set _ _ (by decide), ?_, ?_, ?_, ?_⟩
        · norm_env; rw [hf.env mAcc (by decide), c1]
        · norm_env; rw [hd, c2]
          simp only [st, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
            GF.mulStep_snd]
        · norm_env; rw [hf.env mYY (by decide), c3]
        · norm_env; rw [hf.env mI (by decide), c4]
    · intro b ⟨b0, _, _, _, b4⟩
      simp [b4, b0.M]
  unfold fmulS
  refine Runs.op1 (r_zero C fmulSet a mAcc (by decide)) ?_ (by unfold fmulCost; omega)
  refine Runs.op1 (r_copy C fmulSet _ lA mX (by decide) (by decide)) ?_ (by unfold fmulCost; omega)
  refine Runs.op1 (r_copy C fmulSet _ mYY mY (by decide) (by decide)) ?_ (by unfold fmulCost; omega)
  refine Runs.op1 (r_zero C fmulSet _ mI (by decide)) ?_ (by unfold fmulCost; omega)
  refine Runs.call0 (hloop _ ?_) (fun b _ ⟨_, b1, _, _, _⟩ => ?_) (by unfold fmulCost; omega)
  · refine ⟨((hc.set _ _ (by decide)).set _ _ (by decide) |>.set _ _ (by decide)).set _ _ (by decide),
      ?_, ?_, ?_, ?_⟩ <;> norm_env <;> simp [st, x, y]
  · refine Runs.last (r_copy C fmulSet _ mZ mAcc (by decide) (by decide)) (fun _ => ?_) (by unfold fmulCost; omega)
    norm_env; rw [b1, GF.fmulShift_eq]

/-! ## The inner product of masks: `dB := (Σ_{i<m} x_i y_i) mod 2` -/

/-- The parity of the common ones of the low `j` bits of `x` and `y`. -/
def dotPar (x y j : ℕ) : ℕ := (∑ i ∈ Finset.range j, (x.testBit i && y.testBit i).toNat) % 2

theorem dotPar_succ (x y j : ℕ) :
    dotPar x y (j + 1) = (dotPar x y j + (x / 2 ^ j % 2) * (y / 2 ^ j % 2)) % 2 := by
  unfold dotPar
  rw [Finset.sum_range_succ, div_two_pow_mod_two, div_two_pow_mod_two, Nat.mod_add_mod]
  congr 2
  cases x.testBit j <;> cases y.testBit j <;> rfl

/-- One pass: the low bits of `u`, `v`; `B := (B + u₀v₀) mod 2`. -/
def dotBody : Sc :=
  .seq (.op (.dm dU v2 dQ dBu)) (.seq (.op (.copy dU dQ))
  (.seq (.op (.dm dV v2 dQ dBv)) (.seq (.op (.copy dV dQ))
  (.seq (.op (.mul dBu dBv dQ)) (.seq (.op (.add dB dQ))
  (.seq (.op (.dm dB v2 dQ dR)) (.seq (.op (.copy dB dR)) (.op (.inc dI)))))))))

/-- **Inner product.** `dB := (Σ_{i<m} dX_i dY_i) mod 2` (`vM = m`). -/
def dotS : Sc :=
  .seq (.op (.copy dU dX)) (.seq (.op (.copy dV dY)) (.seq (.op (.zero dB)) (.seq (.op (.zero dI))
  (.loop (.lt dI vM) dotBody))))

def dotSet : List Var := [dB, dU, dV, dI, dQ, dBu, dBv, dR]

def dotCost (m : ℕ) : ℕ := 19 * m + 10

theorem dotS_spec (C : Ctx) (a : Ds) (m p : ℕ) (hc : FCtx a m p) (hm : m + 1 < C.Wd) (hW : 2 ≤ C.Wd) :
    Runs C dotS a (dotCost m) dotSet [] (fun b => b.env dB = dotPar (a.env dX) (a.env dY) m) := by
  set x := a.env dX with hxdef
  set y := a.env dY with hydef
  have h4 : 4 ≤ 2 ^ C.Wd := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ C.Wd := Nat.pow_le_pow_right (by norm_num) hW
  have hmW : m + 1 < 2 ^ C.Wd := lt_of_lt_of_le (by omega) (Nat.lt_two_pow_self (n := C.Wd)).le
  let Inv : ℕ → Ds → Prop := fun j b => FCtx b m p ∧ b.env dU = x / 2 ^ j ∧ b.env dV = y / 2 ^ j ∧
    b.env dI = j ∧ b.env dB = dotPar x y j
  have hloop : ∀ b, Inv 0 b → Runs C (.loop (.lt dI vM) dotBody) b (m * (17 + 2) + 2) dotSet [] (Inv m) := by
    refine Runs.loopN0 (wf_lt (by decide)) m 17 Inv ?_ ?_
    · intro j hj b ⟨b0, b1, b2, b3, b4⟩
      have hp1 : dotPar x y j < 2 := Nat.mod_lt _ (by norm_num)
      have hu : x / 2 ^ j % 2 ≤ 1 := by omega
      have hv : y / 2 ^ j % 2 ≤ 1 := by omega
      have huv : (x / 2 ^ j % 2) * (y / 2 ^ j % 2) ≤ 1 := by
        have := Nat.mul_le_mul hu hv; simpa using this
      refine ⟨by simp only [eval_lt, b3, b0.M, decide_eq_true_eq]; exact hj, ?_⟩
      unfold dotBody
      have f0 := Fx.refl dotSet b
      refine Runs.op1B f0 (r_dm C dotSet b dU v2 dQ dBu (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by rw [b0.two]; norm_num) (by rw [b0.two]; omega))
        (fun f0 => ?_) (by norm_num)
      refine Runs.op1B f0 (r_copy C dotSet _ dU dQ (by decide) (by decide)) (fun f0 => ?_) (by norm_num)
      refine Runs.op1B f0 (r_dm C dotSet _ dV v2 dQ dBv (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by norm_env; rw [b0.two]; norm_num)
        (by norm_env; rw [b0.two]; omega)) (fun f0 => ?_) (by norm_num)
      refine Runs.op1B f0 (r_copy C dotSet _ dV dQ (by decide) (by decide)) (fun f0 => ?_) (by norm_num)
      refine Runs.op1B f0 (r_mul C dotSet _ dBu dBv dQ (by decide) (by decide) (by decide) (by decide)
        (by norm_env; rw [b1, b2, b0.two]; omega)) (fun f0 => ?_) (by norm_num)
      refine Runs.op1B f0 (r_add C dotSet _ dB dQ (by decide) (by decide)
        (by norm_env; rw [b1, b2, b4, b0.two]; omega)) (fun f0 => ?_) (by norm_num)
      refine Runs.op1B f0 (r_dm C dotSet _ dB v2 dQ dR (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by norm_env; rw [b0.two]; norm_num)
        (by norm_env; rw [b0.two]; omega)) (fun f0 => ?_) (by norm_num)
      refine Runs.op1B f0 (r_copy C dotSet _ dB dR (by decide) (by decide)) (fun f0 => ?_) (by norm_num)
      refine Runs.lastB f0 (r_inc C dotSet _ dI (by decide) (by norm_env; rw [b3]; omega)) (fun f0 => ?_)
        (by norm_num)
      refine ⟨b0.of_fx f0 (by decide), ?_, ?_, ?_, ?_⟩
      · norm_env; rw [b1, b0.two, Nat.div_div_eq_div_mul, ← pow_succ]
      · norm_env; rw [b2, b0.two, Nat.div_div_eq_div_mul, ← pow_succ]
      · norm_env; rw [b3]
      · norm_env; rw [b1, b2, b4, b0.two, dotPar_succ]
    · intro b ⟨b0, _, _, b3, _⟩
      simp [b3, b0.M]
  unfold dotS
  refine Runs.op1 (r_copy C dotSet a dU dX (by decide) (by decide)) ?_ (by unfold dotCost; omega)
  refine Runs.op1 (r_copy C dotSet _ dV dY (by decide) (by decide)) ?_ (by unfold dotCost; omega)
  refine Runs.op1 (r_zero C dotSet _ dB (by decide)) ?_ (by unfold dotCost; omega)
  refine Runs.op1 (r_zero C dotSet _ dI (by decide)) ?_ (by unfold dotCost; omega)
  refine (hloop _ ?_).mono (by unfold dotCost; omega) (List.Subset.refl _) (fun b _ hb => hb.2.2.2.2)
  refine ⟨((hc.set _ _ (by decide)).set _ _ (by decide) |>.set _ _ (by decide)).set _ _ (by decide),
    ?_, ?_, ?_, ?_⟩ <;> norm_env <;> simp [x, y, dotPar]

end NearCubicGates.Adapters.ShortPCP.MaskMachine
