import SourceAdapters.ShortPCP.MaskMachineField
import Proof.Wire_3_5.GFExists

/-!
# The mask machine: the exhaustive search for the modulus

 (proof of `lem:small-bias`): "Find an irreducible polynomial of degree `m` over `𝔽₂` by exhaustive
search … and identify `𝔽_{2^m}` with `𝔽₂^m`." The modulus of Step 3 is `Amplified.modulus m = GF.firstPrimitive m`
(`Joins/AmplifiedVerifier.lean:47`), the first `p = 2^m + j` whose LFSR orbit of `1` has period `2^m − 1`
(`GF.PrimitiveCert`, L `Shared/GF.lean:281`; the search of `Joins/BinaryFieldArithmetic.lean`). This module computes
it in the cell language by its definition:
- `perS`: `pPer := GF2.period p m` (the first return of the orbit of `1`, iterating `lfsrS`);
- `srchS`: `vP := GF.firstPrimitive m` (`j = 0, 1, …` until the period is `2^m − 1`).
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.ShortPCP.MaskMachine

open NearCubicGates.Close.Cells NearCubicWires.WireExponent3_5

/-! ## The reference facts -/

theorem period_eq_of_first {p m i : ℕ} (hi1 : 1 ≤ i) (hi : i < 2 ^ m) (h1 : GF2.lfsrPow p m i = 1)
    (hlt : ∀ j, 1 ≤ j → j < i → GF2.lfsrPow p m j ≠ 1) : GF2.period p m = i := by
  unfold GF2.period
  have : (List.range (2 ^ m)).find? (fun j => j ≠ 0 && GF2.lfsrPow p m j == 1) = some i := by
    rw [List.find?_range_eq_some]
    refine ⟨by simp [h1]; omega, List.mem_range.2 hi, fun j hj => ?_⟩
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · simp
    · simp [hlt j hj0 hj]
  rw [this]; rfl

theorem period_eq_zero {p m : ℕ} (h : ∀ j, 1 ≤ j → j < 2 ^ m → GF2.lfsrPow p m j ≠ 1) : GF2.period p m = 0 := by
  unfold GF2.period
  have : (List.range (2 ^ m)).find? (fun j => j ≠ 0 && GF2.lfsrPow p m j == 1) = none := by
    rw [List.find?_range_eq_none]
    intro i hi
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · simp
    · simp [h i hi0 hi]
  rw [this]; rfl

theorem period_lt (p m : ℕ) : GF2.period p m < 2 ^ m := by
  unfold GF2.period
  cases h : (List.range (2 ^ m)).find? (fun j => j ≠ 0 && GF2.lfsrPow p m j == 1) with
  | none => simp
  | some i =>
    rw [List.find?_range_eq_some] at h
    simpa using h.2.1

theorem modulusOk_add {m j : ℕ} (hj : j < 2 ^ m) : GF.ModulusOk (2 ^ m + j) m := by
  refine ⟨?_, by rw [pow_succ]; omega⟩
  rw [Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hj]; rfl

theorem cert_iff {m j : ℕ} (hm : 1 ≤ m) (hj : j < 2 ^ m) :
    GF.PrimitiveCert (2 ^ m + j) m ↔ GF2.period (2 ^ m + j) m + 1 = 2 ^ m := by
  have h1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  unfold GF.PrimitiveCert
  constructor
  · rintro ⟨-, -, h⟩; omega
  · intro h; exact ⟨hm, modulusOk_add hj, by omega⟩

theorem firstPrimitive_eq_of {m j : ℕ} (hj : j < 2 ^ m) (hc : GF.PrimitiveCert (2 ^ m + j) m)
    (hlt : ∀ i < j, ¬ GF.PrimitiveCert (2 ^ m + i) m) : GF.firstPrimitive m = 2 ^ m + j := by
  unfold GF.firstPrimitive
  have : (List.range (2 ^ m)).find? (fun j => decide (GF.PrimitiveCert (2 ^ m + j) m)) = some j := by
    rw [List.find?_range_eq_some]
    exact ⟨by simpa using hc, List.mem_range.2 hj, fun i hi => by simpa using hlt i hi⟩
  rw [this]; rfl

theorem firstPrimitive_eq_none {m : ℕ} (h : ∀ i < 2 ^ m, ¬ GF.PrimitiveCert (2 ^ m + i) m) :
    GF.firstPrimitive m = 2 ^ m := by
  unfold GF.firstPrimitive
  have : (List.range (2 ^ m)).find? (fun j => decide (GF.PrimitiveCert (2 ^ m + j) m)) = none := by
    rw [List.find?_range_eq_none]
    intro i hi; simpa using h i hi
  rw [this]; rfl

/-! ## The field context without the modulus -/

/-- `vM = m`, `vT = 2^m`, `xT = 2^{m+1}` and the constants (the modulus variable is free). -/
structure FBase (a : Ds) (m : ℕ) : Prop where
  one : a.env v1 = 1
  two : a.env v2 = 2
  M : a.env vM = m
  T : a.env vT = 2 ^ m
  T2 : a.env xT = 2 ^ (m + 1)

def fbaseVars : List Var := [v1, v2, vM, vT, xT]

theorem FBase.of_fx {a b : Ds} {m : ℕ} {S : List Var} {w : List Bool} (h : FBase a m) (hf : Fx S w a b)
    (hS : ∀ x ∈ fbaseVars, x ∉ S) : FBase b m :=
  ⟨by rw [hf.env _ (hS _ (by decide))]; exact h.one, by rw [hf.env _ (hS _ (by decide))]; exact h.two,
    by rw [hf.env _ (hS _ (by decide))]; exact h.M, by rw [hf.env _ (hS _ (by decide))]; exact h.T,
    by rw [hf.env _ (hS _ (by decide))]; exact h.T2⟩

theorem FBase.withP {a : Ds} {m p : ℕ} (h : FBase a m) (hP : a.env vP = p) : FCtx a m p :=
  ⟨h.one, h.two, h.M, h.T, h.T2, hP⟩

theorem FCtx.base {a : Ds} {m p : ℕ} (h : FCtx a m p) : FBase a m := ⟨h.one, h.two, h.M, h.T, h.T2⟩

/-! ## The period of the orbit of `1` -/

def pI : Var := ⟨52, by decide⟩
def pPer : Var := ⟨53, by decide⟩
def sJ : Var := ⟨54, by decide⟩
def sBest : Var := ⟨55, by decide⟩
def sTmp : Var := ⟨56, by decide⟩

/-- One pass: `A := A·X`; at the first return to `1` record the index and stop. -/
def perBody : Sc :=
  .seq lfsrS (.ite (.eq lA v1) (.seq (.op (.copy pPer pI)) (.op (.copy pI vT))) (.op (.inc pI)))

/-- **Period.** `pPer := GF2.period p m` for the modulus `vP = p`. -/
def perS : Sc :=
  .seq (.op (.copy lA v1)) (.seq (.op (.copy pI v1)) (.seq (.op (.zero pPer)) (.loop (.lt pI vT) perBody)))

def perSet : List Var := [pPer, pI, lA, xX, xY, xZ, xU, xV, xW, xBu, xBv, xQ]

def perPass (m : ℕ) : ℕ := lfsrCost m + 6

def perCost (m : ℕ) : ℕ := 2 ^ m * (perPass m + 2) + 10

theorem perS_spec (C : Ctx) (a : Ds) (m p : ℕ) (hc : FCtx a m p) (hm1 : 1 ≤ m) (hp : GF.ModulusOk p m)
    (hm : m + 1 < C.Wd) (hW : 2 ≤ C.Wd) :
    Runs C perS a (perCost m) perSet [] (fun b => b.env pPer = GF2.period p m) := by
  have hpw : 2 ^ (m + 1) < 2 ^ C.Wd := Nat.pow_lt_pow_right (by norm_num) hm
  have hm2 : 2 ^ m < 2 ^ (m + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hT1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  let Inv : Ds → Prop := fun b => FCtx b m p ∧ ((b.env pI = 2 ^ m ∧ b.env pPer = GF2.period p m) ∨
    (1 ≤ b.env pI ∧ b.env pI ≤ 2 ^ m ∧ b.env lA = GF2.lfsrPow p m (b.env pI - 1) ∧ b.env pPer = 0 ∧
      ∀ j, 1 ≤ j → j < b.env pI → GF2.lfsrPow p m j ≠ 1))
  have hloop : ∀ b, Inv b → Runs C (.loop (.lt pI vT) perBody) b ((2 ^ m - b.env pI) * (perPass m + 2) + 2)
      perSet [] (fun b => Inv b ∧ (Cnd.lt pI vT).eval b = false) := by
    intro b0 hb0
    refine Runs.loopWF (wf_lt (by decide)) Inv (fun b => 2 ^ m - b.env pI) (perPass m) b0
      (fun b _ hb hev => ?_) hb0
    obtain ⟨c0, hcase⟩ := hb
    have hlt : b.env pI < 2 ^ m := by simpa [c0.T] using hev
    rcases hcase with ⟨h1, -⟩ | ⟨i1, i2, i3, i4, i5⟩
    · omega
    set i := b.env pI with hi
    have hA : b.env lA < 2 ^ m := by rw [i3]; exact (GF.lfsrPow_spec p m hp hm1 _).1
    unfold perBody
    refine Runs.callS0B (Fx.refl perSet b) (lfsrS_spec C b m p c0 hA (hp.2) hm hW) (by decide)
      (fun c fl f0 hq => ?_) (by unfold perPass; omega)
    have hpow : c.env lA = GF2.lfsrPow p m i := by
      rw [hq, i3, show i = (i - 1) + 1 by omega]; rfl
    have cc : FCtx c m p := c0.of_fx f0 (by decide)
    have hcI : c.env pI = i := by rw [fl.env pI (by decide)]
    by_cases h1 : GF2.lfsrPow p m i = 1
    · refine Runs.iteT (wf_eq (by decide)) (by simp [hpow, cc.one, h1]) ?_ (by unfold perPass; omega)
      refine Runs.op1B f0 (r_copy C perSet _ pPer pI (by decide) (by decide)) (fun f1 => ?_)
        (by unfold perPass; omega)
      refine Runs.lastB f1 (r_copy C perSet _ pI vT (by decide) (by decide)) (fun f2 => ?_)
        (by unfold perPass; omega)
      refine ⟨⟨c0.of_fx f2 (by decide), Or.inl ⟨?_, ?_⟩⟩, ?_⟩
      · norm_env; exact cc.T
      · norm_env; rw [hcI]; exact (period_eq_of_first i1 hlt h1 i5).symm
      · norm_env; rw [cc.T]; omega
    · refine Runs.iteF (wf_eq (by decide)) (by simp [hpow, cc.one, h1]) ?_ (by unfold perPass; omega)
      refine Runs.lastB f0 (r_inc C perSet _ pI (by decide) (by rw [hcI]; omega)) (fun f1 => ?_)
        (by unfold perPass; omega)
      refine ⟨⟨c0.of_fx f1 (by decide), Or.inr ⟨?_, ?_, ?_, ?_, ?_⟩⟩, ?_⟩
      · norm_env; omega
      · norm_env; rw [hcI]; omega
      · norm_env; rw [hpow, hcI]; simp
      · norm_env; rw [fl.env pPer (by decide), i4]
      · norm_env; rw [hcI]
        intro j hj1 hj
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
        · exact i5 j hj1 hj
        · exact h1
      · norm_env; rw [hcI]; omega
  unfold perS
  have f0 := Fx.refl perSet a
  refine Runs.op1B f0 (r_copy C perSet a lA v1 (by decide) (by decide)) (fun f0 => ?_) (by unfold perCost; omega)
  refine Runs.op1B f0 (r_copy C perSet _ pI v1 (by decide) (by decide)) (fun f0 => ?_) (by unfold perCost; omega)
  refine Runs.op1B f0 (r_zero C perSet _ pPer (by decide)) (fun f0 => ?_) (by unfold perCost; omega)
  have hI : Inv (((a.set lA (a.env v1)).set pI ((a.set lA (a.env v1)).env v1)).set pPer 0) := by
    refine ⟨hc.of_fx f0 (by decide), Or.inr ⟨?_, ?_, ?_, ?_, ?_⟩⟩ <;> norm_env <;> simp [hc.one, GF2.lfsrPow]
    · exact hT1
    · intro j hj1 hj; omega
  refine (hloop _ hI).mono ?_ (List.Subset.refl _) (fun b _ ⟨⟨b0, hcase⟩, hev⟩ => ?_)
  · have : (2 ^ m - (((a.set lA (a.env v1)).set pI ((a.set lA (a.env v1)).env v1)).set pPer 0).env pI) ≤ 2 ^ m :=
      Nat.sub_le _ _
    have := Nat.mul_le_mul_right (perPass m + 2) this
    unfold perCost; omega
  · have hge : 2 ^ m ≤ b.env pI := by simpa [b0.T] using hev
    rcases hcase with ⟨-, h2⟩ | ⟨-, i2, -, i4, i5⟩
    · exact h2
    · rw [i4, period_eq_zero (fun j hj1 hj => i5 j hj1 (by omega))]

/-! ## The exhaustive search -/

/-- One pass: the candidate `p = 2^m + j`; its period; stop at the first certified candidate. -/
def srchBody : Sc :=
  .seq (.op (.copy vP vT)) (.seq (.op (.add vP sJ)) (.seq perS (.seq (.op (.copy sTmp pPer))
    (.seq (.op (.inc sTmp)) (.ite (.eq sTmp vT) (.seq (.op (.copy sBest vP)) (.op (.copy sJ vT)))
      (.op (.inc sJ)))))))

/-- **Search.** `vP := GF.firstPrimitive m`. -/
def srchS : Sc :=
  .seq (.op (.zero sJ)) (.seq (.op (.copy sBest vT)) (.seq (.loop (.lt sJ vT) srchBody) (.op (.copy vP sBest))))

def srchSet : List Var := [vP, sJ, sBest, sTmp, pPer, pI, lA, xX, xY, xZ, xU, xV, xW, xBu, xBv, xQ]

def srchPass (m : ℕ) : ℕ := perCost m + 20

def srchCost (m : ℕ) : ℕ := 2 ^ m * (srchPass m + 2) + 10

theorem srchS_spec (C : Ctx) (a : Ds) (m : ℕ) (hc : FBase a m) (hm1 : 1 ≤ m) (hm : m + 1 < C.Wd)
    (hW : 2 ≤ C.Wd) :
    Runs C srchS a (srchCost m) srchSet [] (fun b => b.env vP = GF.firstPrimitive m) := by
  have hpw : 2 ^ (m + 1) < 2 ^ C.Wd := Nat.pow_lt_pow_right (by norm_num) hm
  have hm2 : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [pow_succ]; ring
  have hT1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  let Inv : Ds → Prop := fun b => FBase b m ∧ ((b.env sJ = 2 ^ m ∧ b.env sBest = GF.firstPrimitive m) ∨
    (b.env sJ ≤ 2 ^ m ∧ b.env sBest = 2 ^ m ∧ ∀ j < b.env sJ, ¬ GF.PrimitiveCert (2 ^ m + j) m))
  have hloop : ∀ b, Inv b → Runs C (.loop (.lt sJ vT) srchBody) b ((2 ^ m - b.env sJ) * (srchPass m + 2) + 2)
      srchSet [] (fun b => Inv b ∧ (Cnd.lt sJ vT).eval b = false) := by
    intro b0 hb0
    refine Runs.loopWF (wf_lt (by decide)) Inv (fun b => 2 ^ m - b.env sJ) (srchPass m) b0
      (fun b _ hb hev => ?_) hb0
    obtain ⟨c0, hcase⟩ := hb
    have hlt : b.env sJ < 2 ^ m := by simpa [c0.T] using hev
    rcases hcase with ⟨h1, -⟩ | ⟨i2, i3, i4⟩
    · omega
    set j := b.env sJ with hj
    unfold srchBody
    have f0 := Fx.refl srchSet b
    refine Runs.op1B f0 (r_copy C srchSet b vP vT (by decide) (by decide)) (fun f0 => ?_)
      (by unfold srchPass; omega)
    refine Runs.op1B f0 (r_add C srchSet _ vP sJ (by decide) (by decide) (by norm_env; rw [c0.T]; omega))
      (fun f0 => ?_) (by unfold srchPass; omega)
    have hP : FCtx ((b.set vP (b.env vT)).set vP ((b.set vP (b.env vT)).env vP +
        (b.set vP (b.env vT)).env sJ)) m (2 ^ m + j) :=
      (c0.of_fx f0 (by decide)).withP (by norm_env; rw [c0.T])
    refine Runs.callS0B f0 (perS_spec C _ m (2 ^ m + j) hP hm1 (modulusOk_add hlt) hm hW) (by decide)
      (fun c fl f1 hq => ?_) (by unfold srchPass; omega)
    have cc : FBase c m := c0.of_fx f1 (by decide)
    have hcJ : c.env sJ = j := by rw [fl.env sJ (by decide)]; norm_env; rfl
    have hcP : c.env vP = 2 ^ m + j := by
      rw [fl.env vP (by decide)]; norm_env; rw [c0.T]
    have hper := period_lt (2 ^ m + j) m
    refine Runs.op1B f1 (r_copy C srchSet _ sTmp pPer (by decide) (by decide)) (fun f2 => ?_)
      (by unfold srchPass; omega)
    refine Runs.op1B f2 (r_inc C srchSet _ sTmp (by decide) (by norm_env; rw [hq]; omega)) (fun f3 => ?_)
      (by unfold srchPass; omega)
    by_cases hcert : GF.PrimitiveCert (2 ^ m + j) m
    · have he : GF2.period (2 ^ m + j) m + 1 = 2 ^ m := (cert_iff hm1 hlt).1 hcert
      refine Runs.iteT (wf_eq (by decide)) (by norm_env; rw [hq, cc.T]; simpa using he) ?_
        (by unfold srchPass; omega)
      refine Runs.op1B f3 (r_copy C srchSet _ sBest vP (by decide) (by decide)) (fun f4 => ?_)
        (by unfold srchPass; omega)
      refine Runs.lastB f4 (r_copy C srchSet _ sJ vT (by decide) (by decide)) (fun f5 => ?_)
        (by unfold srchPass; omega)
      refine ⟨⟨c0.of_fx f5 (by decide), Or.inl ⟨?_, ?_⟩⟩, ?_⟩
      · norm_env; exact cc.T
      · norm_env; rw [hcP]; exact (firstPrimitive_eq_of hlt hcert i4).symm
      · norm_env; rw [cc.T]; omega
    · have he : ¬ GF2.period (2 ^ m + j) m + 1 = 2 ^ m := fun h => hcert ((cert_iff hm1 hlt).2 h)
      refine Runs.iteF (wf_eq (by decide)) (by norm_env; rw [hq, cc.T]; simpa using he) ?_
        (by unfold srchPass; omega)
      refine Runs.lastB f3 (r_inc C srchSet _ sJ (by decide) (by norm_env; rw [hcJ]; omega)) (fun f4 => ?_)
        (by unfold srchPass; omega)
      refine ⟨⟨c0.of_fx f4 (by decide), Or.inr ⟨?_, ?_, ?_⟩⟩, ?_⟩
      · norm_env; rw [hcJ]; omega
      · norm_env; rw [fl.env sBest (by decide)]; norm_env; exact i3
      · norm_env; rw [hcJ]
        intro i hi
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
        · exact i4 i hi
        · exact hcert
      · norm_env; rw [hcJ]; omega
  unfold srchS
  have f0 := Fx.refl srchSet a
  refine Runs.op1B f0 (r_zero C srchSet a sJ (by decide)) (fun f0 => ?_) (by unfold srchCost; omega)
  refine Runs.op1B f0 (r_copy C srchSet _ sBest vT (by decide) (by decide)) (fun f0 => ?_)
    (by unfold srchCost; omega)
  have hI : Inv ((a.set sJ 0).set sBest ((a.set sJ 0).env vT)) := by
    refine ⟨hc.of_fx f0 (by decide), Or.inr ⟨?_, ?_, ?_⟩⟩ <;> norm_env
    · omega
    · exact hc.T
    · intro j hj; omega
  have hμ := Nat.mul_le_mul_right (srchPass m + 2)
    (Nat.sub_le (2 ^ m) (((a.set sJ 0).set sBest ((a.set sJ 0).env vT)).env sJ))
  refine Runs.callS0B f0 (hloop _ hI) (List.Subset.refl _) (fun b _ f1 ⟨⟨b0, hcase⟩, hev⟩ => ?_) ?_
  · refine Runs.last (r_copy C srchSet _ vP sBest (by decide) (by decide)) (fun _ => ?_) (by unfold srchCost; omega)
    norm_env
    have hge : 2 ^ m ≤ b.env sJ := by simpa [b0.T] using hev
    rcases hcase with ⟨-, h2⟩ | ⟨i2, i3, i4⟩
    · exact h2
    · rw [i3, firstPrimitive_eq_none (fun i hi => i4 i (by omega))]
  · unfold srchCost; omega

end NearCubicGates.Adapters.ShortPCP.MaskMachine
