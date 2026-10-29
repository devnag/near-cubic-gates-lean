import SourceAdapters.ShortPCP.AssemblyCopy
import Proof.Gates.Cells.Run

/-!
# The middle program: from the generated instance to the compilation request

The constructor of `thm:short-pcp-ours`, Step 4, forms the compilation request
`(data, ℓ, KT·(|data| + ℓ + 1)^eT)`; `app:short-pcp-proof`, "The exact Lean interface",
requires both computing and writing that word in polynomial time.

One cell program `mid` reads `natWord |w| ++ w`, where `w = frame x̄ ++ code`,
and prints `frame (frame data ++ frame 1^ℓ ++ frame 1^fuel)`. Here
`data = code ++ frame x̄ ++ natWord 2^(f−2) ++ listWord frame S`.
It calls the mask machine once on `natWord f ++ natWord n`. The field degree `f`
is the first number of the instance word; `n` is the index of the last `1` of
`x̄ = x10^j` (`lem:tm-ram`). The remaining parameters are
`ℓ = c0 + f + bL·|bits f|` and `fuel = KT·(|data| + ℓ + 1)^eT`.

The six phases `phaseA` through `phaseF` charge every step and register value
against one bound `U`. The resulting execution uses at most `57·(U + 1)` cell steps.
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.ShortPCP.Assembly

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation NearCubicGates.Close.Cells

variable {C : Ctx}

/-! ## Words -/

theorem frame_append' (A B : List Bool) : frame (A ++ B) = A.flatMap (fun b => [true, b]) ++ frame B := by
  induction A with
  | nil => rfl
  | cons b A ih => simp [frame, ih]

theorem marks_frame (d : List Bool) : (frame d).flatMap (fun b => [true, b]) = dfr d ++ [true, false] := by
  induction d with
  | nil => rfl
  | cons b d ih => simp [frame, ih, dfr]

theorem dfr_ones (k : ℕ) : dfr (List.replicate k true) = (List.replicate k [true, true, true, true]).flatten := by
  induction k with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ, dfr] at ih ⊢; exact ih

theorem dfr_zeros (k : ℕ) : dfr (List.replicate k false) = (List.replicate k [true, true, true, false]).flatten := by
  induction k with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ, dfr] at ih ⊢; exact ih

theorem frame_frame (d : List Bool) : frame (frame d) = dfr d ++ [true, false, false] := by
  have h := frame_append' (frame d) []
  rw [List.append_nil] at h
  rw [h, marks_frame]; simp [frame]

/-- **The output word**: the doubly framed compilation request, written out. -/
theorem frame_request (d : List Bool) (ℓ F : ℕ) :
    frame (frame d ++ frame (List.replicate ℓ true) ++ frame (List.replicate F true)) =
      dfr d ++ [true, false] ++ (List.replicate ℓ [true, true, true, true]).flatten ++ [true, false] ++
        (List.replicate F [true, true, true, true]).flatten ++ [true, false, false] := by
  rw [frame_append', List.flatMap_append, marks_frame, marks_frame, frame_frame, dfr_ones, dfr_ones]
  simp [List.append_assoc]

theorem natBitLength_two_pow (j : ℕ) : natBitLength (2 ^ j) = j + 1 := by
  unfold natBitLength; rw [Nat.log_pow (by norm_num)]

theorem natWord_two_pow (j : ℕ) :
    natWord (2 ^ j) = List.replicate (j + 1) true ++ false :: (List.replicate j false ++ [true]) := by
  rw [natWord_eq, natBitLength_two_pow]
  congr 2
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.length_ofFn] at h1
  rw [List.getElem_ofFn, Nat.testBit_two_pow]
  by_cases hij : i < j
  · rw [List.getElem_append_left (by simpa using hij), List.getElem_replicate]
    simp only [decide_eq_false_iff_not]; omega
  · rw [List.getElem_append_right (by simpa using hij)]
    simp only [List.length_replicate, List.getElem_singleton, decide_eq_true_eq]; omega

/-- `dfr (natWord 2^{f−2})` as printed by `phaseC`. -/
theorem dfr_dB (f : ℕ) (hf : 2 ≤ f) :
    dfr (natWord (2 ^ (f - 2))) = (List.replicate (f - 1) [true, true, true, true]).flatten ++ [true, true, true, false] ++
      (List.replicate (f - 2) [true, true, true, false]).flatten ++ [true, true, true, true] := by
  rw [natWord_two_pow, show f - 2 + 1 = f - 1 by omega]
  simp [dfr_ones, dfr_zeros, List.append_assoc]

theorem natWord_dB_length (f : ℕ) (hf : 2 ≤ f) : (natWord (2 ^ (f - 2))).length = 2 * f - 1 := by
  rw [natWord_length, natBitLength_two_pow]; omega

theorem nbl_add_two {v U W : ℕ} (hv : v ≤ U) (hU : 1 ≤ U) (hW : 4 * U < 2 ^ W) : natBitLength v + 2 ≤ W := by
  have h1 : natBitLength v ≤ natBitLength U := by
    unfold natBitLength; have := Nat.log_mono_right (b := 2) hv; omega
  have h2 : 2 ^ Nat.log 2 U ≤ U := Nat.pow_log_le_self 2 (by omega)
  have h3 : 2 ^ (Nat.log 2 U + 2) < 2 ^ W := by rw [pow_add]; omega
  have h4 := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp h3
  unfold natBitLength at h1 ⊢; omega

theorem lastTrue_le (l : List Bool) (k acc : ℕ) : lastTrue l k acc ≤ max acc (k + l.length) := by
  induction l generalizing k acc with
  | nil => simp [lastTrue]
  | cons b l ih =>
    simp only [lastTrue, List.length_cons]
    refine (ih _ _).trans ?_
    split_ifs <;> omega

/-! ## Uniform step costs -/

theorem hs_step {s u : St VV MM} {a : DS VV MM} {U k : ℕ} {R1 R2 : DS VV MM → Prop}
    (h1 : Hs C s a U R1) (h2 : ∀ b, R1 b → Hs C u b (k * (U + 1)) R2) : Hs C (.seq s u) a ((k + 1) * (U + 1)) R2 :=
  Hs.mono (Hs.seq h1 h2) (le_of_eq (by ring)) (fun _ h => h)

theorem hs_one {s : St VV MM} {a : DS VV MM} {U : ℕ} {R : DS VV MM → Prop} (h : Hs C s a U R) :
    Hs C s a (1 * (U + 1)) R :=
  Hs.mono h (by omega) (fun _ h => h)

/-! ## The data of one run -/

/-- What the middle program is given (as words and numbers). -/
structure Run where
  xb : List Bool
  cw : List Bool
  rest : List Bool
  f : ℕ
  n : ℕ
  S : List (List Bool)
  c0 : ℕ
  bL : ℕ
  KT : ℕ
  eT : ℕ

namespace Run

variable (R : Run)

/-- The middle input `w = frame x̄ ++ code`. -/
def w : List Bool := frame R.xb ++ R.cw

/-- `listWord frame S`. -/
def sWord : List Bool := natWord R.S.length ++ framesWord R.S

/-- The data word. -/
def data : List Bool := R.cw ++ frame R.xb ++ natWord (2 ^ (R.f - 2)) ++ R.sWord

/-- `ℓ`. -/
def ell : ℕ := R.c0 + R.f + R.bL * natBitLength R.f

/-- The fuel. -/
def fuel : ℕ := R.KT * (R.data.length + R.ell + 1) ^ R.eT

/-- The output word. -/
def out : List Bool :=
  frame (frame R.data ++ frame (List.replicate R.ell true) ++ frame (List.replicate R.fuel true))

/-- The bound charged per step (and of every register value). -/
def bound : ℕ :=
  50 * ((natWord R.w.length ++ R.w).length + R.data.length + R.ell + R.fuel + R.c0 + R.bL + R.KT + R.eT + 10)

/-- The hypotheses on the context. -/
structure Good (C : Ctx) (U : ℕ) : Prop where
  inp : C.inp = natWord R.w.length ++ R.w
  cw : R.cw = natWord R.f ++ R.rest
  n : lastTrue R.xb 0 0 = R.n
  f : 2 ≤ R.f
  call : ∃ s : C.K.Req, C.K.inw s = natWord R.f ++ natWord R.n ∧ C.K.outw s = R.sWord ∧ C.K.bud s ≤ C.Bk
  lk : (natWord R.f).length + (natWord R.n).length ≤ C.Lk
  hU : R.bound + 50 * (C.Lk + C.Bk) ≤ U
  hW : 4 * U < 2 ^ C.Wd
  wd : C.inp.length + 2 ≤ C.Wd

end Run

/-! ## Phase A: constants, the header, `frame x̄`, `f` -/

def phaseA : St VV MM :=
  .seq (.op (.inc v1)) (.seq (.op (.inc v2)) (.seq (.op (.inc v2)) (.seq (readNat) (.seq (.op (.copy endR t3)) (.seq (.op (.add endR ipR)) (.seq (.op (.copy p0R ipR)) (.seq (parseX) (.seq (.op (.copy p1R ipR)) (.seq (readNat) (.seq (.op (.copy fR t3)) (.op (.copy kR t4))))))))))))

namespace Run

variable (R : Run)

/-- `|natWord |w||`, the start of `frame x̄`. -/
def P0 : ℕ := (natWord R.w.length).length
/-- The start of the code word. -/
def P1 : ℕ := R.P0 + (frame R.xb).length

/-- After phase A. -/
structure PostA (b : DS VV MM) : Prop where
  cst : Cst b
  ip : b.env ipR = b.ip
  ipv : b.ip = R.P1 + (natWord R.f).length
  e : b.env endR = (natWord R.w.length ++ R.w).length
  p0 : b.env p0R = R.P0
  p1 : b.env p1R = R.P1
  n : b.env nR = R.n
  f : b.env fR = R.f
  k : b.env kR = natBitLength R.f
  d : b.env dR = 0
  out : b.out = []
  kin : b.kin = []
  kc : b.kc = 0

end Run

theorem bound_inp (R : Run) {U : ℕ} (hg : R.Good C U) : C.inp.length ≤ U := by
  have := hg.hU; rw [hg.inp]; unfold Run.bound at this; omega

theorem one_le_U (R : Run) {U : ℕ} (hg : R.Good C U) : 1 ≤ U := by
  have := hg.hU; unfold Run.bound at this; omega

theorem lt_W (R : Run) {U v : ℕ} (hg : R.Good C U) (hv : v ≤ U) : v < 2 ^ C.Wd := by
  have := hg.hW; omega

theorem nbl_le' (v : ℕ) : natBitLength v ≤ v + 1 := by
  unfold natBitLength; have := Nat.log_le_self 2 v; omega

theorem phaseA_spec (R : Run) (U : ℕ) (hg : R.Good C U) :
    Hs C phaseA (a0 : DS VV MM) (13 * (U + 1)) R.PostA := by
  refine Hs.mono (t := 12 * (U + 1)) ?_ (by omega) (fun _ h => h)
  have hB := hg.hU
  unfold Run.bound at hB
  have hW := hg.hW
  have hinp := hg.inp
  have hcw := hg.cw
  have hiU : 50 * C.inp.length + 500 ≤ U := by rw [hinp]; omega
  have hW4 : 4 < 2 ^ C.Wd := by omega
  have hiW : C.inp.length + 1 < 2 ^ C.Wd := by omega
  have hlen : C.inp.length = (natWord R.w.length).length + (frame R.xb).length + R.cw.length := by
    rw [hinp]; simp [Run.w]; omega
  -- the constants
  refine hs_step (Hs.mono (hs_inc C v1 a0 (by rw [show (a0 : DS VV MM).env v1 = 0 from rfl]; omega)) (by omega)
    (fun _ h => h)) (fun b1 hb1 => ?_)
  have e1 : b1.env v2 = 0 := by rw [hb1]; rfl
  refine hs_step (Hs.mono (hs_inc C v2 b1 (by rw [e1]; omega)) (by omega) (fun _ h => h)) (fun b2 hb2 => ?_)
  have e2 : b2.env v2 = 1 := by rw [hb2, hb1]; rfl
  refine hs_step (Hs.mono (hs_inc C v2 b2 (by rw [e2]; omega)) (by omega) (fun _ h => h)) (fun b3 hb3 => ?_)
  have hc3 : Cst b3 := by subst hb3 hb2 hb1; exact ⟨rfl, rfl, rfl⟩
  have hz3 : ∀ y, y ≠ v1 → y ≠ v2 → b3.env y = 0 := by
    subst hb3 hb2 hb1; intro y h1 h2; vsimp [a0, h1, h2]
  have hio3 : b3.ip = 0 ∧ b3.out = [] ∧ b3.kin = [] ∧ b3.kc = 0 := by
    subst hb3 hb2 hb1; exact ⟨rfl, rfl, rfl, rfl⟩
  -- the header `natWord |w|`
  have hd3 : C.inp.drop b3.ip = natWord R.w.length ++ R.w := by rw [hio3.1, hinp]; rfl
  have hwU : R.w.length ≤ U := by rw [hinp] at hiU; simp at hiU; omega
  refine hs_step (Hs.mono (readNat_spec b3 hc3 (by rw [hz3 ipR (by decide) (by decide), hio3.1]) _ _ hd3
    (nbl_add_two hwU (by omega) hW) (by omega)) (by
      have := nbl_le' R.w.length
      rw [hinp] at hiU; simp at hiU; omega) (fun _ h => h)) (fun b4 hb4 => ?_)
  obtain ⟨h41, h42, h43, h44, h45, h46, h47, h48, h49, hc4⟩ := hb4
  have hP0 : (natWord R.w.length).length = R.P0 := rfl
  refine hs_step (Hs.mono (hs_copy C endR t3 b4 (by decide)) (by omega) (fun _ h => h)) (fun b5 hb5 => ?_)
  have e5 : b5.env endR = R.w.length ∧ b5.env ipR = R.P0 ∧ b5.ip = R.P0 := by
    rw [hb5]; vsimp [h41, h44, h43, hio3.1, Run.P0, natWord_length]
  refine hs_step (Hs.mono (hs_add C endR ipR b5 (by decide) (by rw [e5.1, e5.2.1]; omega)) (by omega)
    (fun _ h => h)) (fun b6 hb6 => ?_)
  refine hs_step (Hs.mono (hs_copy C p0R ipR b6 (by decide)) (by omega) (fun _ h => h)) (fun b7 hb7 => ?_)
  have hc7 : Cst b7 := by rw [hb7, hb6, hb5]; exact ⟨by vsimp [hc4.z], by vsimp [hc4.one], by vsimp [hc4.two]⟩
  have hip7 : b7.ip = R.P0 := by rw [hb7, hb6]; simp [e5.2.2]
  have hipv7 : b7.env ipR = R.P0 := by rw [hb7, hb6]; vsimp [e5.2.1]
  have hwl : R.w.length = (frame R.xb).length + R.cw.length := by simp [Run.w]
  have he7 : b7.env endR = C.inp.length := by
    have := frame_length' R.xb
    rw [hb7, hb6]; vsimp [e5.1, e5.2.1, hlen, Run.P0]; omega
  have hp07 : b7.env p0R = R.P0 := by rw [hb7]; vsimp [hb6, e5.2.1]
  have hio7 : b7.out = [] ∧ b7.kin = [] ∧ b7.kc = 0 := by
    rw [hb7, hb6, hb5]; simp [h45, h46, h48, hio3]
  have hd7' : b7.env dR = 0 := by
    rw [hb7, hb6, hb5]; vsimp []; rw [h49 dR (by decide)]; exact hz3 dR (by decide) (by decide)
  -- `frame x̄`
  have hd7 : C.inp.drop b7.ip = frame R.xb ++ R.cw := by
    rw [hip7, hinp, ← hP0, List.drop_left]; rfl
  refine hs_step (Hs.mono (parseX_spec b7 hc7 (by rw [hip7, hipv7]) R.xb R.cw hd7 hiW) (by
      have := frame_length' R.xb; omega) (fun _ h => h)) (fun b8 hb8 => ?_)
  obtain ⟨h81, h82, h83, h84, h85, h86, h87, h88⟩ := hb8
  have hc8 : Cst b8 := Cst.of_fr hc7 h88 (by decide)
  refine hs_step (Hs.mono (hs_copy C p1R ipR b8 (by decide)) (by omega) (fun _ h => h)) (fun b9 hb9 => ?_)
  -- The field exponent is the first instance field.
  have hip9 : b9.ip = R.P1 := by rw [hb9]; simp [h82, hip7, Run.P1]
  have hc9 : Cst b9 := by rw [hb9]; exact Cst.of_fr hc8 (T := [p1R]) (Fr.set b8 _ (by simp)) (by decide)
  have hipv9 : b9.env ipR = b9.ip := by rw [hb9]; vsimp [h83]
  have hd9 : C.inp.drop b9.ip = natWord R.f ++ R.rest := by
    rw [hip9, Run.P1, ← List.drop_drop, hinp, ← hP0, List.drop_left, Run.w, List.drop_left, hcw]
  have hcwl : R.cw.length = (natWord R.f).length + R.rest.length := by
    rw [hcw]; simp
  have hwd := hg.wd
  have hfW : natBitLength R.f + 2 ≤ C.Wd := by have := natWord_length R.f; omega
  refine hs_step (Hs.mono (readNat_spec b9 hc9 hipv9 R.f _ hd9 hfW (by omega)) (by
      have := natWord_length R.f; omega) (fun _ h => h)) (fun b11 hb11 => ?_)
  obtain ⟨h111, h112, h113, h114, h115, h116, h117, h118, h119, hc11⟩ := hb11
  refine hs_step (Hs.mono (hs_copy C fR t3 b11 (by decide)) (by omega) (fun _ h => h)) (fun b12 hb12 => ?_)
  subst hb12
  refine hs_one (Hs.mono (hs_copy C kR t4 _ (by decide)) (by omega) (fun b hb => ?_))
  subst hb
  -- the frames of the later steps
  have f11 : ∀ y, y ∉ readT → b11.env y = b9.env y := h119
  have f9 : ∀ y, y ≠ p1R → b9.env y = b8.env y := fun y hy => by rw [hb9]; vsimp [hy]
  have f8 : ∀ y, y ∉ parseT → b8.env y = b7.env y := h88
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨by vsimp [hc11.z], by vsimp [hc11.one], by vsimp [hc11.two]⟩
  · vsimp [h114]
  · simp only [DS.set_ip]; rw [h113, hip9]
  · vsimp []; rw [f11 _ (by decide), f9 _ (by decide), f8 _ (by decide), he7, hinp]; simp
  · vsimp []; rw [f11 _ (by decide), f9 _ (by decide), f8 _ (by decide), hp07]
  · vsimp []; rw [f11 _ (by decide), hb9]; vsimp [h83, h82, hip7, Run.P1]
  · vsimp []; rw [f11 _ (by decide), f9 _ (by decide), h81, hg.n]
  · vsimp [h111]
  · vsimp [h112]
  · vsimp []; rw [f11 _ (by decide), f9 _ (by decide), f8 _ (by decide), hd7']
  · simp [h115, hb9, h84, hio7.1]
  · simp [h116, hb9, h85, hio7.2.1]
  · simp [h118, hb9, h87, hio7.2.2]

end NearCubicGates.Adapters.ShortPCP.Assembly
