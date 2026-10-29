import SourceAdapters.Williams.Simulation
import Proof.Gates.WordPrograms.RegArith

/-!
# W05: the output formatter (source output word → `outputWord N P`, exactly)

Emit exactly `N²` entries with width `natBitLength N`, least significant bit first, on a fresh
initially blank tape. Prove the tape-list equality demanded by `MultitapeMultiplier`, not merely equality after
ignoring trailing zeros. Consumer: `MultitapeMultiplier.multiplies` (`Statement.lean:1129–1132`), whose output is
`outputWord N P = encodedNatCellTape (natBitLength N) (rowMajorNatMatrix P)` (`Statement.lean:1114–1115`).
This implements the companion’s exact output convention for `imp:batch`.

**Program** (`formatter`, a `WMX` program): the simulated source output tape is the stream `SIM`, read block by
block in the thermometer code of `Simulation.lean` (bit 0 = non-blank, bit 1 = the digit, bit 2 = separator); the
stream `OUT` starts empty. For each entry (until a blank block): copy its digits to `OUT`, then pad with `false` up to
the width held in register `WD`. `OUT` is written left to right from its end, so its final list is exactly the
concatenation (`writeTapeBit_end`).

**Exported.** `formatter_spec`: from `SIM` holding `(xs.flatMap numberWord)` in blocks from block `p`, `OUT = out`,
the formatter halts with `OUT = out ++ xs.flatMap (fixedWidthNatBits WD)` within
`xs.length * (entryCost w WD + 2) + 1` steps.
-/

namespace NearCubicGates.Adapters.Williams.Format

open NearCubicGates.Published.Williams NearCubicGates.Adapters.Williams
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms

set_option autoImplicit false

/-! ## List facts -/

theorem writeTapeBit_end : ∀ (l : List Bool) (b : Bool), writeTapeBit l l.length b = l ++ [b]
  | [], _ => rfl
  | _ :: l, b => by simp [writeTapeBit, writeTapeBit_end l b]

/-- The digits of `x` as bits, least significant first. -/
def digitBits (x : ℕ) : List Bool := (Nat.digits 2 x).map fun d => decide (d = 1)

theorem numberWord_eq {e : ℕ} (x : ℕ) :
    (numberWord x : List (Symbol e)) = (digitBits x).map Symbol.digit ++ [Symbol.separator] := by
  simp [numberWord, digitBits, Function.comp_def]

/-- Fixed width `W`, least significant bit first, is the digit list padded with `false`. -/
theorem fixedWidth_eq : ∀ (W x : ℕ), x < 2 ^ W →
    WilliamsLoaderForms.fixedWidthNatBits W x = digitBits x ++ List.replicate (W - (digitBits x).length) false
  | 0, x, hx => by
    have : x = 0 := by simpa using hx
    subst this; simp [WilliamsLoaderForms.fixedWidthNatBits, digitBits]
  | W + 1, x, hx => by
    have ih := fixedWidth_eq W (x / 2) (by rw [Nat.div_lt_iff_lt_mul (by norm_num)]; rw [pow_succ] at hx; exact hx)
    have hs : ∀ i : ℕ, x.testBit (i + 1) = (x / 2).testBit i := fun i => Nat.testBit_succ x i
    simp only [WilliamsLoaderForms.fixedWidthNatBits, List.ofFn_succ, Fin.val_zero, Fin.val_succ, hs,
      Nat.testBit_zero] at ih ⊢
    rw [ih]
    rcases Nat.eq_zero_or_pos x with rfl | hpos
    · simp [digitBits, List.replicate_succ]
    · rw [show digitBits x = decide (x % 2 = 1) :: digitBits (x / 2) by
        simp [digitBits, Nat.digits_def' (by norm_num : 1 < 2) hpos]]
      rw [List.length_cons, show W + 1 - ((digitBits (x / 2)).length + 1) = W - (digitBits (x / 2)).length by omega]
      rfl

theorem digitBits_length_le (W x : ℕ) (hx : x < 2 ^ W) : (digitBits x).length ≤ W := by
  have := congrArg List.length (fixedWidth_eq W x hx)
  simp [WilliamsLoaderForms.fixedWidthNatBits] at this
  omega

/-! ## Blocks of a stream -/

/-- From block `p` on, the stream `L` holds the symbols `syms` (then blanks) in blocks of width `x + 4`. -/
def BlocksFrom {x : ℕ} (L : List Bool) (p : ℕ) (syms : List (Symbol x)) : Prop :=
  ∀ q j, j < x + 4 → readTapeBit L ((x + 4) * (p + q) + j) = code (syms.getD q Symbol.blank) j

theorem BlocksFrom.cons {x : ℕ} {L : List Bool} {p : ℕ} {s : Symbol x} {syms : List (Symbol x)}
    (h : BlocksFrom L p (s :: syms)) : BlocksFrom L (p + 1) syms := by
  intro q j hj
  have := h (q + 1) j hj
  rwa [show p + (q + 1) = p + 1 + q by omega, List.getD_cons_succ] at this

theorem BlocksFrom.head {x : ℕ} {L : List Bool} {p : ℕ} {s : Symbol x} {syms : List (Symbol x)}
    (h : BlocksFrom L p (s :: syms)) (j : ℕ) (hj : j < x + 4) : readTapeBit L ((x + 4) * p + j) = code s j := by
  have := h 0 j hj
  simpa using this

theorem BlocksFrom.nil {x : ℕ} {L : List Bool} {p : ℕ} (h : BlocksFrom L p ([] : List (Symbol x))) :
    readTapeBit L ((x + 4) * p) = false := by
  have := h 0 0 (by omega)
  simpa using this

theorem BlocksFrom.drop {x : ℕ} {L : List Bool} : ∀ (A : List (Symbol x)) {p : ℕ} {B : List (Symbol x)},
    BlocksFrom L p (A ++ B) → BlocksFrom L (p + A.length) B
  | [], p, B, h => by simpa using h
  | a :: A, p, B, h => by
    have := BlocksFrom.drop A (BlocksFrom.cons (s := a) h)
    rw [List.length_cons, show p + (A.length + 1) = p + 1 + A.length by omega]
    exact this

theorem code_digit {x : ℕ} (b : Bool) :
    code (Symbol.digit b : Symbol x) 0 = true ∧ code (Symbol.digit b : Symbol x) 1 = b ∧
      code (Symbol.digit b : Symbol x) 2 = false := by
  cases b <;> simp [code, Symbol.digit, Nat.mod_eq_of_lt (show 2 < x + 4 by omega),
    Nat.mod_eq_of_lt (show 1 < x + 4 by omega)]

theorem code_separator {x : ℕ} :
    code (Symbol.separator : Symbol x) 0 = true ∧ code (Symbol.separator : Symbol x) 2 = true := by
  simp [code, Symbol.separator, Nat.mod_eq_of_lt (show 3 < x + 4 by omega)]

/-! ## The program -/

variable {ns nr : ℕ}

/-- `n` forward moves. -/
def fwdN (i : Fin (ns + 1)) : ℕ → WMX ns nr
  | 0 => WMX.skip
  | n + 1 => .seq (WMX.fwd i) (fwdN i n)

section Program
variable (SIM OUT : Fin (ns + 1)) (DG REM WD T : Fin nr) (x : ℕ)

/-- Write one bit at the end of `OUT`. -/
def emit (b : Bool) : WMX ns nr := .seq (WMX.wr OUT b) (WMX.fwd OUT)

/-- One digit (head on bit 2 of a digit block): copy bit 1, count it, move to bit 2 of the next block, and set
`DG` to whether that block is a digit. -/
def digitBody : WMX ns nr :=
  .seq (WMX.bwd SIM) (.seq (.ifs SIM (emit OUT true) (emit OUT false)) (.seq (WMX.dec REM)
    (.seq (fwdN SIM (x + 5)) (.seq (WMX.dec DG) (.ifs SIM WMX.skip (WMX.inc DG))))))

/-- Pad `OUT` with `REM` bits `false`. -/
def padLoop : WMX ns nr := .whr REM (.seq (emit OUT false) (WMX.dec REM))

/-- One entry (head on bit 0 of its first block). -/
def entry : WMX ns nr :=
  .seq (fwdN SIM 2) (.seq (.ifs SIM WMX.skip (WMX.inc DG)) (.seq (addR WD REM T)
    (.seq (.whr DG (digitBody SIM OUT DG REM x)) (.seq (padLoop OUT REM) (fwdN SIM (x + 2))))))

/-- **The formatter**: one entry per non-blank block start. -/
def formatter : WMX ns nr := .whs SIM (entry SIM OUT DG REM WD T x)

end Program

/-! ## Specifications -/

section Specs
variable {cap : ℕ} {SIM OUT : Fin (ns + 1)} {DG REM WD T : Fin nr} {x : ℕ}

/-- The formatter-relevant view of a state. -/
def Fm (SIM OUT : Fin (ns + 1)) (DG REM WD T : Fin nr) (L : List Bool) (W : ℕ) (σ : WState ns nr) (h : ℕ)
    (o : List Bool) (d r : ℕ) : Prop :=
  σ.st SIM = L ∧ σ.sh SIM = h ∧ σ.st OUT = o ∧ σ.sh OUT = o.length ∧ σ.val DG = d ∧ σ.val REM = r ∧
    σ.val WD = W ∧ σ.val T = 0

variable (hSO : SIM ≠ OUT) (hR : [DG, REM, WD, T].Nodup)
include hSO hR

omit hR in
theorem fwdN_spec (n : ℕ) : ∀ (σ : WState ns nr) {L : List Bool} {W h : ℕ} {o : List Bool} {d r : ℕ},
    Fm SIM OUT DG REM WD T L W σ h o d r →
    Runs cap (fwdN SIM n) σ (2 * n) (fun τ => Fm SIM OUT DG REM WD T L W τ (h + n) o d r) := by
  induction n with
  | zero => intro σ L W h o d r hf; exact Runs.of (WXExec.skip (cap := cap) σ) (by simpa using hf)
  | succ n ih =>
    intro σ L W h o d r hf
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hf
    have e := WXExec.fwd (cap := cap) SIM σ
    have hf' : Fm SIM OUT DG REM WD T L W (σ.seth SIM (σ.sh SIM + 1)) (h + 1) o d r := by
      refine ⟨by simpa using h1, by simp [h2], by simpa using h3, ?_, by simpa using h5, by simpa using h6,
        by simpa using h7, by simpa using h8⟩
      simp [Function.update_of_ne (Ne.symm hSO), h4]
    have := Runs.seqE e (ih _ hf')
    exact this.mono (by omega) (fun τ hτ => by rwa [show h + 1 + n = h + (n + 1) by omega] at hτ)

omit hR in
theorem emit_spec (b : Bool) (σ : WState ns nr) {L : List Bool} {W h : ℕ} {o : List Bool} {d r : ℕ}
    (hf : Fm SIM OUT DG REM WD T L W σ h o d r) :
    Runs cap (emit OUT b) σ 3 (fun τ => Fm SIM OUT DG REM WD T L W τ h (o ++ [b]) d r) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hf
  have e1 := WXExec.wr (cap := cap) OUT b σ
  have e2 := WXExec.fwd (cap := cap) OUT (σ.sets OUT (writeTapeBit (σ.st OUT) (σ.sh OUT) b))
  refine Runs.of (WXExec.seq e1 e2) ⟨?_, ?_, ?_, ?_, by simpa using h5, by simpa using h6, by simpa using h7,
    by simpa using h8⟩
  · simp [Function.update_of_ne hSO, h1]
  · simp [Function.update_of_ne hSO, h2]
  · simp [h3, h4, writeTapeBit_end]
  · simp [h4]

/-! ## Frame facts for the view -/

omit hSO in
theorem regs_ne : DG ≠ REM ∧ DG ≠ WD ∧ DG ≠ T ∧ REM ≠ WD ∧ REM ≠ T ∧ WD ≠ T := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true] at hR
  tauto

omit hSO in
theorem fm_setDG {σ : WState ns nr} {L : List Bool} {W h : ℕ} {o : List Bool} {d r : ℕ}
    (hf : Fm SIM OUT DG REM WD T L W σ h o d r) (d' : ℕ) :
    Fm SIM OUT DG REM WD T L W (σ.setv DG d') h o d' r := by
  obtain ⟨n1, n2, n3, n4, n5, n6⟩ := regs_ne hR
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hf
  exact ⟨h1, h2, h3, h4, by simp, by simp [Function.update_of_ne (Ne.symm n1), h6],
    by simp [Function.update_of_ne (Ne.symm n2), h7], by simp [Function.update_of_ne (Ne.symm n3), h8]⟩

omit hSO in
theorem fm_setREM {σ : WState ns nr} {L : List Bool} {W h : ℕ} {o : List Bool} {d r : ℕ}
    (hf : Fm SIM OUT DG REM WD T L W σ h o d r) (r' : ℕ) :
    Fm SIM OUT DG REM WD T L W (σ.setv REM r') h o d r' := by
  obtain ⟨n1, n2, n3, n4, n5, n6⟩ := regs_ne hR
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hf
  exact ⟨h1, h2, h3, h4, by simp [Function.update_of_ne n1, h5], by simp,
    by simp [Function.update_of_ne (Ne.symm n4), h7], by simp [Function.update_of_ne (Ne.symm n5), h8]⟩

omit hR in
theorem fm_seth {σ : WState ns nr} {L : List Bool} {W h : ℕ} {o : List Bool} {d r : ℕ}
    (hf : Fm SIM OUT DG REM WD T L W σ h o d r) (h' : ℕ) :
    Fm SIM OUT DG REM WD T L W (σ.seth SIM h') h' o d r := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hf
  exact ⟨h1, by simp, h3, by simp [Function.update_of_ne (Ne.symm hSO), h4], h5, h6, h7, h8⟩

omit hSO hR in
theorem fm_wbit {σ : WState ns nr} {L : List Bool} {W h : ℕ} {o : List Bool} {d r : ℕ}
    (hf : Fm SIM OUT DG REM WD T L W σ h o d r) : wbit σ SIM = readTapeBit L h := by
  obtain ⟨h1, h2, -⟩ := hf
  simp [wbit, h1, h2]

/-! ## Primitive specifications on the view -/

omit hR in
theorem fwd_spec (σ : WState ns nr) {L : List Bool} {W h : ℕ} {o : List Bool} {d r : ℕ}
    (hf : Fm SIM OUT DG REM WD T L W σ h o d r) :
    Runs cap (WMX.fwd SIM) σ 1 (fun τ => Fm SIM OUT DG REM WD T L W τ (h + 1) o d r) :=
  Runs.of (WXExec.fwd (cap := cap) SIM σ) (by have := fm_seth hSO hf (σ.sh SIM + 1); rwa [hf.2.1] at this ⊢)

omit hR in
theorem bwd_spec (σ : WState ns nr) {L : List Bool} {W h : ℕ} {o : List Bool} {d r : ℕ}
    (hf : Fm SIM OUT DG REM WD T L W σ h o d r) :
    Runs cap (WMX.bwd SIM) σ 1 (fun τ => Fm SIM OUT DG REM WD T L W τ (h - 1) o d r) :=
  Runs.of (WXExec.bwd (cap := cap) SIM σ) (by have := fm_seth hSO hf (σ.sh SIM - 1); rwa [hf.2.1] at this ⊢)

omit hSO in
theorem decREM_spec (σ : WState ns nr) {L : List Bool} {W h : ℕ} {o : List Bool} {d r : ℕ}
    (hf : Fm SIM OUT DG REM WD T L W σ h o d r) (hr : r ≤ cap) :
    Runs cap (WMX.dec REM) σ 1 (fun τ => Fm SIM OUT DG REM WD T L W τ h o d (r - 1)) :=
  Runs.of (WXExec.dec cap REM σ (by rw [hf.2.2.2.2.2.1]; exact hr))
    (by have := fm_setREM hR hf (σ.val REM - 1); rwa [hf.2.2.2.2.2.1] at this ⊢)

omit hSO in
theorem decDG_spec (σ : WState ns nr) {L : List Bool} {W h : ℕ} {o : List Bool} {d r : ℕ}
    (hf : Fm SIM OUT DG REM WD T L W σ h o d r) (hd : d ≤ cap) :
    Runs cap (WMX.dec DG) σ 1 (fun τ => Fm SIM OUT DG REM WD T L W τ h o (d - 1) r) :=
  Runs.of (WXExec.dec cap DG σ (by rw [hf.2.2.2.2.1]; exact hd))
    (by have := fm_setDG hR hf (σ.val DG - 1); rwa [hf.2.2.2.2.1] at this ⊢)

omit hSO in
theorem incDG_spec (σ : WState ns nr) {L : List Bool} {W h : ℕ} {o : List Bool} {d r : ℕ}
    (hf : Fm SIM OUT DG REM WD T L W σ h o d r) (hd : d < cap) :
    Runs cap (WMX.inc DG) σ 3 (fun τ => Fm SIM OUT DG REM WD T L W τ h o (d + 1) r) :=
  Runs.of (WXExec.inc cap DG σ (by rw [hf.2.2.2.2.1]; exact hd))
    (by have := fm_setDG hR hf (σ.val DG + 1); rwa [hf.2.2.2.2.1] at this ⊢)

omit hSO hR in
theorem skip_spec (σ : WState ns nr) {Q : WState ns nr → Prop} (hq : Q σ) : Runs cap WMX.skip σ 0 Q :=
  Runs.of (WXExec.skip (cap := cap) σ) hq

omit hSO in
theorem addR_fm (σ : WState ns nr) {L : List Bool} {W h : ℕ} {o : List Bool} {d : ℕ}
    (hf : Fm SIM OUT DG REM WD T L W σ h o d 0) (hW : W ≤ cap) :
    Runs cap (addR WD REM T) σ (18 * W + 3) (fun τ => Fm SIM OUT DG REM WD T L W τ h o d W) := by
  obtain ⟨n1, n2, n3, n4, n5, n6⟩ := regs_ne hR
  have e := addR_spec cap (Ne.symm n4) n6 n5 σ hf.2.2.2.2.2.2.2 (by rw [hf.2.2.2.2.2.1, hf.2.2.2.2.2.2.1]; omega)
  refine Runs.of (WXExec.mono e (by rw [hf.2.2.2.2.2.2.1])) ?_
  rw [hf.2.2.2.2.2.1, hf.2.2.2.2.2.2.1, Nat.zero_add]
  exact fm_setREM hR hf W

/-! ## The digit loop -/

/-- Cost bound of one digit. -/
def digitCost (x : ℕ) : ℕ := 2 * x + 30

theorem digitBody_spec {L : List Bool} {W p r : ℕ} {o : List Bool} (b : Bool) (D : List Bool)
    (more : List (Symbol x)) (hB : BlocksFrom L p ((b :: D).map Symbol.digit ++ Symbol.separator :: more))
    (hr : r + 1 ≤ cap) (σ : WState ns nr)
    (hf : Fm SIM OUT DG REM WD T L W σ ((x + 4) * p + 2) o 1 (r + 1)) :
    Runs cap (digitBody SIM OUT DG REM x) σ (digitCost x)
      (fun τ => Fm SIM OUT DG REM WD T L W τ ((x + 4) * (p + 1) + 2) (o ++ [b]) (if D = [] then 0 else 1) r) := by
  have hbit : readTapeBit L ((x + 4) * p + 1) = b := by
    rw [hB.head 1 (by omega)]; exact (code_digit b).2.1
  have hB' := hB.cons
  have hnext : readTapeBit L ((x + 4) * (p + 1) + 2) = (if D = [] then true else false) := by
    cases D with
    | nil => rw [hB'.head 2 (by omega)]; simpa using code_separator.2
    | cons b' D' => rw [hB'.head 2 (by omega)]; simpa using (code_digit b').2.2
  have hpos : (x + 4) * (p + 1) + 2 = (x + 4) * p + 2 - 1 + (x + 5) := by rw [Nat.mul_succ]; omega
  refine (Runs.seq (bwd_spec hSO σ hf) fun τ1 f1 => Runs.seq (?_ : Runs cap (.ifs SIM (emit OUT true)
    (emit OUT false)) τ1 4 (fun τ => Fm SIM OUT DG REM WD T L W τ ((x + 4) * p + 2 - 1) (o ++ [b]) 1 (r + 1)))
    fun τ2 f2 => Runs.seq (decREM_spec hR τ2 f2 hr) fun τ3 f3 => Runs.seq (fwdN_spec hSO (x + 5) τ3 f3)
    fun τ4 f4 => Runs.seq (decDG_spec hR τ4 f4 (by omega)) fun τ5 f5 => (?_ : Runs cap
      (.ifs SIM WMX.skip (WMX.inc DG)) τ5 4 _)).mono (by unfold digitCost; omega) (fun τ hτ => hτ)
  · have hw := fm_wbit f1
    rw [show (x + 4) * p + 2 - 1 = (x + 4) * p + 1 by omega, hbit] at hw
    cases b
    · exact Runs.ifsF hw (emit_spec hSO false τ1 f1)
    · exact Runs.ifsT hw (emit_spec hSO true τ1 f1)
  · have hw := fm_wbit f5
    rw [← hpos, hnext] at hw
    rw [← hpos] at f5
    by_cases hD : D = []
    · rw [if_pos hD] at hw
      simp only [hD, if_true]
      exact (Runs.ifsT hw (skip_spec τ5 f5)).cost (by omega)
    · rw [if_neg hD] at hw
      simp only [hD, if_false]
      exact Runs.ifsF hw (incDG_spec hR τ5 f5 (by omega))

/-! ## The loops -/

theorem digitLoop_spec {L : List Bool} {W : ℕ} (more : List (Symbol x)) :
    ∀ (D : List Bool) (p r : ℕ) (o : List Bool) (σ : WState ns nr),
      BlocksFrom L p (D.map Symbol.digit ++ Symbol.separator :: more) → r + D.length ≤ cap →
      Fm SIM OUT DG REM WD T L W σ ((x + 4) * p + 2) o (if D = [] then 0 else 1) (r + D.length) →
      Runs cap (.whr DG (digitBody SIM OUT DG REM x)) σ (D.length * (digitCost x + 2) + 1)
        (fun τ => Fm SIM OUT DG REM WD T L W τ ((x + 4) * (p + D.length) + 2) (o ++ D) 0 r) := by
  intro D
  induction D with
  | nil =>
    intro p r o σ _ _ hf
    exact Runs.of (WXExec.mono (WXExec.whrF (by simpa using hf.2.2.2.2.1)) (by simp)) (by simpa using hf)
  | cons b D ih =>
    intro p r o σ hB hr hf
    have hdg : σ.val DG ≠ 0 := by rw [hf.2.2.2.2.1]; simp
    have hf' : Fm SIM OUT DG REM WD T L W σ ((x + 4) * p + 2) o 1 ((r + D.length) + 1) := by
      simpa [List.length_cons, Nat.add_assoc] using hf
    obtain ⟨τ, e1, q1⟩ := digitBody_spec hSO hR b D more hB (by simp at hr; omega) σ hf'
    obtain ⟨ρ, e2, q2⟩ := ih (p + 1) r (o ++ [b]) τ hB.cons (by simp at hr; omega) q1
    refine ⟨ρ, WXExec.mono (WXExec.whrT hdg e1 e2) ?_, ?_⟩
    · simp only [List.length_cons, Nat.succ_mul]; omega
    · simpa [List.length_cons, Nat.add_assoc, Nat.add_comm 1] using q2

theorem padLoop_spec {L : List Bool} {W h d : ℕ} : ∀ (r : ℕ) (o : List Bool) (σ : WState ns nr), r ≤ cap →
    Fm SIM OUT DG REM WD T L W σ h o d r →
    Runs cap (padLoop OUT REM) σ (r * 7 + 1)
      (fun τ => Fm SIM OUT DG REM WD T L W τ h (o ++ List.replicate r false) d 0) := by
  intro r
  induction r with
  | zero =>
    intro o σ _ hf
    exact Runs.of (WXExec.whrF hf.2.2.2.2.2.1) (by simpa using hf)
  | succ r ih =>
    intro o σ hr hf
    have hrem : σ.val REM ≠ 0 := by rw [hf.2.2.2.2.2.1]; omega
    obtain ⟨τ, e1, q1⟩ := Runs.seq (emit_spec hSO false σ hf) fun τ f => decREM_spec hR τ f hr
    obtain ⟨ρ, e2, q2⟩ := ih (o ++ [false]) τ (by omega) (by simpa using q1)
    refine ⟨ρ, WXExec.mono (WXExec.whrT hrem e1 e2) (by rw [Nat.succ_mul]; omega), ?_⟩
    simpa [List.replicate_succ] using q2

/-- Cost bound of one entry of width `W`. -/
def entryCost (x W : ℕ) : ℕ := W * (digitCost x + 2) + 25 * W + 2 * x + 40

theorem entry_spec {L : List Bool} {W : ℕ} (hcap : W + 1 ≤ cap) (y : ℕ) (hy : y < 2 ^ W)
    (more : List (Symbol x)) (p : ℕ) (o : List Bool) (σ : WState ns nr)
    (hB : BlocksFrom L p (numberWord y ++ more)) (hf : Fm SIM OUT DG REM WD T L W σ ((x + 4) * p) o 0 0) :
    Runs cap (entry SIM OUT DG REM WD T x) σ (entryCost x W)
      (fun τ => Fm SIM OUT DG REM WD T L W τ ((x + 4) * (p + (numberWord y : List (Symbol x)).length))
        (o ++ WilliamsLoaderForms.fixedWidthNatBits W y) 0 0) := by
  set D := digitBits y with hDdef
  have hDW : D.length ≤ W := digitBits_length_le W y hy
  have hB' : BlocksFrom L p (D.map Symbol.digit ++ Symbol.separator :: more) := by
    rw [numberWord_eq, List.append_assoc] at hB; simpa using hB
  have hlen : (numberWord y : List (Symbol x)).length = D.length + 1 := by simp [numberWord_eq, hDdef]
  have hbit2 : readTapeBit L ((x + 4) * p + 2) = (if D = [] then true else false) := by
    cases hD : D with
    | nil => rw [hD] at hB'; rw [hB'.head 2 (by omega)]; simpa using code_separator.2
    | cons b D' => rw [hD] at hB'; rw [hB'.head 2 (by omega)]; simpa using (code_digit b).2.2
  have hloop := digitLoop_spec (cap := cap) (L := L) (W := W) hSO hR more D p (W - D.length) o
  have hfin : (x + 4) * (p + D.length) + 2 + (x + 2) = (x + 4) * (p + (D.length + 1)) := by
    rw [show p + (D.length + 1) = (p + D.length) + 1 by omega, Nat.mul_succ]; omega
  have hm1 : D.length * (digitCost x + 2) ≤ W * (digitCost x + 2) := Nat.mul_le_mul_right _ hDW
  have hm2 : (W - D.length) * 7 ≤ W * 7 := Nat.mul_le_mul_right _ (by omega)
  refine (Runs.seq (fwdN_spec hSO 2 σ hf) fun τ1 f1 =>
    Runs.seq (?_ : Runs cap (.ifs SIM WMX.skip (WMX.inc DG)) τ1 4
      (fun τ => Fm SIM OUT DG REM WD T L W τ ((x + 4) * p + 2) o (if D = [] then 0 else 1) 0)) fun τ2 f2 =>
    Runs.seq (addR_fm hR τ2 f2 (by omega)) fun τ3 f3 =>
    Runs.seq (hloop τ3 hB' (by omega) (by rwa [Nat.sub_add_cancel hDW])) fun τ4 f4 =>
    Runs.seq (padLoop_spec hSO hR (W - D.length) _ τ4 (by omega) f4) fun τ5 f5 =>
    fwdN_spec hSO (x + 2) τ5 f5).mono (by unfold entryCost; omega) ?_
  · have hw := fm_wbit f1
    rw [hbit2] at hw
    by_cases hD : D = []
    · rw [if_pos hD] at hw
      simp only [hD, if_true]
      exact (Runs.ifsT hw (skip_spec τ1 f1)).cost (by omega)
    · rw [if_neg hD] at hw
      simp only [hD, if_false]
      exact Runs.ifsF hw (incDG_spec hR τ1 f1 (by omega))
  · intro τ hτ
    rw [hfin, List.append_assoc] at hτ
    rw [hlen, fixedWidth_eq W y hy]
    exact hτ

/-- **W05.** The formatter turns the blocks of `ys.flatMap numberWord` into `ys.flatMap (fixedWidthNatBits W)`,
appended exactly to `OUT`. -/
theorem formatter_spec {L : List Bool} {W : ℕ} (hcap : W + 1 ≤ cap) :
    ∀ (ys : List ℕ) (p : ℕ) (o : List Bool) (σ : WState ns nr), (∀ y ∈ ys, y < 2 ^ W) →
      BlocksFrom L p (ys.flatMap numberWord : List (Symbol x)) → Fm SIM OUT DG REM WD T L W σ ((x + 4) * p) o 0 0 →
      Runs cap (formatter SIM OUT DG REM WD T x) σ (ys.length * (entryCost x W + 2) + 1)
        (fun τ => ∃ p', Fm SIM OUT DG REM WD T L W τ p'
          (o ++ ys.flatMap (WilliamsLoaderForms.fixedWidthNatBits W)) 0 0) := by
  intro ys
  induction ys with
  | nil =>
    intro p o σ _ hB hf
    have hw := fm_wbit hf
    rw [show (x + 4) * p = (x + 4) * p + 0 from rfl] at hw
    refine Runs.of (WXExec.mono (WXExec.whsF (by rw [hw]; exact hB.nil)) (by simp)) ⟨_, by simpa using hf⟩
  | cons y ys ih =>
    intro p o σ hys hB hf
    have hB0 := hB
    rw [List.flatMap_cons] at hB0
    have hw : wbit σ SIM = true := by
      rw [fm_wbit hf]
      rw [numberWord_eq, List.append_assoc] at hB0
      cases hD : digitBits y with
      | nil =>
        rw [hD] at hB0
        have := (show BlocksFrom L p (Symbol.separator :: ys.flatMap numberWord) by simpa using hB0).head 0
          (by omega)
        rw [Nat.add_zero] at this; rw [this]; exact code_separator.1
      | cons b D' =>
        rw [hD] at hB0
        have := (show BlocksFrom L p (Symbol.digit b :: (D'.map Symbol.digit ++ Symbol.separator ::
          ys.flatMap numberWord)) by simpa using hB0).head 0 (by omega)
        rw [Nat.add_zero] at this; rw [this]; exact (code_digit b).1
    have hB1 : BlocksFrom L p (numberWord y ++ ys.flatMap numberWord : List (Symbol x)) := by
      rwa [List.flatMap_cons] at hB
    obtain ⟨τ, e1, q1⟩ := entry_spec hSO hR hcap y (hys y (by simp)) _ p o σ hB1 hf
    obtain ⟨ρ, e2, q2⟩ := ih _ _ τ (fun z hz => hys z (by simp [hz])) (hB1.drop _) q1
    refine ⟨ρ, WXExec.mono (WXExec.whsT hw e1 e2) (by simp only [List.length_cons, Nat.succ_mul]; omega), ?_⟩
    obtain ⟨p', hp'⟩ := q2
    exact ⟨p', by simpa [List.flatMap_cons, List.append_assoc] using hp'⟩

end Specs

end NearCubicGates.Adapters.Williams.Format
