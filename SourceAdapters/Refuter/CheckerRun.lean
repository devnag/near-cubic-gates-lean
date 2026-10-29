import SourceAdapters.Refuter.Checker

/-!
# One complete check: read the cutoff, run every pass, clean up (input 7, F01 machine layer, part 16)

proof of `lem:multitape-refuter` (one simulation: "the hierarchy verifier guesses a positive length `r` in unary and
copies cells `0,…,r−1` of both prepared tapes … cutoff markers at cell `r`") and SFM78 l.222–233 (the
tape-by-tape check). `checker` = `readR` (the unary cutoff), `passes` (all `t_M` passes), then the
witness head is moved past the guessed trace and the cutoff track `RS` and `R0` are cleared, so that
a second simulation starts from the same reset state `ChkPre`.

`checker_spec`: from `ChkPre v wD p x y`, the flag `ALL` ends set iff it was set and the guessed trace
read at `p` passes `TraceChecks` on the framed tapes `fr(x), fr(y)` with the requested verdict `VD`;
the state is `ChkPre v wD (chkEnd …) x y` again, within `checkerCost v r n` steps
(`a_M + b_M(n + r + 1)`, `r` the guessed cutoff and `n` the guessed number of steps; the witness length
does not enter the cost).
-/

namespace NearCubicGates.Adapters.Refuter.Mach

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairSource NearCubicWires.RepairSource.VerifierEncoding
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.WordPrograms
open NearCubicGates.Adapters.Refuter

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable (cap : ℕ)

/-! ## Clearing the cutoff track -/

/-- `false` written at cells `0, …, k-1`. -/
def wzeros (L0 : List Bool) : ℕ → List Bool
  | 0 => L0
  | k + 1 => writeTapeBit (wzeros L0 k) k false

theorem wzeros_read (L0 : List Bool) : ∀ k h, readTapeBit (wzeros L0 k) h = if h < k then false else readTapeBit L0 h
  | 0, h => by simp [wzeros]
  | k + 1, h => by
    simp only [wzeros]
    rw [readTapeBit_writeTapeBit, wzeros_read L0 k h]
    by_cases hh : h = k
    · simp [hh]
    · by_cases hk : h < k
      · simp [hh, hk, show h < k + 1 by omega]
      · simp [hh, hk, show ¬ h < k + 1 by omega]

/-- Clear cells `0, …, R0-1` of `RS` and return its head. -/
def rsClean : Pg := .seq (repK rR0 rTG (.seq (WMX.wr sRS false) (WMX.fwd sRS))) (bwdK sRS rR0 rTB)

theorem rsClean_spec (σ : St) (hRS : σ.sh sRS = 0) (hTG : σ.val rTG = 0) (hTB : σ.val rTB = 0)
    (hcap : 2 * σ.val rR0 ≤ cap) :
    WXExec cap rsClean σ (σ.sets sRS (wzeros (σ.st sRS) (σ.val rR0))) (40 * σ.val rR0 + 7) := by
  have e1 := Runs.repE (cap := cap) (K := rR0) (K2 := rTG) (body := .seq (WMX.wr sRS false) (WMX.fwd sRS))
    (by decide) 3 (σ.val rR0) (fun k => (σ.sets sRS (wzeros (σ.st sRS) k)).seth sRS k) hcap
    (fun k => by simp) (fun k => by simp)
    (fun k _ v1 v2 => by
      have a1 := WXExec.wr cap sRS false ((((σ.sets sRS (wzeros (σ.st sRS) k)).seth sRS k).setv rR0 v1).setv rTG v2)
      have a2 := WXExec.fwd cap sRS ((((((σ.sets sRS (wzeros (σ.st sRS) k)).seth sRS k).setv rR0 v1).setv rTG
        v2)).sets sRS (writeTapeBit (wzeros (σ.st sRS) k) k false))
      refine (WXExec.seq a1 a2).cast cap ?_ le_rfl
      simp only [wzeros]
      wst)
    (by simp) (by simp [hTG])
  have e0 : (σ.sets sRS (wzeros (σ.st sRS) 0)).seth sRS 0 = σ := by
    simp only [wzeros]; wst
  rw [e0] at e1
  set σ1 := (σ.sets sRS (wzeros (σ.st sRS) (σ.val rR0))).seth sRS (σ.val rR0) with hσ1
  have e2 := bwdK_spec cap (S := sRS) (K := rR0) (K2 := rTB) (by decide) σ1 (by simp [σ1, hTB])
    (by simp [σ1]; omega)
  refine (WXExec.seq e1 e2).cast cap ?_ (by simp [σ1]; ring_nf; omega)
  simp only [σ1]
  wst

/-! ## The reset state of a check -/

/-- The registers that are zero between checks. -/
abbrev chkZ : List (Fin NR) :=
  [rR0, rI, rOK, rQ, rQN, rH, rMK, rP, rOFF, rBIT, rTA, rTB, rTC, rPT, rCONT, rWP, rW0, rW1, rM0, rM1, rDI,
    rA2, rTD, rI1, rWS, rTI, rTG]

/-- The streams a check may change. -/
abbrev chkS : List (Fin (NS + 1)) := [sSIM, sRS, sWIT, sDISP]

/-- The registers a check may change. -/
abbrev chkR : List (Fin NR) := rALL :: chkZ

/-- **The reset state of one check**: the decoded header of `v`, the witness `fr(wD)` read up to
logical position `p`, the framed simulated input tapes `fr(x)`, `fr(y)`, a blank cutoff track. -/
structure ChkPre (v : RepairOrdinary.Verifier) (wD : List Bool) (p : ℕ) (x y : List Bool) (σ : St) : Prop where
  code : σ.st sCODE = VerifierEncoding.code v
  codeh : σ.sh sCODE = 0
  t : σ.val rT = v.tapeCount
  wd : σ.val rWD = cWd v
  ew : σ.val rEW = cEw v
  hb : σ.val rHB = cHb v
  tbl : σ.val rAT = cAt v
  bs : σ.val rBS = cBs v
  start : σ.val rSTART = v.machine.start.val
  wit : σ.st sWIT = RepairOrdinary.frame wD
  wh : σ.sh sWIT = 2 * min p wD.length
  rs : ∀ h, readTapeBit (σ.st sRS) h = false
  rsh : σ.sh sRS = 0
  simh : σ.sh sSIM = 0
  disph : σ.sh sDISP = 0
  xs : σ.st sXS = RepairOrdinary.frame x
  ys : σ.st sYS = RepairOrdinary.frame y
  z : σ.st sZ = []
  xh : σ.sh sXS = 0
  yh : σ.sh sYS = 0
  zh : σ.sh sZ = 0
  vd : σ.val rVD ≤ 1
  all : σ.val rALL ≤ 1
  zero : ∀ R ∈ chkZ, σ.val R = 0

/-- The guessed cutoff of a check reading at `p`. -/
def chkR0 (wD : List Bool) (p : ℕ) : ℕ := gun wD (wD.length + 1) p

/-- The guessed displays of a check reading at `p`. -/
def chkDs (wD : List Bool) (t p : ℕ) : List (Fin t → Bool) := ptrace wD t (p + chkR0 wD p + 1)

/-- The logical witness position after a check reading at `p`. -/
def chkEnd (wD : List Bool) (t p : ℕ) : ℕ := pend wD t (p + chkR0 wD p + 1)

/-- The cost of one check: `a_M + b_M(n + r + 1)`. -/
def checkerCost (v : RepairOrdinary.Verifier) (r n : ℕ) : ℕ :=
  passesCost v r n + 200 * (r + 1) + 40 * (n * (1 + v.tapeCount) + 1) + 100

def checker : Pg :=
  .seq readR (.seq passes (.seq (fwdK sWIT rWS rTB) (.seq (clr rWS) (.seq rsClean (clr rR0)))))

theorem ChkPre.z0 {v : RepairOrdinary.Verifier} {wD : List Bool} {p : ℕ} {x y : List Bool} {σ : St}
    (h : ChkPre v wD p x y σ) {R : Fin NR} (hR : R ∈ chkZ) : σ.val R = 0 := h.zero R hR

/-- The state after reading the cutoff `r` at `p`. -/
def readSt (σ : St) (wD : List Bool) (p r : ℕ) : St :=
  ((σ.setv rR0 r).seth sWIT (2 * min (p + r + 1) wD.length)).sets sRS (wones (σ.st sRS) r)

/-- The state after the cleanup. -/
def cleanSt (τ : St) (r : ℕ) : St :=
  (((τ.seth sWIT (τ.sh sWIT + τ.val rWS)).setv rWS 0).sets sRS (wzeros (τ.st sRS) r)).setv rR0 0

theorem readSt_rest (v : RepairOrdinary.Verifier) (wD : List Bool) (p : ℕ) (x y : List Bool) (σ : St)
    (h : ChkPre v wD p x y σ) (r : ℕ) :
    RestEnc v r ⟨0, by have := v.twoTapes; omega⟩ wD (p + r + 1) (readSt σ wD p r) := by
  have hrs : ∀ k, readTapeBit (wones (σ.st sRS) r) k = decide (k < r) := wones_read _ h.rs r
  unfold readSt
  exact {
    enc := {
      code := by simp [h.code], codeh := by simp [h.codeh], t := by simp [h.t], wd := by simp [h.wd],
      ew := by simp [h.ew], hb := by simp [h.hb], tbl := by simp [h.tbl], bs := by simp [h.bs],
      ii := by simp [h.z0 (R := rI) (by decide)], ok := by simp [h.z0 (R := rOK) (by decide)],
      q := by simp [h.z0 (R := rQ) (by decide), zeroCtl],
      h := by simp [h.z0 (R := rH) (by decide)], sim := rfl, simh := by simp [h.simh],
      rs := by intro k; simpa using hrs k,
      rsh := by simp [h.rsh], wit := by simp [h.wit], disph := by simp [h.disph],
      zQN := by simp [h.z0 (R := rQN) (by decide)], zMK := by simp [h.z0 (R := rMK) (by decide)],
      zP := by simp [h.z0 (R := rP) (by decide)], zOFF := by simp [h.z0 (R := rOFF) (by decide)],
      zBIT := by simp [h.z0 (R := rBIT) (by decide)], zTA := by simp [h.z0 (R := rTA) (by decide)],
      zTB := by simp [h.z0 (R := rTB) (by decide)], zTC := by simp [h.z0 (R := rTC) (by decide)],
      zPT := by simp [h.z0 (R := rPT) (by decide)], zW0 := by simp [h.z0 (R := rW0) (by decide)],
      zW1 := by simp [h.z0 (R := rW1) (by decide)], zM0 := by simp [h.z0 (R := rM0) (by decide)],
      zM1 := by simp [h.z0 (R := rM1) (by decide)], zDI := by simp [h.z0 (R := rDI) (by decide)],
      zA2 := by simp [h.z0 (R := rA2) (by decide)] },
    cont := by simp [h.z0 (R := rCONT) (by decide)], wp := by simp [h.z0 (R := rWP) (by decide)],
    wit := by simp,
    start := by simp [h.start], vd := by simp [h.vd], r0 := by simp, all := by simp [h.all],
    i1 := by simp [h.z0 (R := rI1) (by decide)], tg := by simp [h.z0 (R := rTG) (by decide)],
    ws := by simp [h.z0 (R := rWS) (by decide)], xh := by simp [h.xh], yh := by simp [h.yh],
    zh := by simp [h.zh] }

theorem allR_zero (v : RepairOrdinary.Verifier) (r : ℕ) (wD : List Bool) (p' : ℕ) (τ2 : St)
    (hR2 : RestEnc v r ⟨0, by have := v.twoTapes; omega⟩ wD p' τ2) (hi2 : τ2.val rI = 0)
    (htd2 : τ2.val rTD = 0) (hti2 : τ2.val rTI = 0) :
    ∀ R ∈ allR, R ≠ rALL → R ≠ rWS → τ2.val R = 0 := by
  have hE2 := hR2.enc
  intro R hA ha hb
  simp only [allR, List.mem_cons, List.not_mem_nil, or_false] at hA
  rcases hA with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl
  · exact hE2.ok
  · simpa [zeroCtl] using hE2.q
  · exact hE2.h
  · exact hR2.wp
  · exact hE2.zMK
  · exact hE2.zOFF
  · exact hE2.zQN
  · exact hE2.zW0
  · exact hE2.zW1
  · exact hE2.zM0
  · exact hE2.zM1
  · exact hR2.cont
  · exact hE2.zBIT
  · exact absurd rfl ha
  · exact absurd rfl hb
  · exact hR2.i1
  · exact hi2
  · exact htd2
  · exact hti2

set_option maxHeartbeats 400000 in
theorem cleanSt_pre (v : RepairOrdinary.Verifier) (wD : List Bool) (p : ℕ) (x y : List Bool) (σ : St)
    (h : ChkPre v wD p x y σ) (r : ℕ) (τ2 : St)
    (hR2 : RestEnc v r ⟨0, by have := v.twoTapes; omega⟩ wD (p + r + 1) τ2)
    (hws2 : τ2.val rWS = witMoves wD (p + r + 1) (pend wD v.tapeCount (p + r + 1)))
    (hx2 : τ2.st sXS = RepairOrdinary.frame x) (hy2 : τ2.st sYS = RepairOrdinary.frame y) (hz2 : τ2.st sZ = [])
    (hi2 : τ2.val rI = 0) (htd2 : τ2.val rTD = 0) (hti2 : τ2.val rTI = 0)
    (hf2 : SameExcept (readSt σ wD p r) τ2 passS allR) :
    ChkPre v wD (pend wD v.tapeCount (p + r + 1)) x y (cleanSt τ2 r) := by
  have hE2 := hR2.enc
  have hzs : ∀ R ∈ chkZ, (cleanSt τ2 r).val R = 0 := by
    intro R hR
    by_cases a : R = rR0
    · subst a; simp [cleanSt]
    by_cases b : R = rWS
    · subst b; simp [cleanSt]
    have e : (cleanSt τ2 r).val R = τ2.val R := by simp [cleanSt, Function.update_apply, a, b]
    rw [e]
    by_cases hA : R ∈ allR
    · exact allR_zero v r wD _ τ2 hR2 hi2 htd2 hti2 R hA (by rintro rfl; simp at hR) b
    · rw [hf2.2.1 R hA]; simp [readSt, Function.update_apply, a, h.zero R hR]
  have hpe : p + r + 1 ≤ pend wD v.tapeCount (p + r + 1) := le_of_lt (gend_ge wD v.tapeCount _ _)
  have hm : min (p + r + 1) wD.length ≤ min (pend wD v.tapeCount (p + r + 1)) wD.length :=
    min_le_min_right _ hpe
  have hwh2 := hR2.wit
  exact {
    code := by simp [cleanSt, Function.update_apply, hE2.code]
    codeh := by simp [cleanSt, Function.update_apply, hE2.codeh]
    t := by simp [cleanSt, Function.update_apply, hE2.t]
    wd := by simp [cleanSt, Function.update_apply, hE2.wd]
    ew := by simp [cleanSt, Function.update_apply, hE2.ew]
    hb := by simp [cleanSt, Function.update_apply, hE2.hb]
    tbl := by simp [cleanSt, Function.update_apply, hE2.tbl]
    bs := by simp [cleanSt, Function.update_apply, hE2.bs]
    start := by simp [cleanSt, Function.update_apply, hR2.start]
    wit := by simp [cleanSt, Function.update_apply, hE2.wit]
    wh := by
      simp only [cleanSt, WState.setv_sh, WState.sets_sh, WState.seth_sh, Function.update_self, WState.setv_val]
      rw [hwh2, hws2]; unfold witMoves; omega
    rs := by
      intro k
      simp only [cleanSt, WState.setv_st, WState.sets_st, Function.update_self, WState.seth_st]
      rw [wzeros_read]
      split_ifs with hk
      · rfl
      · rw [hE2.rs k]; simp; omega
    rsh := by simp [cleanSt, Function.update_apply, hE2.rsh]
    simh := by simp [cleanSt, Function.update_apply, hE2.simh]
    disph := by simp [cleanSt, Function.update_apply, hE2.disph]
    xs := by simp [cleanSt, Function.update_apply, hx2]
    ys := by simp [cleanSt, Function.update_apply, hy2]
    z := by simp [cleanSt, Function.update_apply, hz2]
    xh := by simp [cleanSt, Function.update_apply, hR2.xh]
    yh := by simp [cleanSt, Function.update_apply, hR2.yh]
    zh := by simp [cleanSt, Function.update_apply, hR2.zh]
    vd := by simp [cleanSt, Function.update_apply, hR2.vd]
    all := by simp [cleanSt, Function.update_apply, hR2.all]
    zero := hzs }

theorem cleanSt_frame (σ : St) (wD : List Bool) (p r : ℕ) (τ2 : St)
    (hf2 : SameExcept (readSt σ wD p r) τ2 passS allR) : SameExcept σ (cleanSt τ2 r) chkS chkR := by
  refine ⟨fun X hX => ⟨?_, ?_⟩, fun R hR => ?_, ?_⟩
  · have a1 : X ≠ sRS := by rintro rfl; exact hX (by decide)
    have a2 : X ∉ passS := by
      intro m; apply hX; simp only [passS, chkS, List.mem_cons, List.not_mem_nil] at m ⊢; tauto
    have e : (cleanSt τ2 r).st X = τ2.st X := by simp [cleanSt, Function.update_apply, a1]
    rw [e, (hf2.1 X a2).1]
    simp [readSt, Function.update_apply, a1]
  · have a1 : X ≠ sWIT := by rintro rfl; exact hX (by decide)
    have a2 : X ∉ passS := by
      intro m; apply hX; simp only [passS, chkS, List.mem_cons, List.not_mem_nil] at m ⊢; tauto
    have e : (cleanSt τ2 r).sh X = τ2.sh X := by simp [cleanSt, Function.update_apply, a1]
    rw [e, (hf2.1 X a2).2]
    simp [readSt, Function.update_apply, a1]
  · have a1 : R ≠ rR0 := by rintro rfl; exact hR (by decide)
    have a2 : R ≠ rWS := by rintro rfl; exact hR (by decide)
    have a3 : R ∉ allR := by
      intro m; apply hR; simp only [allR, chkR, chkZ, List.mem_cons, List.not_mem_nil] at m ⊢; tauto
    have e : (cleanSt τ2 r).val R = τ2.val R := by simp [cleanSt, Function.update_apply, a1, a2]
    rw [e, hf2.2.1 R a3]
    simp [readSt, Function.update_apply, a1]
  · simpa [cleanSt, readSt] using hf2.2.2

set_option maxHeartbeats 400000 in
/-- **One check** (proof of `lem:multitape-refuter`; SFM78 l.222–233). -/
theorem checker_spec (v : RepairOrdinary.Verifier) (wD : List Bool) (p : ℕ) (x y : List Bool) (σ : St)
    (h : ChkPre v wD p x y σ)
    (hcap : 64 * ((VerifierEncoding.code v).length + 5 * wD.length + 8) ≤ cap) :
    ∃ τ n, WXExec cap checker σ τ n ∧ ChkPre v wD (chkEnd wD v.tapeCount p) x y τ ∧
      (τ.val rALL ≠ 0 ↔ σ.val rALL ≠ 0 ∧
        TraceChecks v.machine (chkR0 wD p) (v.inputTapes x y)
          (traceOfD v.machine v.machine.start (chkDs wD v.tapeCount p)) ∧
        v.accepting (controlAfter v.machine.start
          (traceOfD v.machine v.machine.start (chkDs wD v.tapeCount p))) = decide (σ.val rVD ≠ 0)) ∧
      SameExcept σ τ chkS chkR ∧
      n ≤ checkerCost v (chkR0 wD p) (chkDs wD v.tapeCount p).length := by
  have b3 := tapeCount_le_code v
  simp only [chkDs, chkEnd, chkR0]
  have hrle := gun_le wD (wD.length + 1) p
  generalize hr : gun wD (wD.length + 1) p = r at hrle ⊢
  have e1 : WXExec cap readR σ (readSt σ wD p r) (70 * (r + 1)) := by
    have := readR_spec cap σ wD p h.wit h.wh (h.z0 (by decide)) (h.z0 (by decide)) h.rsh (h.z0 (by decide))
      (h.z0 (by decide)) (by omega)
    rw [hr] at this
    exact this
  have hRest := readSt_rest v wD p x y σ h r
  obtain ⟨τ2, e2, hall2, hR2, hws2, hx2, hy2, hz2, hi2, htd2, hti2, hf2⟩ :=
    passes_spec cap v r wD (p + r + 1) x y (readSt σ wD p r) hRest
      (by simp [readSt, h.z0 (R := rI) (by decide)]) (by simp [readSt, h.z0 (R := rTD) (by decide)])
      (by simp [readSt, h.z0 (R := rTI) (by decide)]) (by simp [readSt, h.xs]) (by simp [readSt, h.ys])
      (by simp [readSt, h.z]) (by omega)
  generalize hn : (ptrace wD v.tapeCount (p + r + 1)).length = n at e2
  have he : pend wD v.tapeCount (p + r + 1) = p + r + 1 + n * (1 + v.tapeCount) + 1 := by
    rw [← hn]; exact gend_eq wD v.tapeCount (wD.length + 1) _
  have hwsle : τ2.val rWS ≤ 2 * (n * (1 + v.tapeCount) + 1) := by
    rw [hws2, he]; unfold witMoves; omega
  have hwsle' : τ2.val rWS ≤ 2 * wD.length := by rw [hws2]; unfold witMoves; omega
  have hE2 := hR2.enc
  have hr02 : τ2.val rR0 = r := hR2.r0
  -- move the witness head past the trace, clear `WS`, the cutoff track and `R0`
  have e3 := fwdK_spec cap (S := sWIT) (K := rWS) (K2 := rTB) (by decide) τ2 hE2.zTB (by lomega)
  have e4 := clr_spec cap rWS (τ2.seth sWIT (τ2.sh sWIT + τ2.val rWS)) (by simp; lomega)
  have e5 := rsClean_spec cap ((τ2.seth sWIT (τ2.sh sWIT + τ2.val rWS)).setv rWS 0) (by simp [hE2.rsh])
    (by simp [hR2.tg]) (by simp [hE2.zTB]) (by simp [hr02]; omega)
  have e6 := clr_spec cap rR0 (((τ2.seth sWIT (τ2.sh sWIT + τ2.val rWS)).setv rWS 0).sets sRS
    (wzeros (τ2.st sRS) r)) (by simp [hr02]; omega)
  refine ⟨cleanSt τ2 r, _, (WXExec.seq e1 (WXExec.seq e2 (WXExec.seq e3 (WXExec.seq e4
    (WXExec.seq (e5.cast cap (by simp [hr02]) le_rfl) e6))))).cast cap rfl le_rfl, ?_, ?_, ?_, ?_⟩
  · exact cleanSt_pre v wD p x y σ h r τ2 hR2 hws2 hx2 hy2 hz2 hi2 htd2 hti2 hf2
  · have e : (cleanSt τ2 r).val rALL = τ2.val rALL := by simp [cleanSt, Function.update_apply]
    rw [e, hall2]
    simp [readSt, Function.update_apply]
  · exact cleanSt_frame σ wD p r τ2 hf2
  · unfold checkerCost
    have a1 : ((τ2.seth sWIT (τ2.sh sWIT + τ2.val rWS)).setv rWS 0).val rR0 = r := by
      simp [Function.update_apply, hr02]
    have a2 : (((τ2.seth sWIT (τ2.sh sWIT + τ2.val rWS)).setv rWS 0).sets sRS (wzeros (τ2.st sRS) r)).val rR0 = r := by
      simp [Function.update_apply, hr02]
    have a3 : (τ2.seth sWIT (τ2.sh sWIT + τ2.val rWS)).val rWS = τ2.val rWS := rfl
    rw [a1, a2, a3]
    generalize passesCost v r n = P
    generalize n * (1 + v.tapeCount) = K at hwsle
    omega

end NearCubicGates.Adapters.Refuter.Mach
