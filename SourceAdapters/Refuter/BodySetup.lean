import SourceAdapters.Refuter.SecondPrep

/-!
# The hierarchy verifier's body, part 1: from the record to the first check (input 7, the paper Step 1)

proof of `lem:multitape-refuter` (`𝒟` "parses its input as `⟨M,N,z⟩` … This takes at most `c_0N` steps … enlarged to
include preparation of the actual tapes") and proof of `cor:framed-refuter` (`fr(x_1)`, `fr(w_i)`). From its cold start
(`coldSt`: the framed record on the input stream, the framed witness on the witness stream, every other
stream blank, every register `0`), `setup` = `parse ; decode ; header ; ALL := 1` reaches the reset state of
the first check, `ChkPre v w 0 fr(x_1) fr(w_i)`, with `TE = N`, `S = g` and the input unchanged.
-/

namespace NearCubicGates.Adapters.Refuter.Mach

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairSource NearCubicWires.RepairSource.VerifierEncoding
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.WordPrograms
open NearCubicGates.Adapters.Refuter

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable (cap : ℕ)

/-- The body's cold start: input `fr(x)`, witness `fr(w)`, all else blank and zero. -/
def coldSt (x w : List Bool) : St :=
  ⟨fun _ => 0, fun j => if j = sIN then RepairOrdinary.frame x else if j = sWIT then RepairOrdinary.frame w else [],
    fun _ => 0, false⟩

def setup : Pg := .seq parse (.seq decode (.seq header (WMX.inc rALL)))

theorem unrank_zero (g : ℕ) : List.ofFn (unrank g 0) = List.replicate g false := by
  apply List.ext_getElem (by simp); intro j h1 h2; simp [unrank]

theorem zeroField_record (M : OrdinaryWeakMachine) (N : ℕ) (hv : machineIndex M + 2 + N / 16 ≤ N) :
    zeroField (machineIndex M) (N - N / 16 - machineIndex M - 2) (N / 16) = List.ofFn (record M N 0) := by
  rw [record_list M N 0 hv, unrank_zero]; rfl

/-- The registers the parse sets and keeps. -/
abbrev setupR : List (Fin NR) := [rTE, rS, rALL]

theorem chkZ_hdrOut : ∀ R ∈ chkZ, R ∉ hdrOut := by decide
theorem chkZ_setupR : ∀ R ∈ chkZ, R ∉ setupR := by decide
theorem chkZ_ne_rAI : ∀ R ∈ chkZ, R ≠ rAI := by decide

set_option maxHeartbeats 400000 in
/-- **From the record to the first check** (proof of `lem:multitape-refuter`; proof of `cor:framed-refuter`). -/
theorem setup_spec (M : OrdinaryWeakMachine) (N i : ℕ) (w : List Bool) (hv : machineIndex M + 2 + N / 16 ≤ N)
    (hcap : 4 * (N + 4) + 2 * machineIndex M + 200 * ((code M.verifier).length + 1) ^ 2 ≤ cap) :
    ∃ σ1 c, WXExec cap setup (coldSt (List.ofFn (record M N i)) w) σ1 c ∧
      ChkPre M.verifier w 0 (List.ofFn (record M N 0)) (List.ofFn (unrank (N / 16) i)) σ1 ∧
      σ1.st sIN = RepairOrdinary.frame (List.ofFn (record M N i)) ∧ σ1.sh sIN = 0 ∧ σ1.val rTE = N ∧
      σ1.val rS = N / 16 ∧ σ1.val rLS = 0 ∧ σ1.val rVD = 0 ∧ σ1.val rALL = 1 ∧
      c ≤ 300 * (N + 3) + 30 * ((code M.verifier).length + 2) * (machineIndex M + 2) +
        5000 * ((code M.verifier).length + 1) ^ 2 + 10 := by
  set a := machineIndex M with ha
  set g := N / 16 with hg
  set b := N - g - a - 2 with hb
  set v := M.verifier with hvv
  set σ0 := coldSt (List.ofFn (record M N i)) w with hσ0
  have hz : (List.ofFn (unrank g i)).length = g := by simp
  -- parse
  obtain ⟨c1, e1⟩ := parse_spec cap σ0 a b (List.ofFn (unrank g i))
    (by simp [σ0, coldSt, record_list M N i hv]; rfl) (by simp [σ0, coldSt]) (by simp [σ0, coldSt])
    (by simp [σ0, coldSt]) (by simp [σ0, coldSt]) (by simp [σ0, coldSt]) (by simp [σ0, coldSt])
    (by simp [σ0, coldSt]) (by simp [σ0, coldSt]) (by simp [σ0, coldSt]) (by simp [σ0, coldSt]) (by simp [σ0, coldSt])
    (by rw [hz]; omega)
  obtain ⟨e1, hc1⟩ := e1
  rw [hz, show a + b + g + 2 = N by omega] at e1
  set P1 := ((((σ0.sets sXS (RepairOrdinary.frame (zeroField a b g))).sets sYS
    (RepairOrdinary.frame (List.ofFn (unrank g i)))).setv rAI a).setv rTE N).setv rS g with hP1
  -- decode
  have hcl : 1 ≤ (code v).length := le_trans (by have := v.twoTapes; omega) (tapeCount_le_code v)
  obtain ⟨c2, e2, hc2⟩ := decode_spec cap P1 (code v) hcl (by simp [P1, machineIndex_eq, ha, hvv])
    (by simp [P1, σ0, coldSt]) (by simp [P1, σ0, coldSt]) (by simp [P1, σ0, coldSt]) (by simp [P1, σ0, coldSt])
    (by simp [P1, σ0, coldSt]) (by simp [P1, σ0, coldSt]) (by simp [P1, σ0, coldSt]) (by simp [P1, σ0, coldSt])
    (by simp [P1, σ0, coldSt]) (by rw [← machineIndex_eq]; omega)
  set P2 := (P1.setv rAI 0).sets sCODE (code v) with hP2
  -- header
  obtain ⟨F, c3, e3, hc3, fT, fWD, fEW, fHB, fAT, fBS, fST, fO⟩ := header_spec cap P2 v (by simp [P2])
    (by simp [P2, P1, σ0, coldSt])
    (by
      intro R hR
      have h1 : R ≠ rAI := by rintro rfl; simp at hR
      have h2 : R ≠ rTE := by rintro rfl; simp at hR
      have h3 : R ≠ rS := by rintro rfl; simp at hR
      simp [P2, P1, σ0, coldSt, Function.update_apply, h1, h2, h3])
    (by omega)
  -- ALL := 1
  have fALL : F rALL = 0 := by rw [fO rALL (by decide)]; simp [P2, P1, σ0, coldSt, Function.update_apply]
  have e4 := WXExec.inc cap rALL (hst P2 0 F) (by simp [fALL]; omega)
  rw [hst_val, fALL, Nat.zero_add] at e4
  have fv : ∀ R, R ∉ hdrOut → R ∉ setupR → R ≠ rAI → F R = 0 := by
    intro R h1 h2 h3
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h2
    rw [fO R h1]; simp [P2, P1, σ0, coldSt, Function.update_apply, h2.1, h2.2.1, h3]
  set σ1 := (hst P2 0 F).setv rALL 1 with hσ1
  have sv : ∀ R, R ≠ rALL → σ1.val R = F R := by intro R hR; simp [σ1, Function.update_apply, hR]
  have sst : ∀ X, σ1.st X = P2.st X := by intro X; rfl
  have ssh : ∀ X, X ≠ sCODE → σ1.sh X = P2.sh X := by intro X hX; simp [σ1, hst, Function.update_apply, hX]
  refine ⟨σ1, _, WXExec.seq e1 (WXExec.seq e2 (WXExec.seq e3 e4)), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact {
      code := by rw [sst]; simp [P2]
      codeh := by simp [σ1]
      t := by rw [sv _ (by decide), fT]
      wd := by rw [sv _ (by decide), fWD]
      ew := by rw [sv _ (by decide), fEW]
      hb := by rw [sv _ (by decide), fHB]
      tbl := by rw [sv _ (by decide), fAT]
      bs := by rw [sv _ (by decide), fBS]
      start := by rw [sv _ (by decide), fST]
      wit := by rw [sst]; simp [P2, P1, σ0, coldSt]
      wh := by rw [ssh _ (by decide)]; simp [P2, P1, σ0, coldSt]
      rs := by intro h; rw [sst]; simp [P2, P1, σ0, coldSt, readTapeBit]
      rsh := by rw [ssh _ (by decide)]; simp [P2, P1, σ0, coldSt]
      simh := by rw [ssh _ (by decide)]; simp [P2, P1, σ0, coldSt]
      disph := by rw [ssh _ (by decide)]; simp [P2, P1, σ0, coldSt]
      xs := by rw [sst]; simp [P2, P1]; exact congrArg _ (zeroField_record M N hv)
      ys := by rw [sst]; simp [P2, P1]
      z := by rw [sst]; simp [P2, P1, σ0, coldSt]
      xh := by rw [ssh _ (by decide)]; simp [P2, P1, σ0, coldSt]
      yh := by rw [ssh _ (by decide)]; simp [P2, P1, σ0, coldSt]
      zh := by rw [ssh _ (by decide)]; simp [P2, P1, σ0, coldSt]
      vd := by rw [sv _ (by decide), fv _ (by decide) (by decide) (by decide)]; omega
      all := by simp [σ1]
      zero := by
        intro R hR
        have h0 : R ≠ rALL := by rintro rfl; simp at hR
        rw [sv R h0]
        exact fv R (chkZ_hdrOut R hR) (chkZ_setupR R hR) (chkZ_ne_rAI R hR) }
  · rw [sst]; simp [P2, P1, σ0, coldSt]
  · rw [ssh _ (by decide)]; simp [P2, P1, σ0, coldSt]
  · rw [sv _ (by decide), fO _ (by decide)]; simp [P2, P1, Function.update_apply]
  · rw [sv _ (by decide), fO _ (by decide)]; simp [P2, P1, Function.update_apply]
  · rw [sv _ (by decide), fv _ (by decide) (by decide) (by decide)]
  · rw [sv _ (by decide), fv _ (by decide) (by decide) (by decide)]
  · simp [σ1]
  · rw [hz] at hc1
    have hf : List.foldl idxStep 1 (code v) = a := rfl
    rw [hf] at hc2
    generalize 30 * ((code v).length + 2) * (a + 2) = X at hc2 ⊢
    generalize 5000 * ((code v).length + 1) ^ 2 = Y at hc3 ⊢
    omega

end NearCubicGates.Adapters.Refuter.Mach
