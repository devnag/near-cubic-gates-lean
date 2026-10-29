import SourceAdapters.Refuter.CodeDecode

/-!
# The header of the machine description (input 7, the record codec, part 4)

proof of `cor:framed-refuter` ("The fixed-machine decoding cost is `a_M`") with SFM78 Condition 1
(`adapters/sourcetext/SFM78.txt` l.323–326, a program code "from which the transition table can be read").
`header` reads `code(M) = 1^t 0 1^s 0 ⟨start⟩ …` from the code stream and sets the registers the checker
uses: `T = t`, `WD = natBitLength s`, `EW = 1 + WD + 4t`, `HB = t + 1 + s + 1 + WD`, `AT = HB + 2s`,
`BS = 2^t·EW`, `START = start` (`cWd … cBs`, `CodeTable.lean`); the code head returns to `0`; every scratch
register ends at `0`. The cost depends only on `M` (part of `a_M`).
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

/-! ## States with a moved code head and a register file -/

/-- `σ` with the code head at `hd` and the registers `f`. -/
def hst (σ : St) (hd : ℕ) (f : Fin NR → ℕ) : St := ⟨Function.update σ.sh sCODE hd, σ.st, f, σ.cell⟩

@[simp] theorem hst_val (σ : St) (hd : ℕ) (f : Fin NR → ℕ) (r : Fin NR) : (hst σ hd f).val r = f r := rfl
@[simp] theorem hst_st (σ : St) (hd : ℕ) (f : Fin NR → ℕ) : (hst σ hd f).st = σ.st := rfl
@[simp] theorem hst_sh_code (σ : St) (hd : ℕ) (f : Fin NR → ℕ) : (hst σ hd f).sh sCODE = hd := by simp [hst]
theorem hst_setv (σ : St) (hd : ℕ) (f : Fin NR → ℕ) (r : Fin NR) (v : ℕ) :
    (hst σ hd f).setv r v = hst σ hd (Function.update f r v) := rfl
theorem hst_seth (σ : St) (hd : ℕ) (f : Fin NR → ℕ) (h : ℕ) : (hst σ hd f).seth sCODE h = hst σ h f := by
  unfold hst WState.seth; congr 1; funext j; by_cases hj : j = sCODE <;> simp [Function.update_apply, hj]
theorem hst_self (σ : St) (h : σ.sh sCODE = 0) : hst σ 0 σ.val = σ := by
  unfold hst; cases σ; congr 1; funext j; by_cases hj : j = sCODE <;> simp_all [Function.update_apply]

/-! ## Reads of the header -/

section Reads
variable (v : RepairOrdinary.Verifier)

/-- The code after its two unary fields. -/
def codeRest : List Bool :=
  fixedBits (cWd v) v.machine.start.val ++ (List.ofFn fun i : Fin v.stateCount => [v.machine.halted i, v.accepting i]).flatten ++
    (List.ofFn fun i : Fin v.stateCount =>
      (List.ofFn fun mask : Fin (2 ^ v.tapeCount) =>
        actionCode (cWd v) (v.machine.rule i (fun tape => mask.val.testBit tape.val))).flatten).flatten

theorem code_shape : code v = List.replicate v.tapeCount true ++ false ::
    (List.replicate v.stateCount true ++ false :: codeRest v) := by
  rw [code_split]; simp [codeRest, cWd, List.append_assoc]

theorem rd_rep_lt (n : ℕ) (rest : List Bool) {j : ℕ} (h : j < n) :
    readTapeBit (List.replicate n true ++ rest) j = true := by
  rw [rd_append_left (by simpa using h), rd_replicate _ _ h]

theorem rd_rep_mid (n : ℕ) (b : Bool) (rest : List Bool) : readTapeBit (List.replicate n true ++ b :: rest) n = b := by
  have := rd_append_right (List.replicate n true) (b :: rest) 0
  simpa [readTapeBit] using this

theorem code_rd_t (j : ℕ) (hj : j < v.tapeCount) : readTapeBit (code v) j = true := by
  rw [code_shape]; exact rd_rep_lt _ _ hj

theorem code_rd_t_end : readTapeBit (code v) v.tapeCount = false := by
  rw [code_shape]; exact rd_rep_mid _ _ _

theorem code_rd_s (j : ℕ) (hj : j < v.stateCount) : readTapeBit (code v) (v.tapeCount + 1 + j) = true := by
  rw [code_shape, show v.tapeCount + 1 + j = (List.replicate v.tapeCount true).length + (j + 1) by simp; omega,
    rd_append_right, rd_cons_succ]
  exact rd_rep_lt _ _ hj

theorem code_rd_s_end : readTapeBit (code v) (v.tapeCount + 1 + v.stateCount) = false := by
  rw [code_shape, show v.tapeCount + 1 + v.stateCount = (List.replicate v.tapeCount true).length +
    (v.stateCount + 1) by simp; omega, rd_append_right, rd_cons_succ]
  exact rd_rep_mid _ _ _

end Reads

/-! ## Counting a run of ones -/

def onesCount (C : Fin NR) : Pg := .whs sCODE (.seq (WMX.inc C) (WMX.fwd sCODE))

theorem onesCount_spec (σ : St) (hd : ℕ) (f : Fin NR → ℕ) (C : Fin NR) (n : ℕ)
    (hr : ∀ k < n, readTapeBit (σ.st sCODE) (hd + k) = true) (he : readTapeBit (σ.st sCODE) (hd + n) = false)
    (hcap : f C + n < cap) :
    WXExec cap (onesCount C) (hst σ hd f) (hst σ (hd + n) (Function.update f C (f C + n))) (n * 7 + 1) := by
  have e := whsE cap (i := sCODE) (body := .seq (WMX.inc C) (WMX.fwd sCODE))
    (fun k => hst σ (hd + k) (Function.update f C (f C + k))) n 5
    (fun k hk => by simp only [wbit, hst_st, hst_sh_code]; exact hr k hk)
    (by simp only [wbit, hst_st, hst_sh_code]; exact he)
    (fun k hk => by
      have e1 := WXExec.inc cap C (hst σ (hd + k) (Function.update f C (f C + k))) (by simp; omega)
      rw [hst_val, Function.update_self, hst_setv] at e1
      have e2 := WXExec.fwd cap sCODE (hst σ (hd + k) (Function.update (Function.update f C (f C + k)) C (f C + k + 1)))
      rw [hst_sh_code, hst_seth] at e2
      refine (WXExec.seq e1 e2).cast cap ?_ le_rfl
      rw [Function.update_idem]; congr 1)
  simp only [Nat.add_zero, Function.update_eq_self] at e
  exact e.mono (by omega)

/-! ## Register steps on `hst` states -/

section HstSteps
variable (σ : St) (hd : ℕ) (F : Fin NR → ℕ)

theorem hst_inc (r : Fin NR) (h : F r < cap) :
    WXExec cap (WMX.inc r) (hst σ hd F) (hst σ hd (Function.update F r (F r + 1))) 3 := by
  have := WXExec.inc cap r (hst σ hd F) (by simpa using h); rwa [hst_val, hst_setv] at this

theorem hst_clr (r : Fin NR) (h : F r ≤ cap) :
    WXExec cap (clr r) (hst σ hd F) (hst σ hd (Function.update F r 0)) (3 * F r + 1) := by
  have := clr_spec cap r (hst σ hd F) (by simpa using h); rwa [hst_val, hst_setv] at this

theorem hst_addR {A B T : Fin NR} (hAB : A ≠ B) (hAT : A ≠ T) (hBT : B ≠ T) (hT : F T = 0) (h : F B + F A ≤ cap) :
    WXExec cap (addR A B T) (hst σ hd F) (hst σ hd (Function.update F B (F B + F A))) (18 * F A + 3) := by
  have := addR_spec cap hAB hAT hBT (hst σ hd F) (by simpa using hT) (by simpa using h)
  rwa [hst_val, hst_val, hst_setv] at this

theorem hst_dbl {P PT TA : Fin NR} (h1 : P ≠ PT) (h2 : P ≠ TA) (h3 : PT ≠ TA) (hPT : F PT = 0) (hTA : F TA = 0)
    (h : 2 * F P ≤ cap) :
    WXExec cap (dbl P PT TA) (hst σ hd F) (hst σ hd (Function.update F P (2 * F P))) (39 * F P + 9) := by
  have := dbl_spec cap h1 h2 h3 (hst σ hd F) (by simpa using hPT) (by simpa using hTA) (by simpa using h)
  rwa [hst_val, hst_setv] at this

theorem hst_fwd : WXExec cap (WMX.fwd sCODE) (hst σ hd F) (hst σ (hd + 1) F) 1 := by
  have := WXExec.fwd cap sCODE (hst σ hd F); rwa [hst_sh_code, hst_seth] at this

theorem hst_bwdK {K K2 : Fin NR} (hKK : K ≠ K2) (hK2 : F K2 = 0) (h : 2 * F K ≤ cap) :
    WXExec cap (bwdK sCODE K K2) (hst σ hd F) (hst σ (hd - F K) F) (16 * F K + 3) := by
  have := bwdK_spec cap (S := sCODE) hKK (hst σ hd F) (by simpa using hK2) (by simpa using h)
  rwa [hst_sh_code, hst_val, hst_seth] at this

theorem hst_half {R : Fin NR} (hR : R ≠ rQ ∧ R ≠ rBIT) (hQ : F rQ = 0) (hB : F rBIT = 0) (h : F R + 2 ≤ cap) :
    WXExec cap (halfLoop R rQ rBIT) (hst σ hd F)
      (hst σ hd (Function.update (Function.update (Function.update F R 0) rQ (F R / 2)) rBIT (F R % 2))) (5 * F R + 10) := by
  have := half_move cap R hR (hst σ hd F) (by simpa using hQ) (by simpa using hB) (by simpa using h)
  rwa [hst_val, hst_setv, hst_setv, hst_setv] at this

theorem hst_move {A B : Fin NR} (hAB : A ≠ B) (hB : F B = 0) (h : F A ≤ cap) :
    WXExec cap (.wm (WM.move A B)) (hst σ hd F) (hst σ hd (Function.update (Function.update F A 0) B (F A))) (7 * F A + 1) := by
  have := WXExec.wm (wmove_spec (cap := cap) A B hAB (F A) (hst σ hd F) (by simp) (by simpa using h) (by simp [hB]; omega))
  rw [hst_setv, hst_setv] at this
  simpa [hB, Function.update_apply, Ne.symm hAB] using this

end HstSteps

/-! ## Counting binary digits -/

def cntLoop (R C : Fin NR) : Pg :=
  .whr R (.seq (halfLoop R rQ rBIT) (.seq (clr rBIT) (.seq (WMX.inc C) (.wm (WM.move rQ R)))))

theorem cntLoop_spec (σ : St) (hd : ℕ) (f : Fin NR → ℕ) {R C : Fin NR}
    (h1 : R ≠ C) (h2 : R ≠ rQ) (h3 : R ≠ rBIT) (h4 : C ≠ rQ) (h5 : C ≠ rBIT) (hQ : f rQ = 0) (hB : f rBIT = 0) (a n : ℕ)
    (hpos : ∀ k < n, a / 2 ^ k ≠ 0) (hz : a / 2 ^ n = 0) (hcap : 2 * a + f C + n + 4 ≤ cap) :
    WXExec cap (cntLoop R C) (hst σ hd (Function.update (Function.update f R a) C (f C)))
      (hst σ hd (Function.update (Function.update f R 0) C (f C + n))) (n * (9 * a + 22) + 1) := by
  have h6 : rQ ≠ rBIT := by decide
  have h1' := Ne.symm h1; have h2' := Ne.symm h2; have h3' := Ne.symm h3
  have h4' := Ne.symm h4; have h5' := Ne.symm h5; have h6' := Ne.symm h6
  have e := whrE cap (r := R) (st := fun k => hst σ hd (Function.update (Function.update f R (a / 2 ^ k)) C (f C + k)))
    n (9 * a + 20)
    (fun k hk => by simp [Function.update_apply, h1, hpos k hk])
    (by simp [Function.update_apply, h1, hz])
    (fun k hk => by
      set G := Function.update (Function.update f R (a / 2 ^ k)) C (f C + k) with hG
      have gR : G R = a / 2 ^ k := by simp [G, Function.update_apply, h1]
      have hv : a / 2 ^ k ≤ a := Nat.div_le_self _ _
      have e1 := hst_half cap σ hd G ⟨h2, h3⟩ (by simp [G, Function.update_apply, h1, h2, h3, h4, h5, h6, h1', h2', h3', h4', h5', h6', hQ])
        (by simp [G, Function.update_apply, h1, h2, h3, h4, h5, h6, h1', h2', h3', h4', h5', h6', hB]) (by rw [gR]; omega)
      set G1 := Function.update (Function.update (Function.update G R 0) rQ (G R / 2)) rBIT (G R % 2) with hG1
      have e2 := hst_clr cap σ hd G1 rBIT (by simp [G1]; omega)
      set G2 := Function.update G1 rBIT 0 with hG2
      have e3 := hst_inc cap σ hd G2 C (by simp [G2, G1, G, Function.update_apply, h1, h2, h3, h4, h5, h6, h1', h2', h3', h4', h5', h6']; omega)
      set G3 := Function.update G2 C (G2 C + 1) with hG3
      have e4 := hst_move cap σ hd G3 (A := rQ) (B := R) (Ne.symm h2)
        (by simp [G3, G2, G1, G, Function.update_apply, h1, h2, h3, h4, h5, h6, h1', h2', h3', h4', h5', h6']) (by simp [G3, G2, G1, G, Function.update_apply, h1, h2, h3, h4, h5, h6, h1', h2', h3', h4', h5', h6']; omega)
      refine (WXExec.seq e1 (WXExec.seq e2 (WXExec.seq e3 e4))).cast cap ?_ ?_
      · have hd' : a / 2 ^ k / 2 = a / 2 ^ (k + 1) := by rw [Nat.div_div_eq_div_mul, pow_succ]
        congr 1; funext r
        simp only [G3, G2, G1, G, Function.update_apply]
        by_cases r1 : r = R
        · subst r1; simp [h1, h2, h3, h4, h5, h6, h1', h2', h3', h4', h5', h6', hd']
        · by_cases r2 : r = C
          · subst r2; simp [h1, h2, h3, h4, h5, h6, h1', h2', h3', h4', h5', h6']; omega
          · by_cases r3 : r = rQ
            · subst r3; simp [h1, h2, h3, h4, h5, h6, h1', h2', h3', h4', h5', h6', hQ]
            · by_cases r4 : r = rBIT
              · subst r4; simp [h1, h2, h3, h4, h5, h6, h1', h2', h3', h4', h5', h6', hB]
              · simp [r1, r2, r3, r4]
      · simp only [G3, G2, G1, G, Function.update_apply]
        simp [h1, h2, h3, h4, h5, h6, h1', h2', h3', h4', h5', h6']
        generalize a / 2 ^ k = v at hv ⊢
        omega)
  simp only [pow_zero, Nat.div_one, Nat.add_zero, hz] at e
  exact e

/-! ## Reading the start control -/

def stBody : Pg := .seq (.ifs sCODE (addR rP rSTART rTA) WMX.skip) (.seq (dbl rP rPT rTA) (WMX.fwd sCODE))

theorem stLoop_spec (σ : St) (off : ℕ) (f : Fin NR → ℕ) (x w : ℕ)
    (hrd : ∀ k < w, readTapeBit (σ.st sCODE) (off + k) = x.testBit k)
    (hPT : f rPT = 0) (hTA : f rTA = 0) (hTG : f rTG = 0) (hW : f rWD = w) (hcap : 4 * 2 ^ w + 4 * w + 8 ≤ cap) :
    WXExec cap (repK rWD rTG stBody) (hst σ off (Function.update (Function.update f rP 1) rSTART 0))
      (hst σ (off + w) (Function.update (Function.update f rP (2 ^ w)) rSTART (x % 2 ^ w))) (w * (60 * 2 ^ w + 30) + 7 * w + 3) := by
  have e := Runs.repE (cap := cap) (K := rWD) (K2 := rTG) (body := stBody) (by decide) (60 * 2 ^ w + 22) w
    (fun k => hst σ (off + k) (Function.update (Function.update f rP (2 ^ k)) rSTART (x % 2 ^ k)))
    (by omega) (fun k => by simp [Function.update_apply]) (fun k => by simp [Function.update_apply])
    (fun k hk v1 v2 => by
      rw [hst_setv, hst_setv, hst_setv, hst_setv]
      set G := Function.update (Function.update (Function.update (Function.update f rP (2 ^ k)) rSTART (x % 2 ^ k)) rWD v1) rTG v2
        with hG
      have gP : G rP = 2 ^ k := by simp [G, Function.update_apply]
      have gS : G rSTART = x % 2 ^ k := by simp [G, Function.update_apply]
      have hpk : 2 ^ k ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) hk.le
      have hmod : x % 2 ^ k < 2 ^ k := Nat.mod_lt _ (by positivity)
      have hstep : x % 2 ^ (k + 1) = x % 2 ^ k + 2 ^ k * (x / 2 ^ k % 2) := Nat.mod_pow_succ
      have hbit := testBit_eq_mod x k
      -- the conditional add
      have eIf : WXExec cap (.ifs sCODE (addR rP rSTART rTA) WMX.skip) (hst σ (off + k) G)
          (hst σ (off + k) (Function.update G rSTART (x % 2 ^ (k + 1)))) (18 * 2 ^ k + 4) := by
        by_cases hb : x.testBit k
        · have hm : x / 2 ^ k % 2 = 1 := by rw [hbit] at hb; simp at hb; omega
          have a1 := hst_addR cap σ (off + k) G (A := rP) (B := rSTART) (T := rTA) (by decide) (by decide) (by decide)
            (by simp [G, Function.update_apply, hTA]) (by rw [gS, gP]; omega)
          rw [gS, gP] at a1
          refine (WXExec.ifsT (by simp only [wbit, hst_st, hst_sh_code]; rw [hrd k hk, hb]) a1).cast cap ?_ le_rfl
          rw [hstep, hm]; ring_nf
        · have hm : x / 2 ^ k % 2 = 0 := by rw [hbit] at hb; simp at hb; omega
          refine (WXExec.ifsF (by simp only [wbit, hst_st, hst_sh_code]; rw [hrd k hk]; simpa using hb)
            (WXExec.skip cap _)).cast cap ?_ (by omega)
          rw [hstep, hm, Nat.mul_zero, Nat.add_zero, ← gS, Function.update_eq_self]
      have a2 := hst_dbl cap σ (off + k) (Function.update G rSTART (x % 2 ^ (k + 1))) (P := rP) (PT := rPT) (TA := rTA)
        (by decide) (by decide) (by decide) (by simp [G, Function.update_apply, hPT]) (by simp [G, Function.update_apply, hTA])
        (by simp [Function.update_apply, gP]; omega)
      have a3 := hst_fwd cap σ (off + k) (Function.update (Function.update G rSTART (x % 2 ^ (k + 1))) rP
        (2 * Function.update G rSTART (x % 2 ^ (k + 1)) rP))
      refine (WXExec.seq eIf (WXExec.seq a2 a3)).cast cap ?_ ?_
      · rw [show off + k + 1 = off + (k + 1) by ring]
        congr 1; funext r
        simp only [G, Function.update_apply]
        by_cases r1 : r = rP
        · subst r1; simp [pow_succ]; ring
        · by_cases r2 : r = rSTART
          · subst r2; simp
          · by_cases r3 : r = rWD
            · subst r3; simp
            · by_cases r4 : r = rTG
              · subst r4; simp
              · simp [r1, r2, r3, r4]
      · simp [Function.update_apply, gP]; omega)
    (by simp [Function.update_apply, hW]) (by simp [Function.update_apply, hTG])
  simp only [pow_zero, Nat.mod_one, Nat.add_zero] at e
  exact e

/-! ## The header program -/

def hdrA : Pg := .seq (onesCount rT) (.seq (WMX.fwd sCODE) (.seq (onesCount rM0) (WMX.fwd sCODE)))
def hdrWD : Pg := .seq (addR rM0 rTC rTA) (cntLoop rTC rWD)
def hdrST : Pg := .seq (WMX.inc rP) (.seq (repK rWD rTG stBody) (clr rP))
def hdrAr : Pg :=
  .seq (WMX.inc rEW) (.seq (addR rWD rEW rTA) (.seq (addR rT rEW rTA) (.seq (addR rT rEW rTA) (.seq (addR rT rEW rTA)
  (.seq (addR rT rEW rTA) (.seq (addR rT rHB rTA) (.seq (WMX.inc rHB) (.seq (addR rM0 rHB rTA) (.seq (WMX.inc rHB)
  (.seq (addR rWD rHB rTA) (.seq (addR rHB rAT rTA) (.seq (addR rM0 rAT rTA) (addR rM0 rAT rTA)))))))))))))
def hdrBS : Pg := .seq (WMX.inc rP) (.seq (repK rT rTG (dbl rP rPT rTA)) (.seq (mulR rP rA2 rEW rBS rTA) (clr rP)))
def hdrEnd : Pg := .seq (bwdK sCODE rHB rTB) (clr rM0)
def header : Pg := .seq hdrA (.seq hdrWD (.seq hdrST (.seq hdrAr (.seq hdrBS hdrEnd))))

/-! ## The arithmetic of the header on three registers -/

/-- `F` with `EW, HB, AT` set. -/
def u3 (F : Fin NR → ℕ) (a b c : ℕ) : Fin NR → ℕ :=
  Function.update (Function.update (Function.update F rEW a) rHB b) rAT c

section U3
variable (F : Fin NR → ℕ) (a b c v : ℕ)
@[simp] theorem u3_ew : u3 F a b c rEW = a := by simp [u3, Function.update_apply]
@[simp] theorem u3_hb : u3 F a b c rHB = b := by simp [u3, Function.update_apply]
@[simp] theorem u3_at : u3 F a b c rAT = c := by simp [u3]
theorem u3_other (r : Fin NR) (h1 : r ≠ rEW) (h2 : r ≠ rHB) (h3 : r ≠ rAT) : u3 F a b c r = F r := by
  simp [u3, Function.update_apply, h1, h2, h3]
theorem u3_upd_ew : Function.update (u3 F a b c) rEW v = u3 F v b c := by
  funext r; simp only [u3, Function.update_apply]; split_ifs <;> simp_all
theorem u3_upd_hb : Function.update (u3 F a b c) rHB v = u3 F a v c := by
  funext r; simp only [u3, Function.update_apply]; split_ifs <;> simp_all
theorem u3_upd_at : Function.update (u3 F a b c) rAT v = u3 F a b v := by
  funext r; simp only [u3, Function.update_apply]; split_ifs <;> simp_all
theorem u3_self (h1 : F rEW = 0) (h2 : F rHB = 0) (h3 : F rAT = 0) : u3 F 0 0 0 = F := by
  funext r; simp only [u3, Function.update_apply]; split_ifs <;> simp_all
end U3

theorem hdrAr_spec (σ : St) (hd : ℕ) (F : Fin NR → ℕ) (t S W : ℕ) (hT : F rT = t) (hM : F rM0 = S) (hW : F rWD = W)
    (h1 : F rEW = 0) (h2 : F rHB = 0) (h3 : F rAT = 0) (hTA : F rTA = 0) (hcap : 8 * (t + S + W + 2) ≤ cap) :
    WXExec cap hdrAr (hst σ hd F) (hst σ hd (u3 F (1 + W + 4 * t) (t + 1 + S + 1 + W) (t + 1 + S + 1 + W + 2 * S)))
      (200 * (t + S + W + 2)) := by
  have o : ∀ (a b c : ℕ) (r : Fin NR), r = rT ∨ r = rM0 ∨ r = rWD ∨ r = rTA → u3 F a b c r = F r := by
    intro a b c r hr; apply u3_other <;> rcases hr with rfl | rfl | rfl | rfl <;> decide
  have ta : ∀ a b c, u3 F a b c rTA = 0 := fun a b c => by rw [o a b c rTA (by simp), hTA]
  have d1 := hst_inc cap σ hd (u3 F 0 0 0) rEW (by simp; omega)
  rw [u3_ew, u3_upd_ew] at d1
  have d2 := hst_addR cap σ hd (u3 F (0 + 1) 0 0) (A := rWD) (B := rEW) (T := rTA) (by decide) (by decide) (by decide)
    (ta _ _ _) (by rw [o _ _ _ rWD (by simp), hW, u3_ew]; omega)
  rw [u3_ew, o _ _ _ rWD (by simp), hW, u3_upd_ew] at d2
  have d3 := hst_addR cap σ hd (u3 F (0 + 1 + W) 0 0) (A := rT) (B := rEW) (T := rTA) (by decide) (by decide) (by decide)
    (ta _ _ _) (by rw [o _ _ _ rT (by simp), hT, u3_ew]; omega)
  rw [u3_ew, o _ _ _ rT (by simp), hT, u3_upd_ew] at d3
  have d4 := hst_addR cap σ hd (u3 F (0 + 1 + W + t) 0 0) (A := rT) (B := rEW) (T := rTA) (by decide) (by decide)
    (by decide) (ta _ _ _) (by rw [o _ _ _ rT (by simp), hT, u3_ew]; omega)
  rw [u3_ew, o _ _ _ rT (by simp), hT, u3_upd_ew] at d4
  have d5 := hst_addR cap σ hd (u3 F (0 + 1 + W + t + t) 0 0) (A := rT) (B := rEW) (T := rTA) (by decide) (by decide)
    (by decide) (ta _ _ _) (by rw [o _ _ _ rT (by simp), hT, u3_ew]; omega)
  rw [u3_ew, o _ _ _ rT (by simp), hT, u3_upd_ew] at d5
  have d6 := hst_addR cap σ hd (u3 F (0 + 1 + W + t + t + t) 0 0) (A := rT) (B := rEW) (T := rTA) (by decide)
    (by decide) (by decide) (ta _ _ _) (by rw [o _ _ _ rT (by simp), hT, u3_ew]; omega)
  rw [u3_ew, o _ _ _ rT (by simp), hT, u3_upd_ew] at d6
  have d7 := hst_addR cap σ hd (u3 F (0 + 1 + W + t + t + t + t) 0 0) (A := rT) (B := rHB) (T := rTA) (by decide) (by decide) (by decide)
    (ta _ _ _) (by rw [o _ _ _ rT (by simp), hT, u3_hb]; omega)
  rw [u3_hb, o _ _ _ rT (by simp), hT, u3_upd_hb] at d7
  have d8 := hst_inc cap σ hd (u3 F (0 + 1 + W + t + t + t + t) (0 + t) 0) rHB (by simp; omega)
  rw [u3_hb, u3_upd_hb] at d8
  have d9 := hst_addR cap σ hd (u3 F (0 + 1 + W + t + t + t + t) (0 + t + 1) 0) (A := rM0) (B := rHB) (T := rTA) (by decide) (by decide)
    (by decide) (ta _ _ _) (by rw [o _ _ _ rM0 (by simp), hM, u3_hb]; omega)
  rw [u3_hb, o _ _ _ rM0 (by simp), hM, u3_upd_hb] at d9
  have d10 := hst_inc cap σ hd (u3 F (0 + 1 + W + t + t + t + t) (0 + t + 1 + S) 0) rHB (by simp; omega)
  rw [u3_hb, u3_upd_hb] at d10
  have d11 := hst_addR cap σ hd (u3 F (0 + 1 + W + t + t + t + t) (0 + t + 1 + S + 1) 0) (A := rWD) (B := rHB) (T := rTA) (by decide)
    (by decide) (by decide) (ta _ _ _) (by rw [o _ _ _ rWD (by simp), hW, u3_hb]; omega)
  rw [u3_hb, o _ _ _ rWD (by simp), hW, u3_upd_hb] at d11
  have d12 := hst_addR cap σ hd (u3 F (0 + 1 + W + t + t + t + t) (0 + t + 1 + S + 1 + W) 0) (A := rHB) (B := rAT) (T := rTA) (by decide) (by decide) (by decide)
    (ta _ _ _) (by rw [u3_hb, u3_at]; omega)
  rw [u3_hb, u3_at, u3_upd_at] at d12
  have d13 := hst_addR cap σ hd (u3 F (0 + 1 + W + t + t + t + t) (0 + t + 1 + S + 1 + W) (0 + (0 + t + 1 + S + 1 + W))) (A := rM0) (B := rAT) (T := rTA) (by decide) (by decide) (by decide)
    (ta _ _ _) (by rw [o _ _ _ rM0 (by simp), hM, u3_at]; omega)
  rw [u3_at, o _ _ _ rM0 (by simp), hM, u3_upd_at] at d13
  have d14 := hst_addR cap σ hd (u3 F (0 + 1 + W + t + t + t + t) (0 + t + 1 + S + 1 + W) (0 + (0 + t + 1 + S + 1 + W) + S)) (A := rM0) (B := rAT) (T := rTA) (by decide) (by decide)
    (by decide) (ta _ _ _) (by rw [o _ _ _ rM0 (by simp), hM, u3_at]; omega)
  rw [u3_at, o _ _ _ rM0 (by simp), hM, u3_upd_at] at d14
  have E := WXExec.seq d1 (WXExec.seq d2 (WXExec.seq d3 (WXExec.seq d4 (WXExec.seq d5 (WXExec.seq d6 (WXExec.seq d7
    (WXExec.seq d8 (WXExec.seq d9 (WXExec.seq d10 (WXExec.seq d11 (WXExec.seq d12 (WXExec.seq d13 d14))))))))))))
  rw [u3_self F h1 h2 h3] at E
  refine E.cast cap ?_ ?_
  · congr 2 <;> omega
  · omega

/-- The registers `header` sets. -/
abbrev hdrOut : List (Fin NR) := [rT, rWD, rEW, rHB, rAT, rBS, rSTART]
/-- The registers `header` needs at `0` (and leaves at `0`). -/
abbrev hdrZ : List (Fin NR) :=
  [rT, rM0, rWD, rSTART, rEW, rHB, rAT, rBS, rTC, rQ, rBIT, rP, rPT, rTA, rTB, rTG, rA2]

theorem powRep (σ : St) (hd : ℕ) (f : Fin NR → ℕ) (t : ℕ) (hPT : f rPT = 0) (hTA : f rTA = 0) (hTG : f rTG = 0)
    (hT : f rT = t) (hcap : 4 * 2 ^ t + 4 * t + 8 ≤ cap) :
    WXExec cap (repK rT rTG (dbl rP rPT rTA)) (hst σ hd (Function.update f rP 1))
      (hst σ hd (Function.update f rP (2 ^ t))) (t * (39 * 2 ^ t + 17) + 7 * t + 3) := by
  have e := Runs.repE (cap := cap) (K := rT) (K2 := rTG) (body := dbl rP rPT rTA) (by decide) (39 * 2 ^ t + 9) t
    (fun k => hst σ hd (Function.update f rP (2 ^ k))) (by omega) (fun k => by simp [Function.update_apply])
    (fun k => by simp [Function.update_apply])
    (fun k hk v1 v2 => by
      rw [hst_setv, hst_setv, hst_setv, hst_setv]
      have hpk : 2 ^ k ≤ 2 ^ t := Nat.pow_le_pow_right (by norm_num) hk.le
      have a1 := hst_dbl cap σ hd (Function.update (Function.update (Function.update f rP (2 ^ k)) rT v1) rTG v2)
        (P := rP) (PT := rPT) (TA := rTA) (by decide) (by decide) (by decide) (by simp [Function.update_apply, hPT])
        (by simp [Function.update_apply, hTA]) (by simp [Function.update_apply]; omega)
      refine a1.cast cap ?_ (by simp [Function.update_apply]; omega)
      congr 1; funext r; simp only [Function.update_apply]
      by_cases r1 : r = rP
      · subst r1; simp [pow_succ]; ring
      · simp [r1])
    (by simp [Function.update_apply, hT]) (by simp [Function.update_apply, hTG])
  simpa using e

set_option maxHeartbeats 400000 in
/-- **The header** (proof of `cor:framed-refuter`; SFM78 Condition 1): the checker's header registers from `code(M)`. -/
theorem header_spec (σ : St) (v : RepairOrdinary.Verifier) (hcode : σ.st sCODE = code v) (hh : σ.sh sCODE = 0)
    (hz : ∀ R ∈ hdrZ, σ.val R = 0) (hcap : 200 * ((code v).length + 1) ^ 2 ≤ cap) :
    ∃ F c, WXExec cap header σ (hst σ 0 F) c ∧ c ≤ 5000 * ((code v).length + 1) ^ 2 ∧
      F rT = v.tapeCount ∧ F rWD = cWd v ∧ F rEW = cEw v ∧ F rHB = cHb v ∧ F rAT = cAt v ∧ F rBS = cBs v ∧
      F rSTART = v.machine.start.val ∧ ∀ R, R ∉ hdrOut → F R = σ.val R := by
  have bt := tapeCount_le_code v
  have bs := stateCount_le_code v
  have bw := wd_le_code v
  have bpt := pow_t_le_code v
  have bpw := pow_wd_le v
  have bhb := hb_le_code v
  have bat := at_le_code v
  have hSpos := stateCount_pos v
  have hstart := ctl_lt_pow v v.machine.start
  set t := v.tapeCount with ht
  set S := v.stateCount with hS
  set W := cWd v with hW
  have hL2 : (code v).length + 1 ≤ ((code v).length + 1) ^ 2 := by nlinarith
  have z : ∀ R ∈ hdrZ, σ.val R = 0 := hz
  -- A: the two unary fields
  have a1 := onesCount_spec cap σ 0 σ.val rT t (fun k hk => by rw [hcode, Nat.zero_add]; exact code_rd_t v k hk)
    (by rw [hcode, Nat.zero_add]; exact code_rd_t_end v) (by rw [z rT (by decide)]; omega)
  have a2 := hst_fwd cap σ (0 + t) (Function.update σ.val rT (σ.val rT + t))
  have a3 := onesCount_spec cap σ (0 + t + 1) (Function.update σ.val rT (σ.val rT + t)) rM0 S
    (fun k hk => by rw [hcode, show 0 + t + 1 + k = t + 1 + k by omega]; exact code_rd_s v k hk)
    (by rw [hcode, show 0 + t + 1 + S = t + 1 + S by omega]; exact code_rd_s_end v)
    (by simp [Function.update_apply, z rM0 (by decide)]; omega)
  set F2 := Function.update (Function.update σ.val rT (σ.val rT + t)) rM0
    (Function.update σ.val rT (σ.val rT + t) rM0 + S) with hF2
  have a4 := hst_fwd cap σ (0 + t + 1 + S) F2
  have eA : WXExec cap hdrA (hst σ 0 σ.val) (hst σ (0 + t + 1 + S + 1) F2) _ :=
    WXExec.seq a1 (WXExec.seq a2 (WXExec.seq a3 a4))
  have f2T : F2 rT = t := by simp [F2, Function.update_apply, z rT (by decide)]
  have f2M : F2 rM0 = S := by simp [F2, Function.update_apply, z rM0 (by decide)]
  have f2o : ∀ R, R ≠ rT → R ≠ rM0 → F2 R = σ.val R := by intro R h1 h2; simp [F2, Function.update_apply, h1, h2]
  set off := 0 + t + 1 + S + 1 with hoff
  -- B: WD
  have b1 := hst_addR cap σ off F2 (A := rM0) (B := rTC) (T := rTA) (by decide) (by decide) (by decide)
    (by rw [f2o _ (by decide) (by decide), z rTA (by decide)]) (by rw [f2o rTC (by decide) (by decide), f2M, z rTC (by decide)]; omega)
  rw [f2o rTC (by decide) (by decide), f2M, z rTC (by decide), Nat.zero_add] at b1
  have hlogS : W = Nat.log 2 S + 1 := rfl
  have b2 := cntLoop_spec cap σ off F2 (R := rTC) (C := rWD) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [f2o rQ (by decide) (by decide), z rQ (by decide)]) (by rw [f2o rBIT (by decide) (by decide), z rBIT (by decide)])
    S W
    (fun k hk => by
      apply Nat.ne_of_gt; apply Nat.div_pos _ (by positivity)
      calc 2 ^ k ≤ 2 ^ Nat.log 2 S := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ ≤ S := Nat.pow_log_le_self 2 (by omega))
    (Nat.div_eq_of_lt (by rw [hlogS]; exact Nat.lt_pow_succ_log_self (by norm_num) _))
    (by rw [f2o rWD (by decide) (by decide), z rWD (by decide)]; nlinarith)
  have hx : Function.update (Function.update F2 rTC S) rWD (F2 rWD) = Function.update F2 rTC S := by
    funext r; by_cases r1 : r = rWD
    · subst r1; simp
    · simp [Function.update_apply, r1]
  rw [hx] at b2
  set F4 := Function.update (Function.update F2 rTC 0) rWD (F2 rWD + W) with hF4
  have eB : WXExec cap hdrWD (hst σ off F2) (hst σ off F4) _ := WXExec.seq b1 b2
  have f4 : ∀ R, F4 R = if R = rWD then W else F2 R := by
    intro R; by_cases r1 : R = rWD
    · subst r1; simp [F4, f2o rWD (by decide) (by decide), z rWD (by decide)]
    · by_cases r2 : R = rTC
      · subst r2; simp [F4, f2o rTC (by decide) (by decide), z rTC (by decide)]
      · simp [F4, Function.update_apply, r1, r2]
  -- C: START
  have c1 := hst_inc cap σ off F4 rP (by rw [f4, if_neg (by decide), f2o rP (by decide) (by decide), z rP (by decide)]; omega)
  rw [f4 rP, if_neg (by decide), f2o rP (by decide) (by decide), z rP (by decide), Nat.zero_add] at c1
  have hF4S : Function.update F4 rP 1 = Function.update (Function.update F4 rP 1) rSTART 0 := by
    funext r; by_cases r1 : r = rSTART
    · subst r1; simp [f4, f2o rSTART (by decide) (by decide), z rSTART (by decide)]
    · simp [Function.update_apply, r1]
  rw [hF4S] at c1
  have c2 := stLoop_spec cap σ off F4 v.machine.start.val W
    (fun k hk => by rw [hcode, hoff, show 0 + t + 1 + S + 1 + k = t + 1 + S + 1 + k by omega]; exact code_start v k hk)
    (by rw [f4, if_neg (by decide), f2o rPT (by decide) (by decide), z rPT (by decide)])
    (by rw [f4, if_neg (by decide), f2o rTA (by decide) (by decide), z rTA (by decide)])
    (by rw [f4, if_neg (by decide), f2o rTG (by decide) (by decide), z rTG (by decide)]) (by rw [f4, if_pos rfl])
    (by nlinarith)
  rw [Nat.mod_eq_of_lt hstart] at c2
  set F6 := Function.update (Function.update F4 rP (2 ^ W)) rSTART v.machine.start.val with hF6
  have c3 := hst_clr cap σ (off + W) F6 rP (by simp [F6]; omega)
  have eC : WXExec cap hdrST (hst σ off F4) (hst σ (off + W) (Function.update F6 rP 0)) _ :=
    WXExec.seq c1 (WXExec.seq c2 c3)
  set F7 := Function.update F6 rP 0 with hF7
  have f7 : ∀ R, F7 R = if R = rSTART then v.machine.start.val else F4 R := by
    intro R; by_cases r1 : R = rSTART
    · subst r1; simp [F7, F6]
    · by_cases r2 : R = rP
      · subst r2; simp [F7, f4, f2o rP (by decide) (by decide), z rP (by decide)]
      · simp [F7, F6, Function.update_apply, r1, r2]
  have v7 : ∀ R, R ∉ [rSTART, rWD, rT, rM0] → F7 R = σ.val R := by
    intro R hR
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hR
    rw [f7, if_neg hR.1, f4, if_neg hR.2.1, f2o R hR.2.2.1 hR.2.2.2]
  have g7 : F7 rT = t ∧ F7 rM0 = S ∧ F7 rWD = W := by
    refine ⟨?_, ?_, ?_⟩ <;> simp only [f7, f4, if_neg (show ¬ (rT = rSTART) by decide),
      if_neg (show ¬ (rM0 = rSTART) by decide), if_neg (show ¬ (rWD = rSTART) by decide),
      if_neg (show ¬ (rT = rWD) by decide), if_neg (show ¬ (rM0 = rWD) by decide), if_true, f2T, f2M]
  obtain ⟨g7T, g7M, g7W⟩ := g7
  -- D: EW, HB, AT
  have dD := hdrAr_spec cap σ (off + W) F7 t S W g7T g7M g7W (v7 rEW (by decide) ▸ z rEW (by decide))
    (v7 rHB (by decide) ▸ z rHB (by decide)) (v7 rAT (by decide) ▸ z rAT (by decide))
    (v7 rTA (by decide) ▸ z rTA (by decide)) (by nlinarith)
  set G := u3 F7 (1 + W + 4 * t) (t + 1 + S + 1 + W) (t + 1 + S + 1 + W + 2 * S) with hG
  have gO : ∀ R, R ∉ [rEW, rHB, rAT] → G R = F7 R := by
    intro R hR; simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hR
    exact u3_other _ _ _ _ R hR.1 hR.2.1 hR.2.2
  have gz : ∀ R, R ∉ [rEW, rHB, rAT, rSTART, rWD, rT, rM0] → G R = 0 → True := fun _ _ _ => trivial
  have gv : ∀ R ∈ hdrZ, R ∉ [rEW, rHB, rAT, rSTART, rWD, rT, rM0] → G R = 0 := by
    intro R hR hn
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
    rw [gO R (by simp [hn.1, hn.2.1, hn.2.2.1]), v7 R (by simp [hn.2.2.2.1, hn.2.2.2.2.1, hn.2.2.2.2.2.1,
      hn.2.2.2.2.2.2]), z R hR]
  -- E: BS
  have e1 := hst_inc cap σ (off + W) G rP (by rw [gv rP (by decide) (by decide)]; omega)
  rw [gv rP (by decide) (by decide), Nat.zero_add] at e1
  have e2 := powRep cap σ (off + W) G t (gv rPT (by decide) (by decide)) (gv rTA (by decide) (by decide))
    (gv rTG (by decide) (by decide)) (by rw [gO rT (by decide), g7T]) (by nlinarith)
  have e3 := mulR_spec cap (A := rP) (A2 := rA2) (B := rEW) (C := rBS) (T := rTA) (by decide)
    (hst σ (off + W) (Function.update G rP (2 ^ t)))
    (by simp [Function.update_apply, gv rA2 (by decide) (by decide)])
    (by simp [Function.update_apply, gv rTA (by decide) (by decide)])
    (by simp [Function.update_apply, gv rBS (by decide) (by decide), G]; nlinarith)
    (by simp; nlinarith)
  simp only [hst_val, Function.update_self, hst_setv] at e3
  rw [show Function.update G rP (2 ^ t) rEW = 1 + W + 4 * t by simp [Function.update_apply, G],
    show Function.update G rP (2 ^ t) rBS = 0 by simp [Function.update_apply, gv rBS (by decide) (by decide)],
    Nat.zero_add] at e3
  have e4 := hst_clr cap σ (off + W) (Function.update (Function.update G rP (2 ^ t)) rBS (2 ^ t * (1 + W + 4 * t))) rP
    (by simp [Function.update_apply]; omega)
  have eE : WXExec cap hdrBS (hst σ (off + W) G) _ _ := WXExec.seq e1 (WXExec.seq e2 (WXExec.seq e3 e4))
  set G4 := Function.update (Function.update (Function.update G rP (2 ^ t)) rBS (2 ^ t * (1 + W + 4 * t))) rP 0 with hG4
  -- F: rewind and clear
  have f1 := hst_bwdK cap σ (off + W) G4 (K := rHB) (K2 := rTB) (by decide)
    (by simp [G4, Function.update_apply, gv rTB (by decide) (by decide)]) (by simp [G4, Function.update_apply, G]; omega)
  rw [show off + W - G4 rHB = 0 by simp [G4, Function.update_apply, G]; omega] at f1
  have f2 := hst_clr cap σ 0 G4 rM0 (by simp [G4, Function.update_apply]; rw [gO rM0 (by decide), g7M]; omega)
  have eF : WXExec cap hdrEnd (hst σ (off + W) G4) _ _ := WXExec.seq f1 f2
  have E := WXExec.seq eA (WXExec.seq eB (WXExec.seq eC (WXExec.seq dD (WXExec.seq eE eF))))
  rw [hst_self σ hh] at E
  refine ⟨_, _, E, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have q1 : F6 rP = 2 ^ W := by simp [F6]
    have q2 : u3 F7 (1 + W + 4 * t) (t + 1 + S + 1 + W) (t + 1 + S + 1 + W + 2 * S) rM0 = S := by
      rw [u3_other _ _ _ _ rM0 (by decide) (by decide) (by decide)]; exact g7M
    simp only [G4, Function.update_apply, G, u3_hb, hst_val]
    simp only [q1, q2, show (rP = rBS) = False by decide, show (rHB = rP) = False by decide,
      show (rHB = rBS) = False by decide, show (rM0 = rP) = False by decide, show (rM0 = rBS) = False by decide,
      if_false, if_true]
    set L := (code v).length with hL
    have bW2 : 2 ^ W ≤ 2 * L := by omega
    have m1 : W * (9 * S + 22) ≤ L * (9 * L + 22) := Nat.mul_le_mul bw (by omega)
    have m2 : W * (60 * 2 ^ W + 30) ≤ L * (120 * L + 30) := Nat.mul_le_mul bw (by omega)
    have m3 : t * (39 * 2 ^ t + 17) ≤ L * (39 * L + 17) := Nat.mul_le_mul bt (by omega)
    have m4 : 2 ^ t * (18 * (1 + W + 4 * t) + 3 + 8) ≤ L * (90 * L + 29) := Nat.mul_le_mul bpt (by omega)
    nlinarith [m1, m2, m3, m4]
  · simp [G4, Function.update_apply]; rw [gO rT (by decide), g7T]
  · simp [G4, Function.update_apply]; rw [gO rWD (by decide), g7W]
  · simp [G4, Function.update_apply, G, cEw]; ring
  · (simp [G4, Function.update_apply, G, cHb]) <;> rfl
  · (simp [G4, Function.update_apply, G, cAt, cHb]) <;> rfl
  · simp [G4, Function.update_apply, cBs, cEw]; ring
  · simp [G4, Function.update_apply]; rw [gO rSTART (by decide), f7, if_pos rfl]
  · intro R hR
    by_cases r1 : R = rM0
    · subst r1; simp [z rM0 (by decide)]
    · by_cases r2 : R = rP
      · subst r2; simp [G4, Function.update_apply, z rP (by decide)]
      · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hR
        rw [Function.update_apply, if_neg r1]
        simp only [G4, Function.update_apply, r2, if_false, show R ≠ rBS from hR.2.2.2.2.2.1]
        rw [gO R (by simp [hR.2.2.1, hR.2.2.2.1, hR.2.2.2.2.1]), v7 R (by simp [hR.2.2.2.2.2.2, hR.2.1, hR.1, r1])]

end NearCubicGates.Adapters.Refuter.Mach
