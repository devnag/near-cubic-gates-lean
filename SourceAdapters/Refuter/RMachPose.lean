import SourceAdapters.Refuter.RMachArith
import SourceAdapters.Refuter.RProgramCall
import Proof.Gates.CheckedPCPP.Clear

/-!
# R poses a query: the compiler call, its ruler, and the cleanup (input 7, R: STEP's query half)

Paper anchor: proof of `lem:multitape-refuter` (each query is the output of ONE compiler — join X5(b) — written in full on the
query tape), (`O(N)` rounds on the same tapes), proof of `cor:framed-refuter`.

* `clrQO X`: the previous query `frame bits ++ blanks` is erased by walking its frame (`clrQO_spec`).
* `rcG`: rewinding the compiler's input stream writes the ruler `G = 1^|input|`; `tlG` appends the
  compiler's step tally `TL = 1^steps` and two more cells and rewinds (`G` bounds every cell the compiler
  can have touched, L's `CheckedPCPP.runFrom_far`), so L's `clearAll`/`clearSelfP` erase the compiler's work
  streams, `TL` and `G` — every scratch stream reads blank again.
-/

namespace NearCubicGates.Adapters.Refuter.RM

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicGates.Close.WordPrograms NearCubicGates.Adapters.Refuter
open NearCubicGates.Close.CheckedPCPP (clearPrefix clearPrefix_blank runFrom_far)
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)
open NearCubicWires.RepairSource.OrdinaryOracleCompose (clockMachine)

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {tc tT : ℕ} (cap : ℕ)

local notation "WS" => WState (NS tc tT) NR

/-! ## Erasing the previous query -/

/-- Erase the pairs `1 b` of `X` up to its frame terminator; `r0` counts, then rewinds. -/
def clrQO (X : Fin (NS tc tT + 1)) : WMX (NS tc tT) NR :=
  .seq (.whs X (.seq (WMX.wr X false) (.seq (WMX.fwd X) (.seq (WMX.wr X false) (.seq (WMX.fwd X)
    (.seq (WMX.inc r0) (WMX.inc r0))))))) (rew X r0)

theorem wtb_clear (L : List Bool) (m : ℕ) (h : m < L.length) :
    writeTapeBit (clearPrefix m L) m false = clearPrefix (m + 1) L := by
  unfold clearPrefix
  have hd : L.drop m = L[m] :: L.drop (m + 1) := List.drop_eq_getElem_cons h
  rw [hd]
  have := NearCubicGates.Close.WorkerArith.wtb_mid (List.replicate m false) (L[m] :: L.drop (m + 1)) false
  rw [List.length_replicate] at this
  rw [this]
  simp only [List.drop_succ_cons, List.drop_zero]
  rw [List.replicate_succ', List.append_assoc, List.singleton_append]

theorem rd_clear_ge (L : List Bool) (m q : ℕ) (h : m ≤ q) : readTapeBit (clearPrefix m L) q = readTapeBit L q := by
  unfold clearPrefix readTapeBit
  by_cases hq : q < L.length
  · rw [List.getD_append_right _ _ _ _ (by simp; omega), List.getD_eq_getElem _ _ (by simp; omega),
      List.getD_eq_getElem _ _ hq]
    simp [List.getElem_drop]
    congr 1; omega
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem clrQO_spec (X : Fin (NS tc tT + 1)) (σ : WS) (l rest : List Bool) (hX : σ.st X = fpre l ++ rest)
    (hrest : ∀ q, readTapeBit rest q = false) (hXh : σ.sh X = 0) (hr0 : σ.val r0 = 0)
    (hcap : 2 * l.length ≤ cap) :
    WXExec cap (clrQO X) σ (σ.sets X (clearPrefix (2 * l.length) (fpre l ++ rest))) (l.length * 27 + 3) := by
  set L := fpre l ++ rest with hL
  have hLlen : 2 * l.length ≤ L.length := by simp [L]
  let st : ℕ → WS := fun k => ((σ.sets X (clearPrefix (2 * k) L)).seth X (2 * k)).setv r0 (2 * k)
  have h0 : st 0 = σ := by
    simp only [st, Nat.mul_zero]
    have : clearPrefix 0 L = σ.st X := by simp [clearPrefix, hX, L]
    rw [this]; wst
  have hloop := loopS cap (i := X)
    (body := .seq (WMX.wr X false) (.seq (WMX.fwd X) (.seq (WMX.wr X false) (.seq (WMX.fwd X)
      (.seq (WMX.inc r0) (WMX.inc r0)))))) st l.length 15
    (fun k hk => by
      simp only [wbit, st, WState.setv_st, WState.seth_st, WState.sets_st, WState.setv_sh, WState.seth_sh,
        Function.update_self]
      rw [rd_clear_ge L _ _ le_rfl]; exact (rd_fpre l rest k hk).1)
    (by
      simp only [wbit, st, WState.setv_st, WState.seth_st, WState.sets_st, WState.setv_sh, WState.seth_sh,
        Function.update_self]
      rw [rd_clear_ge L _ _ le_rfl]; have := rd_fpre_end l rest 0; simp only [Nat.add_zero] at this
      rw [this]; exact hrest 0)
    (fun k hk => by
      have e1 := WXExec.wr cap X false (st k)
      have w1 : writeTapeBit ((st k).st X) ((st k).sh X) false = clearPrefix (2 * k + 1) L := by
        simp only [st, WState.setv_st, WState.seth_st, WState.sets_st, WState.setv_sh, WState.seth_sh,
          Function.update_self]
        exact wtb_clear L (2 * k) (by omega)
      rw [w1] at e1
      have e2 := WXExec.fwd cap X ((st k).sets X (clearPrefix (2 * k + 1) L))
      have e3 := WXExec.wr cap X false (((st k).sets X (clearPrefix (2 * k + 1) L)).seth X
        (((st k).sets X (clearPrefix (2 * k + 1) L)).sh X + 1))
      have w2 : writeTapeBit ((((st k).sets X (clearPrefix (2 * k + 1) L)).seth X
          (((st k).sets X (clearPrefix (2 * k + 1) L)).sh X + 1)).st X)
          ((((st k).sets X (clearPrefix (2 * k + 1) L)).seth X
          (((st k).sets X (clearPrefix (2 * k + 1) L)).sh X + 1)).sh X) false = clearPrefix (2 * k + 2) L := by
        simp only [st, WState.setv_st, WState.seth_st, WState.sets_st, WState.setv_sh, WState.seth_sh,
          WState.sets_sh, Function.update_self]
        rw [wtb_clear L (2 * k + 1) (by omega)]
      rw [w2] at e3
      set τ := (((st k).sets X (clearPrefix (2 * k + 1) L)).seth X
        (((st k).sets X (clearPrefix (2 * k + 1) L)).sh X + 1)).sets X (clearPrefix (2 * k + 2) L) with hτ
      have e4 := WXExec.fwd cap X τ
      have e5 := WXExec.inc cap r0 (τ.seth X (τ.sh X + 1)) (by simp [τ, st]; omega)
      have e6 := WXExec.inc cap r0 ((τ.seth X (τ.sh X + 1)).setv r0 ((τ.seth X (τ.sh X + 1)).val r0 + 1))
        (by simp [τ, st]; omega)
      refine (WXExec.seq e1 (WXExec.seq e2 (WXExec.seq e3 (WXExec.seq e4 (WXExec.seq e5 e6))))).cast cap ?_
        (by omega)
      simp only [τ, st, show 2 * (k + 1) = 2 * k + 2 by ring]
      wst)
  rw [h0] at hloop
  have e7 := rew_spec cap X r0 (st l.length) (2 * l.length) (by simp [st]) hcap
  refine (WXExec.seq hloop e7).cast cap ?_ (by omega)
  simp only [st]
  wst

theorem clearPrefix_fpre_blank (l rest : List Bool) (hrest : ∀ q, readTapeBit rest q = false) :
    ∀ q, readTapeBit (clearPrefix (2 * l.length) (fpre l ++ rest)) q = false := by
  intro q
  by_cases hq : 2 * l.length ≤ q
  · rw [rd_clear_ge _ _ _ hq]
    have := rd_fpre_end l rest (q - 2 * l.length)
    rw [show 2 * l.length + (q - 2 * l.length) = q by omega] at this
    rw [this]; exact hrest _
  · unfold clearPrefix readTapeBit
    rw [List.getD_append _ _ _ _ (by simp; omega)]
    simp

/-! ## The query point -/

theorem qcomp_spec (W : ℕ) (σ : WS) (lo hi vq : ℕ) (hLO : σ.st sLO = num W lo) (hHI : σ.st sHI = num W hi)
    (hQ : σ.st sQ = num W vq) (hsh : ∀ i, σ.sh i = 0) (hF : σ.val bF = 0) (hR : σ.val bR = 0)
    (hlh : lo + hi < 2 ^ W) (hcap : 2 * W + 1 ≤ cap) :
    WXExec cap (.seq (cp sQ sLO) (.seq (ad sQ sHI) (hf sQ))) σ (σ.sets sQ (num W ((lo + hi) / 2)))
      (120 * W + 11) := by
  have e1 := cp_spec (cap := cap) sQ sLO (by ds) σ vq lo hQ hLO hsh hF hR hcap
  have e2 := ad_spec (cap := cap) sQ sHI (by ds) (σ.sets sQ (num W lo)) lo hi (by simp)
    (by simp [Function.update_apply, Fin.ext_iff, hHI]) (by simp [hsh]) (by simp [hF]) (by simp [hR]) hlh hcap
  have e3 := hf_spec (cap := cap) sQ ((σ.sets sQ (num W lo)).sets sQ (num W (lo + hi))) (lo + hi) (by simp)
    (by simp [hsh]) (by simp [hR]) hlh hcap
  refine (WXExec.seq e1 (WXExec.seq e2 e3)).cast cap ?_ (by omega)
  rw [BinW.sets_sets, BinW.sets_sets]

/-! ## The ruler -/

/-- Rewind the compiler's input stream `D` by `rC`, writing one ruler cell per step. -/
def rcG (D : Fin (NS tc tT + 1)) : WMX (NS tc tT) NR :=
  .whr rC (.seq (WMX.wr sG true) (.seq (WMX.fwd sG) (.seq (WMX.bwd D) (.seq (WMX.inc rG) (WMX.dec rC)))))

theorem rcG_spec (D : Fin (NS tc tT + 1)) (hD : D ≠ sG) (σ : WS) (n : ℕ) (hDh : σ.sh D = n) (hC : σ.val rC = n)
    (hG : σ.st sG = []) (hGh : σ.sh sG = 0) (hrG : σ.val rG = 0) (hcap : n + 1 ≤ cap) :
    WXExec cap (rcG D) σ (((((σ.sets sG (List.replicate n true)).seth sG n).seth D 0).setv rG n).setv rC 0)
      (n * 13 + 1) := by
  let st : ℕ → WS := fun k => ((((σ.sets sG (List.replicate k true)).seth sG k).seth D (n - k)).setv rG k).setv rC (n - k)
  have h0 : st 0 = σ := by
    simp only [st, List.replicate_zero, Nat.sub_zero, ← hG, ← hGh, ← hDh, ← hC, ← hrG]; wst
  have hl := loopR cap (r := rC)
    (body := .seq (WMX.wr sG true) (.seq (WMX.fwd sG) (.seq (WMX.bwd D) (.seq (WMX.inc rG) (WMX.dec rC))))) st n 11
    (fun k hk => by simp [st]; omega) (by simp [st])
    (fun k hk => by
      have e1 := WXExec.wr cap sG true (st k)
      have w : writeTapeBit ((st k).st sG) ((st k).sh sG) true = List.replicate (k + 1) true := by
        simp only [st, WState.setv_st, WState.seth_st, WState.sets_st, WState.setv_sh, WState.seth_sh,
          Function.update_self, Function.update_of_ne hD.symm]
        have := wtb_append (List.replicate k true) true
        rw [List.length_replicate] at this
        rw [this, ← List.replicate_succ']
      rw [w] at e1
      have e2 := WXExec.fwd cap sG ((st k).sets sG (List.replicate (k + 1) true))
      have e3 := WXExec.bwd cap D (((st k).sets sG (List.replicate (k + 1) true)).seth sG
        (((st k).sets sG (List.replicate (k + 1) true)).sh sG + 1))
      set τ := (((st k).sets sG (List.replicate (k + 1) true)).seth sG
        (((st k).sets sG (List.replicate (k + 1) true)).sh sG + 1)).seth D ((((st k).sets sG
        (List.replicate (k + 1) true)).seth sG (((st k).sets sG (List.replicate (k + 1) true)).sh sG + 1)).sh D - 1)
        with hτ
      have e4 := WXExec.inc cap rG τ (by simp [τ, st, Function.update_apply, Fin.ext_iff]; omega)
      have e5 := WXExec.dec cap rC (τ.setv rG (τ.val rG + 1)) (by simp [τ, st, Function.update_apply, Fin.ext_iff]; omega)
      refine (WXExec.seq e1 (WXExec.seq e2 (WXExec.seq e3 (WXExec.seq e4 e5)))).cast cap ?_ (by omega)
      simp only [τ, st]
      clear * - hD hk
      have hGC : rG ≠ rC := by decide
      apply WState.eq
      · funext x
        simp only [WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_apply]
        by_cases h1 : x = D
        · subst h1; simp [hD]; omega
        · by_cases h2 : x = sG
          · subst h2; simp [h1]
          · simp [h1, h2]
      · funext x
        simp only [WState.setv_st, WState.seth_st, WState.sets_st, Function.update_apply]
        by_cases h2 : x = sG
        · subst h2; simp
        · simp [h2]
      · funext r
        simp only [WState.setv_val, WState.seth_val, WState.sets_val, Function.update_apply]
        by_cases h1 : r = rC
        · subst h1; simp [hGC.symm]; omega
        · by_cases h2 : r = rG
          · subst h2; simp [hGC]
          · simp [h1, h2]
      · rfl)
  rw [h0] at hl
  refine hl.cast cap ?_ (by omega)
  simp only [st, Nat.sub_self]

/-- One more ruler cell. -/
def oneG : WMX (NS tc tT) NR := .seq (WMX.wr sG true) (.seq (WMX.fwd sG) (WMX.inc rG))

theorem oneG_spec (σ : WS) (n : ℕ) (hG : σ.st sG = List.replicate n true) (hGh : σ.sh sG = n)
    (hrG : σ.val rG = n) (hcap : n + 1 ≤ cap) :
    WXExec cap oneG σ (((σ.sets sG (List.replicate (n + 1) true)).seth sG (n + 1)).setv rG (n + 1)) 7 := by
  have e1 := WXExec.wr cap sG true σ
  have w : writeTapeBit (σ.st sG) (σ.sh sG) true = List.replicate (n + 1) true := by
    rw [hG, hGh]
    have := wtb_append (List.replicate n true) true
    rw [List.length_replicate] at this
    rw [this, ← List.replicate_succ']
  rw [w] at e1
  have e2 := WXExec.fwd cap sG (σ.sets sG (List.replicate (n + 1) true))
  have e3 := WXExec.inc cap rG ((σ.sets sG (List.replicate (n + 1) true)).seth sG
    ((σ.sets sG (List.replicate (n + 1) true)).sh sG + 1)) (by simp [hrG]; omega)
  refine (WXExec.seq e1 (WXExec.seq e2 e3)).cast cap ?_ (by omega)
  simp only [WState.sets_sh, WState.seth_sh, Function.update_self, WState.seth_val, WState.sets_val, hGh, hrG]

/-! ## The call, the tally, the cleanup -/

section Call
variable {Req : Type} {input output : Req → List Bool} {budget : Req → ℕ}
variable (f : WordFunction Req input output budget)

local notation "TC" => f.program.tapeCount
local notation "WSf" => WState (NS f.program.tapeCount tT) NR

/-- The compiler's work streams other than its output, and its step tally. -/
def scratchC : List (Fin (NS f.program.tapeCount tT + 1)) :=
  ((List.finRange f.program.tapeCount).filter (fun j => j ≠ f.program.outputTape)).map sC ++ [sTL]

theorem scratchC_nodup : (scratchC (tT := tT) f).Nodup := by
  unfold scratchC
  refine List.Nodup.append (((List.nodup_finRange _).filter _).map sC_inj) (List.nodup_singleton _) ?_
  intro a ha hb
  simp only [List.mem_singleton] at hb
  obtain ⟨j, -, rfl⟩ := List.mem_map.1 ha
  have := congrArg Fin.val hb; simp at this; omega

theorem scratchC_ne_G : ∀ X ∈ scratchC (tT := tT) f, X ≠ sG := by
  intro X hX
  unfold scratchC at hX
  rcases List.mem_append.1 hX with h | h
  · obtain ⟨j, -, rfl⟩ := List.mem_map.1 h; intro e; have := congrArg Fin.val e; simp at this; omega
  · simp at h; subst h; ds

/-- **The compiler call and the cleanup.** -/
noncomputable def callP : WMX (NS f.program.tapeCount tT) NR :=
  .seq oneG (.seq (WMX.machZ (clockMachine f.program.machine)
    (Fin.addCases (motive := fun _ => Fin (NS f.program.tapeCount tT + 1)) sC (fun _ : Fin 1 => sTL)) sLOG)
    (.seq (NearCubicGates.Close.WorkerArith.tallyP sTL sG rG rT)
    (.seq (NearCubicGates.Close.WorkerArith.clearAll sG r0 (scratchC f))
      (NearCubicGates.Close.WorkerArith.clearSelfP sG r0))))

theorem rd_pad (z : ℕ) (l : List Bool) (q : ℕ) : readTapeBit (ZeroPadding.pad z l) q = readTapeBit l q :=
  rdEq_append_blank l _ (fun _ hb => (List.mem_replicate.1 hb).2) q

theorem callP_spec (req : Req) (σ : WSf) (z : Fin f.program.tapeCount → ℕ) (n lcap : ℕ)
    (hin : ∀ j, σ.st (sC j) = ZeroPadding.pad (z j) (f.program.inputTapes (input req) j))
    (hext : ∀ j q, n < q → readTapeBit (f.program.inputTapes (input req) j) q = false)
    (hTL : σ.st sTL = []) (hLOG : σ.st sLOG = List.replicate lcap false) (hn : budget req ≤ lcap)
    (hG : σ.st sG = List.replicate n true) (hGh : σ.sh sG = n) (hrG : σ.val rG = n)
    (hsh : ∀ i, i ≠ sG → σ.sh i = 0) (hrT : σ.val rT = 0) (hr0 : σ.val r0 = 0)
    (hcap : n + budget req + 2 ≤ cap) :
    ∃ τ : WSf, WXExec cap (callP f) σ τ (2 * budget req + (f.program.tapeCount + 3) * 50 * (n + budget req + 2)) ∧
      τ.st (sC f.program.outputTape) = ZeroPadding.pad (z f.program.outputTape) (output req) ∧
      (∀ j, j ≠ f.program.outputTape → ∀ q, readTapeBit (τ.st (sC j)) q = false) ∧
      (∀ q, readTapeBit (τ.st sTL) q = false) ∧ (∀ q, readTapeBit (τ.st sG) q = false) ∧
      (∀ i, (∀ j, sC j ≠ i) → i ≠ sTL → i ≠ sG → τ.st i = σ.st i) ∧
      (∀ i, τ.sh i = 0) ∧ (∀ r, r ≠ rG → τ.val r = σ.val r) ∧ τ.val rG = 0 ∧ τ.cell = σ.cell := by
  have e1 := oneG_spec cap σ n hG hGh hrG (by omega)
  set σ1 := ((σ.sets sG (List.replicate (n + 1) true)).seth sG (n + 1)).setv rG (n + 1) with hσ1
  have hGne : ∀ j : Fin f.program.tapeCount, sC (tT := tT) j ≠ (sG : Fin (NS f.program.tapeCount tT + 1)) := fun j e => by have := congrArg Fin.val e; simp at this; omega
  have hTLne : ∀ j : Fin f.program.tapeCount, sC (tT := tT) j ≠ (sTL : Fin (NS f.program.tapeCount tT + 1)) := fun j e => by have := congrArg Fin.val e; simp at this; omega
  have hLne : ∀ j : Fin f.program.tapeCount, sC (tT := tT) j ≠ (sLOG : Fin (NS f.program.tapeCount tT + 1)) := fun j e => by have := congrArg Fin.val e; simp at this; omega
  have hTLL : (sTL : Fin (NS f.program.tapeCount tT + 1)) ≠ sLOG := by ds
  have hTLG : (sTL : Fin (NS f.program.tapeCount tT + 1)) ≠ sG := by ds
  have hLG : (sLOG : Fin (NS f.program.tapeCount tT + 1)) ≠ sG := by ds
  obtain ⟨receipt, τ, hrun, hout, hsteps, e2, hst, hTLst, hsh0, hTLsh, hother, hval, hcell⟩ :=
    Mach.clockDock_padded f req cap sC sC_inj sTL sLOG hTLne hLne hTLL σ1 z 0 lcap
      (fun j => by simp only [σ1, WState.setv_st, WState.seth_st, WState.sets_st, Function.update_of_ne (hGne j)]
                   exact hin j)
      (by simp only [σ1, WState.setv_st, WState.seth_st, WState.sets_st, Function.update_of_ne hTLG, hTL]; rfl)
      (fun j => by simp only [σ1, WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_of_ne (hGne j)]
                   exact hsh _ (hGne j))
      (by simp only [σ1, WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_of_ne hTLG]
          exact hsh _ hTLG)
      (by simp only [σ1, WState.setv_st, WState.seth_st, WState.sets_st, Function.update_of_ne hLG, hLOG])
      (by simp only [σ1, WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_of_ne hLG]
          exact hsh _ hLG) hn
  set s := receipt.steps with hs
  have hGo := hother sG (fun j => hGne j) hTLG.symm
  have hτG : τ.st sG = List.replicate (n + 1) true := by rw [hGo.1]; simp [σ1]
  have hτGh : τ.sh sG = n + 1 := by rw [hGo.2]; simp [σ1]
  have hτrG : τ.val rG = n + 1 := by rw [hval]; simp [σ1]
  have hτTL : τ.st sTL = List.replicate s true := by rw [hTLst]; simp
  have hτrT : τ.val rT = 0 := by rw [hval]; simp [σ1, Function.update_apply, Fin.ext_iff, hrT]
  have e3 := NearCubicGates.Close.WorkerArith.tallyM cap sTL sG hTLG rG rT (by decide) τ (n + 1) s hτG hτGh hτrG
    hτTL hTLsh hτrT (by omega)
  set m := n + 1 + s with hm
  set τ2 := ((τ.sets sG (List.replicate m true)).seth sG 0).setv rG 0 with hτ2
  have hXs := scratchC_nodup (tT := tT) f
  have hXG := scratchC_ne_G (tT := tT) f
  have hmem : ∀ i, i ∈ scratchC (tT := tT) f ↔ (∃ j, j ≠ f.program.outputTape ∧ sC j = i) ∨ i = sTL := by
    intro i; simp [scratchC]
  have hX0 : ∀ X ∈ scratchC (tT := tT) f, τ2.sh X = 0 := by
    intro X hX
    have hXG' := hXG X hX
    simp only [τ2, WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_of_ne hXG']
    rcases (hmem X).1 hX with ⟨j, -, rfl⟩ | rfl
    · exact hsh0 j
    · exact hTLsh
  have e4 := NearCubicGates.Close.WorkerArith.clearAllM cap sG r0 m (by omega) (scratchC (tT := tT) f) τ2 hXs hXG
    (by simp [τ2]) (by simp [τ2]) (by simp [τ2, Function.update_apply, Fin.ext_iff, hval, σ1, hr0]) hX0
  set τ3 : WSf := ⟨τ2.sh, fun i => if i ∈ scratchC (tT := tT) f then clearPrefix m (τ2.st i) else τ2.st i, τ2.val,
    τ2.cell⟩ with hτ3
  have hGnot : sG ∉ scratchC (tT := tT) f := fun h => hXG _ h rfl
  have e5 := NearCubicGates.Close.WorkerArith.clearSelfM cap sG r0 τ3 m (by simp [τ3, hGnot, τ2])
    (by simp [τ3, τ2]) (by simp [τ3, τ2, Function.update_apply, Fin.ext_iff, hval, σ1, hr0]) (by omega)
  have hlen : (scratchC (tT := tT) f).length ≤ f.program.tapeCount + 1 := by
    simp only [scratchC, List.length_append, List.length_map, List.length_singleton]
    have := List.length_filter_le (fun j => decide (j ≠ f.program.outputTape)) (List.finRange f.program.tapeCount)
    simp only [List.length_finRange] at this
    omega
  refine ⟨τ3.sets sG (List.replicate m false), (WXExec.seq e1 (WXExec.seq e2 (WXExec.seq e3 (WXExec.seq e4 e5)))).mono
    ?cost, ?hq, ?hoc, ?htl, ?hg, ?hoth, ?hsh, ?hv, ?hvG, ?hc⟩
  case cost =>
    have h1 : (scratchC (tT := tT) f).length * (18 * m + 4) ≤ (f.program.tapeCount + 1) * (18 * m + 4) :=
      Nat.mul_le_mul_right _ hlen
    have h2 : m ≤ n + budget req + 1 := by omega
    nlinarith
  case hq =>
    have hno : sC (tT := tT) f.program.outputTape ∉ scratchC (tT := tT) f := by
      intro h
      rcases (hmem _).1 h with ⟨j, hj, hjj⟩ | h
      · exact hj (sC_inj hjj)
      · exact hTLne _ h
    simp only [WState.sets_st, Function.update_of_ne (hGne _), τ3, hno, if_false, τ2, WState.setv_st,
      WState.seth_st]
    rw [hst, hout]
  case hoc =>
    intro j hj q
    have hin' : sC (tT := tT) j ∈ scratchC (tT := tT) f := (hmem _).2 (Or.inl ⟨j, hj, rfl⟩)
    simp only [WState.sets_st, Function.update_of_ne (hGne _), τ3, hin', if_true, τ2, WState.setv_st,
      WState.seth_st, WState.sets_st, Function.update_of_ne (hGne _)]
    have := clearPrefix_blank m (τ.st (sC j)) (fun q hq => by
      rw [hst, rd_pad]
      have hf := runFrom_far f.program.machine j (budget req) _ n receipt hrun (by simp [initialConfiguration])
        (fun q hq => hext j q hq)
      exact hf.2 q (by omega)) q
    rw [this]; rfl
  case htl =>
    intro q
    have hin' : (sTL : Fin (NS f.program.tapeCount tT + 1)) ∈ scratchC (tT := tT) f := (hmem _).2 (Or.inr rfl)
    simp only [WState.sets_st, Function.update_of_ne hTLG, τ3, hin', if_true, τ2, WState.setv_st,
      WState.seth_st, WState.sets_st, Function.update_of_ne hTLG]
    have := clearPrefix_blank m (τ.st sTL) (fun q hq => by
      rw [hτTL]; unfold readTapeBit; rw [List.getD_eq_default _ _ (by simp; omega)]) q
    rw [this]; rfl
  case hg => intro q; simp only [WState.sets_st, Function.update_self]; exact blank_replicate m q
  case hoth =>
    intro i hi1 hi2 hi3
    have hin' : i ∉ scratchC (tT := tT) f := by
      intro h; rcases (hmem _).1 h with ⟨j, -, rfl⟩ | h
      · exact hi1 j rfl
      · exact hi2 h
    simp only [WState.sets_st, Function.update_of_ne hi3, τ3, hin', if_false, τ2, WState.setv_st, WState.seth_st,
      WState.sets_st, Function.update_of_ne hi3]
    rw [(hother i hi1 hi2).1]
    simp [σ1, Function.update_of_ne hi3]
  case hsh =>
    intro i
    simp only [WState.sets_sh, τ3, τ2, WState.setv_sh, WState.seth_sh, WState.sets_sh]
    by_cases hiG : i = sG
    · subst hiG; simp
    · rw [Function.update_of_ne hiG]
      by_cases hi1 : ∃ j, sC j = i
      · obtain ⟨j, rfl⟩ := hi1; exact hsh0 j
      · by_cases hi2 : i = sTL
        · subst hi2; exact hTLsh
        · rw [(hother i (fun j hj => hi1 ⟨j, hj⟩) hi2).2]
          simp [σ1, Function.update_of_ne hiG]
          exact hsh i hiG
  case hv =>
    intro r hr
    simp only [WState.sets_val, τ3, τ2, WState.setv_val, WState.seth_val, WState.sets_val,
      Function.update_of_ne hr, hval, σ1]
  case hvG => simp [τ3, τ2]
  case hc => simp [τ3, τ2, hcell, σ1]

end Call

end NearCubicGates.Adapters.Refuter.RM
