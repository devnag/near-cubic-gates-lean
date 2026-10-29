import SourceAdapters.Refuter.LoggedRun

/-!
# Preparing the clock (input 7, the clock, part 2)

proof of `lem:multitape-refuter`, Step 1: "First `𝒟` computes `T(N)` and prepares its clock in `O(T(N)+1)` steps"; proof of `cor:framed-refuter`: "After
computing `T(N)` and preparing a clock, impose the uniform step cap `(c_0+2)(T(N)+1)`". The clock is the
unary tape `1^{cap}` of the capped run (`Joins/CappedRun.lean`, `cappedInputTapes`).

`prep` is one fixed program (for the fixed time constructor `p` of `T`) on the outer layout `WMX (tP+66) 8`:
(a) write `fr(1^N)` from the input `fr(x)`; (b) run the step-logged time constructor (`logged`) on it;
(c) count its `s` steps; (d) read its output `T(N)` in binary most significant bit first from cell `s`
(the output has at most `s` cells), doubling a unary register: the doubling costs form a geometric sum
`≤ 2T(N)`; (e) write `1^{1024(T(N)+1)}` on the clock stream. The input and witness streams and the `63` body
streams are never touched.
-/

namespace NearCubicGates.Adapters.Refuter.Clock

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.WordPrograms
open NearCubicGates.Adapters.Refuter NearCubicGates.Adapters.Refuter.Mach
open NearCubicWires.WireExponent3_5.PrimAsm.DockW (updS)
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_other install_slot)
open NearCubicWires.ExtDecompositionBatch (dockH dockH_other dockH_slot Step Step.of_run)

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! ## Generic: loops with varying cost, the geometric sum -/

section Generic
variable {ns nr : ℕ} (cap : ℕ)

theorem exEq' {P : WMX ns nr} {σ τ : WState ns nr} {c : ℕ} (h : WXExec cap P σ τ c) :
    ∃ τ', WXExec cap P σ τ' c ∧ τ' = τ := ⟨_, h, rfl⟩

/-- A register loop through exact states with a cost per pass. -/
theorem whrV {r : Fin nr} {body : WMX ns nr} : ∀ (n : ℕ) (st : ℕ → WState ns nr) (c : ℕ → ℕ),
    (∀ k < n, (st k).val r ≠ 0) → (st n).val r = 0 → (∀ k < n, WXExec cap body (st k) (st (k + 1)) (c k)) →
    WXExec cap (.whr r body) (st 0) (st n) ((Finset.range n).sum (fun k => c k + 2) + 1)
  | 0, st, c, _, hend, _ => by simpa using WXExec.whrF (P := body) hend
  | n + 1, st, c, hv, hend, hstep => by
    have ih := whrV n (fun k => st (k + 1)) (fun k => c (k + 1)) (fun k hk => hv (k + 1) (by omega)) hend
      (fun k hk => hstep (k + 1) (by omega))
    refine (WXExec.whrT (hv 0 (by omega)) (hstep 0 (by omega)) ih).mono ?_
    rw [Finset.sum_range_succ']; omega

theorem sum_div_pow (n : ℕ) : ∀ m, (Finset.range m).sum (fun j => n / 2 ^ (j + 1)) ≤ n := by
  intro m
  induction m generalizing n with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ']
    have h := ih (n / 2)
    have e : ∀ j, n / 2 / 2 ^ (j + 1) = n / 2 ^ (j + 1 + 1) := fun j => by
      rw [Nat.div_div_eq_div_mul, ← pow_succ']
    simp only [e] at h
    simp only [zero_add, pow_one]
    omega

end Generic

theorem wtb_set (l : List Bool) (p : ℕ) (b : Bool) (h : p < l.length) : writeTapeBit l p b = l.set p b := by
  induction l generalizing p with
  | nil => simp at h
  | cons a l ih =>
    cases p with
    | zero => rfl
    | succ p => simp [writeTapeBit, ih p (by simpa using h)]

theorem div_pow_step (n j : ℕ) : n / 2 ^ j = 2 * (n / 2 ^ (j + 1)) + if n.testBit j then 1 else 0 := by
  have h1 : n / 2 ^ (j + 1) = n / 2 ^ j / 2 := by rw [Nat.div_div_eq_div_mul, pow_succ]
  rw [h1, testBit_eq_mod]
  have := Nat.div_add_mod (n / 2 ^ j) 2
  rcases Nat.mod_two_eq_zero_or_one (n / 2 ^ j) with h | h <;> simp [h] <;> omega

theorem rd_bits (n k : ℕ) : readTapeBit n.bits k = n.testBit k := by
  rw [Nat.testBit_eq_inth]; unfold readTapeBit List.getI; rfl

/-! ## The outer layout -/

section Layout
variable (tP : ℕ)

abbrev ONS : ℕ := tP + 66
abbrev ONR : ℕ := 8
abbrev OSt := WState (ONS tP) ONR
abbrev OPg := WMX (ONS tP) ONR

def Sx : Fin (ONS tP + 1) := ⟨0, by unfold ONS; omega⟩
def Sw : Fin (ONS tP + 1) := ⟨1, by unfold ONS; omega⟩
def Scl : Fin (ONS tP + 1) := ⟨2, by unfold ONS; omega⟩
def Slog : Fin (ONS tP + 1) := ⟨3, by unfold ONS; omega⟩
def Stc (j : Fin tP) : Fin (ONS tP + 1) := ⟨4 + j.val, by unfold ONS; omega⟩
def Sfr (k : Fin 63) : Fin (ONS tP + 1) := ⟨4 + tP + k.val, by unfold ONS; omega⟩

@[simp] abbrev oN : Fin ONR := 0
@[simp] abbrev oS : Fin ONR := 1
@[simp] abbrev oV : Fin ONR := 2
@[simp] abbrev oK : Fin ONR := 3
@[simp] abbrev oPT : Fin ONR := 4
@[simp] abbrev oTA : Fin ONR := 5
@[simp] abbrev oTB : Fin ONR := 6
@[simp] abbrev oTG : Fin ONR := 7

@[simp] theorem Sx_val : (Sx tP).val = 0 := rfl
@[simp] theorem Sw_val : (Sw tP).val = 1 := rfl
@[simp] theorem Scl_val : (Scl tP).val = 2 := rfl
@[simp] theorem Slog_val : (Slog tP).val = 3 := rfl
@[simp] theorem Stc_val (j : Fin tP) : (Stc tP j).val = 4 + j.val := rfl
@[simp] theorem Sfr_val (k : Fin 63) : (Sfr tP k).val = 4 + tP + k.val := rfl

def Su : Fin (ONS tP + 1) := ⟨4, by unfold ONS; omega⟩
@[simp] theorem Su_val : (Su tP).val = 4 := rfl

/-- The input, witness and body streams: never touched by `prep`. -/
def Kept (i : Fin (ONS tP + 1)) : Prop := i.val = 1 ∨ 4 + tP ≤ i.val

end Layout

/-- `omega` after unfolding the outer register names. -/
macro "oomega" : tactic => `(tactic| ((try simp only [oN, oS, oV, oK, oPT, oTA, oTB, oTG] at *) <;> omega))

/-! ## (a) `fr(1^N)` -/

section PhaseA
variable (tP : ℕ) (cap : ℕ)

def uBody : OPg tP := .seq (WMX.fwd (Sx tP)) (.seq (pairW (Su tP) true) (.seq (WMX.fwd (Sx tP)) (WMX.inc oN)))

def phaseA : OPg tP :=
  .seq (.whs (Sx tP) (uBody tP)) (.seq (WMX.wr (Su tP) false) (.seq (bwdK (Sx tP) oN oTB) (.seq (bwdK (Sx tP) oN oTB)
    (.seq (bwdK (Su tP) oN oTB) (bwdK (Su tP) oN oTB)))))

theorem sx_ne_su : Sx tP ≠ Su tP := by intro h; have := congrArg Fin.val h; simp at this

set_option maxHeartbeats 400000 in
theorem phaseA_spec (σ : OSt tP) (x : List Bool) (hX : σ.st (Sx tP) = RepairOrdinary.frame x) (hXh : σ.sh (Sx tP) = 0)
    (hU : σ.st (Su tP) = []) (hUh : σ.sh (Su tP) = 0) (hN : σ.val oN = 0) (hTB : σ.val oTB = 0)
    (hcap : 2 * x.length + 2 ≤ cap) :
    ∃ c, WXExec cap (phaseA tP) σ ((σ.sets (Su tP) (RepairOrdinary.frame (List.replicate x.length true))).setv oN x.length) c ∧
      c ≤ 100 * (x.length + 1) := by
  have hne := sx_ne_su tP
  have hne' := Ne.symm hne
  set N := x.length with hNdef
  have e1 := whsE cap (i := Sx tP) (body := uBody tP)
    (fun k => (((σ.seth (Sx tP) (2 * k)).sets (Su tP) (fpre (List.replicate k true))).seth (Su tP) (2 * k)).setv oN k) N 17
    (fun k hk => by
      simp only [wbit, WState.setv_st, WState.seth_st, WState.sets_st, WState.setv_sh, WState.seth_sh, WState.sets_sh]
      rw [Function.update_apply, if_neg hne, Function.update_apply, if_neg hne, Function.update_self, hX,
        frame_eq_fpre, rd_fpre_mark _ _ hk])
    (by
      simp only [wbit, WState.setv_st, WState.seth_st, WState.sets_st, WState.setv_sh, WState.seth_sh, WState.sets_sh]
      rw [Function.update_apply, if_neg hne, Function.update_apply, if_neg hne, Function.update_self, hX,
        frame_eq_fpre, show 2 * N = 2 * x.length + 0 by omega, rd_fpre_after]
      rfl)
    (fun k hk => by
      set τ := (((σ.seth (Sx tP) (2 * k)).sets (Su tP) (fpre (List.replicate k true))).seth (Su tP) (2 * k)).setv oN k with hτ
      have f1 := WXExec.fwd cap (Sx tP) τ
      have p2 := pairW_spec cap (Su tP) true (τ.seth (Sx tP) (τ.sh (Sx tP) + 1))
        (by simp [τ, Function.update_apply, hne'])
      have f3 := WXExec.fwd cap (Sx tP) (((τ.seth (Sx tP) (τ.sh (Sx tP) + 1)).sets (Su tP)
        ((τ.seth (Sx tP) (τ.sh (Sx tP) + 1)).st (Su tP) ++ [true, true])).seth (Su tP)
        ((τ.seth (Sx tP) (τ.sh (Sx tP) + 1)).sh (Su tP) + 2))
      have i4 := WXExec.inc cap oN ((((τ.seth (Sx tP) (τ.sh (Sx tP) + 1)).sets (Su tP)
        ((τ.seth (Sx tP) (τ.sh (Sx tP) + 1)).st (Su tP) ++ [true, true])).seth (Su tP)
        ((τ.seth (Sx tP) (τ.sh (Sx tP) + 1)).sh (Su tP) + 2)).seth (Sx tP) ((((τ.seth (Sx tP) (τ.sh (Sx tP) + 1)).sets (Su tP)
        ((τ.seth (Sx tP) (τ.sh (Sx tP) + 1)).st (Su tP) ++ [true, true])).seth (Su tP)
        ((τ.seth (Sx tP) (τ.sh (Sx tP) + 1)).sh (Su tP) + 2)).sh (Sx tP) + 1)) (by simp [τ]; omega)
      refine (WXExec.seq f1 (WXExec.seq p2 (WXExec.seq f3 i4))).cast cap ?_ (by omega)
      have hl : fpre (List.replicate k true) ++ [true, true] = fpre (List.replicate (k + 1) true) := by
        rw [List.replicate_succ', fpre_snoc]
      apply WState.eq
      · funext j; by_cases a1 : j = Sx tP
        · subst a1; simp [τ, Function.update_apply, hne]; ring
        · by_cases a2 : j = Su tP
          · subst a2; simp [τ, Function.update_apply, hne']; ring
          · simp [τ, Function.update_apply, a1, a2]
      · funext j; by_cases a2 : j = Su tP
        · subst a2; simp [τ, Function.update_apply, hne', hl]
        · simp [τ, Function.update_apply, a2]
      · funext r; by_cases a1 : r = oN
        · subst a1; simp [τ]
        · simp [τ, Function.update_apply, a1]
      · rfl)
  have h0 : (((σ.seth (Sx tP) (2 * 0)).sets (Su tP) (fpre (List.replicate 0 true))).seth (Su tP) (2 * 0)).setv oN 0 = σ := by
    apply WState.eq
    · funext j; by_cases a1 : j = Sx tP
      · subst a1; simp [Function.update_apply, hne, hXh]
      · by_cases a2 : j = Su tP
        · subst a2; simp [hUh]
        · simp [Function.update_apply, a1, a2]
    · funext j; by_cases a2 : j = Su tP
      · subst a2; simp [hU]
      · simp [Function.update_apply, a2]
    · funext r; by_cases a1 : r = oN
      · subst a1; simp [hN]
      · simp [Function.update_apply, a1]
    · rfl
  rw [h0] at e1
  set σ1 := (((σ.seth (Sx tP) (2 * N)).sets (Su tP) (fpre (List.replicate N true))).seth (Su tP) (2 * N)).setv oN N with hσ1
  obtain ⟨σ2, e2, h2⟩ := exEq' cap (WXExec.wr cap (Su tP) false σ1)
  have s2 : σ2.st (Su tP) = RepairOrdinary.frame (List.replicate N true) := by
    rw [h2]; simp [σ1, Function.update_apply, hne']
    rw [show 2 * N = (fpre (List.replicate N true)).length by simp, wtb_append, frame_eq_fpre]
  obtain ⟨σ3, e3, h3⟩ := exEq' cap (bwdK_spec cap (S := Sx tP) (K := oN) (K2 := oTB) (by decide) σ2
    (by rw [h2]; simp [σ1, hTB]) (by rw [h2]; simp [σ1]; omega))
  obtain ⟨σ4, e4, h4⟩ := exEq' cap (bwdK_spec cap (S := Sx tP) (K := oN) (K2 := oTB) (by decide) σ3
    (by rw [h3, h2]; simp [σ1, hTB]) (by rw [h3, h2]; simp [σ1]; omega))
  obtain ⟨σ5, e5, h5⟩ := exEq' cap (bwdK_spec cap (S := Su tP) (K := oN) (K2 := oTB) (by decide) σ4
    (by rw [h4, h3, h2]; simp [σ1, hTB]) (by rw [h4, h3, h2]; simp [σ1]; omega))
  obtain ⟨σ6, e6, h6⟩ := exEq' cap (bwdK_spec cap (S := Su tP) (K := oN) (K2 := oTB) (by decide) σ5
    (by rw [h5, h4, h3, h2]; simp [σ1, hTB]) (by rw [h5, h4, h3, h2]; simp [σ1]; omega))
  refine ⟨_, (WXExec.seq e1 (WXExec.seq e2 (WXExec.seq e3 (WXExec.seq e4 (WXExec.seq e5 e6))))).cast cap ?_ le_rfl, ?_⟩
  · rw [h6, h5, h4, h3]
    apply WState.eq
    · funext j; by_cases a1 : j = Sx tP
      · subst a1; simp [h2, σ1, Function.update_apply, hne, hXh]; omega
      · by_cases a2 : j = Su tP
        · subst a2; simp [h2, σ1, Function.update_apply, hne', hUh]; omega
        · simp [h2, σ1, Function.update_apply, a1, a2]
    · funext j; by_cases a2 : j = Su tP
      · subst a2; simp only [WState.seth_st]; rw [s2]; simp
      · simp [h2, σ1, Function.update_apply, a2]
    · funext r; by_cases a1 : r = oN
      · subst a1; simp [h2, σ1]
      · simp [h2, σ1, Function.update_apply, a1]
    · simp [h2, σ1]
  · rw [h5, h4, h3, h2]; simp [σ1]; omega

end PhaseA

/-! ## (b) the logged time constructor -/

section PhaseB
variable (p : Program) (cap : ℕ)

def tmapB : Fin (p.tapeCount + 1) → Fin (ONS p.tapeCount + 1) := Fin.addCases (Stc p.tapeCount) (fun _ => Slog p.tapeCount)

theorem tmapB_inj : Function.Injective (tmapB p) := by
  intro a b
  refine Fin.addCases (fun i => ?_) (fun i => ?_) a <;> refine Fin.addCases (fun j => ?_) (fun j => ?_) b <;>
    intro h <;> have hv := congrArg Fin.val h <;> simp [tmapB] at hv ⊢
  · exact Fin.ext hv
  · omega
  · omega
  · exact Subsingleton.elim i j

def phaseB : OPg p.tapeCount := .mach (logged p.machine) (tmapB p)

theorem phaseB_spec (σ : OSt p.tapeCount) (word : List Bool)
    (hst : ∀ j, σ.st (Stc p.tapeCount j) = p.inputTapes word j) (hsh : ∀ j, σ.sh (Stc p.tapeCount j) = 0)
    (hlog : σ.st (Slog p.tapeCount) = []) (hlogh : σ.sh (Slog p.tapeCount) = 0)
    (F : ℕ) (r : ExecutionReceipt p.tapeCount p.stateCount) (hr : run p.machine F (p.inputTapes word) = some r) :
    WXExec cap (phaseB p) σ (updS (tmapB p) σ (Fin.addCases r.final.heads (fun _ => r.steps))
      (Fin.addCases r.final.tapes (fun _ => List.replicate r.steps true))) r.steps := by
  have hx := runFrom_exact p.machine F _ r hr
  obtain ⟨r', h1, h2, h3⟩ := logged_run p.machine r.steps _ r 0 hx
  have hc : (⟨(logged p.machine).start, fun j => σ.sh (tmapB p j), fun j => σ.st (tmapB p j)⟩ :
      Configuration (p.tapeCount + 1) p.stateCount) = logConfig (initialConfiguration p.machine (p.inputTapes word)) 0 := by
    apply configuration_ext
    · rfl
    · funext j; refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp [tmapB, logConfig, initialConfiguration, hsh, hlogh]
    · funext j; refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp [tmapB, logConfig, initialConfiguration, hst, hlog]
  refine WXExec.mach σ (tmapB_inj p) ?_
  refine Step.of_run (by rw [hc]; exact h1) ?_ ?_
  · rw [h2]; funext j; refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp [logConfig]
  · rw [h2]; funext j; refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp [logConfig]

theorem updS_kept (σ : OSt p.tapeCount) (hout : Fin (p.tapeCount + 1) → ℕ) (tout : Fin (p.tapeCount + 1) → List Bool)
    (i : Fin (ONS p.tapeCount + 1)) (hi : i.val < 3 ∨ 4 + p.tapeCount ≤ i.val) :
    (updS (tmapB p) σ hout tout).st i = σ.st i ∧ (updS (tmapB p) σ hout tout).sh i = σ.sh i := by
  have hn : ∀ j, tmapB p j ≠ i := by
    intro j
    refine Fin.addCases (fun a => ?_) (fun a => ?_) j <;> intro h <;> have hv := congrArg Fin.val h <;>
      simp [tmapB] at hv <;> omega
  exact ⟨install_other _ _ _ _ hn, dockH_other _ _ _ _ hn⟩

end PhaseB

/-! ## (c) counting the logged steps -/

theorem rd_clrL (l : List Bool) (k j : ℕ) :
    readTapeBit (clrL l k) j = if l.length - k ≤ j then false else readTapeBit l j := by
  by_cases hj : j < l.length
  · have h1 : j < (clrL l k).length := by simpa using hj
    rw [show readTapeBit (clrL l k) j = (clrL l k)[j] by
      simp only [readTapeBit, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1, Option.getD_some], clrL_get]
    split_ifs <;> simp [readTapeBit, List.getD_eq_getElem?_getD, hj, List.getElem?_eq_getElem h1]
  · rw [rd_beyond _ (by simp; omega), rd_beyond _ (by omega)]; simp

section PhaseC
variable (tP : ℕ) (cap : ℕ)

def phaseC : OPg tP :=
  .seq (WMX.bwd (Slog tP)) (.whs (Slog tP) (.seq (WMX.wr (Slog tP) false) (.seq (WMX.bwd (Slog tP)) (WMX.inc oS))))

theorem phaseC_spec (σ : OSt tP) (s : ℕ) (hL : σ.st (Slog tP) = List.replicate s true) (hLh : σ.sh (Slog tP) = s)
    (hS : σ.val oS = 0) (hcap : s < cap) :
    WXExec cap (phaseC tP) σ (((σ.sets (Slog tP) (clrL (List.replicate s true) s)).seth (Slog tP) 0).setv oS s)
      (s * 9 + 3) := by
  have e1 := WXExec.bwd cap (Slog tP) σ
  rw [hLh] at e1
  have e2 := whsE cap (i := Slog tP) (body := .seq (WMX.wr (Slog tP) false) (.seq (WMX.bwd (Slog tP)) (WMX.inc oS)))
    (fun k => ((σ.sets (Slog tP) (clrL (List.replicate s true) k)).seth (Slog tP) (s - 1 - k)).setv oS k) s 7
    (fun k hk => by
      simp only [wbit, WState.setv_st, WState.seth_st, WState.sets_st, WState.setv_sh, WState.seth_sh,
        Function.update_self, rd_clrL, List.length_replicate]
      rw [if_neg (by omega), rd_replicate _ _ (by omega)])
    (by
      simp only [wbit, WState.setv_st, WState.seth_st, WState.sets_st, WState.setv_sh, WState.seth_sh,
        Function.update_self, rd_clrL, List.length_replicate]
      rw [if_pos (by omega)])
    (fun k hk => by
      set τ := ((σ.sets (Slog tP) (clrL (List.replicate s true) k)).seth (Slog tP) (s - 1 - k)).setv oS k with hτ
      have w1 := WXExec.wr cap (Slog tP) false τ
      have b2 := WXExec.bwd cap (Slog tP) (τ.sets (Slog tP) (writeTapeBit (τ.st (Slog tP)) (τ.sh (Slog tP)) false))
      have i3 := WXExec.inc cap oS ((τ.sets (Slog tP) (writeTapeBit (τ.st (Slog tP)) (τ.sh (Slog tP)) false)).seth (Slog tP)
        ((τ.sets (Slog tP) (writeTapeBit (τ.st (Slog tP)) (τ.sh (Slog tP)) false)).sh (Slog tP) - 1)) (by simp [τ]; omega)
      refine (WXExec.seq w1 (WXExec.seq b2 i3)).cast cap ?_ le_rfl
      have hw : writeTapeBit (clrL (List.replicate s true) k) (s - 1 - k) false = clrL (List.replicate s true) (k + 1) := by
        rw [wtb_set _ _ _ (by simp; omega)]; simp [clrL]
      apply WState.eq
      · funext j; by_cases a1 : j = Slog tP
        · subst a1; simp [τ]; omega
        · simp [τ, Function.update_apply, a1]
      · funext j; by_cases a1 : j = Slog tP
        · subst a1; simp [τ, hw]
        · simp [τ, Function.update_apply, a1]
      · funext r; by_cases a1 : r = oS
        · subst a1; simp [τ]
        · simp [τ, Function.update_apply, a1]
      · rfl)
  have h0 : ((σ.sets (Slog tP) (clrL (List.replicate s true) 0)).seth (Slog tP) (s - 1 - 0)).setv oS 0 =
      σ.seth (Slog tP) (s - 1) := by
    apply WState.eq
    · funext j; by_cases a1 : j = Slog tP
      · subst a1; simp
      · simp [Function.update_apply, a1]
    · funext j; by_cases a1 : j = Slog tP
      · subst a1; simp [clrL, hL]
      · simp [Function.update_apply, a1]
    · funext r; by_cases a1 : r = oS
      · subst a1; simp [hS]
      · simp [Function.update_apply, a1]
    · rfl
  rw [h0] at e2
  refine (WXExec.seq e1 e2).cast cap ?_ (by omega)
  rw [show s - 1 - s = 0 by omega]

end PhaseC

/-! ## (d) the binary output to unary, most significant bit first -/

section PhaseD
variable (tP : ℕ) (So : Fin (ONS tP + 1)) (cap : ℕ)

def msbBody : OPg tP :=
  .seq (WMX.dec oK) (.seq (dbl oV oPT oTA) (.seq (.ifs So (WMX.inc oV) WMX.skip) (WMX.bwd So)))

def phaseD : OPg tP :=
  .seq (bwdK So oS oTB) (.seq (fwdK So oS oTB) (.seq (addR oS oK oTA) (.seq (WMX.inc oK) (.whr oK (msbBody tP So)))))

theorem msbBody_step (σ : OSt tP) (B : List Bool) (n s k : ℕ) (hB : ∀ j, readTapeBit B j = n.testBit j)
    (hst : σ.st So = B) (hPT : σ.val oPT = 0) (hTA : σ.val oTA = 0) (hk : k < s + 1) (hn : 2 * n + 2 ≤ cap)
    (hs : s + 2 ≤ cap) :
    WXExec cap (msbBody tP So) (((σ.seth So (s - k)).setv oK (s + 1 - k)).setv oV (n / 2 ^ (s + 1 - k)))
      (((σ.seth So (s - (k + 1))).setv oK (s + 1 - (k + 1))).setv oV (n / 2 ^ (s + 1 - (k + 1))))
      (39 * (n / 2 ^ (s + 1 - k)) + 18) := by
  set τ := ((σ.seth So (s - k)).setv oK (s + 1 - k)).setv oV (n / 2 ^ (s + 1 - k)) with hτ
  have hv : n / 2 ^ (s + 1 - k) ≤ n := Nat.div_le_self _ _
  have hstep := div_pow_step n (s - k)
  rw [show s - k + 1 = s + 1 - k by omega] at hstep
  obtain ⟨τ1, e1, h1⟩ := exEq' cap (WXExec.dec cap oK τ (by simp [τ]; omega))
  obtain ⟨τ2, e2, h2⟩ := exEq' cap (dbl_spec cap (P := oV) (PT := oPT) (TA := oTA) (by decide) (by decide) (by decide) τ1
    (by rw [h1]; simp [τ, hPT]) (by rw [h1]; simp [τ, hTA]) (by rw [h1]; simp [τ]; omega))
  have hb : wbit τ2 So = n.testBit (s - k) := by rw [h2, h1]; simp [τ, wbit, hst, hB]
  have e3 : WXExec cap (.ifs So (WMX.inc oV) WMX.skip) τ2
      (τ2.setv oV (τ2.val oV + if n.testBit (s - k) then 1 else 0)) 4 := by
    cases hc : n.testBit (s - k)
    · refine (WXExec.ifsF (by rw [hb, hc]) (WXExec.skip cap τ2)).cast cap ?_ (by omega)
      apply WState.eq <;> try rfl
      funext r; by_cases a : r = oV
      · subst a; simp
      · simp [Function.update_apply, a]
    · exact WXExec.ifsT (by rw [hb, hc]) (WXExec.inc cap oV τ2 (by rw [h2, h1]; simp [τ]; omega))
  obtain ⟨τ3, e3, h3⟩ := exEq' cap e3
  refine (WXExec.seq e1 (WXExec.seq e2 (WXExec.seq e3 (WXExec.bwd cap So τ3)))).cast cap ?_ (by rw [h1]; simp [τ]; omega)
  rw [h3, h2, h1]
  apply WState.eq
  · funext j; by_cases a : j = So
    · subst a; simp [τ]; omega
    · simp [τ, Function.update_apply, a]
  · rfl
  · funext r
    by_cases a1 : r = oV
    · subst a1; simp [τ, show s + 1 - (k + 1) = s - k by omega]; rw [hstep]; try ring
    · by_cases a2 : r = oK
      · subst a2; simp [τ]; omega
      · simp [τ, Function.update_apply, a1, a2]
  · rfl

theorem sum_msb (n s : ℕ) : (Finset.range (s + 1)).sum (fun k => 39 * (n / 2 ^ (s + 1 - k)) + 18 + 2) ≤
    39 * n + 20 * (s + 1) := by
  have h1 : (Finset.range (s + 1)).sum (fun k => n / 2 ^ (s + 1 - k)) ≤ n := by
    have e := Finset.sum_range_reflect (fun j => n / 2 ^ (j + 1)) (s + 1)
    have e2 : (Finset.range (s + 1)).sum (fun k => n / 2 ^ (s + 1 - 1 - k + 1)) =
        (Finset.range (s + 1)).sum (fun k => n / 2 ^ (s + 1 - k)) := by
      apply Finset.sum_congr rfl; intro k hk; simp at hk; congr 2; omega
    rw [← e2, e]; exact sum_div_pow n (s + 1)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul]
  omega

set_option maxHeartbeats 400000 in
theorem phaseD_spec (σ : OSt tP) (B : List Bool) (n s : ℕ) (hB : ∀ j, readTapeBit B j = n.testBit j)
    (hlen : ∀ j, s ≤ j → n.testBit j = false) (hst : σ.st So = B) (hh : σ.sh So ≤ s) (hS : σ.val oS = s)
    (hK : σ.val oK = 0) (hV : σ.val oV = 0) (hPT : σ.val oPT = 0) (hTA : σ.val oTA = 0) (hTB : σ.val oTB = 0)
    (hcap : 2 * n + 2 * s + 8 ≤ cap) :
    ∃ c, WXExec cap (phaseD tP So) σ (((σ.seth So 0).setv oK 0).setv oV n) c ∧ c ≤ 40 * n + 80 * (s + 1) := by
  have hn : n < 2 ^ s := Nat.lt_pow_two_of_testBit n (fun j hj => hlen j hj)
  have hz : n / 2 ^ (s + 1) = 0 := Nat.div_eq_of_lt (lt_of_lt_of_le hn (Nat.pow_le_pow_right (by norm_num) (by omega)))
  have e1 := bwdK_spec cap (S := So) (K := oS) (K2 := oTB) (by decide) σ hTB (by rw [hS]; omega)
  rw [hS, show σ.sh So - s = 0 by omega] at e1
  have e2 := fwdK_spec cap (S := So) (K := oS) (K2 := oTB) (by decide) (σ.seth So 0) (by simp [hTB]) (by simp [hS]; omega)
  have v2 : (σ.seth So 0).val oS = s := by simp [hS]
  rw [v2] at e2
  simp only [WState.seth_sh, Function.update_self, Nat.zero_add] at e2
  have hσ2 : (σ.seth So 0).seth So s = σ.seth So s := by
    apply WState.eq <;> try rfl
    funext j; by_cases a : j = So
    · rw [a]; simp
    · simp [Function.update_apply, a]
  rw [hσ2] at e2
  have e3 := addR_spec cap (A := oS) (B := oK) (T := oTA) (by decide) (by decide) (by decide) (σ.seth So s)
    (by simp [hTA]) (by simp [hS, hK]; omega)
  have v3 : (σ.seth So s).val oK + (σ.seth So s).val oS = s := by simp [hS, hK]
  rw [v3] at e3
  have e4 := WXExec.inc cap oK ((σ.seth So s).setv oK s) (by simp; omega)
  simp only [WState.setv_val, Function.update_self] at e4
  have e5 := whrV cap (r := oK) (body := msbBody tP So) (s + 1)
    (fun k => ((σ.seth So (s - k)).setv oK (s + 1 - k)).setv oV (n / 2 ^ (s + 1 - k)))
    (fun k => 39 * (n / 2 ^ (s + 1 - k)) + 18)
    (fun k hk => by simp; omega) (by simp)
    (fun k hk => msbBody_step tP So cap σ B n s k hB hst hPT hTA hk (by omega) (by omega))
  have h0 : ((σ.seth So (s - 0)).setv oK (s + 1 - 0)).setv oV (n / 2 ^ (s + 1 - 0)) =
      ((σ.seth So s).setv oK s).setv oK (s + 1) := by
    rw [Nat.sub_zero, Nat.sub_zero, hz]
    apply WState.eq <;> try rfl
    funext r
    by_cases a1 : r = oV
    · rw [a1]; simp [hV]
    · by_cases a2 : r = oK
      · rw [a2]; simp
      · simp [Function.update_apply, a1, a2]
  rw [h0] at e5
  refine ⟨_, (WXExec.seq e1 (WXExec.seq e2 (WXExec.seq e3 (WXExec.seq e4 e5)))).cast cap ?_ le_rfl, ?_⟩
  · simp only [Nat.sub_self, pow_zero, Nat.div_one, show s - (s + 1) = 0 by omega]
  · have hsum := sum_msb n s
    have w1 : (σ.seth So s).val oS = s := by simp [hS]
    have w2 : (σ.seth So s).val oK = 0 := by simp [hK]
    try simp only [WState.seth_val, hS, hK]
    omega

end PhaseD

/-! ## (e) the clock tape `1^{1024(T(N)+1)}` -/

section PhaseE
variable (tP : ℕ) (cap : ℕ)

def dblRep : ℕ → OPg tP
  | 0 => WMX.skip
  | k + 1 => .seq (dbl oK oPT oTA) (dblRep k)

theorem dblRep_spec (σ : OSt tP) (hPT : σ.val oPT = 0) (hTA : σ.val oTA = 0) :
    ∀ k m, σ.val oK = m → 2 ^ (k + 1) * m ≤ cap →
      ∃ c, WXExec cap (dblRep tP k) σ (σ.setv oK (2 ^ k * m)) c ∧ c + 39 * m ≤ 39 * (2 ^ k * m) + 10 * k := by
  intro k
  induction k generalizing σ with
  | zero =>
    intro m hm _
    refine ⟨0, (WXExec.skip cap σ).cast cap ?_ le_rfl, by simp⟩
    apply WState.eq <;> try rfl
    funext r; by_cases a : r = oK
    · subst a; simp [hm]
    · simp [Function.update_apply, a]
  | succ k ih =>
    intro m hm hc
    have hp : 2 * m ≤ 2 ^ (k + 1 + 1) * m := Nat.mul_le_mul_right _ (by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (k + 1 + 1) := Nat.pow_le_pow_right (by norm_num) (by omega))
    have e1 := dbl_spec cap (P := oK) (PT := oPT) (TA := oTA) (by decide) (by decide) (by decide) σ hPT hTA
      (by rw [hm]; omega)
    obtain ⟨c2, e2, hc2⟩ := ih (σ.setv oK (2 * σ.val oK)) (by simp [hPT]) (by simp [hTA]) (2 * m) (by simp [hm])
      (by rw [show 2 ^ (k + 1) * (2 * m) = 2 ^ (k + 1 + 1) * m by ring]; exact hc)
    refine ⟨_, (WXExec.seq e1 e2).cast cap ?_ le_rfl, ?_⟩
    · apply WState.eq <;> try rfl
      funext r; by_cases a : r = oK
      · subst a; simp [pow_succ]; try ring
      · simp [Function.update_apply, a]
    · rw [hm]
      have e : 2 ^ k * (2 * m) = 2 ^ (k + 1) * m := by ring
      rw [e] at hc2
      omega

def clkBody : OPg tP := .seq (WMX.wr (Scl tP) true) (WMX.fwd (Scl tP))

def phaseE : OPg tP :=
  .seq (addR oV oK oTA) (.seq (WMX.inc oK) (.seq (dblRep tP 10) (.seq (repK oK oTG (clkBody tP)) (bwdK (Scl tP) oK oTB))))

/-- The clock length for `T(N) = n`. -/
def clockLen (n : ℕ) : ℕ := 1024 * (n + 1)

set_option maxHeartbeats 400000 in
theorem phaseE_spec (σ : OSt tP) (n : ℕ) (hK : σ.val oK = 0) (hV : σ.val oV = n) (hPT : σ.val oPT = 0)
    (hTA : σ.val oTA = 0) (hTB : σ.val oTB = 0) (hTG : σ.val oTG = 0) (hC : σ.st (Scl tP) = []) (hCh : σ.sh (Scl tP) = 0)
    (hcap : 4096 * (n + 1) ≤ cap) :
    ∃ c, WXExec cap (phaseE tP) σ ((σ.setv oK (clockLen n)).sets (Scl tP) (List.replicate (clockLen n) true)) c ∧
      c ≤ 1000000 * (n + 1) := by
  have hL : 2 ^ 10 * (n + 1) = clockLen n := by simp [clockLen]
  have e1 := addR_spec cap (A := oV) (B := oK) (T := oTA) (by decide) (by decide) (by decide) σ hTA
    (by rw [hK, hV]; omega)
  rw [hK, hV, Nat.zero_add] at e1
  have e2 := WXExec.inc cap oK (σ.setv oK n) (by simp; omega)
  simp only [WState.setv_val, Function.update_self] at e2
  have hσ2 : (σ.setv oK n).setv oK (n + 1) = σ.setv oK (n + 1) := by
    apply WState.eq <;> try rfl
    funext r; by_cases a : r = oK
    · subst a; simp
    · simp [Function.update_apply, a]
  rw [hσ2] at e2
  obtain ⟨c3, e3, hc3⟩ := dblRep_spec tP cap (σ.setv oK (n + 1)) (by simp [hPT]) (by simp [hTA]) 10 (n + 1)
    (by simp) (by norm_num; omega)
  have hσ3 : (σ.setv oK (n + 1)).setv oK (2 ^ 10 * (n + 1)) = σ.setv oK (clockLen n) := by
    rw [hL]
    apply WState.eq <;> try rfl
    funext r; by_cases a : r = oK
    · subst a; simp
    · simp [Function.update_apply, a]
  rw [hσ3] at e3
  have hcl : clockLen n = 1024 * (n + 1) := rfl
  have e4 := Runs.repE (cap := cap) (K := oK) (K2 := oTG) (body := clkBody tP) (by decide) 3 (clockLen n)
    (fun j => ((σ.setv oK (clockLen n)).sets (Scl tP) (List.replicate j true)).seth (Scl tP) j) (by omega)
    (fun j => by simp) (fun j => by simp)
    (fun j _ v1 v2 => by
      refine (WXExec.seq (WXExec.wr cap (Scl tP) true _) (WXExec.fwd cap (Scl tP) _)).cast cap ?_ le_rfl
      apply WState.eq
      · funext i; by_cases a : i = Scl tP
        · subst a; simp
        · simp [Function.update_apply, a]
      · funext i; by_cases a : i = Scl tP
        · subst a; simp [wtb_rep]
        · simp [Function.update_apply, a]
      · rfl
      · rfl)
    (by simp) (by simp [hTG])
  have h40 : ((σ.setv oK (clockLen n)).sets (Scl tP) (List.replicate 0 true)).seth (Scl tP) 0 = σ.setv oK (clockLen n) := by
    apply WState.eq
    · funext i; by_cases a : i = Scl tP
      · subst a; simp [hCh]
      · simp [Function.update_apply, a]
    · funext i; by_cases a : i = Scl tP
      · subst a; simp [hC]
      · simp [Function.update_apply, a]
    · rfl
    · rfl
  rw [h40] at e4
  have e5 := bwdK_spec cap (S := Scl tP) (K := oK) (K2 := oTB) (by decide)
    (((σ.setv oK (clockLen n)).sets (Scl tP) (List.replicate (clockLen n) true)).seth (Scl tP) (clockLen n))
    (by simp [hTB]) (by simp; omega)
  refine ⟨_, (WXExec.seq e1 (WXExec.seq e2 (WXExec.seq e3 (WXExec.seq e4 e5)))).cast cap ?_ le_rfl, ?_⟩
  · apply WState.eq
    · funext i; by_cases a : i = Scl tP
      · subst a; simp [hCh]
      · simp [Function.update_apply, a]
    · rfl
    · rfl
    · rfl
  · simp only [WState.setv_val, WState.sets_val, WState.seth_val, Function.update_self]
    have h10 : 2 ^ 10 * (n + 1) = 1024 * (n + 1) := by norm_num
    rw [h10] at hc3
    simp only [hcl]
    linarith

end PhaseE


/-! ## The whole preparation -/

section Prep
variable (p : Program) (cap : ℕ)

/-- The output stream of the time constructor. -/
def Sout : Fin (ONS p.tapeCount + 1) := Stc p.tapeCount p.outputTape

def prep : OPg p.tapeCount :=
  .seq (phaseA p.tapeCount) (.seq (phaseB p) (.seq (phaseC p.tapeCount) (.seq (phaseD p.tapeCount (Sout p))
    (phaseE p.tapeCount))))

/-- The outer cold start: input `fr(x)`, witness `fr(w)`, all else blank and zero. -/
def ocold (x w : List Bool) : OSt p.tapeCount :=
  ⟨fun _ => 0, fun i => if i = Sx p.tapeCount then RepairOrdinary.frame x else if i = Sw p.tapeCount then
    RepairOrdinary.frame w else [], fun _ => 0, false⟩

/-- The preparation's cost bound. -/
def prepBound (C N n : ℕ) : ℕ := 100 * (N + 1) + 100 * C * (n + 1) + 2000000 * (n + 1)

@[simp] theorem ocold_val (x w : List Bool) (r : Fin ONR) : (ocold p x w).val r = 0 := rfl
@[simp] theorem ocold_sh (x w : List Bool) (i : Fin (ONS p.tapeCount + 1)) : (ocold p x w).sh i = 0 := rfl
@[simp] theorem ocold_sx (x w : List Bool) : (ocold p x w).st (Sx p.tapeCount) = RepairOrdinary.frame x := by
  simp [ocold]
@[simp] theorem ocold_sw (x w : List Bool) : (ocold p x w).st (Sw p.tapeCount) = RepairOrdinary.frame w := by
  simp [ocold, Sx, Sw]
theorem ocold_other (x w : List Bool) (i : Fin (ONS p.tapeCount + 1)) (h : 2 ≤ i.val) : (ocold p x w).st i = [] := by
  have h1 : i ≠ Sx p.tapeCount := by intro e; rw [e] at h; simp at h
  have h2 : i ≠ Sw p.tapeCount := by intro e; rw [e] at h; simp at h
  simp [ocold, h1, h2]

theorem stc_zero (h : 0 < p.tapeCount) : Stc p.tapeCount ⟨0, h⟩ = Su p.tapeCount := Fin.ext (by simp)

set_option maxHeartbeats 400000 in
/-- **The clock** (proof of `lem:multitape-refuter`; proof of `cor:framed-refuter`): from the outer cold start, `prep` leaves the input and the witness
in place, the `63` body streams blank, and the clock stream `1^{1024(T(N)+1)}`, all heads at `0`, within
`prepBound C N T(N)` steps. -/
theorem prep_spec (T : ℕ → ℕ) (C : ℕ)
    (wf : RepairOrdinary.WordFunction ℕ (fun n => List.replicate n true) (fun n => (T n).bits) (fun n => C * (T n + 1)))
    (hp : wf.program = p) (x w : List Bool)
    (hcap : 2 * x.length + 2 * C * (T x.length + 1) + 4096 * (T x.length + 1) + 8 ≤ cap) :
    ∃ τ c, WXExec cap (prep p) (ocold p x w) τ c ∧
      τ.st (Sx p.tapeCount) = RepairOrdinary.frame x ∧ τ.sh (Sx p.tapeCount) = 0 ∧
      τ.st (Sw p.tapeCount) = RepairOrdinary.frame w ∧ τ.sh (Sw p.tapeCount) = 0 ∧
      τ.st (Scl p.tapeCount) = List.replicate (clockLen (T x.length)) true ∧ τ.sh (Scl p.tapeCount) = 0 ∧
      (∀ k, τ.st (Sfr p.tapeCount k) = [] ∧ τ.sh (Sfr p.tapeCount k) = 0) ∧
      c ≤ prepBound C x.length (T x.length) := by
  subst hp
  set N := x.length with hN
  set n := T N with hn
  have hcap' : 2 * N + 2 * (C * (n + 1)) + 4096 * (n + 1) + 8 ≤ cap := by
    have := hcap; rw [show 2 * C * (n + 1) = 2 * (C * (n + 1)) by ring] at this; exact this
  have h2 : 2 ≤ wf.program.tapeCount := wf.program.twoTapes
  set σ0 := ocold wf.program x w with hσ0
  have v0 : ∀ r, σ0.val r = 0 := fun r => rfl
  have sh0 : ∀ i, σ0.sh i = 0 := fun i => rfl
  -- (a)
  obtain ⟨cA, eA, hcA⟩ := phaseA_spec wf.program.tapeCount cap σ0 x (ocold_sx _ _ _) (sh0 _)
    (ocold_other _ _ _ _ (by simp <;> omega)) (sh0 _) (v0 _) (v0 _) (by omega)
  set σA := (σ0.sets (Su wf.program.tapeCount) (RepairOrdinary.frame (List.replicate N true))).setv oN N with hσA
  -- (b)
  obtain ⟨r, hr, hout⟩ := wf.realizes N
  set word := List.replicate N true with hword
  have eB := phaseB_spec wf.program cap σA word
    (by
      intro j
      rcases j with ⟨jv, hjv⟩
      by_cases hj : jv = 0
      · subst hj
        rw [stc_zero wf.program (by omega)]
        simp [σA, Program.inputTapes, hword]
      · have hne : Stc wf.program.tapeCount ⟨jv, hjv⟩ ≠ Su wf.program.tapeCount := fun h => hj (by
          have := congrArg Fin.val h; simp at this; omega)
        simp only [σA, WState.setv_st, WState.sets_st, Function.update_apply, hne, if_false]
        rw [ocold_other _ _ _ _ (by simp <;> omega)]
        simp [Program.inputTapes, hj])
    (fun j => by simp [σA, sh0]) (by simp only [σA, WState.setv_st, WState.sets_st, Function.update_apply, show Slog wf.program.tapeCount ≠ Su wf.program.tapeCount by intro e; have := congrArg Fin.val e; simp at this, if_false]; exact ocold_other _ _ _ _ (by simp <;> omega))
    (by simp [σA, sh0]) _ r hr
  set s := r.steps with hs
  set σB := updS (tmapB wf.program) σA (Fin.addCases r.final.heads (fun _ => s))
    (Fin.addCases r.final.tapes (fun _ => List.replicate s true)) with hσB
  have hsF : s ≤ C * (n + 1) := runFrom_steps_le wf.program.machine _ _ r hr
  -- facts about the time constructor's run
  have hinit : ∀ i, (initialConfiguration wf.program.machine (wf.program.inputTapes word)).heads i ≤ 0 := fun i => le_rfl
  obtain ⟨bh, bl⟩ := run_bounds wf.program.machine _ _ r 0 hr hinit
  have hOutLen : (r.final.tapes wf.program.outputTape).length ≤ s := by
    have := bl wf.program.outputTape (by simp [initialConfiguration, Program.inputTapes, wf.program.outputFresh])
    omega
  have hOutH : r.final.heads wf.program.outputTape ≤ s := by have := bh wf.program.outputTape; omega
  have hbits : (r.final.tapes wf.program.outputTape) = n.bits := hout
  have hlen : ∀ j, s ≤ j → n.testBit j = false := by
    intro j hj
    rw [Nat.testBit_eq_inth]
    unfold List.getI
    rw [List.getD_eq_default _ _ (by rw [← hbits]; omega)]
    rfl
  -- reading σB
  have bSlog : σB.st (Slog wf.program.tapeCount) = List.replicate s true ∧ σB.sh (Slog wf.program.tapeCount) = s := by
    have e : Slog wf.program.tapeCount = tmapB wf.program (Fin.natAdd wf.program.tapeCount (0 : Fin 1)) := by simp [tmapB]
    rw [e]
    exact ⟨by simp [σB, updS, install_slot _ (tmapB_inj wf.program)], by simp [σB, updS, dockH_slot _ (tmapB_inj wf.program)]⟩
  have bOut : σB.st (Sout wf.program) = n.bits ∧ σB.sh (Sout wf.program) ≤ s := by
    have e : Sout wf.program = tmapB wf.program (Fin.castAdd 1 wf.program.outputTape) := by simp [tmapB, Sout]
    rw [e]
    refine ⟨by simp [σB, updS, install_slot _ (tmapB_inj wf.program), hbits], ?_⟩
    simp [σB, updS, dockH_slot _ (tmapB_inj wf.program)]; exact hOutH
  have bKept : ∀ i : Fin (ONS wf.program.tapeCount + 1), i.val < 3 ∨ 4 + wf.program.tapeCount ≤ i.val → σB.st i = σA.st i ∧ σB.sh i = σA.sh i :=
    fun i hi => updS_kept wf.program σA _ _ i hi
  have bval : ∀ r, σB.val r = σA.val r := fun r => rfl
  -- (c)
  have eC := phaseC_spec wf.program.tapeCount cap σB s bSlog.1 bSlog.2 (by rw [bval]; simp [σA, v0]) (by omega)
  set σC := ((σB.sets (Slog wf.program.tapeCount) (clrL (List.replicate s true) s)).seth (Slog wf.program.tapeCount) 0).setv oS s with hσC
  have so_ne : Sout wf.program ≠ Slog wf.program.tapeCount := by
    intro h; have := congrArg Fin.val h; simp [Sout] at this <;> omega
  -- (d)
  obtain ⟨cD, eD, hcD⟩ := phaseD_spec wf.program.tapeCount (Sout wf.program) cap σC n.bits n s (rd_bits n) hlen
    (by simp [σC, Function.update_apply, so_ne, bOut.1]) (by simp [σC, Function.update_apply, so_ne]; exact bOut.2)
    (by simp [σC]) (by simp [σC, bval, σA, v0]) (by simp [σC, bval, σA, v0]) (by simp [σC, bval, σA, v0])
    (by simp [σC, bval, σA, v0]) (by simp [σC, bval, σA, v0]) (by omega)
  set σD := ((σC.seth (Sout wf.program) 0).setv oK 0).setv oV n with hσD
  have scl_ne1 : Scl wf.program.tapeCount ≠ Sout wf.program := by
    intro h; have := congrArg Fin.val h; simp [Sout] at this <;> omega
  have scl_ne2 : Scl wf.program.tapeCount ≠ Slog wf.program.tapeCount := by intro h; have := congrArg Fin.val h; simp at this
  -- (e)
  obtain ⟨cE, eE, hcE⟩ := phaseE_spec wf.program.tapeCount cap σD n (by simp [σD]) (by simp [σD]) (by simp [σD, σC, bval, σA, v0])
    (by simp [σD, σC, bval, σA, v0]) (by simp [σD, σC, bval, σA, v0]) (by simp [σD, σC, bval, σA, v0])
    (by
      simp only [σD, σC, WState.setv_st, WState.seth_st, WState.sets_st, Function.update_apply, scl_ne2, if_false]
      rw [(bKept (Scl wf.program.tapeCount) (by simp)).1]
      simp only [σA, WState.setv_st, WState.sets_st, Function.update_apply,
        show Scl wf.program.tapeCount ≠ Su wf.program.tapeCount by intro e; have := congrArg Fin.val e; simp at this,
        if_false]
      exact ocold_other _ _ _ _ (by simp <;> omega))
    (by
      simp only [σD, σC, WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_apply, scl_ne1, scl_ne2,
        if_false]
      rw [(bKept (Scl wf.program.tapeCount) (by simp)).2]; simp [σA, sh0])
    (by linarith [hcap'])
  set τ := (σD.setv oK (clockLen n)).sets (Scl wf.program.tapeCount) (List.replicate (clockLen n) true) with hτ
  -- the kept streams of τ
  have kept : ∀ i : Fin (ONS wf.program.tapeCount + 1), i.val < 2 ∨ 4 + wf.program.tapeCount ≤ i.val → τ.st i = σ0.st i ∧ τ.sh i = σ0.sh i := by
    intro i hi
    have n1 : i ≠ Scl wf.program.tapeCount := by intro h; rw [h] at hi; simp at hi; omega
    have n2 : i ≠ Slog wf.program.tapeCount := by intro h; rw [h] at hi; simp at hi; omega
    have n3 : i ≠ Sout wf.program := by intro h; rw [h] at hi; simp [Sout] at hi; omega
    have n4 : i ≠ Su wf.program.tapeCount := by intro h; rw [h] at hi; simp at hi; omega
    have hb := bKept i (by omega)
    refine ⟨?_, ?_⟩
    · simp only [τ, σD, σC, WState.sets_st, WState.setv_st, WState.seth_st, Function.update_apply, n1, n2, if_false]
      rw [hb.1]; simp only [σA, WState.setv_st, WState.sets_st, Function.update_apply, n4, if_false]
    · simp only [τ, σD, σC, WState.sets_sh, WState.setv_sh, WState.seth_sh, Function.update_apply, n1, n2, n3, if_false]
      rw [hb.2]; simp only [σA, WState.setv_sh, WState.sets_sh]
  refine ⟨τ, _, WXExec.seq eA (WXExec.seq eB (WXExec.seq eC (WXExec.seq eD eE))), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [(kept _ (by simp)).1]; exact ocold_sx _ _ _
  · rw [(kept _ (by simp)).2]; rfl
  · rw [(kept _ (by simp)).1]; exact ocold_sw _ _ _
  · rw [(kept _ (by simp)).2]; rfl
  · simp [τ]
  · simp only [τ, WState.sets_sh]
    simp [σD, Function.update_apply, scl_ne1]
    simp only [σC, WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_apply, scl_ne2, if_false]
    rw [(bKept (Scl wf.program.tapeCount) (by simp)).2]; simp [σA, sh0]
  · intro k
    have hk := kept (Sfr wf.program.tapeCount k) (by simp)
    refine ⟨?_, ?_⟩
    · rw [hk.1]; exact ocold_other _ _ _ _ (by simp <;> omega)
    · rw [hk.2]; rfl
  · unfold prepBound
    have : s * 9 + 3 ≤ 9 * C * (n + 1) + 3 := by nlinarith
    nlinarith

end Prep

end NearCubicGates.Adapters.Refuter.Clock
