import SourceAdapters.Refuter.RLoadPost
import SourceAdapters.Refuter.RMachine

/-!
# R's loader (input 7, R: INIT) and the refuter for every admissible clock

Paper context: `lem:multitape-refuter`, Steps 1 and 4, and `cor:framed-refuter`. The refuter computes
the supplied clock, prepares the diagonal records and initializes the search state. One fixed oracle
program has a polynomial time bound whose degree is independent of `M`; its coefficient and onset may
depend on `M`.

`loadP p` (`p` the time constructor of `T`) is R's loader: parse `fr(fr(code) fr(1^N))` (`parseP`), write the
time constructor's input `fr(1^N)` (`tcinP`), run the time constructor through `WMX.machZ` of its clocked
machine (`callT`, L's `clockMachine`; `Mach.clockDock_padded`: heads restored, unary step count on `TLI`, log
restored), then `postP`. `initOK`: it satisfies `InitOK` with `C0` the time constructor's coefficient, cost
`C·(T(N)+1)^2` (`C` depends on `M` through `|code M|` and `machineIndex M`), onset `16(machineIndex M + 3)`.

**`loaderExists`**: `∀ T, TimeConstructible T → InClockRange T → LoaderExists T`, and with
`refuterRealization_of_loader` (RMachine): `RefuterRealization T` for every admissible clock from the X5(b) join.
-/

namespace NearCubicGates.Adapters.Refuter.RM

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairSource
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicGates.Close.WordPrograms NearCubicGates.Adapters.Refuter NearCubicGates.Adapters.Compile
open NearCubicWires.RepairSource.OrdinaryOracleCompose (clockMachine)
open NearCubicWires.Bindings.CLW20Theorem113 (pairInput TimeConstructible InClockRange)
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! ## The loader program -/

section Prog
variable {tc : ℕ} (p : RepairOrdinary.Program)

/-- The time constructor's input stream. -/
def k0 : Fin (NS tc p.tapeCount + 1) := sK ⟨0, by have := p.twoTapes; omega⟩

/-- The time constructor, clocked (unary step count on `TLI`), heads restored, log `LOG`. -/
noncomputable def callT : WMX (NS tc p.tapeCount) NR :=
  WMX.machZ (clockMachine p.machine)
    (Fin.addCases (motive := fun _ => Fin (NS tc p.tapeCount + 1)) sK (fun _ : Fin 1 => sTLI)) sLOG

/-- **R's loader.** -/
noncomputable def loadP : WMX (NS tc p.tapeCount) NR :=
  .seq (parseP sIN sCODE sNU r0 rC r1) (.seq (tcinP sNU (k0 p) r0 r1) (.seq (callT p) (postP p)))

end Prog

/-! ## Cost bounds -/

theorem postBound_le (c m N n s CT X : ℕ) (hX : 1 ≤ X) (hN : N + 1 ≤ X) (hn : n ≤ X) (hs : s ≤ CT * X) :
    postBound c m N n s ≤ (50 * CT + c * (40 * m + 50) + 1600) * X ^ 2 := by
  have hY : X ≤ X ^ 2 := by nlinarith
  have hY1 : 1 ≤ X ^ 2 := by nlinarith
  have h1 : (N / 16 + 1) * (41 * (N / 16 + 2) + 20) ≤ X * (82 * X + 20) := Nat.mul_le_mul (by omega) (by omega)
  have h2 : X * (82 * X + 20) ≤ 102 * X ^ 2 := by nlinarith
  have h3 : CT * X ≤ CT * X ^ 2 := Nat.mul_le_mul_left _ hY
  have h4 : c * (40 * m + 50) ≤ c * (40 * m + 50) * X ^ 2 := Nat.le_mul_of_pos_right _ (by omega)
  have h5 : 50 * (N / 16 + 2) + 1 ≤ 101 * X := by omega
  unfold postBound
  nlinarith

theorem total_le (c m N CT X P : ℕ) (hX : 1 ≤ X) (hN : N + 1 ≤ X)
    (hP : P ≤ (50 * CT + c * (40 * m + 50) + 1600) * X ^ 2) :
    100 * (c + N + 1) + 1 + (40 * (N + 1) + 1 + (2 * (CT * X) + 2 + 1 + P)) ≤
      (200 * (c + 1) * (m + 1) + 60 * CT + 2000) * X ^ 2 := by
  have hY : X ≤ X ^ 2 := by nlinarith
  have hY1 : 1 ≤ X ^ 2 := by nlinarith
  have a1 : c + N + 1 ≤ (c + 1) * X ^ 2 := by nlinarith
  have a2 : N + 1 ≤ X ^ 2 := le_trans hN hY
  have a3 : CT * X ≤ CT * X ^ 2 := Nat.mul_le_mul_left _ hY
  have a4 : 40 * c * m + 150 * c + 52 * CT + 1745 ≤ 200 * (c + 1) * (m + 1) + 60 * CT + 2000 := by nlinarith
  have a5 := Nat.mul_le_mul_right (X ^ 2) a4
  nlinarith

/-! ## Reading the state `postP` leaves -/

section PostRead
variable {tc : ℕ} (p : RepairOrdinary.Program)

theorem postSt_sh (ρ : WState (NS tc p.tapeCount) NR) (code : List Bool) (N n : ℕ) :
    (postSt p ρ code N n).sh = ρ.sh := by
  simp only [postSt, setsL_sh, WState.sets_sh]

theorem postSt_val (ρ : WState (NS tc p.tapeCount) NR) (code : List Bool) (N n : ℕ) :
    (postSt p ρ code N n).val = ρ.val := by
  simp only [postSt, setsL_val, WState.sets_val]

theorem postSt_cell (ρ : WState (NS tc p.tapeCount) NR) (code : List Bool) (N n : ℕ) :
    (postSt p ρ code N n).cell = ρ.cell := by
  simp only [postSt, setsL_cell, WState.sets_cell]

theorem postSt_far (ρ : WState (NS tc p.tapeCount) NR) (code : List Bool) (N n : ℕ)
    (Y : Fin (NS tc p.tapeCount + 1)) (hY : 29 ≤ Y.val) : (postSt p ρ code N n).st Y = ρ.st Y := by
  have ne : ∀ X : Fin (NS tc p.tapeCount + 1), X.val < 29 → Y ≠ X := fun X hX h => by rw [h] at hY; omega
  simp only [postSt]
  rw [setsL_other _ _ Y (by
    simp only [flagList, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨ne _ (by simp), ne _ (by simp), ne _ (by simp), ne _ (by simp), ne _ (by simp), ne _ (by simp),
      ne _ (by simp)⟩)]
  simp only [WState.sets_st, Function.update_of_ne (ne sFF (by simp)), Function.update_of_ne (ne sSV (by simp)),
    Function.update_of_ne (ne sONE (by simp))]
  rw [setsL_other _ _ Y (by
    simp only [numList, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨ne _ (by simp), ne _ (by simp), ne _ (by simp), ne _ (by simp), ne _ (by simp), ne _ (by simp),
      ne _ (by simp), ne _ (by simp), ne _ (by simp), ne _ (by simp)⟩)]
  simp only [WState.sets_st, Function.update_of_ne (ne sXU (by simp)), Function.update_of_ne (ne sMU (by simp)),
    Function.update_of_ne (ne sGU (by simp)), Function.update_of_ne (ne sTU (by simp))]

end PostRead

/-! ## The loader satisfies `InitOK` -/

section Init
variable {budget : CNFCompilationRequest → ℕ} {query : CNFCompilationRequest → ℕ}
variable (f : WordFunction CNFCompilationRequest CNFCompilationRequest.word
  (fun r => RepairOrdinary.frame (query r).bits) budget)

theorem foldl_idx (M : OrdinaryWeakMachine) : (VerifierEncoding.code M.verifier).foldl idx 1 = machineIndex M := rfl

theorem cold_other {tT : ℕ} (input : List Bool) (Lc : ℕ) (Y : Fin (NS f.program.tapeCount tT + 1)) (h1 : Y ≠ sIN)
    (h2 : Y ≠ sLOG) : (cold (tT := tT) f input Lc).st Y = [] := by
  simp only [cold, if_neg h1, if_neg h2]

theorem cold_log {tT : ℕ} (input : List Bool) (Lc : ℕ) :
    (cold (tT := tT) f input Lc).st sLOG = List.replicate Lc false := by
  simp [cold, show (sLOG : Fin (NS f.program.tapeCount tT + 1)) ≠ sIN by ds]

theorem cold_in {tT : ℕ} (input : List Bool) (Lc : ℕ) :
    (cold (tT := tT) f input Lc).st sIN = RepairOrdinary.frame input := by
  simp [cold]

set_option maxHeartbeats 400000 in
/-- **R's loader satisfies the loader contract.** -/
theorem initOK (T : ℕ → ℕ) (hT : InClockRange T) (CT : ℕ)
    (wf : RepairOrdinary.WordFunction ℕ (fun n => List.replicate n true) (fun n => (T n).bits)
      (fun n => CT * (T n + 1))) :
    InitOK (tT := wf.program.tapeCount) f T (loadP (tc := f.program.tapeCount) wf.program) := by
  refine ⟨CT, fun M _ => ?_⟩
  set code := VerifierEncoding.code M.verifier with hcode
  set m := machineIndex M with hm
  have hfm : code.foldl idx 1 = m := foldl_idx M
  refine ⟨200 * (code.length + 1) * (m + 1) + 60 * CT + 2000, 16 * (m + 3), fun N hN Lc hLc => ?_⟩
  set X := T N + 1 with hX
  have hNT : N ≤ T N := hT.1 N
  set g := N / 16 with hg
  have hgm : g + m + 2 ≤ N := by omega
  -- the cold start
  set σ0 := cold (tT := wf.program.tapeCount) f (pairInput M N) Lc with hσ0
  set cap := 4 * (code.length + m + N + T N + CT * X + 20) + 100 with hcap
  have hk0 : ∀ Y : Fin (NS f.program.tapeCount wf.program.tapeCount + 1), Y.val < 41 → Y ≠ k0 wf.program :=
    fun Y hY h => by rw [h] at hY; simp only [k0, sK_val] at hY; omega
  -- parse and the time constructor's input
  have nIN : ∀ Y : Fin (NS f.program.tapeCount wf.program.tapeCount + 1), 0 < Y.val → Y ≠ sIN := fun Y hY h => by
    rw [h] at hY; simp at hY
  have e1 := parse_spec cap sIN sCODE sNU r0 rC r1 (by ds) (by ds) (by ds) (by decide) (by decide) (by decide) σ0
    code N (by rw [hσ0, cold_in]; rfl) (by rw [hσ0]; exact cold_other f _ _ _ (by ds) (by ds))
    (by rw [hσ0]; exact cold_other f _ _ _ (by ds) (by ds)) rfl rfl rfl rfl rfl rfl (by omega)
  set σ1 := (σ0.sets sCODE (RepairOrdinary.frame code)).sets sNU (List.replicate N true) with hσ1
  have nk1 := hk0 sNU (by simp)
  have nk2 := hk0 sCODE (by simp)
  have nk3 := hk0 sIN (by simp)
  have nk4 := hk0 sLOG (by simp)
  have nk5 := hk0 sTLI (by simp)
  have e2 := tcin_spec cap sNU (k0 wf.program) r0 r1 nk1 (by decide) σ1 N
    (by simp [hσ1]) rfl
    (by simp only [hσ1, WState.sets_st, Function.update_of_ne nk1, Function.update_of_ne nk1.symm, Function.update_of_ne nk2, Function.update_of_ne nk2.symm]
        try rw [hσ0]
        exact cold_other f _ _ _ nk3.symm nk4.symm) rfl rfl rfl (by omega)
  set σ2 := σ1.sets (k0 wf.program) (RepairOrdinary.frame (List.replicate N true)) with hσ2
  -- the clock
  have hKne : ∀ (j : Fin wf.program.tapeCount) (Y : Fin (NS f.program.tapeCount wf.program.tapeCount + 1)),
      Y.val < 41 → sK j ≠ Y := fun j Y hY h => by rw [← h] at hY; simp only [sK_val] at hY; omega
  have hσ2log : σ2.st sLOG = List.replicate Lc false := by
    simp only [hσ2, hσ1, WState.sets_st, Function.update_of_ne nk4, Function.update_of_ne nk4.symm,
      Function.update_of_ne (show (sLOG : Fin (NS f.program.tapeCount wf.program.tapeCount + 1)) ≠ sNU by ds),
      Function.update_of_ne (show (sLOG : Fin (NS f.program.tapeCount wf.program.tapeCount + 1)) ≠ sCODE by ds)]
    try rw [hσ0]
    exact cold_log f _ _
  have hσ2tli : σ2.st sTLI = [] := by
    simp only [hσ2, hσ1, WState.sets_st, Function.update_of_ne nk5, Function.update_of_ne nk5.symm,
      Function.update_of_ne (show (sTLI : Fin (NS f.program.tapeCount wf.program.tapeCount + 1)) ≠ sNU by ds),
      Function.update_of_ne (show (sTLI : Fin (NS f.program.tapeCount wf.program.tapeCount + 1)) ≠ sCODE by ds)]
    try rw [hσ0]
    exact cold_other f _ _ sTLI (by ds) (by ds)
  have hσ2sh : ∀ i, σ2.sh i = 0 := fun i => by rw [hσ2, hσ1, hσ0]; rfl
  obtain ⟨receipt, τ3, hrun, hout, hsteps, e3, hst, hTLst, hsh0, hTLsh, hother, hval, hcell⟩ :=
    Mach.clockDock_padded wf N cap sK sK_inj sTLI sLOG (fun j => hKne j _ (by simp)) (fun j => hKne j _ (by simp))
      (by ds) σ2 (fun _ => 0) 0 Lc
      (fun j => by
        rw [ZeroPadding.pad_zero]
        simp only [RepairOrdinary.Program.inputTapes]
        by_cases hj : j.val = 0
        · have : sK (tc := f.program.tapeCount) j = k0 wf.program := by simp [k0, Fin.ext_iff, hj]
          rw [if_pos hj, this, hσ2]; simp
        · rw [if_neg hj]
          have h1 : sK (tc := f.program.tapeCount) j ≠ k0 wf.program := fun h => hj (by simpa [k0, Fin.ext_iff] using h)
          simp only [hσ2, hσ1, WState.sets_st, Function.update_of_ne h1, Function.update_of_ne (hKne j sNU (by simp)),
            Function.update_of_ne (hKne j sCODE (by simp))]
          try rw [hσ0]
          exact cold_other f _ _ (sK j) (hKne j _ (by simp)) (hKne j _ (by simp)))
      (by rw [hσ2tli]; rfl) (fun j => hσ2sh _) (hσ2sh _) hσ2log (hσ2sh _) hLc
  set s := receipt.steps with hs
  have hsX : s ≤ CT * X := hsteps
  -- `T(N) < 2^s`: the output has at most `s` cells
  have hinit : ∀ i, (initialConfiguration wf.program.machine
      (wf.program.inputTapes (List.replicate N true))).heads i ≤ 0 := fun i => le_rfl
  obtain ⟨-, bl⟩ := Clock.run_bounds wf.program.machine _ _ receipt 0 hrun hinit
  have hOutLen : (T N).bits.length ≤ s := by
    have := bl wf.program.outputTape
      (by simp [initialConfiguration, RepairOrdinary.Program.inputTapes, wf.program.outputFresh])
    have hout' : receipt.final.tapes wf.program.outputTape = (T N).bits := hout
    rw [hout'] at this; omega
  have hlen : ∀ j, s ≤ j → (T N).testBit j = false := by
    intro j hj
    rw [Nat.testBit_eq_inth]
    unfold List.getI
    rw [List.getD_eq_default _ _ (by omega)]
    rfl
  have hn : T N < 2 ^ s := Nat.lt_pow_two_of_testBit _ hlen
  -- the state after the clock
  have hfix : ∀ Y : Fin (NS f.program.tapeCount wf.program.tapeCount + 1), Y.val < 41 → Y ≠ sTLI →
      τ3.st Y = σ2.st Y := fun Y hY hY' => (hother Y (fun j => hKne j Y hY) hY').1
  have hsh3 : ∀ i, τ3.sh i = 0 := by
    intro i
    by_cases h1 : ∃ j, sK j = i
    · obtain ⟨j, rfl⟩ := h1; exact hsh0 j
    · by_cases h2 : i = sTLI
      · rw [h2]; exact hTLsh
      · rw [(hother i (fun j hj => h1 ⟨j, hj⟩) h2).2]; exact hσ2sh i
  have hv3 : ∀ r, τ3.val r = 0 := fun r => by rw [hval, hσ2, hσ1, hσ0]; rfl
  have ev2 : ∀ Y : Fin (NS f.program.tapeCount wf.program.tapeCount + 1), Y.val < 41 → Y ≠ sTLI → Y ≠ sIN →
      Y ≠ sLOG → Y ≠ sCODE → Y ≠ sNU → τ3.st Y = [] := fun Y hY h1 h2 h3 h4 h5 => by
    rw [hfix Y hY h1, hσ2, hσ1]
    simp only [WState.sets_st, Function.update_of_ne (hk0 Y hY), Function.update_of_ne h4, Function.update_of_ne h5]
    try rw [hσ0]
    exact cold_other f _ _ Y h2 h3
  -- everything after the clock
  have e4 := post_spec wf.program cap τ3 code N (T N) s hsh3 hv3 (by rw [hTLst]; simp)
    (by simp only [ko]; rw [hst, ZeroPadding.pad_zero]; exact hout) hn (ev2 _ (by simp) (by ds) (by ds) (by ds)
      (by ds) (by ds))
    (by rw [hfix _ (by simp) (by ds)]; simp only [hσ2, hσ1, WState.sets_st, Function.update_of_ne nk1, Function.update_of_ne nk1.symm,
        Function.update_self])
    (ev2 _ (by simp) (by ds) (by ds) (by ds) (by ds) (by ds))
    (by rw [hfix _ (by simp) (by ds)]; simp only [hσ2, hσ1, WState.sets_st, Function.update_of_ne nk2, Function.update_of_ne nk2.symm,
        Function.update_of_ne (show (sCODE : Fin (NS f.program.tapeCount wf.program.tapeCount + 1)) ≠ sNU by ds),
        Function.update_self])
    (ev2 _ (by simp) (by ds) (by ds) (by ds) (by ds) (by ds)) (ev2 _ (by simp) (by ds) (by ds) (by ds) (by ds) (by ds))
    (fun Y hY => by
      simp only [numList, List.mem_cons, List.not_mem_nil, or_false] at hY
      rcases hY with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact ev2 _ (by simp) (by ds) (by ds) (by ds) (by ds) (by ds))
    (fun q hq => by
      simp only [flagList, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact ev2 _ (by simp) (by ds) (by ds) (by ds) (by ds) (by ds))
    (by rw [hfm]; omega) (by rw [hfm]; omega)
  rw [hfm] at e4
  set τ := postSt wf.program τ3 code N (T N) with hτ
  refine ⟨cap, τ, (WXExec.seq e1 (WXExec.seq e2 (WXExec.seq e3 e4))).mono ?_, ?_⟩
  · -- the cost
    have hP := postBound_le code.length m N (T N) s CT X (by omega) (by omega) (by omega) hsX
    exact total_le code.length m N CT X _ (by omega) (by omega) hP
  · -- the fresh round state
    clear e1 e2 e3 e4
    have hdat : dat M T N = ⟨code, m, N - g - m - 2, g, T N⟩ := rfl
    rw [hdat]
    have hτ3code : τ3.st sCODE = RepairOrdinary.frame code := by
      rw [hfix _ (by simp) (by ds)]
      simp only [hσ2, hσ1, WState.sets_st, Function.update_of_ne nk2, Function.update_of_ne nk2.symm,
        Function.update_of_ne (show (sCODE : Fin (NS f.program.tapeCount wf.program.tapeCount + 1)) ≠ sNU by ds),
        Function.update_self]
    have hτ3log : τ3.st sLOG = List.replicate Lc false := by rw [hfix _ (by simp) (by ds)]; exact hσ2log
    have hτ3C : ∀ j : Fin f.program.tapeCount, τ3.st (sC j) = [] := by
      intro j
      have hj := j.isLt
      have h1 : ∀ j' : Fin wf.program.tapeCount, sK j' ≠ sC j := fun j' h => by
        have := congrArg Fin.val h; simp at this; omega
      rw [(hother (sC j) h1 (fun h => by have := congrArg Fin.val h; simp at this; omega)).1]
      have h2 : sC (tT := wf.program.tapeCount) j ≠ k0 wf.program := fun h => by
        have := congrArg Fin.val h; simp [k0] at this; omega
      have h3 : sC (tT := wf.program.tapeCount) j ≠ sNU := fun h => by
        have := congrArg Fin.val h; simp at this; omega
      have h4 : sC (tT := wf.program.tapeCount) j ≠ sCODE := fun h => by
        have := congrArg Fin.val h; simp at this; omega
      simp only [hσ2, hσ1, WState.sets_st, Function.update_of_ne h2, Function.update_of_ne h3, Function.update_of_ne h4]
      try rw [hσ0]
      exact cold_other f _ _ _ (fun h => by have := congrArg Fin.val h; simp at this)
        (fun h => by have := congrArg Fin.val h; simp at this; omega)
    have hC : ∀ j : Fin f.program.tapeCount, τ.st (sC j) = [] := fun j => by
      rw [hτ, postSt_far _ _ _ _ _ _ (by simp; omega)]; exact hτ3C j
    have hOUT : τ3.st sOUT = [] := ev2 _ (by simp) (by ds) (by ds) (by ds) (by ds) (by ds)
    have hG : τ3.st sG = [] := ev2 _ (by simp) (by ds) (by ds) (by ds) (by ds) (by ds)
    have hTL : τ3.st sTL = [] := ev2 _ (by simp) (by ds) (by ds) (by ds) (by ds) (by ds)
    have hP : ∀ Y, τ.st Y = (postSt wf.program τ3 code N (T N)).st Y := fun Y => rfl
    simp only [postSt, hfm] at hP
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, by simp [SS.fresh], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ⟨0, ?_⟩, ⟨0, ?_⟩,
      ⟨0, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, fun j _ => hC j, ⟨[], [], by simp only [qo]; rw [hC]; rfl, fun _ => rfl, by simp⟩, ?_,
      fun i => by rw [hτ, postSt_sh]; exact hsh3 i, fun r => by rw [hτ, postSt_val]; exact hv3 r,
      by rw [hτ, postSt_cell, hcell, hσ2, hσ1, hσ0]; rfl⟩ <;>
      simp [hP, setsL, numList, flagList, Function.update_apply, Fin.ext_iff, SS.fresh, hτ3code, hτ3log, hOUT, hG,
        hTL, hg]

end Init

/-! ## The loader contract and the refuter -/

/-- **The loader contract holds for every admissible clock.** -/
theorem loaderExists (T : ℕ → ℕ) (hTc : TimeConstructible T) (hT : InClockRange T) : LoaderExists T := by
  obtain ⟨CT, -, ⟨wf⟩⟩ := hTc
  intro K d query f
  exact ⟨wf.program.tapeCount, loadP wf.program, initOK f T hT CT wf⟩

/-- **`RefuterRealization T` for every time-constructible clock in range, from the X5(b) join.** -/
theorem refuterRealization_of_computationToCNF (h : ComputationToCNF) :
    ∀ T : ℕ → ℕ, TimeConstructible T → InClockRange T → RefuterRealization T :=
  refuterRealization_of_loader h (fun T hTc hT => loaderExists T hTc hT)

end NearCubicGates.Adapters.Refuter.RM
