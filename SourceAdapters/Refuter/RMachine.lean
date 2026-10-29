import SourceAdapters.Refuter.RMachRound

/-!
# R's two machines satisfy the round contract, given the loader (input 7, R: assembly)

Paper anchor: `lem:multitape-refuter` and `cor:framed-refuter` (one oracle
program, one degree fixed before `M`; per `M` a coefficient and an onset).

The round machine is `MS = (stepP f).compile`. Between pieces the physical tapes are only known up to
`Mach.Parked` (exact on the output stream, the answer cell and the query tape); `Enc` packages `Rep` with it.
`machines_of_init` builds `RoundMachines T query` from `step_spec` and the initialization contract `InitOK`: a
word program that takes the cold input tapes of `pairInput M N` to `Rep … SS.fresh false` within
`C·(T(N)+1)^2` steps (parse, clock, constants).
-/

namespace NearCubicGates.Adapters.Refuter.RM

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairSource
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicGates.Close.WordPrograms NearCubicGates.Adapters.Refuter NearCubicGates.Adapters.Compile
open NearCubicWires.RepairSource.OrdinaryOracleCompose (Ports)
open NearCubicWires.WireExponent3_5.PrimAsm.DockW (tape_cases)
open NearCubicWires.Bindings.CLW20Theorem113 (pairInput TimeConstructible InClockRange)

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {tT : ℕ}
variable {budget : CNFCompilationRequest → ℕ} {query : CNFCompilationRequest → ℕ}
variable (f : WordFunction CNFCompilationRequest CNFCompilationRequest.word
  (fun r => RepairOrdinary.frame (query r).bits) budget)

local notation "WSf" => WState (NS f.program.tapeCount tT) NR

/-- The exact streams: output, answer cell, query tape. -/
def Ex (i : Fin (NS f.program.tapeCount tT + 1)) : Prop := i = sOUT ∨ i = sANS ∨ i = qo (tT := tT) f

/-- The per-run data of `M` at length `N`. -/
structure Dat where
  code : List Bool
  mi : ℕ
  xr : ℕ
  g : ℕ
  TN : ℕ

def dat (M : OrdinaryWeakMachine) (T : ℕ → ℕ) (N : ℕ) : Dat :=
  ⟨VerifierEncoding.code M.verifier, machineIndex M, N - N / 16 - machineIndex M - 2, N / 16, T N⟩

/-- The cold word state from which INIT starts. -/
def cold (input : List Bool) (Lc : ℕ) : WSf :=
  ⟨fun _ => 0, fun i => if i = sIN then RepairOrdinary.frame input else if i = sLOG then List.replicate Lc false else [],
    fun _ => 0, false⟩

/-- **The contract for R's loader.** A word program taking the cold input `pairInput M N` to the
fresh round state (`Rep … SS.fresh false`, empty previous query) within `C (T N + 1)^2` steps, for every log
length `Lc ≥ C0 (T N + 1)` (the clock function's call needs `C0 (T N + 1)` blank log cells). -/
def InitOK (T : ℕ → ℕ) (initP : WMX (NS f.program.tapeCount tT) NR) : Prop :=
  ∃ C0 : ℕ, ∀ M : OrdinaryWeakMachine, OrdinaryLittleO M T → ∃ C onset : ℕ, ∀ N, onset ≤ N → ∀ Lc,
    C0 * (T N + 1) ≤ Lc → ∃ (cap : ℕ) (τ : WSf), WXExec cap initP (cold (tT := tT) f (pairInput M N) Lc) τ
      (C * (T N + 1) ^ 2) ∧
      Rep f (dat M T N).code (dat M T N).mi (dat M T N).xr (dat M T N).g (dat M T N).TN Lc SS.fresh false τ

/-- Physical tapes read like the word state, exact on `Ex`. -/
theorem Parked.of_rd {σ σ' : WSf} {a : Fin (NS f.program.tapeCount tT + 2 + NR) → List Bool}
    (h : Mach.Parked (Ex f) σ a) (hrd : ∀ i, RdEq (σ'.st i) (σ.st i)) (hex : ∀ i, Ex f i → σ'.st i = σ.st i) :
    Mach.Parked (Ex f) σ' a :=
  ⟨fun i => (hrd i).trans (h.read i), fun i hi => (h.exact i hi).trans (hex i hi).symm, h.cell, h.reg⟩

theorem rest_of (σ : WSf) (hsh : ∀ i, σ.sh i = 0) (hv : ∀ r, σ.val r = 0) (hc : σ.cell = false) : Mach.Rest σ :=
  ⟨hsh, hv, hc⟩

/-- The cold tapes are parked. -/
theorem parked_input (input : List Bool) (Lc : ℕ) :
    Mach.Parked (Ex (tT := tT) f) (cold (tT := tT) f input Lc)
      (fun j : Fin (NS f.program.tapeCount tT + 2 + NR) => if j.val = 0 then RepairOrdinary.frame input else []) := by
  refine ⟨fun i => ?_, fun i hi => ?_, ?_, fun r => ?_⟩
  · by_cases h0 : i = sIN
    · subst h0
      have h1 : (sTape (nr := NR) (sIN : Fin (NS f.program.tapeCount tT + 1))).val = 0 := rfl
      simp only [cold, if_pos rfl, h1, if_true]; exact RdEq.refl _
    · have hv : (sTape (nr := NR) i).val ≠ 0 := by
        simp only [sTape]; split_ifs with h
        · exact absurd (Fin.ext (by simpa [sIN] using h)) h0
        · omega
      simp only [cold, h0, if_false, hv]
      split_ifs
      · exact rdEq_blank _ (fun b hb => (List.mem_replicate.1 hb).2)
      · exact RdEq.refl _
  · have h0 : i ≠ sIN := by
      rcases hi with rfl | rfl | rfl
      · ds
      · ds
      · simp only [qo]; exact (sC_ne _ _ (by simp)).symm

    have hv : (sTape (nr := NR) i).val ≠ 0 := by
      simp only [sTape]; split_ifs with h
      · exact absurd (Fin.ext (by simpa [sIN] using h)) h0
      · omega
    have hL : i ≠ sLOG := by
      rcases hi with rfl | rfl | rfl
      · ds
      · ds
      · simp only [qo]; exact (sC_ne _ _ (by simp)).symm
    simp [cold, h0, hL, hv]
  · simp [cTape]; exact RdEq.refl _
  · simp [rTape]; exact RdEq.refl _

/-- The ports of R: output stream, query tape = the compiler's output stream. -/
def rports : Ports (NS f.program.tapeCount tT + 2 + NR) where
  twoTapes := by unfold NS; omega
  outputTape := sTape sOUT
  outputFresh := by simp [sTape, sOUT]
  queryTape := sTape (qo (tT := tT) f)
  queryFresh := by simp [sTape, qo, sC]

theorem pow_bound (c K d X : ℕ) (hX : 1 ≤ X) : K * (c + 3 * X) ^ d ≤ K * (c + 3) ^ d * X ^ d := by
  rw [mul_assoc, ← mul_pow]
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by nlinarith) d)

theorem le_pow_succ (X d k : ℕ) (hX : 1 ≤ X) (hk : k ≤ d + 1) : X ^ k ≤ X ^ (d + 1) := Nat.pow_le_pow_right hX hk

/-- **The two machines of R satisfy the round contract, given the loader.** -/
theorem machines_of_init (T : ℕ → ℕ) (hT : InClockRange T) (K d : ℕ) (hbud : ∀ r, budget r ≤ K * r.measure ^ d)
    (initP : WMX (NS f.program.tapeCount tT) NR) (hinit : InitOK (tT := tT) f T initP) :
    Nonempty (RoundMachines T query) := by
  obtain ⟨C0, hI⟩ := hinit
  refine ⟨⟨NS f.program.tapeCount tT + 2 + NR, initP.size, (stepP (tT := tT) f).size, rports f, initP.compile,
    (stepP (tT := tT) f).compile, sTape sANS, sTape sDONE, 2 * d + 2, fun M hM => ?_⟩⟩
  obtain ⟨CI, oI, hIM⟩ := hI M hM
  set c := (VerifierEncoding.code M.verifier).length with hc
  set m := machineIndex M with hm
  set A := c + m + 3 + K * (c + 3) ^ d + 1 + C0 + 10 with hA
  let Lc : ℕ → ℕ := fun N => K * (c + 3 * (T N + 1)) ^ d + 1 + C0 * (T N + 1)
  refine ⟨CI + (f.program.tapeCount + 3) * 2000 * A ^ 2, max oI (16 * (m + 3)),
    fun N S β a => ∃ σ : WSf, Mach.Parked (Ex f) σ a ∧
      Rep f (dat M T N).code (dat M T N).mi (dat M T N).xr (dat M T N).g (dat M T N).TN (Lc N) S β σ,
    fun N hN => ?_⟩
  have hN1 : oI ≤ N := le_of_max_le_left hN
  have hN2 : 16 * (m + 3) ≤ N := le_of_max_le_right hN
  have hg1 : 1 ≤ N / 16 := by omega
  have hrec : machineIndex M + 2 + N / 16 ≤ N := by omega
  have hTN : N ≤ T N := hT.1 N
  set X := T N + 1 with hX
  have hX1 : 1 ≤ X := by omega
  -- the size bound
  have hsize : (dat M T N).code.length + (dat M T N).mi + (dat M T N).xr + (dat M T N).g + (dat M T N).TN + Lc N + 10
      ≤ A * X ^ (d + 1) := by
    simp only [dat, Lc]
    have h1 := pow_bound c K d X hX1
    have hXd : X ^ d ≤ X ^ (d + 1) := le_pow_succ X d d hX1 (by omega)
    have hX1' : X ≤ X ^ (d + 1) := by
      calc X = X ^ 1 := (pow_one X).symm
        _ ≤ X ^ (d + 1) := le_pow_succ X d 1 hX1 (by omega)
    have h1' : 1 ≤ X ^ (d + 1) := Nat.one_le_pow _ _ hX1
    have e1 : K * (c + 3) ^ d * X ^ d ≤ K * (c + 3) ^ d * X ^ (d + 1) := Nat.mul_le_mul_left _ hXd
    have e2 : C0 * X ≤ C0 * X ^ (d + 1) := Nat.mul_le_mul_left _ hX1'
    have e3 : (c + m + 3) * X ≤ (c + m + 3) * X ^ (d + 1) := Nat.mul_le_mul_left _ hX1'
    have e4 : N - N / 16 - m - 2 + N / 16 + T N ≤ 3 * X := by omega
    have e5 : c + m + (N - N / 16 - m - 2) + N / 16 + T N ≤ (c + m + 3) * X := by nlinarith
    have e6 : 11 ≤ 11 * X ^ (d + 1) := by omega
    calc c + m + (N - N / 16 - m - 2) + N / 16 + T N + (K * (c + 3 * X) ^ d + 1 + C0 * X) + 10
        ≤ (c + m + 3) * X ^ (d + 1) + K * (c + 3) ^ d * X ^ (d + 1) + 11 * X ^ (d + 1) + C0 * X ^ (d + 1) := by
          omega
      _ ≤ A * X ^ (d + 1) := by rw [hA]; nlinarith
  have hpow : X ^ 2 ≤ X ^ (2 * d + 2) := Nat.pow_le_pow_right hX1 (by omega)
  have hsq : (A * X ^ (d + 1)) ^ 2 = A ^ 2 * X ^ (2 * d + 2) := by ring
  constructor
  · -- INIT
    obtain ⟨cap, τ, hex, hrep⟩ := hIM N hN1 (Lc N) (by simp only [Lc]; omega)
    have hex' := WXExec.mono hex (show CI * X ^ 2 ≤ (CI + (f.program.tapeCount + 3) * 2000 * A ^ 2) * X ^ (2 * d + 2) by
      calc CI * X ^ 2 ≤ CI * X ^ (2 * d + 2) := Nat.mul_le_mul_left _ hpow
        _ ≤ _ := Nat.mul_le_mul_right _ (by omega))
    obtain ⟨b, hb, hpb⟩ := Mach.ready_parked hex' ⟨fun _ => rfl, fun _ => rfl, rfl⟩
      ⟨hrep.sh, hrep.val, hrep.cell⟩ (Ex f) _ (parked_input f (pairInput M N) (Lc N))
    exact ⟨b, hb, τ, hpb, hrep⟩
  · -- STEP
    intro S β a ⟨σ, hpk, hrep⟩ hgood
    have hLc : ∀ S', Range (2 ^ (N / 16)) S' → budget (stateRequest M T N S') + 1 ≤ Lc N := by
      intro S' hR
      have hmeas := stateRequest_measure M T hT.1 N S' hR
      have h1 := hbud (stateRequest M T N S')
      have hmono : (stateRequest M T N S').measure ^ d ≤ (c + 3 * X) ^ d := Nat.pow_le_pow_left hmeas d
      have h2 : K * (stateRequest M T N S').measure ^ d ≤ K * (c + 3 * X) ^ d := Nat.mul_le_mul_left _ hmono
      simp only [Lc]; rw [← hX]; omega
    obtain ⟨τ, hex, hW⟩ := step_spec (40 * (A * X ^ (d + 1))) f M T N (dat M T N).code (dat M T N).mi
      (dat M T N).xr (dat M T N).g (dat M T N).TN (Lc N) rfl rfl rfl rfl rfl hg1 hrec hLc (by omega) S β σ hrep hgood
    have hcost : (f.program.tapeCount + 3) * 2000 * ((dat M T N).code.length + (dat M T N).mi + (dat M T N).xr +
        (dat M T N).g + (dat M T N).TN + Lc N + 10) ^ 2 ≤
        (CI + (f.program.tapeCount + 3) * 2000 * A ^ 2) * X ^ (2 * d + 2) := by
      calc _ ≤ (f.program.tapeCount + 3) * 2000 * (A * X ^ (d + 1)) ^ 2 :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hsize 2)
        _ = (f.program.tapeCount + 3) * 2000 * A ^ 2 * X ^ (2 * d + 2) := by rw [hsq]; ring
        _ ≤ _ := Nat.mul_le_mul_right _ (by omega)
    have hRσ : Mach.Rest σ := ⟨hrep.sh, hrep.val, hrep.cell⟩
    have hW' : StepW f M T N (dat M T N).code (dat M T N).mi (dat M T N).xr (dat M T N).g (dat M T N).TN (Lc N) τ
        (round (2 ^ (N / 16)) (N / 16 + 1) S β) := hW
    clear hW
    cases hr : round (2 ^ (N / 16)) (N / 16 + 1) S β with
    | inr p =>
      rw [hr] at hW'
      obtain ⟨hD, hO, hsh, hv, hcl⟩ := hW'
      obtain ⟨b, hb, hpb⟩ := Mach.ready_parked (hex.mono hcost) hRσ ⟨hsh, hv, hcl⟩ (Ex f) a hpk
      refine ⟨b, hb, ?_⟩
      exact ⟨by rw [hpb.read0 sDONE, hD]; rfl, by
        show b (sTape sOUT) = _
        rw [hpb.exact sOUT (Or.inl rfl), hO]⟩
    | inl S' =>
      rw [hr] at hW'
      obtain ⟨hD, ⟨pad, hq⟩, hsh, hv, hcl, ⟨b0, hb0⟩, hGb, hTLb, hCb, hnext⟩ := hW'
      obtain ⟨b, hb, hpb⟩ := Mach.ready_parked (hex.mono hcost) hRσ ⟨hsh, hv, hcl⟩ (Ex f) a hpk
      refine ⟨b, hb, ?_⟩
      refine ⟨by rw [hpb.read0 sDONE, hD]; rfl, ⟨pad, by
        show b (sTape (qo (tT := tT) f)) = _
        rw [hpb.exact _ (Or.inr (Or.inr rfl)), hq]⟩, fun β' => ⟨reset f τ β', ?_, hnext β'⟩⟩
      have h1 := Mach.Parked.answer hpb sANS (Or.inr (Or.inl rfl)) β'
      rw [hb0] at h1
      have hw1 : writeTapeBit [b0] 0 β' = [β'] := rfl
      rw [hw1] at h1
      refine Parked.of_rd f h1 (fun i => ?_) (fun i hi => ?_)
      · by_cases hi : i = sANS
        · subst hi; simp [reset]; exact RdEq.refl _
        · simp only [reset, hi, if_false, WState.sets_st, Function.update_of_ne hi]
          split_ifs with h
          · rcases h with rfl | rfl | ⟨j, hj, rfl⟩
            · exact rdEq_nil_of_blank _ hGb
            · exact rdEq_nil_of_blank _ hTLb
            · exact rdEq_nil_of_blank _ (hCb j hj)
          · exact RdEq.refl _
      · rcases hi with rfl | rfl | rfl
        · have h2 : (sOUT : Fin (NS f.program.tapeCount tT + 1)) ≠ sANS := by ds
          have h3 : ¬ ((sOUT : Fin (NS f.program.tapeCount tT + 1)) = sG ∨
              (sOUT : Fin (NS f.program.tapeCount tT + 1)) = sTL ∨
              ∃ j, j ≠ f.program.outputTape ∧ sC j = (sOUT : Fin (NS f.program.tapeCount tT + 1))) := by
            rintro (h | h | ⟨j, -, h⟩)
            · exact absurd h (by ds)
            · exact absurd h (by ds)
            · exact absurd h (sC_ne _ _ (by simp)).symm
          simp only [reset, h2, h3, if_false, WState.sets_st, Function.update_of_ne h2]
        · simp [reset]
        · have h2 : (qo (tT := tT) f) ≠ sANS := (sC_ne _ _ (by simp)).symm
          have h3 : ¬ ((qo (tT := tT) f) = sG ∨ qo (tT := tT) f = sTL ∨
              ∃ j, j ≠ f.program.outputTape ∧ sC j = qo (tT := tT) f) := by
            rintro (h | h | ⟨j, hj, h⟩)
            · exact absurd h (sC_ne _ _ (by simp)).symm
            · exact absurd h (sC_ne _ _ (by simp)).symm
            · exact hj (sC_inj h)
          simp only [reset, h2, h3, if_false, WState.sets_st, Function.update_of_ne h2]

/-- **The loader contract** (the input to `MachinesFromCompiler T`): for every compiler of join X5(b),
some clock-tape count and an INIT word program satisfying `InitOK`. -/
def LoaderExists (T : ℕ → ℕ) : Prop :=
  ∀ (K d : ℕ) (query : CNFCompilationRequest → ℕ)
    (f : WordFunction CNFCompilationRequest CNFCompilationRequest.word
      (fun r => RepairOrdinary.frame (query r).bits) (fun r => K * r.measure ^ d)),
    ∃ (tT : ℕ) (initP : WMX (NS f.program.tapeCount tT) NR), InitOK (tT := tT) f T initP

/-- **`MachinesFromCompiler T` from the loader.** -/
theorem machinesFromCompiler_of_loader (T : ℕ → ℕ) (hT : InClockRange T) (h : LoaderExists T) :
    MachinesFromCompiler T := fun K d query f => by
  obtain ⟨tT, initP, hi⟩ := h K d query f
  exact machines_of_init (tT := tT) f T hT K d (fun _ => le_rfl) initP hi

/-- **`RefuterRealization T`, every admissible clock, from the `ComputationToCNF` interface and the loader.** -/
theorem refuterRealization_of_loader (h : ComputationToCNF)
    (hl : ∀ T : ℕ → ℕ, TimeConstructible T → InClockRange T → LoaderExists T) :
    ∀ T : ℕ → ℕ, TimeConstructible T → InClockRange T → RefuterRealization T :=
  refuterRealization_all h (fun T hTc hTr => machinesFromCompiler_of_loader T hTr (hl T hTc hTr))

end NearCubicGates.Adapters.Refuter.RM
