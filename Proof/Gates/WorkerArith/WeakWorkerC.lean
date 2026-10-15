import Proof.Gates.WorkerArith.WeakWorkerB

/-!
# WeakWorker, part C: one run of the worker program on every input

From the cold start the worker program halts within `F N + 40` with the result cell
`[N₀ ≤ N] && verdict` (`Worker.verdict`: the oracle field decodes and the decoded guess passes the test).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.WorkerArith.WeakWorker

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.SourceInterfaces NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutLanguage
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicWires.RepairOrdinary.Streaming NearCubicWires.RepairOrdinary.RadixSemantics
open NearCubicWires.CanonicalWitnessCodec NearCubicWires.Bindings.CLW20Lemma311
open NearCubicGates.PublishedSources.PCPP NearCubicGates.Close.Gadget NearCubicGates.Close.Transfer
open NearCubicGates.Close NearCubicGates.Close.WordPrograms NearCubicGates.Close.CheckedPCPP NearCubicGates.Close.Interfaces
open NearCubicGates.Close.Setup NearCubicGates.Close.TermLoop
open NearCubicGates.Close.Worker (width pcpp gadgets)

variable {s : GateSources} {P : ThreeQueryPCPP} {g : GateParams} (D : SetupData s P g)

/-- The oracle flag at loop entry. -/
theorem entry_flag {N : ℕ} (x : BitInput N) (bits : List Bool) (pad : ℕ) (B : Outer.OuterGuess (width s g N))
    (jk : Fin (nsW D + 1) → List Bool) :
    (LoopEntry D N x bits pad B jk).st (sFL D) = [true] ∧ (LoopEntry D N x bits pad B jk).sh (sFL D) = 0 := by
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8⟩ := named_vals D
  have w1 := D.cf.wOut.isLt
  have w2 := D.cf.sOut.isLt
  have w3 : D.flag.val < D.tA := D.flag.isLt
  have ne : ∀ i : Fin (nsW D + 1), i.val ≠ (sFL D).val → sFL D ≠ i := fun i h e => h (by rw [e])
  have n1 := ne (sX D) (by omega)
  have n2 := ne (sBW D) (by omega)
  have n3 := ne (sWT D) (by omega)
  have n4 := ne (sCW D) (by omega)
  have n5 := ne (sVI D) (by omega)
  have n6 := ne (sJ D) (by omega)
  have n7 := ne (sSUP D) (by omega)
  constructor
  · simp only [LoopEntry]
    rw [if_neg n1, if_neg n2, if_neg n3, if_neg n4, if_neg n5, if_neg n6, if_neg n7, if_pos trivial]
  · simp only [LoopEntry]
    rw [if_neg n3, if_neg n5]

/-- The result cell of a run. -/
theorem worker_exec {B1 B2 : ℕ} (ctr : Counter B1 B2) (hD : Counter.DenOK ctr) (budget : ℕ → ℕ) (εT ω : ℚ)
    (setup : WMX (nsW D) nrW) (hct : ctr.program.program.tapeCount = D.tc)
    (vm : Worker.VerdictMachine P.gamma εT) (vmap : Fin vm.wf.program.tapeCount → Fin (nsW D + 1))
    (padF F : ℕ → ℕ)
    (hsetup : SetupSpec D setup) (hloop : TermLoopIdeal D ctr hct ω) (hexit : LoopExitVI D ctr ω hD)
    (hinj : Function.Injective vmap) (hin : vmap (inTape vm.wf.program) = sVI D) (hL : ∀ j, vmap j ≠ sL D)
    (hbl : ∀ j, j ≠ inTape vm.wf.program → BlankAtExit D (vmap j))
    (hpad : ∀ N, N / 16 + 1 ≤ padF N)
    (hacc : ∀ N (x : BitInput N) (bits : List Bool) (Bo : Outer.OuterGuess (width s g N)), D.N0 ≤ N →
      Worker.Decodes (width s g N) (guessWord N bits (padF N)) Bo →
      ∃ cap Z Bc V, LoopFit (P := P) ctr ω x bits (padF N) Bo cap Z Bc V ∧ capA D N (padF N) ≤ cap ∧
        setupCap D x bits (padF N) Bo ≤ cap ∧
        2 * (Worker.verdictWord ((theGuess s P g x bits (padF N)).verdictReq P x ctr hD ω)).length + 2 ≤ cap ∧
        setupCost D x bits (padF N) Bo +
          loopCost D.tc Z Bc (frontSize s P g x Bo) (gadgets s g N) (loopBud s P g x bits (padF N) Bo ctr ω) +
          2 * vm.budget ((theGuess s P g x bits (padF N)).verdictReq P x ctr hD ω) +
          12 * (Worker.verdictWord ((theGuess s P g x bits (padF N)).verdictReq P x ctr hD ω)).length + 100 ≤ F N)
    (hrej : ∀ N (x : BitInput N) (bits : List Bool), rejectCost D x bits (padF N) + 10 ≤ F N)
    (N : ℕ) (x : BitInput N) (bits : List Bool) :
    ∃ cap τ n, WXExec cap (workerW D setup (termLoopW D ctr hct ω) vm vmap) (coldState D (List.ofFn x) bits) τ n ∧
      n ≤ F N + 40 ∧
      τ.cell = (decide (D.N0 ≤ N) && Worker.verdict s P g ctr budget εT ω N x (guessWord N bits (padF N))) := by
  classical
  set w := guessWord N bits (padF N) with hw
  by_cases hacc' : D.N0 ≤ N ∧ Worker.setupFlag s P g N x w = true
  · -- both circuit fields decode and the set-up's guards hold: set-up, loop, tail
    obtain ⟨hN0, hsf⟩ := hacc'
    have hsf' := hsf
    unfold Worker.setupFlag at hsf'
    rw [Bool.and_eq_true, decide_eq_true_iff] at hsf'
    obtain ⟨Bo, hBo⟩ := Worker.exists_decodes_of_oracleOK s g hsf'.1
    have hpair : Worker.PairOK s g x Bo := by
      have h := hsf'.2
      unfold Worker.Guess.SetupOK at h
      rwa [Worker.decodeGuess_oracle_eq s P g N x w Bo hBo] at h
    obtain ⟨cap, Z, Bc, V, hfit, hcA, hcS, hcV, hcost⟩ := hacc N x bits Bo hN0 hBo
    obtain ⟨jk, τ1, e1, s1⟩ := (hsetup N x bits (padF N) cap (hpad N) hcA).1 Bo hN0 hBo hpair hcS
    have hfl : wbit τ1 (sFL D) = true := by
      obtain ⟨f1, f2⟩ := entry_flag D x bits (padF N) Bo jk
      unfold wbit
      rw [s1.sh, f2, ← s1.st (sFL D) 0, f1]; rfl
    obtain ⟨τ2, e2, s2⟩ := hloop x bits (padF N) Bo jk cap Z Bc V hfit τ1 s1
    set req := (theGuess s P g x bits (padF N)).verdictReq P x ctr hD ω with hreq
    obtain ⟨τ3, e3, h3⟩ := tail_run D vm vmap hinj hin hL hbl ctr ω x bits (padF N) Bo jk req
      (hexit x bits (padF N) Bo jk hBo) cap hcV τ2 s2
    refine ⟨cap, τ3, _, WXExec.seq e1 (WXExec.ifsT hfl (WXExec.seq e2 e3)), by omega, ?_⟩
    rw [h3, Worker.verdict_eq_bit s P g ctr hD budget εT ω N x w, hsf]
    simp [hN0, hreq, theGuess, hw]
  · -- reject
    have hrej' : N < D.N0 ∨ Worker.setupFlag s P g N x w = false := by
      by_cases h : D.N0 ≤ N
      · right; cases hb : Worker.setupFlag s P g N x w
        · rfl
        · exact absurd ⟨h, hb⟩ hacc'
      · left; omega
    obtain ⟨τ1, e1, hf1, hc1⟩ := (hsetup N x bits (padF N) (capA D N (padF N)) (hpad N) le_rfl).2 hrej'
    refine ⟨capA D N (padF N), τ1, _, WXExec.seq e1 (WXExec.ifsF hf1 (WXExec.wm (WExec.skip τ1))), ?_, ?_⟩
    · have := hrej N x bits; omega
    · rw [hc1]
      by_cases h : D.N0 ≤ N
      · have hok : Worker.setupFlag s P g N x w = false := by
          rcases hrej' with h' | h'
          · omega
          · exact h'
        unfold Worker.verdict
        simp [hok]
      · simp [h]

end NearCubicGates.Close.WorkerArith.WeakWorker
