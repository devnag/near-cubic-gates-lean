import Proof.Gates.WorkerArith.WeakWorkerC

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

/-- The honest witness word: the encoding, then blanks up to `⌊N/16⌋` bits. -/
theorem honest_word (enc : List Bool) (m pad : ℕ) (hm : enc.length ≤ m) :
    Codec.prefixBits (List.ofFn fun i : Fin m => enc.getD i.val false) m ++ List.replicate pad false =
      enc ++ (List.replicate (m - enc.length) false ++ List.replicate pad false) := by
  have h1 : Codec.prefixBits (List.ofFn fun i : Fin m => enc.getD i.val false) m =
      List.ofFn fun i : Fin m => enc.getD i.val false := by
    unfold Codec.prefixBits
    congr 1; funext i
    simp [List.getD_eq_getElem?_getD, i.isLt]
  have h2 : (List.ofFn fun i : Fin m => enc.getD i.val false) = enc ++ List.replicate (m - enc.length) false := by
    apply List.ext_getElem (by simp; omega)
    intro i hi1 hi2
    simp only [List.getElem_ofFn]
    by_cases h : i < enc.length
    · rw [List.getElem_append_left h]; simp [List.getD_eq_getElem?_getD, h]
    · rw [List.getElem_append_right (by omega)]; simp [List.getD_eq_getElem?_getD, h]
  rw [h1, h2, List.append_assoc]

/-- **WeakWorker.** -/
theorem WeakWorker_of (s : GateSources) (P : ThreeQueryPCPP) (g : GateParams) {B1 B2 : ℕ} (ctr : Counter B1 B2)
    (hD : Counter.DenOK ctr) (budget : ℕ → ℕ) (εT ω : ℚ) : WeakWorkerOf s P g ctr hD budget εT ω := by
  intro D setup hct vm vmap padF F hot A B a sigma hsetup hloop hexit hinj hin hL hbl hpad hacc hrej henv ha hsig
    hsplitF hhot
  set prog := workerW D setup (termLoopW D ctr hct ω) vm vmap with hprog
  set M := workerMachine D setup (termLoopW D ctr hct ω) vm vmap with hM
  have hrun : ∀ N (x : BitInput N) (bits : List Bool), ∃ r, run M (F N + 40)
      ((UAcceptanceCarrier.verifier M (two_le_wTapes D) (wResult D)).inputTapes (List.ofFn x) bits) = some r ∧
      r.final.scanned (wResult D) =
        (decide (D.N0 ≤ N) && Worker.verdict s P g ctr budget εT ω N x (guessWord N bits (padF N))) := by
    intro N x bits
    obtain ⟨cap, τ, n, e, hn, hc⟩ := worker_exec D ctr hD budget εT ω setup hct vm vmap padF F hsetup hloop hexit hinj
      hin hL hbl hpad hacc hrej N x bits
    obtain ⟨r, hr, hsc⟩ := worker_run D prog cap n (F N + 40) (List.ofFn x) bits τ e hn
    exact ⟨r, hr, hsc.trans hc⟩
  refine ⟨⟨wTapes D, prog.size, M, two_le_wTapes D, wResult D, fun N => F N + 40, ?_, ?_, ?_, A, B, a, sigma, hot,
    ha, hsig, ?_⟩⟩
  · intro N x bits
    obtain ⟨r, hr, _⟩ := hrun N x bits
    exact ⟨r, hr⟩
  · intro N x bits hdec
    obtain ⟨r, hr, hsc⟩ := hrun N x bits
    obtain ⟨act, hact, hs⟩ := hdec
    rw [hr, Option.some.injEq] at hact
    subst hact
    rw [hsc, Bool.and_eq_true] at hs
    exact Worker.verdict_sound s P g ctr budget εT ω N x _ hs.2
  · obtain ⟨on, hon⟩ := henv
    refine ⟨max on D.N0, fun N hN x G hsz hcert => ?_⟩
    obtain ⟨hlen, hC⟩ := hon N (le_trans (le_max_left _ _) hN) x G hsz
    set enc := Worker.encodeGuess s P g x G with henc
    refine ⟨fun i => enc.getD i.val false, ?_⟩
    obtain ⟨r, hr, hsc⟩ := hrun N x (List.ofFn fun i : Fin (N / 16) => enc.getD i.val false)
    refine ⟨r, hr, ?_⟩
    rw [hsc]
    have hw : guessWord N (List.ofFn fun i : Fin (N / 16) => enc.getD i.val false) (padF N) =
        enc ++ (List.replicate (N / 16 - enc.length) false ++ List.replicate (padF N) false) := by
      unfold guessWord; exact honest_word enc (N / 16) (padF N) hlen
    rw [hw, Worker.verdict_encode s P g ctr budget εT ω x G hC hcert]
    simp [le_trans (le_max_right _ _) hN]
  · exact split_of (fun N => F N + 40) hot (fun N => width s g N) A a B sigma hsplitF hhot

end NearCubicGates.Close.WorkerArith.WeakWorker
