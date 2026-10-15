import Proof.Gates.WorkerArith.WeakWorker
import Proof.Gates.WorkerArith.VerdictMain
import Proof.Gates.TermLoop.Final
import Proof.Gates.Setup.UniformSpec
import Proof.Gates.Counter.OutOK
import Proof.Gates.WorkerArith.VerdictMap

set_option autoImplicit false

namespace NearCubicGates.Close.WorkerArith

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.SourceInterfaces NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutLanguage
open NearCubicWires.RepairOrdinary.Streaming NearCubicWires.RepairOrdinary.RadixSemantics
open NearCubicWires.CanonicalWitnessCodec NearCubicWires.Bindings.CLW20Lemma311
open NearCubicGates.PublishedSources.PCPP NearCubicGates.Close.Gadget NearCubicGates.Close.Transfer
open NearCubicGates.Close NearCubicGates.Close.WordPrograms NearCubicGates.Close.CheckedPCPP NearCubicGates.Close.Interfaces
open NearCubicGates.Close.Setup NearCubicGates.Close.TermLoop NearCubicGates.Close.WorkerArith.WeakWorker
open NearCubicGates.Close.Worker (width pcpp gadgets)

noncomputable section

def VmapFacts {s : GateSources} {P : ThreeQueryPCPP} {g : GateParams} (D : SetupData s P g) {γ εT : ℚ}
    (vm : Worker.VerdictMachine γ εT) : Prop :=
  ∃ vmap : Fin vm.wf.program.tapeCount → Fin (nsW D + 1),
    Function.Injective vmap ∧ vmap (inTape vm.wf.program) = sVI D ∧ (∀ j, vmap j ≠ sL D) ∧
      (∀ j, j ≠ inTape vm.wf.program → BlankAtExit D (vmap j))

theorem vmapFacts {s : GateSources} {P : ThreeQueryPCPP} {g : GateParams} (D : SetupData s P g) (γ εT : ℚ) :
    VmapFacts D (verdictMachine γ εT) :=
  ⟨_, WorkerBounds.vmap_ok D (verdictMachine γ εT) (WorkerBounds.verdict_room D γ εT)⟩

/-- What `WeakWorker.WeakWorkerOf` asks beyond the machines: the padding, the fuel with its per-run fits, the guess envelope and
the runtime split (paper v2 lines 2393–2407). -/
def WeakWorkerRest (s : GateSources) (P : ThreeQueryPCPP) (g : GateParams) {B1 B2 : ℕ} (ctr : Counter B1 B2)
    (hD : Counter.DenOK ctr) (budget : ℕ → ℕ) (εT ω : ℚ) (D : SetupData s P g)
    (vm : Worker.VerdictMachine P.gamma εT) : Prop :=
  ∃ (padF F hot : ℕ → ℕ) (A B a sigma : ℕ),
    (∀ N, N / 16 + 1 ≤ padF N) ∧
    (∀ N (x : BitInput N) (bits : List Bool) (Bo : Outer.OuterGuess (width s g N)), D.N0 ≤ N →
      Worker.Decodes (width s g N) (guessWord N bits (padF N)) Bo →
      ∃ cap Z Bc V, LoopFit (P := P) ctr ω x bits (padF N) Bo cap Z Bc V ∧ capA D N (padF N) ≤ cap ∧
        setupCap D x bits (padF N) Bo ≤ cap ∧
        2 * (Worker.verdictWord ((theGuess s P g x bits (padF N)).verdictReq P x ctr hD ω)).length + 2 ≤ cap ∧
        setupCost D x bits (padF N) Bo +
          loopCost D.tc Z Bc (frontSize s P g x Bo) (gadgets s g N) (loopBud s P g x bits (padF N) Bo ctr ω) +
          2 * vm.budget ((theGuess s P g x bits (padF N)).verdictReq P x ctr hD ω) +
          12 * (Worker.verdictWord ((theGuess s P g x bits (padF N)).verdictReq P x ctr hD ω)).length + 100 ≤ F N) ∧
    (∀ N (x : BitInput N) (bits : List Bool), rejectCost D x bits (padF N) + 10 ≤ F N) ∧
    (∃ onset, ∀ N, onset ≤ N → ∀ (x : BitInput N) (G : Worker.Guess (width s g N)), G.SizeOK P x ctr budget →
      (Worker.encodeGuess s P g x G).length ≤ N / 16 ∧
        ∀ j < G.auxCount P x, (G.circuits j).coeffs.length = (G.circuits j).gates.length) ∧
    a ≤ g.k + 1 ∧ Outer.apad s.mw (g.sv s) + 1 ≤ sigma ∧
    (∃ onset, ∀ N, onset ≤ N → F N + 40 + 2 ≤ A * (N + 1) ^ a + hot N) ∧
    (∃ onset, ∀ N, onset ≤ N →
      hot N * (width s g N) ^ sigma ≤ B * 2 ^ (width s g N))

theorem workerSupply_of
    (hrest : ∀ (s : GateSources) (P : ThreeQueryPCPP) (B1 B2 : ℕ) (ctr : Counter B1 B2) (η εT ω : ℚ)
      (hD : Counter.DenOK ctr), Counter.OutOK ctr → 0 < η → 0 < ω →
      ∃ d0 : ℕ, ∀ g : GateParams, d0 ≤ g.k + 1 →
        ∃ D : SetupData s P g, (∃ prog : WMX (nsW D) nrW, SetupSpec D prog) ∧
          ctr.program.program.tapeCount = D.tc ∧
          VmapFacts D (verdictMachine P.gamma εT) ∧
          WeakWorkerRest s P g ctr hD (Closure.budgetOf η) εT ω D (verdictMachine P.gamma εT)) :
    Closure.WorkerSupply := by
  intro s P B1 B2 ctr η εT ω hD hO hη hω
  obtain ⟨d0, hd0⟩ := hrest s P B1 B2 ctr η εT ω hD hO hη hω
  refine ⟨d0, fun g hg => ?_⟩
  obtain ⟨D, ⟨prog, hprog⟩, hct, ⟨vmap, hinj, hin, hL, hbl⟩, padF, F, hot, A, B, a, sigma, hpad, hacc, hrej, henv, ha,
    hsig, hsplitF, hhot⟩ := hd0 g hg
  exact WeakWorker_of s P g ctr hD (Closure.budgetOf η) εT ω D prog hct (verdictMachine P.gamma εT) vmap padF F hot
    A B a sigma hprog (termLoop_ideal D ctr hct ω) (loopExit_vi D ctr ω hD) hinj hin hL hbl hpad hacc
    hrej henv ha hsig hsplitF hhot

end

end NearCubicGates.Close.WorkerArith
