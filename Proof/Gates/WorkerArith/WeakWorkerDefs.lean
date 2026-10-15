import Proof.Gates.TermLoop.Defs
import Proof.Gates.Closure.Obligations
import Proof.Gates.WorkerArith.RuntimeSplit
import Proof.Gates.WorkerArith.CtrCall

set_option autoImplicit false

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

noncomputable section

variable {ns nr : ℕ}

/-- Read the verdict bit (`bitWord b = natWord b`: the bit sits at position `2`) into the result cell. -/
def resultW (o : Fin (ns + 1)) : WM ns nr := .seq (.fwd o) (.seq (.fwd o) (.ifs o (.setc true) (.setc false)))

section Prog
variable {s : GateSources} {P : ThreeQueryPCPP} {g : GateParams} (D : SetupData s P g) {γ εT : ℚ}

def tailW (vm : Worker.VerdictMachine γ εT) (vmap : Fin vm.wf.program.tapeCount → Fin (nsW D + 1)) :
    WMX (nsW D) nrW :=
  .seq (.wm (WM.rewind (sVI D) (regE 9))) (.seq (WMX.machZ vm.wf.program.machine vmap (sL D))
    (.wm (resultW (vmap vm.wf.program.outputTape))))

/-- **The worker program.** -/
def workerW (setup loop : WMX (nsW D) nrW) (vm : Worker.VerdictMachine γ εT)
    (vmap : Fin vm.wf.program.tapeCount → Fin (nsW D + 1)) : WMX (nsW D) nrW :=
  .seq setup (.ifs (sFL D) (.seq loop (tailW D vm vmap)) (.wm .skip))

/-- The worker's tape count. -/
abbrev wTapes : ℕ := nsW D + 2 + nrW

theorem three_le : 3 ≤ wTapes D := by unfold wTapes nsW; omega

def tSwap : Fin (wTapes D) ≃ Fin (wTapes D) :=
  Equiv.swap ⟨1, by have := three_le D; omega⟩ ⟨2, by have := three_le D; omega⟩

/-- **The worker machine.** -/
def workerMachine (setup loop : WMX (nsW D) nrW) (vm : Worker.VerdictMachine γ εT)
    (vmap : Fin vm.wf.program.tapeCount → Fin (nsW D + 1)) :
    Machine (wTapes D) (workerW D setup loop vm vmap).size :=
  TapeRenaming.machine (tSwap D) (workerW D setup loop vm vmap).compile

/-- The result tape (the renamed cell). -/
def wResult : Fin (wTapes D) := ⟨2, by have := three_le D; omega⟩

/-- The streams that read blank, head `0`, at the loop exit (the spare streams `5 … 15` but the log, and the counter
block): room for the verdict machine's work tapes. -/
def BlankAtExit (i : Fin (nsW D + 1)) : Prop :=
  (5 ≤ i.val ∧ i.val < 16 ∧ i ≠ sL D) ∨ 16 + D.tA + D.cf.t ≤ i.val

end Prog

/-! ## The statement -/

def WeakWorkerOf (s : GateSources) (P : ThreeQueryPCPP) (g : GateParams) {B1 B2 : ℕ} (ctr : Counter B1 B2)
    (hD : Counter.DenOK ctr) (budget : ℕ → ℕ) (εT ω : ℚ) : Prop :=
  ∀ (D : SetupData s P g) (setup : WMX (nsW D) nrW) (hct : ctr.program.program.tapeCount = D.tc)
    (vm : Worker.VerdictMachine P.gamma εT) (vmap : Fin vm.wf.program.tapeCount → Fin (nsW D + 1))
    (padF F hot : ℕ → ℕ) (A B a sigma : ℕ),
    SetupSpec D setup → TermLoopIdeal D ctr hct ω → LoopExitVI D ctr ω hD →
    Function.Injective vmap → vmap (inTape vm.wf.program) = sVI D → (∀ j, vmap j ≠ sL D) →
    (∀ j, j ≠ inTape vm.wf.program → BlankAtExit D (vmap j)) →
    (∀ N, N / 16 + 1 ≤ padF N) →
    (∀ N (x : BitInput N) (bits : List Bool) (Bo : Outer.OuterGuess (width s g N)), D.N0 ≤ N →
      Worker.Decodes (width s g N) (guessWord N bits (padF N)) Bo →
      ∃ cap Z Bc V, LoopFit (P := P) ctr ω x bits (padF N) Bo cap Z Bc V ∧ capA D N (padF N) ≤ cap ∧
        setupCap D x bits (padF N) Bo ≤ cap ∧
        2 * (Worker.verdictWord ((theGuess s P g x bits (padF N)).verdictReq P x ctr hD ω)).length + 2 ≤ cap ∧
        setupCost D x bits (padF N) Bo +
          loopCost D.tc Z Bc (frontSize s P g x Bo) (gadgets s g N) (loopBud s P g x bits (padF N) Bo ctr ω) +
          2 * vm.budget ((theGuess s P g x bits (padF N)).verdictReq P x ctr hD ω) +
          12 * (Worker.verdictWord ((theGuess s P g x bits (padF N)).verdictReq P x ctr hD ω)).length + 100 ≤ F N) →
    (∀ N (x : BitInput N) (bits : List Bool), rejectCost D x bits (padF N) + 10 ≤ F N) →
    (∃ onset, ∀ N, onset ≤ N → ∀ (x : BitInput N) (G : Worker.Guess (width s g N)), G.SizeOK P x ctr budget →
      (Worker.encodeGuess s P g x G).length ≤ N / 16 ∧
        ∀ j < G.auxCount P x, (G.circuits j).coeffs.length = (G.circuits j).gates.length) →
    a ≤ g.k + 1 → Outer.apad s.mw (g.sv s) + 1 ≤ sigma →
    (∃ onset, ∀ N, onset ≤ N → F N + 40 + 2 ≤ A * (N + 1) ^ a + hot N) →
    (∃ onset, ∀ N, onset ≤ N →
      hot N * (width s g N) ^ sigma ≤ B * 2 ^ (width s g N)) →
    Nonempty (Closure.WorkerMachine s P g ctr budget εT ω)

end

end NearCubicGates.Close.WorkerArith.WeakWorker
