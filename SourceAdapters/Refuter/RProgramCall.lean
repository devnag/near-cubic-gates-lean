import Proof.Gates.WorkerArith.CtrCallC
import Proof.MachineModel.OrdinaryZeroPadding
import SourceAdapters.Refuter.RProgramWMX

/-!
# A reusable clocked call of a word function on blank-padded streams (input 7, R: the compiler call)

Paper anchor: proof of `lem:multitape-refuter` (each query of `R_T` is produced by ONE compiler — join X5(b)
`ComputationToCNF`, an ordinary `WordFunction` — and written in full) and proof of `lem:multitape-refuter`
(`O(N)` adaptive queries, so the same compiler runs `O(N)` times on the same tapes).

L's `WorkerArith.clockDock` runs a word function inside a word program (`WMX.machZ` of
`clockMachine`, heads restored to `0`, a unary clock of the steps left on stream `TL`) but only from
EXACTLY empty work streams. After the first query the compiler's streams hold blanks of unknown
length, so R needs the padded form, `clockDock_padded`: every stream may carry any number of trailing
blank cells (`ZeroPadding.pad`). The run is the same (`ZeroPadding.run_config`), and every output
stream is EXACTLY the word function's tape padded with blanks; in particular the output stream is
`frame bits ++ blanks` whenever the function's output is `frame bits`, which is literally the query
tape form the oracle step requires (`Statement.lean` §14, `OrdinaryOracleStep.ask`).
-/

namespace NearCubicGates.Adapters.Refuter.Mach

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.OrdinaryOracleCompose

set_option autoImplicit false
set_option linter.unusedSimpArgs false

variable {ns nr : ℕ}

/-- **The padded clocked call.** Work streams hold the word function's initial tapes padded with
`z j` blanks, the clock stream `TL` holds `zT` blanks, the log `L` at least `budget` blanks. The call
leaves each work stream as the function's final tape padded with `z j` blanks, `TL` as the unary step
count padded with `zT` blanks, every touched head at `0`, and everything else unchanged. -/
theorem clockDock_padded {Request : Type} {input output : Request → List Bool} {budget : Request → ℕ}
    (f : WordFunction Request input output budget) (req : Request) (cap : ℕ)
    (tmap : Fin f.program.tapeCount → Fin (ns + 1)) (hinj : Function.Injective tmap) (TL L : Fin (ns + 1))
    (hTL : ∀ j, tmap j ≠ TL) (hL : ∀ j, tmap j ≠ L) (hTLL : TL ≠ L) (σ : WState ns nr)
    (z : Fin f.program.tapeCount → ℕ) (zT lcap : ℕ)
    (hin : ∀ j, σ.st (tmap j) = ZeroPadding.pad (z j) (f.program.inputTapes (input req) j))
    (hTLe : σ.st TL = List.replicate zT false)
    (h0 : ∀ j, σ.sh (tmap j) = 0) (hTLh : σ.sh TL = 0) (hLst : σ.st L = List.replicate lcap false)
    (hLsh : σ.sh L = 0) (hn : budget req ≤ lcap) :
    ∃ (receipt : ExecutionReceipt f.program.tapeCount f.program.stateCount) (τ : WState ns nr),
      run f.program.machine (budget req) (f.program.inputTapes (input req)) = some receipt ∧
      receipt.final.tapes f.program.outputTape = output req ∧ receipt.steps ≤ budget req ∧
      WXExec cap (WMX.machZ (clockMachine f.program.machine)
        (Fin.addCases (motive := fun _ => Fin (ns + 1)) tmap (fun _ : Fin 1 => TL)) L) σ τ (2 * budget req + 2) ∧
      (∀ j, τ.st (tmap j) = ZeroPadding.pad (z j) (receipt.final.tapes j)) ∧
      τ.st TL = ZeroPadding.pad zT (List.replicate receipt.steps true) ∧
      (∀ j, τ.sh (tmap j) = 0) ∧ τ.sh TL = 0 ∧
      (∀ i, (∀ j, tmap j ≠ i) → i ≠ TL → τ.st i = σ.st i ∧ τ.sh i = σ.sh i) ∧
      τ.val = σ.val ∧ τ.cell = σ.cell := by
  obtain ⟨receipt, hrun, hout⟩ := f.realizes req
  obtain ⟨r', hr', hfin, hst⟩ := NearCubicGates.Close.Worker.clock_runFrom f.program.machine (budget req)
    (initialConfiguration f.program.machine (f.program.inputTapes (input req))) 0 receipt hrun
  set caps : Fin (f.program.tapeCount + 1) → ℕ := Fin.addCases z (fun _ : Fin 1 => zT) with hcaps
  obtain ⟨r'', hr'', hfin'', hst'', _⟩ := ZeroPadding.run_config (clockMachine f.program.machine) caps
    (budget req) _ r' hr'
  set tmap' := Fin.addCases (motive := fun _ => Fin (ns + 1)) tmap (fun _ : Fin 1 => TL) with htm
  have hinj' := addCases_inj tmap hinj TL hTL
  have hL' : ∀ j, tmap' j ≠ L := by
    intro j; refine Fin.addCases (fun k => ?_) (fun k => ?_) j
    · simp only [htm, Fin.addCases_left]; exact hL k
    · simp only [htm, Fin.addCases_right]; exact hTLL
  have hcfg : (⟨(clockMachine f.program.machine).start, fun _ => 0, fun j => σ.st (tmap' j)⟩ :
      Configuration (f.program.tapeCount + 1) f.program.stateCount) =
      ZeroPadding.config caps
        (clockConfig (initialConfiguration f.program.machine (f.program.inputTapes (input req))) 0) := by
    apply configuration_ext
    · rfl
    · funext j; refine Fin.addCases (fun k => ?_) (fun k => ?_) j <;>
        simp [ZeroPadding.config, clockConfig, initialConfiguration]
    · funext j; refine Fin.addCases (fun k => ?_) (fun k => ?_) j
      · simp only [htm, hcaps, Fin.addCases_left, ZeroPadding.config, clockConfig, initialConfiguration]
        exact hin k
      · simp only [htm, hcaps, Fin.addCases_right, ZeroPadding.config, clockConfig, List.replicate_zero]
        rw [hTLe]; simp [ZeroPadding.pad]
  rw [← hcfg] at hr''
  have hStep : Step (clockMachine f.program.machine) (budget req) (fun _ => 0) (fun j => σ.st (tmap' j))
      r''.final.heads r''.final.tapes := Step.of_run (r := r'') hr'' rfl rfl
  obtain ⟨τ, e, hd⟩ := WXExec.machZ_ex cap hinj' hL' σ hStep (fun j => by
      refine Fin.addCases (fun k => ?_) (fun k => ?_) j
      · simp only [htm, Fin.addCases_left]; exact h0 k
      · simp only [htm, Fin.addCases_right]; exact hTLh) hLst hLsh hn
  have hsteps : receipt.steps ≤ budget req := runFrom_steps_le _ _ _ receipt hrun
  refine ⟨receipt, τ, hrun, hout, hsteps, e, fun j => ?_, ?_, fun j => ?_, ?_, fun i hi hiT => ?_, hd.val, hd.cell⟩
  · have := hd.st (Fin.castAdd 1 j)
    simp only [htm, Fin.addCases_left] at this
    rw [this, hfin'', hfin]; simp [clockConfig, ZeroPadding.config, hcaps]
  · have := hd.st (Fin.natAdd f.program.tapeCount 0)
    simp only [htm, Fin.addCases_right] at this
    rw [this, hfin'', hfin]; simp [clockConfig, ZeroPadding.config, hcaps]
  · have := hd.sh (Fin.castAdd 1 j)
    simp only [htm, Fin.addCases_left] at this
    exact this
  · have := hd.sh (Fin.natAdd f.program.tapeCount 0)
    simp only [htm, Fin.addCases_right] at this
    exact this
  · exact hd.other i (fun j => by
      refine Fin.addCases (fun k => ?_) (fun k => ?_) j
      · simp only [htm, Fin.addCases_left]; exact hi k
      · simp only [htm, Fin.addCases_right]; exact fun h => hiT h.symm)

/-- A padded framed word is the oracle's query-tape form `frame bits ++ padding`. -/
theorem pad_frame (z : ℕ) (bits : List Bool) :
    ZeroPadding.pad z (RepairOrdinary.frame bits) =
      RepairOrdinary.frame bits ++ List.replicate (z - (RepairOrdinary.frame bits).length) false := rfl

end NearCubicGates.Adapters.Refuter.Mach
