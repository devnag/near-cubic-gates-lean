import Proof.Gates.WorkerArith.CtrCallB

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicGates.Close.WorkerArith

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.CheckedPCPP NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairSource.OrdinaryOracleCompose

variable {ns nr : ℕ}

theorem writeTapeBit_len : ∀ (l : List Bool) (h : ℕ) (b : Bool), (writeTapeBit l h b).length = max l.length (h + 1)
  | [], 0, _ => rfl
  | [], h + 1, b => by
    simp only [writeTapeBit, List.length_cons, writeTapeBit_len [] h b, List.length_nil]; omega
  | _ :: _, 0, _ => by simp [writeTapeBit]
  | _ :: t, h + 1, b => by
    simp only [writeTapeBit, List.length_cons, writeTapeBit_len t h b]; omega

/-- A tape's length grows by at most one cell per step. -/
theorem runFrom_len {t s : ℕ} (M : Machine t s) (i : Fin t) :
    ∀ (fuel : ℕ) (c : Configuration t s) (B : ℕ) (r : ExecutionReceipt t s),
      runFrom M fuel c = some r → c.heads i ≤ B → (c.tapes i).length ≤ B + 1 →
      r.final.heads i ≤ B + r.steps ∧ (r.final.tapes i).length ≤ B + r.steps + 1
  | 0, c, B, r, hr, hh, hq => by
    simp only [runFrom] at hr
    split at hr
    · cases hr; exact ⟨by simpa using hh, by simpa using hq⟩
    · contradiction
  | fuel + 1, c, B, r, hr, hh, hq => by
    simp only [runFrom] at hr
    split at hr
    · cases hr; exact ⟨by simpa using hh, by simpa using hq⟩
    · cases hs : step M c with
      | none => simp [hs] at hr
      | some d =>
        cases ht : runFrom M fuel d with
        | none => simp [hs, ht] at hr
        | some tail =>
          simp only [hs, ht, Option.some.injEq] at hr
          subst hr
          unfold step at hs
          cases ha : M.rule c.control c.scanned with
          | none => simp [ha] at hs
          | some a =>
            simp only [ha, Option.map_some, Option.some.injEq] at hs
            subst hs
            have hdh : (applyAction c a).heads i ≤ B + 1 := by
              simp only [applyAction]
              cases a.move i <;> simp [HeadMove.apply] <;> omega
            have hdq : ((applyAction c a).tapes i).length ≤ B + 1 + 1 := by
              simp only [applyAction]
              cases a.write i with
              | none => simp; omega
              | some v => simp only; rw [writeTapeBit_len]; omega
            obtain ⟨h1, h2⟩ := runFrom_len M i fuel _ (B + 1) tail ht hdh hdq
            refine ⟨by simp only; omega, by simp only; omega⟩

theorem clockDock {Request : Type} {input output : Request → List Bool} {budget : Request → ℕ}
    (f : WordFunction Request input output budget) (req : Request) (cap : ℕ)
    (tmap : Fin f.program.tapeCount → Fin (ns + 1)) (hinj : Function.Injective tmap) (TL L : Fin (ns + 1))
    (hTL : ∀ j, tmap j ≠ TL) (hL : ∀ j, tmap j ≠ L) (hTLL : TL ≠ L) (σ : WState ns nr)
    (hin : ∀ j, σ.st (tmap j) = f.program.inputTapes (input req) j) (hTLe : σ.st TL = [])
    (h0 : ∀ j, σ.sh (tmap j) = 0) (hTLh : σ.sh TL = 0) (hLst : σ.st L = List.replicate (budget req) false)
    (hLsh : σ.sh L = 0) :
    ∃ (receipt : ExecutionReceipt f.program.tapeCount f.program.stateCount) (τ : WState ns nr),
      run f.program.machine (budget req) (f.program.inputTapes (input req)) = some receipt ∧
      receipt.final.tapes f.program.outputTape = output req ∧ receipt.steps ≤ budget req ∧
      WXExec cap (WMX.machZ (clockMachine f.program.machine)
        (Fin.addCases (motive := fun _ => Fin (ns + 1)) tmap (fun _ : Fin 1 => TL)) L) σ τ (2 * budget req + 2) ∧
      (∀ j, τ.st (tmap j) = receipt.final.tapes j) ∧ τ.st TL = List.replicate receipt.steps true ∧
      (∀ j, τ.sh (tmap j) = 0) ∧ τ.sh TL = 0 ∧
      (∀ i, (∀ j, tmap j ≠ i) → i ≠ TL → τ.st i = σ.st i ∧ τ.sh i = σ.sh i) ∧ τ.val = σ.val ∧ τ.cell = σ.cell := by
  obtain ⟨receipt, hrun, hout⟩ := f.realizes req
  obtain ⟨r', hr', hfin, hst⟩ := NearCubicGates.Close.Worker.clock_runFrom f.program.machine (budget req)
    (initialConfiguration f.program.machine (f.program.inputTapes (input req))) 0 receipt hrun
  set tmap' := Fin.addCases (motive := fun _ => Fin (ns + 1)) tmap (fun _ : Fin 1 => TL) with htm
  have hinj' := addCases_inj tmap hinj TL hTL
  have hL' : ∀ j, tmap' j ≠ L := by
    intro j; refine Fin.addCases (fun k => ?_) (fun k => ?_) j
    · simp only [htm, Fin.addCases_left]; exact hL k
    · simp only [htm, Fin.addCases_right]; exact hTLL
  have hcfg : (⟨(clockMachine f.program.machine).start, fun _ => 0, fun j => σ.st (tmap' j)⟩ :
      Configuration (f.program.tapeCount + 1) f.program.stateCount) =
      clockConfig (initialConfiguration f.program.machine (f.program.inputTapes (input req))) 0 := by
    apply configuration_ext
    · rfl
    · funext j; refine Fin.addCases (fun k => ?_) (fun k => ?_) j <;> simp [clockConfig, initialConfiguration]
    · funext j; refine Fin.addCases (fun k => ?_) (fun k => ?_) j
      · simp only [htm, Fin.addCases_left, clockConfig, initialConfiguration]; exact hin k
      · simp only [htm, Fin.addCases_right, clockConfig, List.replicate_zero]; exact hTLe
  rw [← hcfg] at hr'
  have hStep : Step (clockMachine f.program.machine) (budget req) (fun _ => 0) (fun j => σ.st (tmap' j))
      r'.final.heads r'.final.tapes := Step.of_run (r := r') hr' rfl rfl
  obtain ⟨τ, e, hd⟩ := WXExec.machZ_ex cap hinj' hL' σ hStep (fun j => by
      refine Fin.addCases (fun k => ?_) (fun k => ?_) j
      · simp only [htm, Fin.addCases_left]; exact h0 k
      · simp only [htm, Fin.addCases_right]; exact hTLh) hLst hLsh le_rfl
  have hsteps : receipt.steps ≤ budget req := runFrom_steps_le _ _ _ receipt hrun
  refine ⟨receipt, τ, hrun, hout, hsteps, e, fun j => ?_, ?_, fun j => ?_, ?_, fun i hi hiT => ?_, hd.val, hd.cell⟩
  · have := hd.st (Fin.castAdd 1 j)
    simp only [htm, Fin.addCases_left] at this
    rw [this, hfin]; simp [clockConfig]
  · have := hd.st (Fin.natAdd f.program.tapeCount 0)
    simp only [htm, Fin.addCases_right] at this
    rw [this, hfin]; simp [clockConfig]
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

end NearCubicGates.Close.WorkerArith
