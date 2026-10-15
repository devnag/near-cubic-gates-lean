import Proof.Gates.Expand.PolyTabStage1b

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicGates.Close.Expand.PolyTab

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat (enc stp enc_length)
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat (appendO)
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicGates.Close.CounterMachine NearCubicGates.Close.Tabulator NearCubicGates.Close.Interfaces.Formats
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicWires.ExtDecompositionBatch (Step)

section Dock
variable {ns nr : ℕ}

theorem wf_machZ_exact {Request : Type} {input output : Request → List Bool} {budget : Request → ℕ}
    (f : WordFunction Request input output budget) (req : Request) {cap : ℕ}
    (tmap : Fin f.program.tapeCount → Fin (ns + 1)) (hinj : Function.Injective tmap) (L : Fin (ns + 1))
    (hL : ∀ j, tmap j ≠ L) (σ : WState ns nr) (h0 : ∀ j, σ.sh (tmap j) = 0)
    (hin : ∀ j, σ.st (tmap j) = f.program.inputTapes (input req) j)
    (lcap : ℕ) (hLst : σ.st L = List.replicate lcap false) (hLsh : σ.sh L = 0) (hn : budget req ≤ lcap) :
    ∃ τ, WXExec cap (WMX.machZ f.program.machine tmap L) σ τ (2 * budget req + 2) ∧
      τ.st (tmap f.program.outputTape) = output req ∧ (∀ j, τ.sh (tmap j) = 0) ∧
      (∀ i, (∀ j, tmap j ≠ i) → τ.st i = σ.st i ∧ τ.sh i = σ.sh i) ∧ τ.val = σ.val ∧ τ.cell = σ.cell := by
  obtain ⟨receipt, hrun, hout⟩ := f.realizes req
  have e : (fun j => σ.st (tmap j)) = f.program.inputTapes (input req) := funext hin
  have hr : runFrom f.program.machine (budget req) ⟨f.program.machine.start, fun _ => 0, fun j => σ.st (tmap j)⟩ =
      some receipt := by rw [e]; exact hrun
  obtain ⟨τ, hτ, hd⟩ := WXExec.machZ_ex (cap := cap) hinj hL σ (Step.of_run (r := receipt) hr rfl rfl) h0 hLst hLsh hn
  exact ⟨τ, hτ, by rw [hd.st]; exact hout, fun j => by rw [hd.sh], hd.other, hd.val, hd.cell⟩

end Dock

variable {te qa : ℕ}

local notation "WX" => WMX (NSx te qa) NRk
local notation "WSt" => WState (NSx te qa) NRk

/-! ## Copying the formula -/

/-- Copy the framed word at `sI`'s head to `X`, then rewind `X` (`rX 8` the output counter). -/
def cpForm (X : Fin (NSx te qa + 1)) : WX :=
  .seq (.wm (Codec.copyFrameW sI X (rX 8))) (.wm (WM.rewind X (rX 8)))

theorem cpForm_spec (cap : ℕ) (X : Fin (NSx te qa + 1)) (hX : sI ≠ X) (w pre rest : List Bool) (σ : WSt)
    (hst : σ.st sI = pre ++ frame w ++ rest) (hsh : σ.sh sI = pre.length) (hXs : σ.st X = []) (hXh : σ.sh X = 0)
    (h8 : σ.val (rX 8) = 0) (hcap : 4 * w.length + 4 ≤ cap) :
    WXExec cap (cpForm X) σ ((σ.sets X (frame w)).seth sI (pre.length + 2 * w.length))
      (22 * w.length + 1 + 1 + 7 + 1 + (5 * (2 * w.length + 1) + 1)) := by
  have e1 := Codec.copyFrame_loop cap sI X hX (rX 8) rest w pre σ hst hsh (by rw [hXs, hXh]; rfl) (by omega)
  set σ1 := (appendO σ X (rX 8) (marks w)).seth sI (pre.length + 2 * w.length) with hσ1
  have e2 := emitC_spec (cap := cap) X (rX 8) false σ1
    (by simp [hσ1, appendO, Function.update_apply, hX.symm, hXs, hXh]) (by simp [hσ1, appendO, h8, marks]; omega)
  set σ2 := ((σ1.sets X (σ1.st X ++ [false])).seth X (σ1.sh X + 1)).setv (rX 8) (σ1.val (rX 8) + 1) with hσ2
  have hv2 : σ2.val (rX 8) = 2 * w.length + 1 := by simp [hσ2, hσ1, appendO, h8, marks]; omega
  have e3 := wrewind_spec (cap := cap) X (rX 8) (2 * w.length + 1) σ2 hv2 (by omega)
  refine WXExec.cast cap (WXExec.seq (WXExec.wm (WExec.seq e1 e2)) (WXExec.wm e3)) ?_ (by simp [marks] <;> omega)
  apply WState.eq
  · funext y; by_cases hy : y = X
    · subst hy; simp [hσ2, hσ1, appendO, hX.symm] <;> simp [hXs, Codec.frame_eq_marks, marks]
    · by_cases hy' : y = sI
      · subst hy'; simp [hσ2, hσ1, appendO, hX]
      · simp [hσ2, hσ1, appendO, Function.update_of_ne hy, Function.update_of_ne hy']
  · funext y; by_cases hy : y = X
    · subst hy; simp [hσ2, hσ1, appendO, hX.symm, hXh, marks] <;> simp [hXs, Codec.frame_eq_marks, marks]
    · by_cases hy' : y = sI
      · subst hy'; simp [hσ2, hσ1, appendO, hX]
      · simp [hσ2, hσ1, appendO, Function.update_of_ne hy, Function.update_of_ne hy']
  · funext q; by_cases hq : q = rX 8
    · subst hq; simp [hσ2, hσ1, appendO, h8]
    · simp [hσ2, hσ1, appendO, Function.update_of_ne hq]
  · simp [hσ2, hσ1, appendO]

end NearCubicGates.Close.Expand.PolyTab
