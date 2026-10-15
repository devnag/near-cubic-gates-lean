import Proof.Gates.WordPrograms.WMX
import Proof.Wire_3_5.PrimTReadEq
import Proof.MachineModel.ClockJoin

set_option autoImplicit false

namespace NearCubicGates.Close.CheckedPCPP

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicGates.Close.WordPrograms NearCubicWires.WireExponent3_5 NearCubicWires.ExtDecompositionBatch

/-- Configurations that run alike: same control and heads; tapes read alike, and equal on `E`. -/
structure ConfRel {t s : ℕ} (E : Fin t → Prop) (c c' : Configuration t s) : Prop where
  control : c.control = c'.control
  heads : c.heads = c'.heads
  read : ∀ i, RdEq (c.tapes i) (c'.tapes i)
  exact : ∀ i, E i → c.tapes i = c'.tapes i

theorem step_rel {t s : ℕ} (M : Machine t s) (E : Fin t → Prop) {c c' : Configuration t s} (h : ConfRel E c c') :
    (step M c = none ∧ step M c' = none) ∨
      ∃ d d', step M c = some d ∧ step M c' = some d' ∧ ConfRel E d d' := by
  have hscan : c.scanned = c'.scanned := by
    funext i
    unfold Configuration.scanned
    rw [h.heads]
    exact h.read i _
  unfold step
  rw [h.control, hscan]
  cases hr : M.rule c'.control c'.scanned with
  | none => left; simp
  | some a =>
    right
    refine ⟨applyAction c a, applyAction c' a, rfl, rfl, ⟨rfl, ?_, ?_, ?_⟩⟩
    · funext i; simp only [applyAction, h.heads]
    · intro i
      simp only [applyAction]
      cases a.write i with
      | none => exact h.read i
      | some v => rw [h.heads]; exact rdEq_write (h.read i) _ v
    · intro i hi
      simp only [applyAction]
      cases a.write i with
      | none => exact h.exact i hi
      | some v => rw [h.heads, h.exact i hi]

theorem runFrom_rel {t s : ℕ} (M : Machine t s) (E : Fin t → Prop) (fuel : ℕ) {c c' : Configuration t s}
    (h : ConfRel E c c') (r : ExecutionReceipt t s) (hr : runFrom M fuel c = some r) :
    ∃ r', runFrom M fuel c' = some r' ∧ ConfRel E r.final r'.final ∧ r'.steps = r.steps := by
  induction fuel generalizing c c' r with
  | zero =>
    by_cases hh : M.halted c.control = true
    · have hh' : M.halted c'.control = true := h.control ▸ hh
      simp only [runFrom, hh, hh', if_true, Option.some.injEq] at hr ⊢
      subst hr
      exact ⟨_, rfl, h, rfl⟩
    · simp [runFrom, hh] at hr
  | succ fuel ih =>
    by_cases hh : M.halted c.control = true
    · have hh' : M.halted c'.control = true := h.control ▸ hh
      simp only [runFrom, hh, hh', if_true, Option.some.injEq] at hr ⊢
      subst hr
      exact ⟨_, rfl, h, rfl⟩
    · have hh' : ¬ M.halted c'.control = true := h.control ▸ hh
      rcases step_rel M E h with ⟨hn, _⟩ | ⟨d, d', hd, hd', hdd⟩
      · simp [runFrom, hh, hn] at hr
      · cases ht : runFrom M fuel d with
        | none => simp [runFrom, hh, hd, ht] at hr
        | some tail =>
          simp only [runFrom, hh, hd, ht, Option.some.injEq, Bool.false_eq_true, if_false] at hr
          subst hr
          obtain ⟨tail', ht', hrel, hs⟩ := ih hdd tail ht
          refine ⟨⟨tail'.final, tail'.steps + 1, max c'.tapeCells tail'.peakTapeCells⟩, ?_, hrel, ?_⟩
          · simp only [runFrom, hh', hd', ht', Bool.false_eq_true, if_false]
          · simp [hs]

variable {ns nr : ℕ}

/-- The empty-work-tape bank of a word state: its streams, an empty cell tape and empty register tapes. -/
def coldBank (σ : WState ns nr) : Fin (ns + 2 + nr) → List Bool :=
  fun j => match role j with
    | .stream i => σ.st i
    | .cell => []
    | .reg _ => []

theorem coldBank_s (σ : WState ns nr) (i : Fin (ns + 1)) : coldBank σ (sTape i) = σ.st i := by
  simp [coldBank, role_sTape]
theorem coldBank_c (σ : WState ns nr) : coldBank σ (cTape (ns := ns) (nr := nr)) = [] := by
  simp [coldBank, role_cTape]
theorem coldBank_r (σ : WState ns nr) (r : Fin nr) : coldBank σ (rTape (ns := ns) r) = [] := by
  simp [coldBank, role_rTape]

theorem WXExec.ready {cap : ℕ} {P : WMX ns nr} {σ τ : WState ns nr} {n : ℕ} (h : WXExec cap P σ τ n)
    (hsh : ∀ i, σ.sh i = 0) (hval : ∀ r, σ.val r = 0) (hcell : σ.cell = false)
    (hsh' : ∀ i, τ.sh i = 0) (hval' : ∀ r, τ.val r = 0) :
    ∃ out, ClockJoin.ReadyRun P.compile n (coldBank σ) out ∧ ∀ i, out (sTape i) = τ.st i := by
  obtain ⟨r, hr, hh, ht, hs⟩ := WXExec.run cap h hsh hval
  let E : Fin (ns + 2 + nr) → Prop := fun j => ∃ i, j = sTape i
  have hrel : ConfRel E (initialConfiguration P.compile (wenc cap σ).A)
      (initialConfiguration P.compile (coldBank σ)) := by
    refine ⟨rfl, rfl, ?_, ?_⟩
    · intro j
      simp only [initialConfiguration]
      rcases PrimAsm.DockW.tape_cases j with ⟨i, rfl⟩ | rfl | ⟨q, rfl⟩
      · rw [wenc_A_s, coldBank_s]; exact RdEq.refl _
      · rw [PrimAsm.DockW.wenc_A_c, coldBank_c, hcell]; exact rdEq_blank _ (by simp)
      · rw [wenc_A_r, coldBank_r, hval q, regTape_zero]; exact rdEq_blank _ (by simp)
    · rintro j ⟨i, rfl⟩
      simp only [initialConfiguration]
      rw [wenc_A_s, coldBank_s]
  obtain ⟨r', hr', hrel', hst⟩ := runFrom_rel P.compile E n hrel r hr
  refine ⟨r'.final.tapes, ⟨r', hr', rfl, ?_, ?_⟩, ?_⟩
  · intro j
    rw [← hrel'.heads, hh]
    rcases PrimAsm.DockW.tape_cases j with ⟨i, rfl⟩ | rfl | ⟨q, rfl⟩
    · rw [wenc_H_s]; exact hsh' i
    · exact PrimAsm.DockW.wenc_H_c cap τ
    · rw [wenc_H_r]; exact hval' q
  · rw [hst]; exact hs
  · intro i
    rw [← hrel'.exact (sTape i) ⟨i, rfl⟩, ht, wenc_A_s]

theorem WXExec.readyRewound {cap : ℕ} {P : WMX ns nr} {σ τ : WState ns nr} {n : ℕ} (h : WXExec cap P σ τ n)
    (hsh : ∀ i, σ.sh i = 0) (hval : ∀ r, σ.val r = 0) (hcell : σ.cell = false) :
    ∃ out, ClockJoin.ReadyRun (Rewind.machine P.compile) (2 * n + 2)
      (Fin.addCases (coldBank σ) (fun _ => [])) out ∧ ∀ i, out ((sTape i).castAdd 1) = τ.st i := by
  obtain ⟨r, hr, _, ht, hs⟩ := WXExec.run cap h hsh hval
  let E : Fin (ns + 2 + nr) → Prop := fun j => ∃ i, j = sTape i
  have hrel : ConfRel E (initialConfiguration P.compile (wenc cap σ).A)
      (initialConfiguration P.compile (coldBank σ)) := by
    refine ⟨rfl, rfl, ?_, ?_⟩
    · intro j
      simp only [initialConfiguration]
      rcases PrimAsm.DockW.tape_cases j with ⟨i, rfl⟩ | rfl | ⟨q, rfl⟩
      · rw [wenc_A_s, coldBank_s]; exact RdEq.refl _
      · rw [PrimAsm.DockW.wenc_A_c, coldBank_c, hcell]; exact rdEq_blank _ (by simp)
      · rw [wenc_A_r, coldBank_r, hval q, regTape_zero]; exact rdEq_blank _ (by simp)
    · rintro j ⟨i, rfl⟩
      simp only [initialConfiguration]
      rw [wenc_A_s, coldBank_s]
  obtain ⟨r', hr', hrel', hst⟩ := runFrom_rel P.compile E n hrel r hr
  obtain ⟨q, hq, hqt, hqh, hqs, _⟩ := Rewind.reset_run P.compile n (coldBank σ) r' hr'
  refine ⟨q.final.tapes, ⟨q, ?_, rfl, hqh, ?_⟩, ?_⟩
  · have hmore := run_moreFuel (Rewind.machine P.compile) (2 * r'.steps + 2) ((2 * n + 2) - (2 * r'.steps + 2)) _ q hq
    rw [Nat.add_sub_of_le (by rw [hst]; omega)] at hmore
    exact hmore
  · rw [hqs, hst]; omega
  · intro i
    rw [hqt, ← hrel'.exact (sTape i) ⟨i, rfl⟩, ht, wenc_A_s]

theorem wordFunction_machZ {Request : Type} {input output : Request → List Bool} {budget : Request → ℕ}
    (f : WordFunction Request input output budget) (req : Request) {cap : ℕ}
    (tmap : Fin f.program.tapeCount → Fin (ns + 1)) (hinj : Function.Injective tmap) (L : Fin (ns + 1))
    (hL : ∀ j, tmap j ≠ L) (σ : WState ns nr) (h0 : ∀ j, σ.sh (tmap j) = 0)
    (hin : ∀ j, RdEq (σ.st (tmap j)) (f.program.inputTapes (input req) j))
    (lcap : ℕ) (hLst : σ.st L = List.replicate lcap false) (hLsh : σ.sh L = 0) (hn : budget req ≤ lcap) :
    ∃ τ tout, WXExec cap (WMX.machZ f.program.machine tmap L) σ τ (2 * budget req + 2) ∧
      Docked tmap σ τ (fun _ => 0) tout ∧ RdEq (τ.st (tmap f.program.outputTape)) (output req) := by
  obtain ⟨receipt, hrun, hout⟩ := f.realizes req
  have hrel : ConfRel (fun _ => False) (initialConfiguration f.program.machine (f.program.inputTapes (input req)))
      ⟨f.program.machine.start, fun _ => 0, fun j => σ.st (tmap j)⟩ :=
    ⟨rfl, rfl, fun j => (hin j).symm, fun _ h => h.elim⟩
  obtain ⟨r', hr', hrel', _⟩ := runFrom_rel f.program.machine _ (budget req) hrel receipt hrun
  obtain ⟨τ, hτ, hd⟩ := WXExec.machZ_ex cap hinj hL σ (Step.of_run (r := r') hr' rfl rfl) h0 hLst hLsh hn
  refine ⟨τ, r'.final.tapes, hτ, hd, ?_⟩
  rw [hd.st]
  exact (hrel'.read f.program.outputTape).symm.trans (by rw [hout]; exact RdEq.refl _)

end NearCubicGates.Close.CheckedPCPP
