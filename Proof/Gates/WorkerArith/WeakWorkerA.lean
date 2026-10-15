import Proof.Gates.WorkerArith.WeakWorkerDefs

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.WorkerArith.WeakWorker

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicGates.Close NearCubicGates.Close.WordPrograms NearCubicGates.Close.CheckedPCPP
open NearCubicGates.Close.Setup

/-- Extra fuel does not change a finished run. -/
theorem runFrom_mono {t s : ℕ} (M : Machine t s) :
    ∀ (f f' : ℕ) (c : Configuration t s) (r : ExecutionReceipt t s), runFrom M f c = some r → f ≤ f' →
      runFrom M f' c = some r
  | 0, f', c, r, h, _ => by
    simp only [runFrom] at h
    split at h
    · next hh =>
      cases f' with
      | zero => simp [runFrom, hh] at h ⊢; exact h
      | succ f' => simp [runFrom, hh] at h ⊢; exact h
    · cases h
  | f + 1, f', c, r, h, hle => by
    obtain ⟨f'', rfl⟩ : ∃ f'', f' = f'' + 1 := ⟨f' - 1, by omega⟩
    simp only [runFrom] at h ⊢
    split at h
    · next hh => rw [if_pos hh]; exact h
    · next hh =>
      rw [if_neg hh]
      split at h
      · cases h
      · next next' hs =>
        split at h
        · cases h
        · next suf hsuf =>
          rw [runFrom_mono M f f'' next' suf hsuf (by omega)]
          exact h

theorem rdEq_nil_of_false (l : List Bool) (h : ∀ b ∈ l, b = false) : RdEq l [] := by
  intro p
  simp only [readTapeBit, List.getD_eq_getElem?_getD, List.getElem?_nil, Option.getD_none]
  rcases hp : l[p]? with _ | b
  · rfl
  · have := h b (List.mem_of_getElem? hp); simp [this]

theorem regTape_false (cap : ℕ) : ∀ b ∈ regTape cap 0, b = false := by
  intro b hb
  simp only [regTape, List.replicate_zero, List.nil_append, List.mem_cons, List.mem_replicate] at hb
  rcases hb with h | ⟨_, h⟩ <;> exact h

open NearCubicWires.SourceInterfaces NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutLanguage
open NearCubicGates.PublishedSources.PCPP NearCubicGates.Close.Gadget NearCubicGates.Close.Transfer

variable {s : GateSources} {P : ThreeQueryPCPP} {g : GateParams} (D : SetupData s P g)

/-- The verifier's input tapes, renamed, read like the encoded cold start. -/
theorem cold_rdEq (cap : ℕ) (xs bits : List Bool) (j : Fin (wTapes D)) :
    RdEq ((wenc cap (coldState D xs bits)).A j)
      ((fun i : Fin (wTapes D) => if i.val = 0 then RepairOrdinary.frame xs else if i.val = 1 then RepairOrdinary.frame bits
        else []) (tSwap D j)) := by
  have hsw : ∀ i : Fin (wTapes D), (tSwap D i).val = if i.val = 1 then 2 else if i.val = 2 then 1 else i.val := by
    intro i
    unfold tSwap
    by_cases h1 : i.val = 1
    · rw [show i = ⟨1, by have := three_le D; omega⟩ from Fin.ext h1, Equiv.swap_apply_left]; simp
    · by_cases h2 : i.val = 2
      · rw [show i = ⟨2, by have := three_le D; omega⟩ from Fin.ext h2, Equiv.swap_apply_right]; simp
      · rw [Equiv.swap_apply_of_ne_of_ne (fun h => h1 (by rw [h])) (fun h => h2 (by rw [h]))]
        simp [h1, h2]
  simp only [hsw]
  unfold wenc
  simp only
  unfold role
  by_cases h0 : j.val = 0
  · simp only [h0, dif_pos, if_true]
    have : (0 : Fin (nsW D + 1)) = sX D := rfl
    simp [coldState, this]; exact RdEq.refl _
  by_cases h1 : j.val = 1
  · simp only [h0, h1, dif_neg, dif_pos, if_true]
    simp only [show ¬ (2 = 0) from by omega, show ¬ (2 = 1) from by omega, if_false]
    exact rdEq_nil_of_false _ (by simp [coldState])
  by_cases hs : j.val ≤ nsW D + 1
  · rw [dif_neg h0, dif_neg h1, dif_pos hs]
    by_cases h2 : j.val = 2
    · simp only [h2, if_true, show ¬ (2 = 1) from by omega, if_false, show ¬ ((1 : ℕ) = 0) from by omega]
      have : (⟨2 - 1, by unfold nsW; omega⟩ : Fin (nsW D + 1)) = sBW D := rfl
      simp only [this, coldState]
      rw [if_neg (by intro h; have := congrArg Fin.val h; simp [sBW, sX, fixS] at this), if_pos trivial]
      exact RdEq.refl _
    · simp only [h1, h2, if_false, h0]
      simp only [coldState]
      have hX : (⟨j.val - 1, by omega⟩ : Fin (nsW D + 1)) ≠ sX D := by
        intro h; have := congrArg Fin.val h; simp [sX, fixS] at this; omega
      have hB : (⟨j.val - 1, by omega⟩ : Fin (nsW D + 1)) ≠ sBW D := by
        intro h; have := congrArg Fin.val h; simp [sBW, fixS] at this; omega
      rw [if_neg hX, if_neg hB]; exact RdEq.refl _
  · rw [dif_neg h0, dif_neg h1, dif_neg hs]
    simp only [h0, h1, if_false]
    have hj2 : ¬ j.val = 2 := by unfold nsW at hs; omega
    simp only [hj2, if_false]
    rw [if_neg h0, if_neg h1]
    exact rdEq_nil_of_false _ (regTape_false cap)

theorem two_le_wTapes : 2 ≤ wTapes D := by have := three_le D; omega

/-- **The bridge.** A run of the compiled worker program from the cold start is a run of the worker machine on proof
1's input tapes, within any larger fuel, whose result tape scans the final cell. -/
theorem worker_run (prog : WMX (nsW D) nrW) (cap n fuel : ℕ) (xs bits : List Bool) (τ : WState (nsW D) nrW)
    (h : WXExec cap prog (coldState D xs bits) τ n) (hf : n ≤ fuel) :
    ∃ r, run (TapeRenaming.machine (tSwap D) prog.compile) fuel
        ((UAcceptanceCarrier.verifier (TapeRenaming.machine (tSwap D) prog.compile) (two_le_wTapes D)
          (wResult D)).inputTapes xs bits) = some r ∧
      r.final.scanned (wResult D) = τ.cell := by
  obtain ⟨r0, hr0, hh0, ht0, _⟩ := h.run cap (fun _ => rfl) (fun _ => rfl)
  set I : Fin (wTapes D) → List Bool := fun i =>
    if i.val = 0 then RepairOrdinary.frame xs else if i.val = 1 then RepairOrdinary.frame bits else [] with hI
  have hrel : ConfRel (fun _ => False) (initialConfiguration prog.compile (wenc cap (coldState D xs bits)).A)
      (initialConfiguration prog.compile (fun j => I (tSwap D j))) :=
    ⟨rfl, rfl, fun j => cold_rdEq D cap xs bits j, fun _ h => h.elim⟩
  obtain ⟨r1, hr1, hrel1, _⟩ := runFrom_rel prog.compile _ n hrel r0 hr0
  have hr1' := runFrom_mono prog.compile n fuel _ r1 hr1 hf
  have hren := TapeRenaming.run_rename (tSwap D) prog.compile fuel _ r1 hr1'
  have hcfg : TapeRenaming.config (tSwap D) (initialConfiguration prog.compile (fun j => I (tSwap D j))) =
      initialConfiguration (TapeRenaming.machine (tSwap D) prog.compile) I := by
    unfold TapeRenaming.config initialConfiguration
    congr 1
    funext i
    simp [Function.comp_def]
  rw [hcfg] at hren
  refine ⟨TapeRenaming.receipt (tSwap D) r1, ?_, ?_⟩
  · rw [UAcceptanceCarrier.inputTapes_eq]
    exact hren
  · have hw : wResult D = tSwap D ⟨1, by have := three_le D; omega⟩ := by
      unfold tSwap wResult; rw [Equiv.swap_apply_left]
    show (TapeRenaming.config (tSwap D) r1.final).scanned (wResult D) = τ.cell
    rw [hw]
    have := congrFun (TapeRenaming.config_scanned (tSwap D) r1.final) ⟨1, by have := three_le D; omega⟩
    simp only [Function.comp_apply] at this
    rw [this]
    have hc : r1.final.scanned ⟨1, by have := three_le D; omega⟩ = r0.final.scanned ⟨1, by have := three_le D; omega⟩ := by
      unfold Configuration.scanned
      rw [← hrel1.heads]
      exact (hrel1.read _ _).symm
    rw [hc]
    unfold Configuration.scanned
    rw [ht0, hh0]
    have h1 : (⟨1, by have := three_le D; omega⟩ : Fin (wTapes D)) = cTape := rfl
    rw [h1]
    unfold wenc
    simp only
    rw [show role (cTape (ns := nsW D) (nr := nrW)) = .cell from role_cTape]
    simp [readTapeBit]

end NearCubicGates.Close.WorkerArith.WeakWorker
