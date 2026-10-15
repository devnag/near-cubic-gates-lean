import Proof.Amplification.RecoveryUnpairEntry

/-! Static tape selection for the shared arithmetic controller. Only the
finite, input-independent tape wiring uses classical choice. Actual reads,
writes and moves are the selected finite machine's source transitions; all
unselected tapes and head positions remain present and unchanged. -/
namespace NearCubicWires.RepairOrdinary.RecoveryFocus
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def pick {t u : Nat} (slot : Fin t → Fin u) (i : Fin u) : Option (Fin t) :=
  if h : ∃ j, slot j = i then some h.choose else none

theorem pick_slot {t u : Nat} (slot : Fin t → Fin u) (hinj : Function.Injective slot) (j : Fin t) :
    pick slot (slot j) = some j := by
  classical
  have h : ∃ k, slot k = slot j := ⟨j, rfl⟩
  simp only [pick, dif_pos h]
  exact congrArg some (hinj h.choose_spec)

theorem slot_of_pick {t u : Nat} (slot : Fin t → Fin u) {i : Fin u} {j : Fin t}
    (h : pick slot i = some j) : slot j = i := by
  classical
  unfold pick at h
  split at h
  · next hex =>
    have hj := Option.some.inj h
    exact hj ▸ hex.choose_spec
  · simp at h

noncomputable def config {t u s : Nat} (slot : Fin t → Fin u)
    (ambientHeads : Fin u → Nat) (ambientTapes : Fin u → List Bool)
    (source : Configuration t s) : Configuration u s :=
  ⟨source.control,
    fun i => match pick slot i with | some j => source.heads j | none => ambientHeads i,
    fun i => match pick slot i with | some j => source.tapes j | none => ambientTapes i⟩

noncomputable def action {t u s : Nat} (slot : Fin t → Fin u) (a : Action t s) : Action u s :=
  ⟨a.nextControl,
    fun i => match pick slot i with | some j => a.write j | none => none,
    fun i => match pick slot i with | some j => a.move j | none => .stay⟩

noncomputable def machine {t u s : Nat} (slot : Fin t → Fin u) (p : Machine t s) : Machine u s where
  descriptionBits := 0
  start := p.start
  halted := p.halted
  rule := fun state bits => (p.rule state (bits ∘ slot)).map (action slot)

theorem scanned_config {t u s : Nat} (slot : Fin t → Fin u) (hinj : Function.Injective slot)
    (heads : Fin u → Nat) (tapes : Fin u → List Bool) (source : Configuration t s) :
    (config slot heads tapes source).scanned ∘ slot = source.scanned := by
  funext j
  simp [config, Configuration.scanned, pick_slot slot hinj]

theorem action_config {t u s : Nat} (slot : Fin t → Fin u)
    (heads : Fin u → Nat) (tapes : Fin u → List Bool) (source : Configuration t s) (a : Action t s) :
    applyAction (config slot heads tapes source) (action slot a) =
      config slot heads tapes (applyAction source a) := by
  apply configuration_ext
  · rfl
  · funext i
    cases hp : pick slot i <;> simp [applyAction, config, action, hp, HeadMove.apply]
  · funext i
    cases hp : pick slot i <;> simp [applyAction, config, action, hp]

theorem step_config {t u s : Nat} (slot : Fin t → Fin u) (hinj : Function.Injective slot)
    (p : Machine t s) (heads : Fin u → Nat) (tapes : Fin u → List Bool) (source : Configuration t s) :
    step (machine slot p) (config slot heads tapes source) =
      (step p source).map (config slot heads tapes) := by
  change ((p.rule source.control ((config slot heads tapes source).scanned ∘ slot)).map _).map _ = _
  rw [scanned_config slot hinj]
  simp only [step, Option.map_map, Function.comp_def, action_config]

/-- Full interpreter transport with the exact transition count. No claim
that unused ambient storage is free is made by this theorem. -/
theorem run_config {t u s : Nat} (slot : Fin t → Fin u) (hinj : Function.Injective slot)
    (p : Machine t s) (heads : Fin u → Nat) (tapes : Fin u → List Bool)
    (fuel : Nat) (source : Configuration t s) (receipt : ExecutionReceipt t s)
    (hrun : runFrom p fuel source = some receipt) :
    ∃ result : ExecutionReceipt u s,
      runFrom (machine slot p) fuel (config slot heads tapes source) = some result ∧
      result.final = config slot heads tapes receipt.final ∧ result.steps = receipt.steps := by
  induction fuel generalizing source receipt with
  | zero =>
    simp only [runFrom] at hrun
    split at hrun
    · next hh =>
      cases hrun
      refine ⟨⟨config slot heads tapes source, 0, (config slot heads tapes source).tapeCells⟩, ?_, rfl, rfl⟩
      simp [runFrom, machine, config, hh]
    · contradiction
  | succ fuel ih =>
    simp only [runFrom] at hrun
    split at hrun
    · next hh =>
      cases hrun
      refine ⟨⟨config slot heads tapes source, 0, (config slot heads tapes source).tapeCells⟩, ?_, rfl, rfl⟩
      simp [runFrom, machine, config, hh]
    · next hh =>
      cases hs : step p source with
      | none => simp [hs] at hrun
      | some next =>
        cases ht : runFrom p fuel next with
        | none => simp [hs, ht] at hrun
        | some tail =>
          simp only [hs, ht, Option.some.injEq] at hrun
          subst receipt
          obtain ⟨result, hr, hf, hsteps⟩ := ih next tail ht
          have hstep : step (machine slot p) (config slot heads tapes source) =
              some (config slot heads tapes next) := by rw [step_config slot hinj, hs]; rfl
          refine ⟨⟨result.final, result.steps + 1,
            max (config slot heads tapes source).tapeCells result.peakTapeCells⟩, ?_, hf, ?_⟩
          · exact runFrom_step (machine slot p) _ _ result
              (by simpa [machine, config] using hh) hstep hr
          · simp only [hsteps]

end NearCubicWires.RepairOrdinary.RecoveryFocus
