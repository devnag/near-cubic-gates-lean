import Proof.PCP.VerifierDecodingFront

/-! The capped table-size guard on the retained twenty-tape decoder store.
Only its seven selected tapes move. Its capped backing is observational zero
padding; the enclosing entry removes it by reverse simulation. -/
namespace NearCubicWires.RepairSource.VerifierDecoding.TableGuardLayout
open LocalBitMultitape RepairOrdinary RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

abbrev states := 2+Fintype.card (RecoveryCalls.Control TableBoundMachine.sizes)
def slot : Fin 7 → Fin 20 := ![14,15,3,1,16,2,17]
theorem slot_injective : Function.Injective slot := by decide
theorem slot_pick (i : Fin 20) : RecoveryFocus.pick slot i=
    ![none,some 3,some 5,some 2,none,none,none,none,none,none,
      none,none,none,none,some 0,some 1,some 4,some 6,none,none] i := by
  fin_cases i
  all_goals first
    | exact RecoveryFocus.pick_slot slot slot_injective 0
    | exact RecoveryFocus.pick_slot slot slot_injective 1
    | exact RecoveryFocus.pick_slot slot slot_injective 2
    | exact RecoveryFocus.pick_slot slot slot_injective 3
    | exact RecoveryFocus.pick_slot slot slot_injective 4
    | exact RecoveryFocus.pick_slot slot slot_injective 5
    | exact RecoveryFocus.pick_slot slot slot_injective 6
    | simp [RecoveryFocus.pick,slot]
  all_goals intro j; fin_cases j <;> decide
noncomputable def machine := RecoveryFocus.machine slot TableBoundEntry.machine
noncomputable def localEntry (c t s : ℕ) : Configuration 7 states :=
  ZeroPadding.config (TableBoundEntry.capacity c)
    (Composition.leftConfig _ (TableBoundEntry.initial c t s))
noncomputable def input {a : ℕ} (base : Configuration 20 a) : Configuration 20 states :=
  ⟨machine.start,base.heads,base.tapes⟩
noncomputable def output {a : ℕ} (base : Configuration 20 a) (c t s : ℕ) :=
  RecoveryFocus.config slot base.heads base.tapes
    (Composition.rightConfig 2 (TableBoundMachine.succeeded c t s))
structure Entry {a : ℕ} (base : Configuration 20 a) (c t s : ℕ) : Prop where
  heads : ∀ i, base.heads (slot i)=(localEntry c t s).heads i
  tapes : ∀ i, base.tapes (slot i)=(localEntry c t s).tapes i

theorem focused_input {a : ℕ} (base : Configuration 20 a) (c t s : ℕ)
    (h : Entry base c t s) :
    RecoveryFocus.config slot base.heads base.tapes (localEntry c t s)=input base := by
  apply configuration_ext
  · rfl
  · funext i; fin_cases i
    all_goals simp only [RecoveryFocus.config,slot_pick,input]
    all_goals first
      | rfl | exact (h.heads 0).symm | exact (h.heads 1).symm
      | exact (h.heads 2).symm | exact (h.heads 3).symm | exact (h.heads 4).symm
      | exact (h.heads 5).symm | exact (h.heads 6).symm
  · funext i; fin_cases i
    all_goals simp only [RecoveryFocus.config,slot_pick,input]
    all_goals first
      | rfl | exact (h.tapes 0).symm | exact (h.tapes 1).symm
      | exact (h.tapes 2).symm | exact (h.tapes 3).symm | exact (h.tapes 4).symm
      | exact (h.tapes 5).symm | exact (h.tapes 6).symm

theorem guard_run {a : ℕ} (base : Configuration 20 a) (c t s : ℕ)
    (h : Entry base c t s) (hc : 1≤c) (ht : t≤c) (hs : s ≤ c) (hspos : 0<s) :
    ∃ r, runFrom machine (TableBoundMachine.budget c+2) (input base)=some r ∧
      r.steps≤TableBoundMachine.budget c+2 ∧ r.final.scanned 17=decide (2^t*s ≤ c) ∧
      (2^t*s ≤ c → r.final=output base c t s) := by
  obtain ⟨raw,final,hr,hsteps,hresult,hfinal⟩ := TableBoundEntry.table_bound_run c t s hc ht hs hspos
  obtain ⟨padded,hp,hpf,hps,_⟩ := ZeroPadding.run_config TableBoundEntry.machine
    (TableBoundEntry.capacity c) _ _ raw hr
  obtain ⟨r,hrun,hf,hst⟩ := RecoveryFocus.run_config slot slot_injective TableBoundEntry.machine
    base.heads base.tapes _ _ padded hp
  change runFrom machine (TableBoundMachine.budget c+2)
    (RecoveryFocus.config slot base.heads base.tapes (localEntry c t s))=some r at hrun
  rw [focused_input base c t s h] at hrun
  have hfinal' : r.final=RecoveryFocus.config slot base.heads base.tapes
      (Composition.rightConfig 2 final) := by rw [hf,hpf,hfinal]
  refine ⟨r,hrun,by omega,?_,?_⟩
  · rw [hfinal']
    by_cases he : 2^t*s ≤ c
    · simp only [TableBoundMachine.Result,if_pos he] at hresult
      simp [he,hresult,Configuration.scanned,RecoveryFocus.config,slot_pick,
        Composition.rightConfig,TableBoundMachine.succeeded,RecoveryCalls.stopped,
        TableBoundMachine.acceptOutput,TableBoundMachine.productOutput,TableBoundMachine.store,readTapeBit]
    · simp only [TableBoundMachine.Result,if_neg he] at hresult
      simp [he,Configuration.scanned,RecoveryFocus.config,slot_pick,Composition.rightConfig,hresult,readTapeBit]
  · intro he
    simp only [TableBoundMachine.Result,if_pos he] at hresult
    rw [hfinal',hresult]
    rfl

end NearCubicWires.RepairSource.VerifierDecoding.TableGuardLayout
