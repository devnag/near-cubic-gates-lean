import Proof.PCP.VerifierDecodingTableGuardLayout
import Proof.PCP.VerifierDecodingTableRun

/-! Counted record validation uses the actual e counter produced by the
table guard. The retained start-state field is outside this static focus. -/
namespace NearCubicWires.RepairSource.VerifierDecoding.TableLayout
open LocalBitMultitape RepairOrdinary RecoveryExecution RecordsMachine
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

abbrev states := Fintype.card (RecoveryCalls.Control TableValidation.sizes)
def slot : Fin 9 → Fin 20 := ![0,18,10,7,12,13,1,19,16]
theorem slot_injective : Function.Injective slot := by decide
theorem slot_pick (i : Fin 20) : RecoveryFocus.pick slot i=
    ![some 0,some 6,none,none,none,none,none,some 3,none,none,
      some 2,none,some 4,some 5,none,none,some 8,none,some 1,some 7] i := by
  fin_cases i
  all_goals first
    | exact RecoveryFocus.pick_slot slot slot_injective 0
    | exact RecoveryFocus.pick_slot slot slot_injective 1
    | exact RecoveryFocus.pick_slot slot slot_injective 2
    | exact RecoveryFocus.pick_slot slot slot_injective 3
    | exact RecoveryFocus.pick_slot slot slot_injective 4
    | exact RecoveryFocus.pick_slot slot slot_injective 5
    | exact RecoveryFocus.pick_slot slot slot_injective 6
    | exact RecoveryFocus.pick_slot slot slot_injective 7
    | exact RecoveryFocus.pick_slot slot slot_injective 8
    | simp [RecoveryFocus.pick,slot]
  all_goals intro j; fin_cases j <;> decide
noncomputable def machine := RecoveryFocus.machine slot TableValidation.machine
def capacity (c : ℕ) : Fin 9 → ℕ := fun i => if i=6 then c+2 else 0
noncomputable def localEntry (bound : List Bool) (t c e : ℕ) (x : State) :=
  ZeroPadding.config (capacity c) (TableValidation.initial bound t (2*bound.length+1) c e x)
noncomputable def input {a : ℕ} (base : Configuration 20 a) : Configuration 20 states :=
  ⟨machine.start,base.heads,base.tapes⟩
noncomputable def output {a : ℕ} (base : Configuration 20 a) (bound : List Bool)
    (t c e : ℕ) (out : State) :=
  RecoveryFocus.config slot base.heads base.tapes
    (ZeroPadding.config (capacity c) (TableValidation.endpoint bound t (2*bound.length+1) c e out))
structure Entry {a : ℕ} (base : Configuration 20 a) (bound : List Bool)
    (t c e : ℕ) (x : State) : Prop where
  heads : ∀ i, base.heads (slot i)=(localEntry bound t c e x).heads i
  tapes : ∀ i, base.tapes (slot i)=(localEntry bound t c e x).tapes i

theorem focused_input {a : ℕ} (base : Configuration 20 a) (bound : List Bool)
    (t c e : ℕ) (x : State) (h : Entry base bound t c e x) :
    RecoveryFocus.config slot base.heads base.tapes (localEntry bound t c e x)=input base := by
  apply configuration_ext
  · rfl
  · funext i; fin_cases i
    all_goals simp only [RecoveryFocus.config,slot_pick,input]
    all_goals first
      | rfl | exact (h.heads 0).symm | exact (h.heads 1).symm
      | exact (h.heads 2).symm | exact (h.heads 3).symm | exact (h.heads 4).symm
      | exact (h.heads 5).symm | exact (h.heads 6).symm | exact (h.heads 7).symm
      | exact (h.heads 8).symm
  · funext i; fin_cases i
    all_goals simp only [RecoveryFocus.config,slot_pick,input]
    all_goals first
      | rfl | exact (h.tapes 0).symm | exact (h.tapes 1).symm
      | exact (h.tapes 2).symm | exact (h.tapes 3).symm | exact (h.tapes 4).symm
      | exact (h.tapes 5).symm | exact (h.tapes 6).symm | exact (h.tapes 7).symm
      | exact (h.tapes 8).symm

theorem table_run {a : ℕ} (base : Configuration 20 a) (bound : List Bool)
    (t c e : ℕ) (x : State) (h : Entry base bound t c e x) (he : e≤c) (hx : Inv bound x) :
    ∃ r, runFrom machine (e*(8*bound.length+12*t+34)+11) (input base)=some r ∧
      r.steps≤e*(8*bound.length+12*t+34)+11 ∧
      r.final.scanned 19=TableValidation.valid bound t e x.bits ∧
      (TableValidation.valid bound t e x.bits=true → ∃ out : State,
        r.final=output base bound t c e out ∧
        out.pre++frame out.bits=x.pre++frame x.bits ∧
        out.pre.length=x.pre.length+2*width bound t*e ∧ out.bits=[] ∧ Inv bound out) := by
  obtain ⟨raw,hr,hsteps,hbit,hgood⟩ := TableValidation.table_run bound t (2*bound.length+1) c e
    (Nat.le_refl _) he x hx
  obtain ⟨padded,hp,hpf,hps,_⟩ := ZeroPadding.run_config TableValidation.machine (capacity c) _ _ raw hr
  obtain ⟨r,hrun,hf,hst⟩ := RecoveryFocus.run_config slot slot_injective TableValidation.machine
    base.heads base.tapes _ _ padded hp
  change runFrom machine (e*(8*bound.length+12*t+34)+11)
    (RecoveryFocus.config slot base.heads base.tapes (localEntry bound t c e x))=some r at hrun
  rw [focused_input base bound t c e x h] at hrun
  refine ⟨r,hrun,by omega,?_,?_⟩
  · rw [hf,hpf]
    have hb : (ZeroPadding.config (capacity c) raw.final).scanned 7=
        TableValidation.valid bound t e x.bits := by rw [ZeroPadding.scanned_config]; exact hbit
    simpa [Configuration.scanned,RecoveryFocus.config,slot_pick] using hb
  · intro hv
    obtain ⟨out,hout,hsource,hpos,hbits,hinv⟩ := hgood hv
    refine ⟨out,?_,hsource,hpos,hbits,hinv⟩
    rw [hf,hpf,hout]
    rfl

end NearCubicWires.RepairSource.VerifierDecoding.TableLayout
