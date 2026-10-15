import Proof.MachineModel.UEmissionData
import Proof.MachineModel.UAggregateClock

/-! Fixed157t event emitter: the complete prepared prefix, its actual
bounded transition walk, and a physical rejecting branch. -/
namespace NearCubicWires.RepairOrdinary.UEmission
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def reject : Machine 157 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 1
  rule := fun q _ => if q.val=0 then some
    ⟨1,fun i => if i=156 then some false else none,fun _ => .stay⟩ else none

def rejected {s : ℕ} (c : Configuration 157 s) : Configuration 157 2 :=
  ⟨1,c.heads,fun i => if i=156 then writeTapeBit (c.tapes i) (c.heads i) false else c.tapes i⟩

theorem reject_run {s : ℕ} (c : Configuration 157 s) :
    ∃ r,runFrom reject 1 (Composition.restart c reject.start)=some r ∧
      r.final=rejected c ∧ r.steps=1 := by
  have hs : step reject (Composition.restart c 0)=some (rejected c) := by
    simp only [step,reject,Composition.restart,Fin.val_zero,↓reduceIte,Option.map_some]
    congr 1
    apply configuration_ext
    · rfl
    · funext i
      simp only [applyAction,HeadMove.apply,rejected]
    · funext i
      simp only [applyAction,rejected]
      split_ifs <;> rfl
  exact (Timed.single (by rfl : reject.halted (0 : Fin 2)=false) hs).run (by rfl)

noncomputable abbrev preparedStates := Fintype.card (RecoveryCalls.Control UPrepared.sizes)
abbrev transitionStates := Fintype.card (RecoveryCalls.Control TransitionWalk.sizes)
noncomputable def sizes : Fin 3 → ℕ := ![preparedStates,transitionStates,2]
noncomputable def programs : (j : Fin 3) → Machine 157 (sizes j)
  | ⟨0,_⟩ => TapeEmbedding.machine 18 UPrepared.machine
  | ⟨1,_⟩ => UTransition.machine
  | ⟨2,_⟩ => reject
  | ⟨n+3,h⟩ => False.elim (by omega)
def next : (j : Fin 3) → Fin (sizes j) → (Fin 157 → Bool) → Option (Fin 3)
  | ⟨0,_⟩,_,bits => if bits 79 then some 1 else some 2
  | ⟨1,_⟩,_,_ => none
  | ⟨2,_⟩,_,_ => none
  | ⟨n+3,h⟩,_,_ => False.elim (by omega)
noncomputable def machine := RecoveryCalls.machine sizes programs 0 next
def input (raw witness : List Bool) : Fin 157 → List Bool :=
  fun i => Fin.addCases (UPrepared.input raw witness) (fun _ : Fin 18 => []) i
def budget (raw : List Bool) := UAggregateClock.emissionFuel raw.length

def Outcome {s : ℕ} (raw witness : List Bool) (final : Configuration 157 s) : Prop :=
  (¬UFront.Accepted raw witness ∧ final.scanned 156=false) ∨
    ∃ d,Fields raw witness d ∧ TraceResult raw.length d final

theorem Fields.walk_bound {raw witness : List Bool} {d : TraceData} (h : Fields raw witness d) :
    walkBudget raw witness d≤UAggregateClock.walkFuel raw.length := by
  have hc : (RepairSource.VerifierEncoding.code d.verifier).length≤Nat.log 2 raw.length := by
    rw [h.code_eq]
    exact h.code_bound
  exact UAggregateClock.actual_walk_bound raw.length d.verifier (2*d.word.length)
    (frame witness) (2*(ClockDyadicLedger.width raw.length+d.choices.length))
    d.input d.choices d.count hc
    (UAggregateClock.event_bound _ _ _ h.event_count h.code_bound)

theorem walk_tail {s : ℕ} (raw witness : List Bool) (base : Configuration 139 s)
    (hp : UPrepared.Prepared raw witness base) :
    ∃ n final,n≤UAggregateClock.walkFuel raw.length+1 ∧
      Timed machine n (controlConfig (RecoveryCalls.code sizes 1)
        (UTransition.entry (UTransition.extended base).heads (UTransition.extended base).tapes)) final ∧
      machine.halted final.control=true ∧ Outcome raw witness final := by
  obtain ⟨d,hd,r,hr,hresult⟩ := prepared_trace_run raw witness base hp
  obtain ⟨n,hn,hstop⟩ := stop_receipt sizes programs 0 next 1
    (walkBudget raw witness d) _ r hr (by rfl)
  have hb := hd.walk_bound
  refine ⟨n,_,by omega,hstop,?_,Or.inr ⟨d,hd,?_⟩⟩
  · simp [machine,RecoveryCalls.machine,RecoveryCalls.stopped]
  · exact ⟨hresult.decision,hresult.result_head,hresult.emitted⟩

theorem reject_tail {s : ℕ} (raw witness : List Bool) (base : Configuration 157 s)
    (hbad : ¬UFront.Accepted raw witness) (htape : base.tapes 156=[])
    (hhead : base.heads 156=0) :
    ∃ n final,n≤2 ∧
      Timed machine n (controlConfig (RecoveryCalls.code sizes 2)
        (Composition.restart base reject.start)) final ∧
      machine.halted final.control=true ∧ Outcome raw witness final := by
  obtain ⟨r,hr,hfinal,_⟩ := reject_run base
  obtain ⟨n,hn,hstop⟩ := stop_receipt sizes programs 0 next 2 1 _ r hr (by rfl)
  refine ⟨n,_,hn,hstop,?_,Or.inl ⟨hbad,?_⟩⟩
  · simp [machine,RecoveryCalls.machine,RecoveryCalls.stopped]
  · change r.final.scanned 156=false
    rw [hfinal]
    simp [rejected,Configuration.scanned,htape,hhead,writeTapeBit,readTapeBit]

end NearCubicWires.RepairOrdinary.UEmission
