import Proof.PCP.ProjectionNormalizationQueryReady

/-! Raw source headers feed the complete physical driver producer. The
source remains at the first query field throughout the arithmetic calls. -/
namespace NearCubicWires.RepairSource.ProjectionNormalization.StreamPrepare
open SourceInterfaces ExecutableInterfaces LocalBitMultitape RepairOrdinary RecoveryExecution VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def extras (R Q : ℕ) : Fin 16 → List Bool := fun i =>
  if i=0 then List.replicate R true else if i=1 then List.replicate Q true else []
noncomputable def input (p : RawProjectionPCP) (R Q : ℕ) : Fin 29 → List Bool :=
  Fin.addCases (motive := fun _ : Fin (13+16) => List Bool) (Header.input p.word) (extras R Q)
def slots : Fin 18 → Fin 29 := ![13,14,5,11,15,16,17,18,19,20,21,22,23,24,25,26,27,28]
theorem slots_injective : Function.Injective slots := by decide
noncomputable def headers := TapeEmbedding.machine 16 Header.machine
def retreat : Machine 29 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==1
  rule := fun q _ => if q.val=0 then some ⟨1,fun _ => none,
    fun i => if i=5 ∨ i=11 then .left else .stay⟩ else none
noncomputable def prefixMachine := Composition.machine headers retreat
noncomputable def driverProgram := RecoveryFocus.machine slots Drivers.machine
noncomputable def machine := Composition.machine prefixMachine driverProgram
def budget (p : RawProjectionPCP) (R Q : ℕ) := Header.budget p.width.bits p.queries.bits+3+Drivers.budget R Q p.queries
def Fields (p : RawProjectionPCP) (R Q : ℕ) (tapes : Fin 29 → List Bool) : Prop :=
  tapes 0=p.word ∧ Drivers.Fields R Q p.width p.queries (fun i => tapes (slots i))

theorem retreat_run (c : Configuration 29 2) (hc : c.control=0) :
    ∃ r,runFrom retreat 1 c=some r ∧ r.final.tapes=c.tapes ∧
      (∀ i,r.final.heads i=if i=5 ∨ i=11 then c.heads i-1 else c.heads i) ∧ r.steps=1 := by
  let f : Configuration 29 2 := ⟨1,(fun i => if i=5 ∨ i=11 then c.heads i-1 else c.heads i),c.tapes⟩
  have h : step retreat c=some f := by
    simp [step,retreat,hc]
    apply configuration_ext
    · rfl
    · funext i; by_cases hi : i=5 ∨ i=11 <;> simp [applyAction,HeadMove.apply,f,hi]
    · rfl
  obtain ⟨r,hr,hf,hs⟩ := (Timed.single (by simp [retreat,hc]) h).run (by rfl)
  exact ⟨r,hr,by rw [hf],by intro i; rw [hf],hs⟩

def headerHeads (pos : ℕ) : Fin 13 → ℕ := fun i => if i=0 then pos else if i=5 ∨ i=11 then 1 else 0
def embeddedHeads (pos : ℕ) : Fin 29 → ℕ := fun i => if i=0 then pos else if i=5 ∨ i=11 then 1 else 0
def sourceHeads (pos : ℕ) : Fin 29 → ℕ := fun i => if i=0 then pos else 0

theorem heads_embed (pos : ℕ) :
    Fin.addCases (motive := fun _ : Fin (13+16) => ℕ) (headerHeads pos) (fun _ : Fin 16 => 0)=embeddedHeads pos := by
  funext i; fin_cases i <;> rfl

theorem heads_retreat (pos : ℕ) :
    (fun i : Fin 29 => if i=5 ∨ i=11 then embeddedHeads pos i-1 else embeddedHeads pos i)=sourceHeads pos := by
  funext i; fin_cases i <;> rfl

theorem bank_input (R Q r q : ℕ) (data : Fin 13 → List Bool)
    (h5 : data 5=CompareMachine.word r) (h11 : data 11=CompareMachine.word q) :
    (fun i => Fin.addCases data (extras R Q) (slots i))=Drivers.input R Q r q := by
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact h5
  · exact h11
  all_goals rfl

theorem embed_initial {t e s : ℕ} (p : Machine t s) (data : Fin t → List Bool) (extra : Fin e → List Bool) :
    TapeEmbedding.config (fun _ : Fin e => 0) extra (initialConfiguration p data)=
      initialConfiguration (TapeEmbedding.machine e p)
        (Fin.addCases (motive := fun _ : Fin (t+e) => List Bool) data extra) := by
  apply configuration_ext
  · rfl
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
      simp [TapeEmbedding.config,initialConfiguration]
  · rfl

theorem prefix_run (p : RawProjectionPCP) (R Q : ℕ) :
    ∃ r,run prefixMachine (Header.budget p.width.bits p.queries.bits+2) (input p R Q)=some r ∧
      r.steps ≤ Header.budget p.width.bits p.queries.bits+2 ∧ r.final.tapes 0=p.word ∧
      (∀ i,r.final.tapes (slots i)=Drivers.input R Q p.width p.queries i) ∧
      (∀ i,r.final.heads i=if i=0 then (QueryBytes.header p).length else 0) := by
  have hword : Header.source p.width.bits p.queries.bits
      (Rows.stream (QueryBytes.rowsBits (queryRows p))++QueryBytes.suffix p)=p.word := by
    rw [QueryBytes.source_split p]
    simp [Header.source,QueryBytes.header,List.append_assoc]
  obtain ⟨base,hbase,hsource,hwidth,hqueries,hheads,hsteps⟩ := Header.headers_run p.width.bits p.queries.bits
    (Rows.stream (QueryBytes.rowsBits (queryRows p))++QueryBytes.suffix p)
  rw [hword] at hbase hsource
  rw [RecoveryUnpair.bits_value] at hwidth hqueries
  let a := TapeEmbedding.receipt (fun _ : Fin 16 => 0) (extras R Q) base
  have ha := TapeEmbedding.run_embed Header.machine (fun _ : Fin 16 => 0) (extras R Q) _ _ base hbase
  rw [embed_initial] at ha
  have haheads : a.final.heads=embeddedHeads (QueryBytes.header p).length := by
    have hh : base.final.heads=headerHeads (QueryBytes.header p).length := funext hheads
    change Fin.addCases (motive := fun _ : Fin (13+16) => ℕ) base.final.heads (fun _ : Fin 16 => 0)=_
    rw [hh]
    exact heads_embed _
  obtain ⟨b,hb,hbt,hbh,hbs⟩ := retreat_run (Composition.restart a.final retreat.start) rfl
  have hAB := Composition.run_join headers retreat _ 1 _ a b ha hb
  let ab := Composition.joinedReceipt a b
  have habhead (i : Fin 29) : ab.final.heads i=if i=0 then (QueryBytes.header p).length else 0 := by
    change b.final.heads i=_
    rw [hbh]
    change (if i=5 ∨ i=11 then a.final.heads i-1 else a.final.heads i)=_
    rw [haheads]
    exact congrFun (heads_retreat _) i
  refine ⟨ab,hAB,?_,?_,?_,habhead⟩
  · change base.steps+1+b.steps ≤ _
    omega
  · change b.final.tapes 0=p.word
    rw [hbt]
    exact hsource
  · intro i
    change b.final.tapes (slots i)=Drivers.input R Q p.width p.queries i
    rw [hbt]
    exact congrFun (bank_input R Q p.width p.queries base.final.tapes hwidth hqueries) i

theorem prepare_run (p : RawProjectionPCP) (R Q : ℕ) (hr : p.width ≤ R) (hq : p.queries ≤ Q) :
    ∃ r,run machine (budget p R Q) (input p R Q)=some r ∧ r.steps ≤ budget p R Q ∧
      Fields p R Q r.final.tapes ∧
      (∀ i,r.final.heads i=if i=0 then (QueryBytes.header p).length else 0) := by
  obtain ⟨ab,hAB,habs,hsource,habinput,habhead⟩ := prefix_run p R Q
  obtain ⟨out,⟨localRun,hl,hlt,hlh,hls⟩,hfields⟩ := Drivers.drivers_run R Q p.width p.queries hr hq
  obtain ⟨c,hc,hcf,hcs⟩ := RecoveryFocus.run_config slots slots_injective Drivers.machine
    ab.final.heads ab.final.tapes _ _ localRun hl
  have he : RecoveryFocus.config slots ab.final.heads ab.final.tapes
      (initialConfiguration Drivers.machine (Drivers.input R Q p.width p.queries))=
      Composition.restart ab.final driverProgram.start := by
    apply TransitionEvent.focused_eq slots slots_injective (Composition.restart ab.final driverProgram.start)
    · rfl
    · intro i
      change 0=ab.final.heads (slots i)
      rw [habhead]
      fin_cases i <;> rfl
    · intro i
      exact (habinput i).symm
    · intro i _; rfl
    · intro i _; rfl
  rw [he] at hc
  have h := Composition.run_join prefixMachine driverProgram _ _ _ ab c hAB hc
  have htime : (Header.budget p.width.bits p.queries.bits+2)+1+Drivers.budget R Q p.queries=budget p R Q := by rfl
  rw [htime] at h
  refine ⟨Composition.joinedReceipt ab c,h,?_,?_,?_⟩
  · change ab.steps+1+c.steps ≤ _
    dsimp only [budget]
    omega
  · constructor
    · change c.final.tapes 0=p.word
      rw [hcf]
      have hp : RecoveryFocus.pick slots 0=none := by
        simp [RecoveryFocus.pick,show ¬∃ i,slots i=0 by decide]
      simpa only [RecoveryFocus.config,hp] using hsource
    · change Drivers.Fields R Q p.width p.queries (fun i => c.final.tapes (slots i))
      have ht : (fun i => c.final.tapes (slots i))=out := by
        funext i
        simp [hcf,RecoveryFocus.config,RecoveryFocus.pick_slot slots slots_injective,hlt]
      rw [ht]
      exact hfields
  · intro i
    change c.final.heads i=_
    rw [hcf]
    by_cases hi : ∃ j,slots j=i
    · obtain ⟨j,rfl⟩ := hi
      simp only [RecoveryFocus.config,RecoveryFocus.pick_slot slots slots_injective]
      rw [hlh]
      fin_cases j <;> rfl
    · have hp : RecoveryFocus.pick slots i=none := by simp [RecoveryFocus.pick,hi]
      simpa only [RecoveryFocus.config,hp] using habhead i

end NearCubicWires.RepairSource.ProjectionNormalization.StreamPrepare
