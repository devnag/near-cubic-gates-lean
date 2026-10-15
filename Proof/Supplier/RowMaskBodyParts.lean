import Proof.Supplier.RowMaskIndexAppend

/-! Physical monomial-mask workspace: source cursor, occurrence-index
template, live occurrence word, and live occurrence-count sentinel. -/
namespace NearCubicWires.RepairOrdinary.RowMaskBodyParts
open LocalBitMultitape RecoveryExecution Streaming RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def cfg {s : ℕ} (q : Fin s) (source : List Bool) (pos j count : ℕ) (out : List Bool) : Configuration 4 s :=
  ⟨q,![pos,1,out.length,count+1],![source,UnaryTemplate.tape j,out,CompareMachine.word count]⟩
def appendSlots : Fin 2→Fin 4 := ![1,2]
theorem append_injective : Function.Injective appendSlots := by decide
noncomputable def appendMachine := RecoveryFocus.machine appendSlots RowMaskIndexAppend.machine
theorem append_pick (i : Fin 4) : RecoveryFocus.pick appendSlots i=
    if i=1 then some 0 else if i=2 then some 1 else none := by
  fin_cases i
  all_goals
    first
    | exact RecoveryFocus.pick_slot appendSlots append_injective 0
    | exact RecoveryFocus.pick_slot appendSlots append_injective 1
    | decide

theorem append_run (source : List Bool) (pos j count : ℕ) (out : List Bool) :
    ∃ r,runFrom appendMachine (2*j+4) (cfg appendMachine.start source pos j count out)=some r ∧
      r.final=cfg 4 source pos j count (out++RowIndexField.word j) ∧ r.steps=2*j+4 := by
  obtain ⟨base,hbase,bf,bs⟩ := RowMaskIndexAppend.append_run j out
  let ambient := cfg appendMachine.start source pos j count out
  obtain ⟨r,hr,rf,rs⟩ := RecoveryFocus.run_config appendSlots append_injective RowMaskIndexAppend.machine
    ambient.heads ambient.tapes _ _ base hbase
  have hi : RecoveryFocus.config appendSlots ambient.heads ambient.tapes
      (RowMaskIndexAppend.cfg RowMaskIndexAppend.machine.start j 1 out)=ambient := by
    apply WilliamsSourceCrop.focus_same
    · intro i; fin_cases i <;> rfl
    · intro i; fin_cases i <;> rfl
  rw [hi] at hr
  refine ⟨r,hr,?_,rs.trans bs⟩
  rw [rf,bf]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [RecoveryFocus.config,append_pick,ambient,cfg,RowMaskIndexAppend.cfg]
  · funext i; fin_cases i <;> simp [RecoveryFocus.config,append_pick,ambient,cfg,RowMaskIndexAppend.cfg]

def indexSlots : Fin 1→Fin 4 := fun _=>1
theorem index_injective : Function.Injective indexSlots := by intro a b _; exact Subsingleton.elim _ _
noncomputable def indexMachine := RecoveryFocus.machine indexSlots RowCoordinateIncrement.machine
theorem index_pick (i : Fin 4) : RecoveryFocus.pick indexSlots i=if i=1 then some 0 else none := by
  fin_cases i
  all_goals first | exact RecoveryFocus.pick_slot indexSlots index_injective 0 | decide

theorem index_run (source : List Bool) (pos j count : ℕ) (out : List Bool) :
    ∃ r,runFrom indexMachine (2*j+9) (cfg indexMachine.start source pos j count out)=some r ∧
      r.final.heads=(cfg indexMachine.start source pos (j+1) count out).heads ∧
      r.final.tapes=(cfg indexMachine.start source pos (j+1) count out).tapes ∧ r.steps=2*j+9 := by
  obtain ⟨base,hbase,bh,bt,bs⟩ := RowCoordinateIncrement.increment_run j
  let ambient := cfg indexMachine.start source pos j count out
  obtain ⟨r,hr,rf,rs⟩ := RecoveryFocus.run_config indexSlots index_injective RowCoordinateIncrement.machine
    ambient.heads ambient.tapes _ _ base hbase
  have hi : RecoveryFocus.config indexSlots ambient.heads ambient.tapes
      (RowCoordinateIncrement.cfg RowCoordinateIncrement.machine.start 1 (UnaryTemplate.tape j))=ambient := by
    apply WilliamsSourceCrop.focus_same
    · intro i; rfl
    · intro i; rfl
  rw [hi] at hr
  refine ⟨r,hr,?_,?_,rs.trans bs⟩
  · rw [rf]
    simp only [RecoveryFocus.config,bh]
    funext i; fin_cases i <;> simp [index_pick,ambient,cfg]
  · rw [rf]
    change RecoveryRootRound.install indexSlots ambient.tapes base.final.tapes=_
    rw [bt]
    funext i; fin_cases i <;> simp [RecoveryRootRound.install,index_pick,ambient,cfg]

def moveMachine : Machine 4 2 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val==1
  rule := fun q bits=>if q.val=0 then some ⟨1,
    ![none,none,none,if bits 0 then some true else none],
    ![.right,.stay,.stay,if bits 0 then .right else .stay]⟩ else none

theorem move_run (pre tail : List Bool) (bit : Bool) (j count : ℕ) (out : List Bool) :
    ∃ r,runFrom moveMachine 1 (cfg 0 (pre++bit::tail) pre.length j count out)=some r ∧
      r.final=cfg 1 (pre++bit::tail) (pre.length+1) j (count+bit.toNat) out ∧ r.steps=1 := by
  have hs : step moveMachine (cfg 0 (pre++bit::tail) pre.length j count out)=
      some (cfg 1 (pre++bit::tail) (pre.length+1) j (count+bit.toNat) out) := by
    simp [step,moveMachine,cfg,Configuration.scanned,read_append]
    cases bit <;> apply configuration_ext
    all_goals first
      | rfl
      | (funext i; fin_cases i <;> simp [applyAction,HeadMove.apply,Bool.toNat])
    all_goals simpa [CompareMachine.word,List.replicate_add] using
      write_append (false::List.replicate count true) true
  exact (Timed.single (by rfl) hs).run (by rfl)

noncomputable def tailMachine := Composition.machine indexMachine moveMachine
theorem tail_run (pre tail : List Bool) (bit : Bool) (j count : ℕ) (out : List Bool) :
    ∃ r,runFrom tailMachine (2*j+11) (cfg tailMachine.start (pre++bit::tail) pre.length j count out)=some r ∧
      r.final.heads=(cfg tailMachine.start (pre++bit::tail) (pre.length+1) (j+1) (count+bit.toNat) out).heads ∧
      r.final.tapes=(cfg tailMachine.start (pre++bit::tail) (pre.length+1) (j+1) (count+bit.toNat) out).tapes ∧
      r.steps=2*j+11 := by
  obtain ⟨a,ha,ah,atapes,as⟩ := index_run (pre++bit::tail) pre.length j count out
  obtain ⟨b,hb,bf,bs⟩ := move_run pre tail bit (j+1) count out
  have hi : Composition.restart a.final moveMachine.start=cfg 0 (pre++bit::tail) pre.length (j+1) count out := by
    apply configuration_ext
    · rfl
    · exact ah
    · exact atapes
  rw [←hi] at hb
  have h := Composition.run_join indexMachine moveMachine _ _ _ a b ha hb
  have ht : 2*j+9+1+1=2*j+11 := by omega
  rw [ht] at h
  refine ⟨Composition.joinedReceipt a b,h,?_,?_,?_⟩
  · change b.final.heads=_; rw [bf]; rfl
  · change b.final.tapes=_; rw [bf]; rfl
  · change a.steps+1+b.steps=_; rw [as,bs,ht]

end NearCubicWires.RepairOrdinary.RowMaskBodyParts
