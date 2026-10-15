import Proof.Amplification.RecoveryCursorCalls

/-! Literal streaming layouts joining the certificate field reader to the
first-match row checker. The source cursor and unary width cursor survive
the inner row comparison at their actual positions. -/
namespace NearCubicWires.RepairOrdinary.RecoveryValuationStream
open LocalBitMultitape RecoveryExecution RecoveryRootRound RadixSemantics
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

structure Data where
  source : List Bool
  pos : Nat
  width : Nat
  index : List Bool
  row : List Bool
  found : Bool
  value : Bool
  valid : Bool
  capacity : Nat

def Data.cfg {s : Nat} (d : Data) (q : Fin s) : Configuration 8 s :=
  ⟨q,![d.pos,0,1,0,0,0,0,0],![d.source,d.row,CompareMachine.word (d.width+1),
    frame d.index,[d.found],[d.value],List.replicate d.capacity false,[d.valid]]⟩
def fieldSlots : Fin 3→Fin 8 := ![0,1,2]
def rowSlots : Fin 5→Fin 8 := ![3,1,4,5,6]
theorem fieldSlots_injective : Function.Injective fieldSlots := by decide
theorem rowSlots_injective : Function.Injective rowSlots := by decide
noncomputable def fieldMachine := RecoveryFocus.machine fieldSlots FieldMachine.machine
noncomputable def rowMachine := RecoveryFocus.machine rowSlots RecoveryValuationRow.machine

private theorem focus_configuration {t u s : Nat} (slots : Fin t→Fin u) (hinj : Function.Injective slots)
    (heads : Fin u→Nat) (tapes : Fin u→List Bool) (inner : Configuration t s) (target : Configuration u s)
    (hc : inner.control=target.control)
    (hh : ∀ j,inner.heads j=target.heads (slots j))
    (ht : ∀ j,inner.tapes j=target.tapes (slots j))
    (hoh : ∀ i,(∀ j,slots j≠i)→heads i=target.heads i)
    (hot : ∀ i,(∀ j,slots j≠i)→tapes i=target.tapes i) :
    RecoveryFocus.config slots heads tapes inner=target := by
  apply configuration_ext
  · exact hc
  · funext i
    cases hp : RecoveryFocus.pick slots i with
    | some j =>
      have hi := RecoveryFocus.slot_of_pick slots hp
      simpa only [RecoveryFocus.config,hp] using (hh j).trans (congrArg target.heads hi)
    | none =>
      simp only [RecoveryFocus.config,hp]
      exact hoh i (by intro j he; subst i; rw [RecoveryFocus.pick_slot slots hinj] at hp; contradiction)
  · funext i
    cases hp : RecoveryFocus.pick slots i with
    | some j =>
      have hi := RecoveryFocus.slot_of_pick slots hp
      simpa only [RecoveryFocus.config,hp] using (ht j).trans (congrArg target.tapes hi)
    | none =>
      simp only [RecoveryFocus.config,hp]
      exact hot i (by intro j he; subst i; rw [RecoveryFocus.pick_slot slots hinj] at hp; contradiction)

def Data.afterField (d : Data) (bits : List Bool) : Data :=
  {d with pos:=d.pos+2*bits.length,row:=frame bits}

theorem field_run (d : Data) (pre bits tail : List Bool)
    (hs : d.source=pre++Streaming.marks bits++tail) (hp : d.pos=pre.length)
    (hw : bits.length=d.width+1) (hb : d.row.length≤2*(d.width+1)+1) :
    ∃ r : ExecutionReceipt 8 6,
      runFrom fieldMachine (4*(d.width+1)+2) (d.cfg 0)=some r ∧
      r.final=(d.afterField bits).cfg 4 ∧ r.steps=4*(d.width+1)+2 := by
  obtain ⟨base,hr,hf,hsteps,_⟩ := FieldMachine.field_run pre bits tail d.row (by rw [hw]; exact hb)
  obtain ⟨r,hrun,hfinal,hcount⟩ := RecoveryFocus.run_config fieldSlots fieldSlots_injective
    FieldMachine.machine (d.cfg (0 : Fin 6)).heads (d.cfg (0 : Fin 6)).tapes _ _ base hr
  have hin : RecoveryFocus.config fieldSlots (d.cfg (0 : Fin 6)).heads (d.cfg (0 : Fin 6)).tapes
      (FieldMachine.scan 0 (pre++Streaming.marks bits++tail) pre.length bits.length 0 [] d.row)=d.cfg 0 := by
    apply focus_configuration fieldSlots fieldSlots_injective
    · rfl
    · intro j; fin_cases j <;> simp [FieldMachine.scan,Data.cfg,fieldSlots,hp]
    · intro j; fin_cases j <;> simp [FieldMachine.scan,Data.cfg,fieldSlots,hs,hw,StablePartition.Workspace.overlay]
    · intro i _; rfl
    · intro i _; rfl
  rw [hin,hw] at hrun
  refine ⟨r,hrun,?_,by rw [hcount,hsteps,hw]⟩
  rw [hfinal,hf]
  apply focus_configuration fieldSlots fieldSlots_injective
  · rfl
  · intro j; fin_cases j <;> simp [FieldMachine.finished,Data.cfg,fieldSlots,Data.afterField,hp]
  · intro j; fin_cases j <;> simp [FieldMachine.finished,Data.cfg,fieldSlots,Data.afterField,hs,hw]
  · intro i hi; fin_cases i <;> first | rfl | exact False.elim (hi 0 rfl)
  · intro i hi; fin_cases i <;> first | rfl | exact False.elim (hi 1 rfl)

def Data.afterMatch (d : Data) (eq bit : Bool) : Data :=
  {d with
    found:=RecoveryValuationRow.matched d.found eq
    value:=RecoveryValuationRow.selected d.found eq bit d.value
    capacity:=max d.capacity (2*d.index.length+2)}
def Data.afterRow (d : Data) (key : List Bool) (bit : Bool) : Data :=
  d.afterMatch (decide (RadixSemantics.value d.index=RadixSemantics.value key)) bit

theorem row_input (d : Data) (key : List Bool) (bit : Bool) (hr : d.row=frame (key++[bit])) :
    RecoveryFocus.config rowSlots (d.cfg rowMachine.start).heads (d.cfg rowMachine.start).tapes
      (initialConfiguration RecoveryValuationRow.machine
        ![frame d.index,frame (key++[bit]),[d.found],[d.value],List.replicate d.capacity false])=
      d.cfg rowMachine.start := by
  apply focus_configuration rowSlots rowSlots_injective
  · rfl
  · intro j; fin_cases j <;> rfl
  · intro j; fin_cases j <;> simp [initialConfiguration,Data.cfg,rowSlots,hr]
  · intro i _; rfl
  · intro i _; rfl

def rowResult (d : Data) (key : List Bool) (bit eq : Bool) (q : Fin 9) : Configuration 5 9 :=
  ⟨q,fun _=>0,
    ![frame d.index,frame (key++[bit]),[RecoveryValuationRow.matched d.found eq],
      [RecoveryValuationRow.selected d.found eq bit d.value],
      List.replicate (max d.capacity (2*d.index.length+2)) false]⟩

theorem row_result_heads (d : Data) (key : List Bool) (bit eq : Bool) (q : Fin 9) (j : Fin 5) :
    (rowResult d key bit eq q).heads j=((d.afterMatch eq bit).cfg q).heads (rowSlots j) := by
  fin_cases j <;> rfl

theorem row_result_tapes (d : Data) (key : List Bool) (bit eq : Bool) (q : Fin 9)
    (hr : d.row=frame (key++[bit])) (j : Fin 5) :
    (rowResult d key bit eq q).tapes j=((d.afterMatch eq bit).cfg q).tapes (rowSlots j) := by
  fin_cases j <;> simp [rowResult,Data.cfg,Data.afterMatch,rowSlots,hr]

private theorem unchanged_eight (a b c d e f g z e' f' g' : List Bool) (i : Fin 8)
    (h4 : i≠4) (h5 : i≠5) (h6 : i≠6) :
    ![a,b,c,d,e,f,g,z] i=![a,b,c,d,e',f',g',z] i := by
  fin_cases i <;> first | rfl | contradiction

theorem row_outside_tapes (d : Data) (bit eq : Bool) (q : Fin 9) (i : Fin 8)
    (hi : ∀ j,rowSlots j≠i) :
    (d.cfg rowMachine.start).tapes i=((d.afterMatch eq bit).cfg q).tapes i := by
  exact unchanged_eight _ _ _ _ _ _ _ _ _ _ _ i
    (Ne.symm (hi 2)) (Ne.symm (hi 3)) (Ne.symm (hi 4))

theorem row_output_bits (d : Data) (key : List Bool) (bit eq : Bool) (hr : d.row=frame (key++[bit]))
    (q : Fin 9) :
    RecoveryFocus.config rowSlots (d.cfg rowMachine.start).heads (d.cfg rowMachine.start).tapes
      (⟨q,fun _=>0,
        ![frame d.index,frame (key++[bit]),
          [RecoveryValuationRow.matched d.found eq],
          [RecoveryValuationRow.selected d.found eq bit d.value],
          List.replicate (max d.capacity (2*d.index.length+2)) false]⟩ : Configuration 5 9)=
      (d.afterMatch eq bit).cfg q := by
  exact focus_configuration rowSlots rowSlots_injective _ _ (rowResult d key bit eq q) _ rfl
    (row_result_heads d key bit eq q) (row_result_tapes d key bit eq q hr)
    (by intro i _; rfl) (row_outside_tapes d bit eq q)

theorem row_output (d : Data) (key : List Bool) (bit : Bool) (hr : d.row=frame (key++[bit]))
    (q : Fin 9) :
    RecoveryFocus.config rowSlots (d.cfg rowMachine.start).heads (d.cfg rowMachine.start).tapes
      (⟨q,fun _=>0,
        ![frame d.index,frame (key++[bit]),
          [RecoveryValuationRow.matched d.found (decide (RadixSemantics.value d.index=RadixSemantics.value key))],
          [RecoveryValuationRow.selected d.found (decide (RadixSemantics.value d.index=RadixSemantics.value key)) bit d.value],
          List.replicate (max d.capacity (2*d.index.length+2)) false]⟩ : Configuration 5 9)=
      (d.afterRow key bit).cfg q :=
  row_output_bits d key bit (decide (RadixSemantics.value d.index=RadixSemantics.value key)) hr q

theorem row_run (d : Data) (key : List Bool) (bit : Bool)
    (hw : d.index.length=key.length) (hr : d.row=frame (key++[bit])) :
    ∃ r : ExecutionReceipt 8 9,
      runFrom rowMachine (4*d.index.length+6) (d.cfg rowMachine.start)=some r ∧
      r.final=(d.afterRow key bit).cfg r.final.control ∧ r.steps=4*d.index.length+6 := by
  obtain ⟨base,hbase,ht,hh,hsteps⟩ := RecoveryValuationRow.row_ready d.index key d.found d.value bit d.capacity hw
  obtain ⟨r,hrun,hfinal,hcount⟩ := RecoveryFocus.run_config rowSlots rowSlots_injective
    RecoveryValuationRow.machine (d.cfg rowMachine.start).heads (d.cfg rowMachine.start).tapes _ _ base hbase
  rw [row_input d key bit hr] at hrun
  have he : base.final=(⟨base.final.control,fun _=>0,
      ![frame d.index,frame (key++[bit]),
        [RecoveryValuationRow.matched d.found (decide (RadixSemantics.value d.index=RadixSemantics.value key))],
        [RecoveryValuationRow.selected d.found (decide (RadixSemantics.value d.index=RadixSemantics.value key)) bit d.value],
        List.replicate (max d.capacity (2*d.index.length+2)) false]⟩ : Configuration 5 9) := by
    apply configuration_ext
    · rfl
    · exact funext hh
    · exact ht
  have hf := hfinal
  rw [he,row_output d key bit hr] at hf
  exact ⟨r,hrun,by rw [hf]; rfl,hcount.trans hsteps⟩

end NearCubicWires.RepairOrdinary.RecoveryValuationStream
