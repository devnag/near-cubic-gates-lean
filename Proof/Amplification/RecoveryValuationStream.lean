import Proof.Amplification.RecoveryValuationStreamTapes

/-! Enclosing physical read-and-check of one serialized valuation row.
The real field reader advances the witness cursor, and its retained bytes
feed the first-match comparison before the success bit is written. -/
namespace NearCubicWires.RepairOrdinary.RecoveryValuationStream
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def flagMachine (bit : Bool) : Machine 8 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==1
  rule := fun q _ => if q.val=0 then
    some ⟨1,fun i=>if i=7 then some bit else none,fun _=>.stay⟩ else none

theorem flag_raw {s : Nat} (c : Configuration 8 s) (old bit : Bool)
    (hh : c.heads 7=0) (ht : c.tapes 7=[old]) :
    ∃ r : ExecutionReceipt 8 2,
      runFrom (flagMachine bit) 1 (RecoveryCalls.restarted (flagMachine bit) c.heads c.tapes)=some r ∧
      r.final=(⟨1,c.heads,Function.update c.tapes 7 [bit]⟩ : Configuration 8 2) ∧ r.steps=1 := by
  have hs : step (flagMachine bit) (RecoveryCalls.restarted (flagMachine bit) c.heads c.tapes)=
      some (⟨1,c.heads,Function.update c.tapes 7 [bit]⟩ : Configuration 8 2) := by
    apply congrArg some
    apply configuration_ext
    · rfl
    · rfl
    · funext i
      by_cases hi : i=7
      · subst i
        simp [applyAction,flagMachine,RecoveryCalls.restarted,hh,ht,writeTapeBit]
      · simp [applyAction,flagMachine,RecoveryCalls.restarted,hi]
  exact (Timed.single (by rfl) hs).run (by rfl)

private theorem update_eight (a b c d e f g z z' : List Bool) :
    Function.update (![a,b,c,d,e,f,g,z] : Fin 8→List Bool) 7 z'=![a,b,c,d,e,f,g,z'] := by
  funext i
  fin_cases i <;> simp

theorem flag_run (d : Data) (bit : Bool) :
    ∃ r : ExecutionReceipt 8 2,
      runFrom (flagMachine bit) 1 (d.cfg 0)=some r ∧
      r.final=({d with valid:=bit} : Data).cfg 1 ∧ r.steps=1 := by
  obtain ⟨r,hr,hf,ht⟩ := flag_raw (d.cfg (0 : Fin 2)) d.valid bit rfl rfl
  refine ⟨r,hr,?_,ht⟩
  rw [hf]
  apply configuration_ext
  · rfl
  · rfl
  · exact update_eight _ _ _ _ _ _ _ _ _

abbrev sizes : Fin 4→Nat := ![6,9,2,2]
noncomputable def programs : (j : Fin 4)→Machine 8 (sizes j)
  | ⟨0,_⟩=>fieldMachine
  | ⟨1,_⟩=>rowMachine
  | ⟨2,_⟩=>flagMachine true
  | ⟨3,_⟩=>flagMachine false
  | ⟨n+4,h⟩=>False.elim (by omega)
def next (j : Fin 4) (q : Fin (sizes j)) (_ : Fin 8→Bool) : Option (Fin 4) :=
  if j.val=0 then if q.val=4 then some 1 else some 3 else
    if j.val=1 then some 2 else none
noncomputable abbrev machine := RecoveryCalls.machine sizes programs 0 next

def Data.done (d : Data) (key : List Bool) (bit : Bool) : Data :=
  {(d.afterField (key++[bit])).afterRow key bit with valid:=true}
def budget (width : Nat) := 8*width+16

theorem success_run (d : Data) (pre key tail : List Bool) (bit : Bool)
    (hs : d.source=pre++Streaming.marks (key++[bit])++tail) (hp : d.pos=pre.length)
    (hi : d.index.length=d.width) (hw : key.length=d.width)
    (hb : d.row.length≤2*(d.width+1)+1) :
    ∃ r : ExecutionReceipt 8 (Fintype.card (RecoveryCalls.Control sizes)),
      runFrom machine (budget d.width) (d.cfg machine.start)=some r ∧
      r.final=(d.done key bit).cfg (RecoveryCalls.controlCode sizes none) ∧ r.steps≤budget d.width := by
  have hlen : (key++[bit]).length=d.width+1 := by simp [hw]
  obtain ⟨r0,hr0,hf0,_⟩ := field_run d pre (key++[bit]) tail hs hp hlen hb
  obtain ⟨n0,hn0,h0⟩ := call_receipt sizes programs 0 next 0 1 _ _ r0 hr0 (by rw [hf0]; rfl)
  rw [hf0] at h0
  change Timed machine n0 (d.cfg (RecoveryCalls.code sizes 0 (0 : Fin 6)))
    ((d.afterField (key++[bit])).cfg (RecoveryCalls.code sizes 1 rowMachine.start)) at h0
  obtain ⟨r1,hr1,hf1,_⟩ := row_run (d.afterField (key++[bit])) key bit (by simpa [Data.afterField] using hi.trans hw.symm) rfl
  obtain ⟨n1,hn1,h1⟩ := call_receipt sizes programs 0 next 1 2 _ _ r1 hr1 (by rfl)
  rw [hf1] at h1
  change Timed machine n1 ((d.afterField (key++[bit])).cfg (RecoveryCalls.code sizes 1 rowMachine.start))
    (((d.afterField (key++[bit])).afterRow key bit).cfg (RecoveryCalls.code sizes 2 (0 : Fin 2))) at h1
  obtain ⟨r2,hr2,hf2,_⟩ := flag_run ((d.afterField (key++[bit])).afterRow key bit) true
  obtain ⟨n2,hn2,h2⟩ := stop_receipt sizes programs 0 next 2 _ _ r2 hr2 (by rfl)
  rw [hf2] at h2
  change Timed machine n2 (((d.afterField (key++[bit])).afterRow key bit).cfg (RecoveryCalls.code sizes 2 (0 : Fin 2)))
    ((d.done key bit).cfg (RecoveryCalls.controlCode sizes none)) at h2
  have h := (h0.trans h1).trans h2
  have hn : n0+n1+n2≤budget d.width := by
    change n1≤4*d.index.length+6+1 at hn1
    rw [hi] at hn1
    unfold budget
    omega
  obtain ⟨r,hr,hf,ht⟩ := h.run (by simp [RecoveryCalls.machine,Data.cfg])
  have hm := runFrom_moreFuel machine (n0+n1+n2) (budget d.width-(n0+n1+n2)) _ r hr
  rw [Nat.add_sub_of_le hn] at hm
  exact ⟨r,hm,hf,ht.le.trans hn⟩

open private focus_configuration from Proof.Amplification.RecoveryValuationStreamTapes

theorem field_short (d : Data) (pre bits : List Bool)
    (hs : d.source=pre++frame bits) (hp : d.pos=pre.length)
    (hw : bits.length<d.width+1) (hb : d.row.length≤2*(d.width+1)+1) :
    ∃ r : ExecutionReceipt 8 6,
      runFrom fieldMachine (2*bits.length+1) (d.cfg 0)=some r ∧
      r.final.control=5 ∧ r.final.heads 7=0 ∧ r.final.tapes 7=[d.valid] ∧ r.steps=2*bits.length+1 := by
  obtain ⟨base,hr,hf,hsteps,_⟩ := RepairSource.VerifierDecoding.FieldMachine.field_reject_run
    pre bits d.row (d.width+1) hw hb
  obtain ⟨r,hrun,hfinal,hcount⟩ := RecoveryFocus.run_config fieldSlots fieldSlots_injective
    RepairSource.VerifierDecoding.FieldMachine.machine (d.cfg (0 : Fin 6)).heads (d.cfg (0 : Fin 6)).tapes _ _ base hr
  have hin : RecoveryFocus.config fieldSlots (d.cfg (0 : Fin 6)).heads (d.cfg (0 : Fin 6)).tapes
      (RepairSource.VerifierDecoding.FieldMachine.scan 0 (pre++frame bits) pre.length (d.width+1) 0 [] d.row)=d.cfg 0 := by
    apply focus_configuration fieldSlots fieldSlots_injective
    · rfl
    · intro j; fin_cases j <;> simp [RepairSource.VerifierDecoding.FieldMachine.scan,Data.cfg,fieldSlots,hp]
    · intro j; fin_cases j <;> simp [RepairSource.VerifierDecoding.FieldMachine.scan,Data.cfg,fieldSlots,hs,StablePartition.Workspace.overlay]
    · intro i _; rfl
    · intro i _; rfl
  rw [hin] at hrun
  have hnot : ¬∃ j,fieldSlots j=7 := by decide
  have h7 : RecoveryFocus.pick fieldSlots 7=none := by simp [RecoveryFocus.pick,hnot]
  refine ⟨r,hrun,?_,?_,?_,hcount.trans hsteps⟩
  · rw [hfinal,hf]; rfl
  · simp [hfinal,RecoveryFocus.config,h7,Data.cfg]
  · simp [hfinal,RecoveryFocus.config,h7,Data.cfg]

theorem failure_run (d : Data) (pre bits : List Bool)
    (hs : d.source=pre++frame bits) (hp : d.pos=pre.length)
    (hw : bits.length<d.width+1) (hb : d.row.length≤2*(d.width+1)+1) :
    ∃ r : ExecutionReceipt 8 (Fintype.card (RecoveryCalls.Control sizes)),
      runFrom machine (budget d.width) (d.cfg machine.start)=some r ∧
      r.final.tapes 7=[false] ∧ r.final.heads 7=0 ∧ r.steps≤budget d.width := by
  obtain ⟨r0,hr0,hc0,hh0,ht0,_⟩ := field_short d pre bits hs hp hw hb
  obtain ⟨n0,hn0,h0⟩ := call_receipt sizes programs 0 next 0 3 _ _ r0 hr0 (by rw [hc0]; rfl)
  obtain ⟨r1,hr1,hf1,_⟩ := flag_raw r0.final d.valid false hh0 ht0
  obtain ⟨n1,hn1,h1⟩ := stop_receipt sizes programs 0 next 3 _ _ r1 hr1 (by rfl)
  have h := h0.trans h1
  have hn : n0+n1≤budget d.width := by unfold budget; omega
  obtain ⟨r,hr,hf,ht⟩ := h.run (by simp [RecoveryCalls.machine,RecoveryCalls.stopped])
  have hm := runFrom_moreFuel machine (n0+n1) (budget d.width-(n0+n1)) _ r hr
  rw [Nat.add_sub_of_le hn] at hm
  exact ⟨r,hm,by simp [hf,hf1,RecoveryCalls.stopped],
    by simpa [hf,hf1,RecoveryCalls.stopped] using hh0,ht.le.trans hn⟩

end NearCubicWires.RepairOrdinary.RecoveryValuationStream
