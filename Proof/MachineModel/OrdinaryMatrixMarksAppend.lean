import Proof.MachineModel.OrdinaryMatrixSignedEntryRetained

/-! Append framed marks for a raw matrix block using its physical finite
length sentinel. This leaves the global append cursor streaming and restores
the length driver; the enclosing Williams serializer writes one final false. -/
namespace NearCubicWires.RepairOrdinary.MatrixMarksAppend
open LocalBitMultitape RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def cfg {s : ℕ} (q : Fin s) (count dh : ℕ) (source : List Bool) (pos : ℕ) (out : List Bool) : Configuration 3 s :=
  ⟨q,![dh,pos,out.length],![UnaryTemplate.tape count,source,out]⟩
def raw : Machine 3 3 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==2
  rule := fun q scan => if q.val=0 then
      some (if scan 0 then ⟨1,![none,none,some true],![.stay,.stay,.right]⟩
        else ⟨2,fun _ => none,fun _ => .stay⟩)
    else if q.val=1 then some ⟨0,![none,none,some (scan 1)],fun _ => .right⟩ else none

theorem mark_step (count done : ℕ) (source out : List Bool) (pos : ℕ) (hc : done<count) :
    step raw (cfg 0 count (done+1) source pos out)=some (cfg 1 count (done+1) source pos (out++[true])) := by
  simp [step,raw,cfg,Configuration.scanned,UnaryTemplate.tape_mark count done hc]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction,Streaming.write_append]

theorem bit_step (count done : ℕ) (pre tail out : List Bool) (bit : Bool) :
    step raw (cfg 1 count (done+1) (pre++bit::tail) pre.length out)=
      some (cfg 0 count (done+2) (pre++bit::tail) (pre.length+1) (out++[bit])) := by
  simp [step,raw,cfg,Configuration.scanned,Streaming.read_append]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction,Streaming.write_append]

theorem stop_step (count : ℕ) (source out : List Bool) (pos : ℕ) :
    step raw (cfg 0 count (count+1) source pos out)=some (cfg 2 count (count+1) source pos out) := by
  simp [step,raw,cfg,Configuration.scanned]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
  · rfl

theorem raw_prefix (bits pre suffix out : List Bool) (count done : ℕ) (hc : done+bits.length=count) :
    Timed raw (2*bits.length+1)
      (cfg 0 count (done+1) (pre++bits++suffix) pre.length out)
      (cfg 2 count (count+1) (pre++bits++suffix) (pre.length+bits.length) (out++Streaming.marks bits)) := by
  induction bits generalizing pre out done with
  | nil =>
    have hd : done=count := by simpa using hc
    subst done
    simpa [Streaming.marks] using Timed.single (by rfl) (stop_step count (pre++suffix) out pre.length)
  | cons bit bits ih =>
    have h0 := Timed.single (by rfl) (mark_step count done (pre++bit::bits++suffix) out pre.length (by simp only [List.length_cons] at hc; omega))
    simp only [List.append_assoc,List.cons_append] at h0
    have h1 := Timed.single (by rfl) (bit_step count done pre (bits++suffix) (out++[true]) bit)
    have ht := ih (pre++[bit]) (out++[true,bit]) (done+1) (by simp only [List.length_cons] at hc; omega)
    have hh := h0.trans (h1.trans (by simpa [List.append_assoc,Nat.add_assoc] using ht))
    have htime : 1+(1+(2*bits.length+1))=2*(bit::bits).length+1 := by simp; omega
    rw [htime] at hh
    simpa [Streaming.marks,List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh

def reset : Machine 3 3 := TapeEmbedding.machine 2 UnaryTemplate.machine
def machine := Composition.machine raw reset

theorem append_run (bits pre suffix out : List Bool) : ∃ actual,
    runFrom machine (3*bits.length+4) (cfg machine.start bits.length 1 (pre++bits++suffix) pre.length out)=some actual ∧
    actual.final=cfg 5 bits.length 1 (pre++bits++suffix) (pre.length+bits.length) (out++Streaming.marks bits) ∧
    actual.steps=3*bits.length+4 := by
  obtain ⟨base,hb,bf,bs⟩ := (raw_prefix bits pre suffix out bits.length 0 (by omega)).run (by rfl)
  obtain ⟨body,hr,rf,rs,_⟩ := UnaryTemplate.reset_run bits.length
  let extraT : Fin 2 → List Bool := ![pre++bits++suffix,out++Streaming.marks bits]
  let extraH : Fin 2 → ℕ := ![pre.length+bits.length,(out++Streaming.marks bits).length]
  have he := TapeEmbedding.run_embed UnaryTemplate.machine extraH extraT _ _ body hr
  let resetReceipt := TapeEmbedding.receipt extraH extraT body
  have hi : TapeEmbedding.config extraH extraT (UnaryTemplate.config 0 (UnaryTemplate.tape bits.length) (bits.length+1))=
      Composition.restart base.final reset.start := by
    rw [bf]
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  rw [hi] at he
  have hj := Composition.run_join raw reset _ _ _ base resetReceipt hb he
  have hn : 2*bits.length+1+1+(bits.length+2)=3*bits.length+4 := by omega
  rw [hn] at hj
  refine ⟨Composition.joinedReceipt base resetReceipt,hj,?_,?_⟩
  · change Composition.rightConfig 3 (TapeEmbedding.config extraH extraT body.final)=_
    rw [rf]
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  · change base.steps+1+body.steps=_
    omega

end NearCubicWires.RepairOrdinary.MatrixMarksAppend
