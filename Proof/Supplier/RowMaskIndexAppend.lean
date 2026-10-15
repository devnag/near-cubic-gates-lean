import Proof.Supplier.RowTupleAdvance

/-! A selected monomial-mask bit appends the current positional index in
the exact internal occurrence format consumed by the common row bank. -/
namespace NearCubicWires.RepairOrdinary.RowMaskIndexAppend
open LocalBitMultitape RecoveryExecution Streaming
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def copy : Machine 2 2 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val==1
  rule := fun q bits=>if q.val=0 then some (if bits 0 then
    ⟨0,![none,some true],![.right,.right]⟩ else ⟨1,![none,some false],![.stay,.right]⟩) else none
def cfg {s : ℕ} (q : Fin s) (n pos : ℕ) (out : List Bool) : Configuration 2 s :=
  ⟨q,![pos,out.length],![UnaryTemplate.tape n,out]⟩

theorem true_step (n k : ℕ) (hk : k<n) (out : List Bool) :
    step copy (cfg 0 n (k+1) out)=some (cfg 0 n (k+2) (out++[true])) := by
  simp [step,copy,cfg,Configuration.scanned,UnaryTemplate.tape_mark n k hk]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction,write_append]

theorem delimiter_step (n : ℕ) (out : List Bool) :
    step copy (cfg 0 n (n+1) out)=some (cfg 1 n (n+1) (out++[false])) := by
  simp [step,copy,cfg,Configuration.scanned]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction,write_append]

theorem remaining (n k count : ℕ) (hk : k+count=n) (out : List Bool) :
    Timed copy (count+1) (cfg 0 n (k+1) out)
      (cfg 1 n (n+1) (out++RowIndexField.word count)) := by
  induction count generalizing k out with
  | zero =>
    have he : k=n := by omega
    subst k
    simpa [RowIndexField.word] using Timed.single (by rfl) (delimiter_step n out)
  | succ count ih =>
    have htail := ih (k+1) (by omega) (out++[true])
    have h := (Timed.single (by rfl) (true_step n k (by omega) out)).trans htail
    have hw : (out++[true])++RowIndexField.word count=out++RowIndexField.word (count+1) := by
      simp [RowIndexField.word,List.replicate_succ,List.append_assoc]
    simpa only [hw,show 1+(count+1)=count+1+1 by omega] using h

def last := TapeEmbedding.machine 1 UnaryTemplate.machine
def machine := Composition.machine copy last

theorem append_run (n : ℕ) (out : List Bool) :
    ∃ r,runFrom machine (2*n+4) (cfg machine.start n 1 out)=some r ∧
      r.final=cfg 4 n 1 (out++RowIndexField.word n) ∧ r.steps=2*n+4 := by
  obtain ⟨a,ha,af,as⟩ := (remaining n 0 n (by omega) out).run (by rfl)
  obtain ⟨b,hb,bf,bs,_⟩ := UnaryTemplate.reset_run n
  let eh : Fin 1→ℕ := fun _=>(out++RowIndexField.word n).length
  let et : Fin 1→List Bool := fun _=>out++RowIndexField.word n
  have hlast := TapeEmbedding.run_embed UnaryTemplate.machine eh et _ _ b hb
  have hi : TapeEmbedding.config eh et (UnaryTemplate.config 0 (UnaryTemplate.tape n) (n+1))=
      Composition.restart a.final last.start := by
    rw [af]
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  rw [hi] at hlast
  have whole := Composition.run_join copy last _ _ _ a (TapeEmbedding.receipt eh et b) ha hlast
  have ht : n+1+1+(n+2)=2*n+4 := by omega
  rw [ht] at whole
  refine ⟨Composition.joinedReceipt a (TapeEmbedding.receipt eh et b),whole,?_,?_⟩
  · change Composition.rightConfig 2 (TapeEmbedding.config eh et b.final)=_
    rw [bf]
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  · change a.steps+1+b.steps=_
    rw [as,bs,ht]

end NearCubicWires.RepairOrdinary.RowMaskIndexAppend
