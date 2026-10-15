import Proof.Supplier.EquationRowRequest

/-! One actual streaming scalar widening for the B.2 doubled-cut producer.
It copies a framed field, appends one false high bit, consumes the original
terminator and retains the global destination append cursor. -/
namespace NearCubicWires.RepairOrdinary.EquationWiden
open LocalBitMultitape RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def machine : Machine 2 5 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==4
  rule := fun q bs =>
    if q.val=0 then some ⟨if bs 0 then 1 else 2,![none,some true],![.right,.right]⟩
    else if q.val=1 then some ⟨0,![none,some (bs 0)],![.right,.right]⟩
    else if q.val=2 then some ⟨3,![none,some false],![.stay,.right]⟩
    else if q.val=3 then some ⟨4,![none,some false],![.stay,.right]⟩
    else none

def cfg (q : Fin 5) (source : List Bool) (pos : ℕ) (out : List Bool) : Configuration 2 5 :=
  ⟨q,![pos,out.length],![source,out]⟩

theorem marker (source out : List Bool) (pos : ℕ) (b : Bool)
    (hb : readTapeBit source pos=b) :
    step machine (cfg 0 source pos out)=
      some (cfg (if b then 1 else 2) source (pos+1) (out++[true])) := by
  simp [step,machine,cfg,Configuration.scanned,hb]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction,Streaming.write_append]

theorem bit (source out : List Bool) (pos : ℕ) (b : Bool)
    (hb : readTapeBit source pos=b) :
    step machine (cfg 1 source pos out)=some (cfg 0 source (pos+1) (out++[b])) := by
  simp [step,machine,cfg,Configuration.scanned,hb]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction,Streaming.write_append]

theorem high (source out : List Bool) (pos : ℕ) :
    step machine (cfg 2 source pos out)=some (cfg 3 source pos (out++[false])) := by
  simp [step,machine,cfg]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction,Streaming.write_append]

theorem stop (source out : List Bool) (pos : ℕ) :
    step machine (cfg 3 source pos out)=some (cfg 4 source pos (out++[false])) := by
  simp [step,machine,cfg]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction,Streaming.write_append]

theorem timed (pre bits suffix out : List Bool) :
    Timed machine (2*bits.length+3)
      (cfg 0 (pre++frame bits++suffix) pre.length out)
      (cfg 4 (pre++frame bits++suffix) (pre.length+(frame bits).length)
        (out++frame (bits++[false]))) := by
  induction bits generalizing pre out with
  | nil =>
    have hread : readTapeBit (pre++frame []++suffix) pre.length=false := by
      simpa only [frame,List.append_assoc,List.cons_append,List.nil_append] using
        Streaming.read_append pre suffix false
    have h0 := Timed.single (by rfl) (marker _ out pre.length false hread)
    have h1 := Timed.single (by rfl) (high (pre++frame []++suffix) (out++[true]) (pre.length+1))
    have h2 := Timed.single (by rfl) (stop (pre++frame []++suffix) ((out++[true])++[false]) (pre.length+1))
    simpa [frame,List.append_assoc] using (h0.trans h1).trans h2
  | cons b bits ih =>
    have hread : readTapeBit (pre++frame (b::bits)++suffix) pre.length=true := by
      simpa only [frame,List.append_assoc,List.cons_append] using
        Streaming.read_append pre (b::frame bits++suffix) true
    have hdata : readTapeBit (pre++frame (b::bits)++suffix) (pre.length+1)=b := by
      have h := Streaming.read_append (pre++[true]) (frame bits++suffix) b
      simpa only [frame,List.append_assoc,List.cons_append,List.nil_append,List.length_append,
        List.length_singleton] using h
    have h0 := Timed.single (by rfl) (marker _ out pre.length true hread)
    have h1 := Timed.single (by rfl) (bit _ (out++[true]) (pre.length+1) b hdata)
    have ht := ih (pre++[true,b]) ((out++[true])++[b])
    have hentry : cfg 0 (pre++frame (b::bits)++suffix) (pre.length+1+1) ((out++[true])++[b])=
        cfg 0 ((pre++[true,b])++frame bits++suffix) (pre++[true,b]).length ((out++[true])++[b]) := by
      simp [cfg,frame,List.append_assoc]
    rw [←hentry] at ht
    have hall := (h0.trans h1).trans ht
    convert hall using 1 <;> simp [cfg,frame,List.append_assoc] <;> omega

theorem field_run (pre bits suffix out : List Bool) :
    ∃ r,runFrom machine (2*bits.length+3)
      (cfg 0 (pre++frame bits++suffix) pre.length out)=some r ∧
      r.final=cfg 4 (pre++frame bits++suffix) (pre.length+(frame bits).length)
        (out++frame (bits++[false])) ∧ r.steps=2*bits.length+3 := by
  exact (timed pre bits suffix out).run (by rfl)

end NearCubicWires.RepairOrdinary.EquationWiden

