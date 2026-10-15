import Proof.MachineModel.OrdinaryMatrixScoreSkipField

/-! Literal framed-field copy into the local cut bank. Every source marker,
data bit and delimiter is physically copied, with both cursors streaming. -/
namespace NearCubicWires.RepairOrdinary.MatrixScoreBankField
open LocalBitMultitape RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def machine : Machine 2 3 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==2
  rule := fun q bits => if q.val=0 then
    some ⟨if bits 0 then 1 else 2,![none,some (bits 0)],fun _ => .right⟩
    else if q.val=1 then some ⟨0,![none,some (bits 0)],fun _ => .right⟩ else none
def cfg (q : Fin 3) (source : List Bool) (pos : ℕ) (out : List Bool) : Configuration 2 3 :=
  ⟨q,![pos,out.length],![source,out]⟩

theorem marker (pre suffix out : List Bool) (bit : Bool) :
    step machine (cfg 0 (pre++bit::suffix) pre.length out)=
      some (cfg (if bit then 1 else 2) (pre++bit::suffix) (pre.length+1) (out++[bit])) := by
  simp [step,machine,cfg,Configuration.scanned,Streaming.read_append]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction,Streaming.write_append]
theorem data (pre suffix out : List Bool) (bit : Bool) :
    step machine (cfg 1 (pre++bit::suffix) pre.length out)=
      some (cfg 0 (pre++bit::suffix) (pre.length+1) (out++[bit])) := by
  simp [step,machine,cfg,Configuration.scanned,Streaming.read_append]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction,Streaming.write_append]

theorem field_prefix (bits pre suffix out : List Bool) :
    Timed machine (2*bits.length+1) (cfg 0 (pre++frame bits++suffix) pre.length out)
      (cfg 2 (pre++frame bits++suffix) (pre.length+(frame bits).length) (out++frame bits)) := by
  induction bits generalizing pre out with
  | nil =>
    simpa [frame] using Timed.single (by rfl) (marker pre suffix out false)
  | cons bit bits ih =>
    have ht := ih (pre++[true,bit]) (out++[true,bit])
    have hs := marker pre (bit::(frame bits++suffix)) out true
    have hd := data (pre++[true]) (frame bits++suffix) (out++[true]) bit
    have hsource : (pre++[true])++bit::(frame bits++suffix)=pre++true::bit::(frame bits++suffix) := by simp [List.append_assoc]
    simp only [List.length_append,List.length_cons,List.length_nil] at hd
    rw [hsource] at hd
    have he : pre.length+1+1=(pre++[true,bit]).length := by simp
    rw [he] at hd
    have hs2 : pre++true::bit::(frame bits++suffix)=(pre++[true,bit])++frame bits++suffix := by simp [List.append_assoc]
    rw [hs2] at hs hd
    have hout : (out++[true])++[bit]=out++[true,bit] := by simp [List.append_assoc]
    rw [hout] at hd
    have h := (Timed.single (by rfl) hs).trans ((Timed.single (by rfl) hd).trans ht)
    have htime : 1+(1+(2*bits.length+1))=2*(bit::bits).length+1 := by simp; omega
    have hend : (pre++[true,bit]).length+(frame bits).length=pre.length+(frame (bit::bits)).length := by simp; omega
    have hword : (pre++[true,bit])++frame bits++suffix=pre++frame (bit::bits)++suffix := by simp [frame,List.append_assoc]
    have houtput : (out++[true,bit])++frame bits=out++frame (bit::bits) := by simp [frame,List.append_assoc]
    rw [htime,hend,hword,houtput] at h
    exact h

theorem field_run (bits pre suffix out : List Bool) :
    ∃ actual,runFrom machine (2*bits.length+1) (cfg 0 (pre++frame bits++suffix) pre.length out)=some actual ∧
      actual.final=cfg 2 (pre++frame bits++suffix) (pre.length+(frame bits).length) (out++frame bits) ∧
      actual.steps=2*bits.length+1 := (field_prefix bits pre suffix out).run (by rfl)

end NearCubicWires.RepairOrdinary.MatrixScoreBankField
