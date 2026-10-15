import Proof.MachineModel.OrdinaryMatrixScoreNegativeFold

/-! The left-score consumer skips the intervening right-weight fields on
the original raw cut stream. This field scan charges every marker, data bit
and delimiter and preserves the source bytes. -/
namespace NearCubicWires.RepairOrdinary.MatrixScoreSkipField
open LocalBitMultitape RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def machine : Machine 1 3 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==2
  rule := fun q bits => if q.val=0 then
    some ⟨if bits 0 then 1 else 2,fun _ => none,fun _ => .right⟩
    else if q.val=1 then some ⟨0,fun _ => none,fun _ => .right⟩ else none
def cfg (q : Fin 3) (source : List Bool) (pos : ℕ) : Configuration 1 3 :=
  ⟨q,fun _ => pos,fun _ => source⟩

theorem marker (pre suffix : List Bool) (bit : Bool) :
    step machine (cfg 0 (pre++bit::suffix) pre.length)=
      some (cfg (if bit then 1 else 2) (pre++bit::suffix) (pre.length+1)) := by
  simp [step,machine,cfg,Configuration.scanned,Streaming.read_append]
  rfl
theorem data (source : List Bool) (pos : ℕ) :
    step machine (cfg 1 source pos)=some (cfg 0 source (pos+1)) := by
  simp [step,machine,cfg]
  rfl

theorem field_prefix (bits pre suffix : List Bool) :
    Timed machine (2*bits.length+1) (cfg 0 (pre++frame bits++suffix) pre.length)
      (cfg 2 (pre++frame bits++suffix) (pre.length+(frame bits).length)) := by
  induction bits generalizing pre with
  | nil =>
    simpa [frame] using Timed.single (by rfl) (marker pre suffix false)
  | cons bit bits ih =>
    have ht := ih (pre++[true,bit])
    have hs := marker pre (bit::(frame bits++suffix)) true
    have hd := data (pre++true::bit::(frame bits++suffix)) (pre.length+1)
    have he : pre.length+1+1=(pre++[true,bit]).length := by simp
    rw [he] at hd
    have hsource : pre++true::bit::(frame bits++suffix)=(pre++[true,bit])++frame bits++suffix := by
      simp [List.append_assoc]
    rw [hsource] at hs hd
    have h := (Timed.single (by rfl) hs).trans ((Timed.single (by rfl) hd).trans ht)
    have htime : 1+(1+(2*bits.length+1))=2*(bit::bits).length+1 := by simp; omega
    have hend : (pre++[true,bit]).length+(frame bits).length=pre.length+(frame (bit::bits)).length := by simp; omega
    have hword : (pre++[true,bit])++frame bits++suffix=pre++frame (bit::bits)++suffix := by simp [frame,List.append_assoc]
    rw [htime,hend,hword] at h
    exact h

theorem field_run (bits pre suffix : List Bool) :
    ∃ actual,runFrom machine (2*bits.length+1) (cfg 0 (pre++frame bits++suffix) pre.length)=some actual ∧
      actual.final=cfg 2 (pre++frame bits++suffix) (pre.length+(frame bits).length) ∧
      actual.steps=2*bits.length+1 := (field_prefix bits pre suffix).run (by rfl)

end NearCubicWires.RepairOrdinary.MatrixScoreSkipField
