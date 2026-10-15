import Proof.Supplier.RowMaskMeaning

/-! Reset a short binary row cursor by real writes, preserving every frame
marker and reusing the same bounded reset log as counter advancement. -/
namespace NearCubicWires.RepairOrdinary.RowBinaryClear
open LocalBitMultitape RecoveryExecution RecoveryRootRound Streaming SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def raw : Machine 1 3 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val==2
  rule := fun q bits=>if q.val=0 then some (if bits 0 then
    ⟨1,fun _=>none,fun _=>.right⟩ else ⟨2,fun _=>none,fun _=>.stay⟩)
    else if q.val=1 then some ⟨0,fun _=>some false,fun _=>.right⟩ else none
def cfg (q : Fin 3) (source : List Bool) (pos : ℕ) : Configuration 1 3 :=
  ⟨q,fun _=>pos,fun _=>source⟩

theorem mark_step (pre tail : List Bool) :
    step raw (cfg 0 (pre++true::tail) pre.length)=some (cfg 1 (pre++true::tail) (pre.length+1)) := by
  simp [step,raw,cfg,Configuration.scanned,read_append]
  rfl
theorem bit_step (pre tail : List Bool) (bit : Bool) :
    step raw (cfg 1 (pre++bit::tail) pre.length)=some (cfg 0 (pre++false::tail) (pre.length+1)) := by
  simp [step,raw,cfg]
  apply configuration_ext
  · rfl
  · rfl
  · funext i; exact BinaryIncrement.write_prefix pre tail bit false
theorem stop_step (pre : List Bool) :
    step raw (cfg 0 (pre++[false]) pre.length)=some (cfg 2 (pre++[false]) pre.length) := by
  simp [step,raw,cfg,Configuration.scanned,read_append]
  rfl

theorem clear_timed (pre bits : List Bool) :
    Timed raw (2*bits.length+1) (cfg 0 (pre++frame bits) pre.length)
      (cfg 2 (pre++frame (List.replicate bits.length false)) (pre.length+2*bits.length)) := by
  induction bits generalizing pre with
  | nil => simpa [frame] using Timed.single (by rfl) (stop_step pre)
  | cons bit bits ih =>
    have hmark : step raw (cfg 0 (pre++frame (bit::bits)) pre.length)=
        some (cfg 1 (pre++frame (bit::bits)) (pre.length+1)) := by
      simpa [frame] using mark_step pre (bit::frame bits)
    have hbit : step raw (cfg 1 (pre++frame (bit::bits)) (pre.length+1))=
        some (cfg 0 ((pre++[true,false])++frame bits) (pre.length+2)) := by
      simpa [frame,List.append_assoc] using bit_step (pre++[true]) (frame bits) bit
    have ht := ih (pre++[true,false])
    simp only [List.length_append,List.length_cons,List.length_nil] at ht
    have whole := ((Timed.single (by rfl) hmark).trans (Timed.single (by rfl) hbit)).trans ht
    have he : 1+1+(2*bits.length+1)=2*(bit::bits).length+1 := by simp; omega
    rw [he] at whole
    have hpos : pre.length+2+2*bits.length=pre.length+2*(bits.length+1) := by omega
    rw [hpos] at whole
    simpa [frame,List.replicate_succ,List.append_assoc] using whole

def machine := Rewind.machine raw

theorem clear_ready (bits : List Bool) :
    ReadyRun machine (4*bits.length+4)
      ![frame bits,List.replicate (2*bits.length+1) false]
      ![frame (List.replicate bits.length false),List.replicate (2*bits.length+1) false] := by
  obtain ⟨base,hr,bf,bs⟩ := (clear_timed [] bits).run (by rfl)
  simp only [List.nil_append,List.length_nil,zero_add] at hr bf
  have hin : cfg 0 (frame bits) 0=initialConfiguration raw (fun _=>frame bits) := rfl
  rw [hin] at hr
  obtain ⟨r,hrun,rt,rc,rh,rs,_⟩ := Rewind.Workspace.reset_workspace raw _ _ base hr (2*bits.length+1)
  rw [bs] at hrun rc rs
  have he : 2*(2*bits.length+1)+2=4*bits.length+4 := by omega
  rw [he] at hrun rs
  refine ⟨r,?_,?_,rh,rs⟩
  · convert hrun using 2
    all_goals first | rfl | (funext i; fin_cases i <;> rfl)
  · funext i
    fin_cases i
    · simpa [bf,cfg] using rt 0
    · simpa using rc

theorem binary_ready (w n : ℕ) :
    ReadyRun machine (4*w+4) ![frame (binary w n),List.replicate (2*w+1) false]
      ![frame (binary w 0),List.replicate (2*w+1) false] := by
  simpa only [binary_length,RankCarrier.binary_zero] using clear_ready (binary w n)

end NearCubicWires.RepairOrdinary.RowBinaryClear
