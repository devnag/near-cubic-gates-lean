import Proof.PCP.VerifierDecodingRepeat
import Proof.MachineModel.OrdinaryMemoryEmitReady

/-! Initial simulated heads are actual serialized zero fields, one per
validated tape. The width and tape-count drivers are retained and reused. -/
namespace NearCubicWires.RepairOrdinary.UHeadArray
open LocalBitMultitape RecoveryExecution RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def field (w : ℕ) := frame (List.replicate w false)
def fields (w n : ℕ) : List Bool := (List.replicate n (field w)).flatten
@[simp] theorem fields_length (w n : ℕ) : (fields w n).length=n*(2*w+1) := by
  simp [fields,field]

def stepData (w : ℕ) (out : List Bool) : Bool × List Bool := (true,out++field w)
def source (w : ℕ) (out : List Bool) := MemoryEmitReady.config (0 : Fin 5) (List.replicate w false) out (2*w+1)
noncomputable def machine := RepeatMachine.machine (MemoryEmitReady.machine true) (fun _ _ => true)
def budget (w t : ℕ) := t*(4*w+7)+3

theorem iterate_fields (w n : ℕ) (out : List Bool) :
    RepeatMachine.iterate (stepData w) n out=(true,out++fields w n) := by
  induction n generalizing out with
  | zero => simp [RepeatMachine.iterate,fields]
  | succ n ih =>
    simp [RepeatMachine.iterate,stepData,ih,fields,List.replicate_succ,List.append_assoc]

theorem repeated_run (w t : ℕ) :
    ∃ r,runFrom machine (budget w t) (RepeatMachine.cfg 0 (source w []) t 1)=some r ∧
      r.steps≤budget w t ∧ r.final=RepeatMachine.cfg 3 (source w (fields w t)) t 1 := by
  have supplier (out : List Bool) (_ : True) :
      ∃ r,runFrom (MemoryEmitReady.machine true) (4*w+4) (source w out)=some r ∧
        r.steps≤4*w+4 ∧ r.final.heads=(source w (stepData w out).2).heads ∧
        r.final.tapes=(source w (stepData w out).2).tapes ∧
        (true : Bool)=(stepData w out).1 ∧ ((stepData w out).1=true → True) := by
    obtain ⟨r,hr,hf,hs⟩ := MemoryEmitReady.field_run true (List.replicate w false) out (2*w+1) (by simp)
    have hend : out++Streaming.marks (List.replicate w false)++MemoryEmitField.suffix true=out++field w := by
      have hz : Streaming.marks (List.replicate w false)++[false]=frame (List.replicate w false) := by
        simpa only [List.append_nil,frame] using (Streaming.frame_append (List.replicate w false) []).symm
      simpa only [field,MemoryEmitField.suffix,↓reduceIte,List.append_assoc] using
        congrArg (fun bits => out++bits) hz
    simp only [List.length_replicate] at hr hs
    rw [hend] at hf
    refine ⟨r,hr,hs.le,?_,?_,rfl,by simp⟩
    · rw [hf]; rfl
    · rw [hf]; rfl
  obtain ⟨r,hr,hs,hf⟩ := RepeatMachine.repeat_run (MemoryEmitReady.machine true) (fun _ _ => true)
    (source w) (stepData w) (fun _ => True) (4*w+4) (by intros; rfl) supplier t [] trivial
  have he : 4*w+4+3=4*w+7 := by omega
  simp only [he] at hr hs
  have hfinal : r.final=RepeatMachine.cfg 3 (source w (fields w t)) t 1 := by
    simpa only [RepeatMachine.Result,iterate_fields,List.nil_append,↓reduceIte] using hf
  exact ⟨r,hr,hs,hfinal⟩

end NearCubicWires.RepairOrdinary.UHeadArray
