import Proof.CaseAnalysis.RowsEstimatorAppendRaw
import Proof.PCP.PCPSerializerReuseCopy

/-! The paid six-field append restores its local record cursor while leaving
the growing global stream at its append cursor. The existing finite reset
backing is retained and can be used again. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.AppendCopy
open LocalBitMultitape RepairSource.ProjectionNormalization
open CloseoutRowsEstimatorCoefficients
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def machine := CursorRestore.machine AppendRaw.machine 0
def caps (C : ℕ) : Fin 3→ℕ := ![0,0,C]
def entry (source out : List Bool) (C : ℕ) : Configuration 3 20 :=
  ⟨machine.start,![0,out.length,0],![source,out,List.replicate C false]⟩

theorem run (b : ℕ) (q : CompetitorValidity.Estimate) (count denominator C : ℕ) (out : List Bool)
    (hC:20*b+27≤C) :
    ∃ r,runFrom machine (40*b+56) (entry (Stream.recordWord b q count denominator) out C)=some r ∧
      r.final.heads=![0,(out++Stream.recordWord b q count denominator).length,0] ∧
      r.final.tapes=![Stream.recordWord b q count denominator,out++Stream.recordWord b q count denominator,
        List.replicate C false] ∧ r.steps≤40*b+56:=by
  obtain ⟨source,hr,hf,hs⟩:=AppendRaw.run b q count denominator [] [] out
  simp only [List.nil_append,List.append_nil,List.length_nil,Nat.zero_add] at hr hf
  obtain ⟨base,delta,hb,hd,hbs,hbf⟩:=
    CursorRestore.restore_run AppendRaw.machine 0 (AppendRaw.forward 0) _ _ source hr
  have he:2*source.steps+2=40*b+56:=by omega
  rw [he] at hb
  obtain ⟨r,hrun,hrt,hrs,_⟩:=ZeroPadding.run_config machine (caps C) _ _ base hb
  have hi:ZeroPadding.config (caps C)
      (Rewind.recording (AppendRaw.cfg AppendRaw.machine.start (Stream.recordWord b q count denominator) 0 out) 0)=
      entry (Stream.recordWord b q count denominator) out C:=by
    apply configuration_ext
    · rfl
    · funext i;fin_cases i <;>rfl
    · funext i;fin_cases i
      · exact ZeroPadding.pad_zero _
      · exact ZeroPadding.pad_zero _
      · change ZeroPadding.pad C []=List.replicate C false
        simp [ZeroPadding.pad]
  rw [hi] at hrun
  refine ⟨r,hrun,?_,?_,?_⟩
  · rw [hrt,hbf,hf]
    funext i;fin_cases i <;>rfl
  · rw [hrt,hbf,hf]
    funext i;fin_cases i
    · exact ZeroPadding.pad_zero _
    · exact ZeroPadding.pad_zero _
    · change ZeroPadding.pad C (List.replicate delta false)=List.replicate C false
      exact PCPSerializerReuse.pad_zeros C delta (by omega)
  · omega

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.AppendCopy
