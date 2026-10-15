import Proof.CaseAnalysis.RowsGateMeasuredPorts

/-! The bottom traversal appends native requests and unary resource totals
without revisiting their growing prefixes. Both source heads and the paid
local log return to zero. The global append cursor remains at the new end. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsCircuitAppend
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def frameCfg (q : Fin 4) (cap : ℕ) (bits out : List Bool) : Configuration 3 4 :=
  ⟨q,![0,out.length,0],![ZeroPadding.pad cap (frame bits),out,List.replicate cap false]⟩

theorem frame_run (cap : ℕ) (bits out : List Bool) (hc : 2*bits.length+1 ≤ cap) : ∃ r,
    runFrom CompetitorFrameAppend.machine (4*bits.length+3) (frameCfg 0 cap bits out)=some r ∧
      r.final=frameCfg 3 cap bits (out++frame bits) ∧ r.steps=4*bits.length+3 := by
  obtain ⟨base,hb,bf,bs⟩:=CompetitorRawFrameAppend.raw_append_run bits out cap hc
  obtain ⟨r,hr,rf,rs,_⟩:=ZeroPadding.run_config CompetitorFrameAppend.machine ![cap,0,0] _ _ base hb
  have eqcfg (q : Fin 4) (output : List Bool) :
      ZeroPadding.config ![cap,0,0] (CompetitorRawFrameAppend.cfg q bits output cap)=frameCfg q cap bits output := by
    apply configuration_ext
    · rfl
    · rfl
    · funext i;fin_cases i
      · rfl
      · exact ZeroPadding.pad_zero output
      · exact ZeroPadding.pad_zero (List.replicate cap false)
  rw [eqcfg] at hr
  exact ⟨r,hr,by rw [rf,bf,eqcfg],rs.trans bs⟩

def unary : Machine 4 5 := MaskedReset.machine ClockUnarySum.raw ![true,true,false]
def unaryCfg (q : Fin 5) (cap a b : ℕ) (out : List Bool) : Configuration 4 5 :=
  ⟨q,![0,0,out.length,0],![ZeroPadding.pad cap (List.replicate a true),
    ZeroPadding.pad cap (List.replicate b true),out,List.replicate cap false]⟩

theorem raw_unary_run (a b : ℕ) (out : List Bool) : ∃ r,
    runFrom ClockUnarySum.raw (a+b+2) (ClockUnarySum.cfg 0 a b 0 0 out)=some r ∧
      r.final=ClockUnarySum.cfg 2 a b a b (out++List.replicate (a+b) true) ∧ r.steps=a+b+2 := by
  have left:=ClockUnarySum.left_prefix a b 0 a out (by omega)
  have right:=ClockUnarySum.right_prefix a b 0 b (out++List.replicate a true) (by omega)
  obtain ⟨last,hl,hf,hs,_⟩:=right.run (by rfl) (by simp;omega)
  obtain ⟨r,hr,rf,rs,_⟩:=left.followedBy last hl
  refine ⟨r,?_,?_,by omega⟩
  · simpa only [show (a+1)+(b+1)=a+b+2 by omega] using hr
  · rw [rf,hf,List.append_assoc,←List.replicate_add]

theorem unary_run (cap a b : ℕ) (out : List Bool) (hc : a+b+2 ≤ cap) : ∃ r,
    runFrom unary (2*(a+b)+6) (unaryCfg 0 cap a b out)=some r ∧
      r.final=unaryCfg 4 cap a b (out++List.replicate (a+b) true) ∧ r.steps=2*(a+b)+6 := by
  obtain ⟨base,hb,bf,bs⟩:=raw_unary_run a b out
  obtain ⟨stage,hl,lf,ls,_⟩:=MaskedReset.workspace_run ClockUnarySum.raw ![true,true,false]
    _ cap _ base hb (by intro i;fin_cases i <;> simp [ClockUnarySum.cfg]) (by omega)
  obtain ⟨r,hr,rf,rs,_⟩:=ZeroPadding.run_config unary ![cap,cap,0,0] _ _ stage hl
  have start : ZeroPadding.config ![cap,cap,0,0]
      (ZeroPadding.config (Rewind.Workspace.capacities 3 cap)
        (Rewind.recording (ClockUnarySum.cfg 0 a b 0 0 out) 0))=unaryCfg 0 cap a b out := by
    apply configuration_ext
    · rfl
    · funext i;fin_cases i <;> rfl
    · funext i;fin_cases i
      · change ZeroPadding.pad cap (ZeroPadding.pad 0 (List.replicate a true))=_
        rw [ZeroPadding.pad_zero];rfl
      · change ZeroPadding.pad cap (ZeroPadding.pad 0 (List.replicate b true))=_
        rw [ZeroPadding.pad_zero];rfl
      · change ZeroPadding.pad 0 (ZeroPadding.pad 0 out)=out
        simp only [ZeroPadding.pad_zero]
      · change ZeroPadding.pad 0 (ZeroPadding.pad cap [])=List.replicate cap false
        simp [ZeroPadding.pad]
  rw [start] at hr
  refine ⟨r,?_,?_,by omega⟩
  · simpa only [bs,show 2*(a+b+2)+2=2*(a+b)+6 by omega] using hr
  · rw [rf,lf,bf]
    apply configuration_ext
    · rfl
    · funext i;fin_cases i <;> rfl
    · funext i;fin_cases i
      · rfl
      · rfl
      · exact ZeroPadding.pad_zero _
      · exact ZeroPadding.pad_zero _

end NearCubicWires.RepairOrdinary.CloseoutRowsCircuitAppend
