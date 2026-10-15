import Proof.CaseAnalysis.RowsEstimatorAppendCopy

/-! Append an actual emitted record from its logical end cursor. The same
retained raw capacity pays the initial return, and the already allocated
zero log is reused for the subsequent copy and return. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.AppendReturn
open LocalBitMultitape CloseoutRowsEstimatorCoefficients
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def rewindSlots : Fin 3→Fin 4 := ![0,2,3]
def copySlots : Fin 3→Fin 4 := ![0,1,3]
noncomputable def first:=RecoveryFocus.machine rewindSlots CompetitorRecordRewind.machine
noncomputable def last:=RecoveryFocus.machine copySlots AppendCopy.machine
noncomputable def machine:=Composition.machine first last
def data (source out : List Bool) (C : ℕ) : Fin 4→List Bool :=
  ![source,out,List.replicate C true,List.replicate C false]
noncomputable def entry (source out : List Bool) (C : ℕ) :=
  (⟨machine.start,![source.length,out.length,0,0],data source out C⟩ : Configuration 4 _)
def budget (b C : ℕ):=2*C+40*b+59

theorem rewind (source out : List Bool) (C : ℕ) (hC:source.length≤C) :
    ∃ r,runFrom first (2*C+2)
      ⟨first.start,![source.length,out.length,0,0],data source out C⟩=some r ∧
      r.final.heads=![0,out.length,0,0] ∧ r.final.tapes=data source out C ∧ r.steps=2*C+2:=by
  obtain ⟨raw,hr,hf,hs⟩:=CompetitorRecordRewind.rewind_run source C source.length hC
  obtain ⟨pad,hp,pf,ps,_⟩:=ZeroPadding.run_config CompetitorRecordRewind.machine
    (AppendCopy.caps C) _ _ raw hr
  have hi:ZeroPadding.config (AppendCopy.caps C)
      (CompetitorRecordRewind.cfg 0 source source.length C 0 0 [])=
      (⟨CompetitorRecordRewind.machine.start,![source.length,0,0],
        ![source,List.replicate C true,List.replicate C false]⟩ : Configuration 3 3):=by
    apply configuration_ext
    · rfl
    · rfl
    · funext i;fin_cases i
      · exact ZeroPadding.pad_zero _
      · exact ZeroPadding.pad_zero _
      · change ZeroPadding.pad C []=List.replicate C false
        simp [ZeroPadding.pad]
  rw [hi] at hp
  have pheads:pad.final.heads=fun _=>0:=by
    rw [pf,hf]
    funext i;fin_cases i <;>rfl
  have ptapes:pad.final.tapes=![source,List.replicate C true,List.replicate C false]:=by
    rw [pf,hf]
    funext i;fin_cases i
    · exact ZeroPadding.pad_zero _
    · exact ZeroPadding.pad_zero _
    · exact PCPSerializerReuse.pad_zeros C C (by rfl)
  obtain ⟨r,rr,_,rs,rh,rt,keep⟩:=RecoveryFocus.dock rewindSlots (by decide)
    CompetitorRecordRewind.machine (2*C+2) (![source.length,out.length,0,0] : Fin 4→ℕ)
    (data source out C) _ (by intro i;fin_cases i <;>rfl) (by intro i;fin_cases i <;>rfl) pad hp
  refine ⟨r,rr,?_,?_,rs.trans (ps.trans hs)⟩
  · funext i;fin_cases i
    · exact (rh 0).trans (congrFun pheads 0)
    · exact (keep 1 (by decide)).1
    · exact (rh 1).trans (congrFun pheads 1)
    · exact (rh 2).trans (congrFun pheads 2)
  · funext i;fin_cases i
    · exact (rt 0).trans (congrFun ptapes 0)
    · exact (keep 1 (by decide)).2
    · exact (rt 1).trans (congrFun ptapes 1)
    · exact (rt 2).trans (congrFun ptapes 2)

theorem run (b : ℕ) (q : CompetitorValidity.Estimate) (count denominator C : ℕ) (out : List Bool)
    (hC:20*b+27≤C) :
    ∃ r,runFrom machine (budget b C) (entry (Stream.recordWord b q count denominator) out C)=some r ∧
      r.final.heads=![0,(out++Stream.recordWord b q count denominator).length,0,0] ∧
      r.final.tapes=data (Stream.recordWord b q count denominator)
        (out++Stream.recordWord b q count denominator) C ∧ r.steps≤budget b C:=by
  let word:=Stream.recordWord b q count denominator
  obtain ⟨before,hb,bh,bt,bs⟩:=rewind word out C (by rw [Stream.record_length];omega)
  obtain ⟨base,hbase,bhh,btt,bss⟩:=AppendCopy.run b q count denominator C out hC
  obtain ⟨after,ha,_,ast,ah,atp,keep⟩:=RecoveryFocus.dock copySlots (by decide)
    AppendCopy.machine (40*b+56) before.final.heads before.final.tapes _
    (by intro i;rw [bh];fin_cases i <;>rfl) (by intro i;rw [bt];fin_cases i <;>rfl) base hbase
  have hl:runFrom last (40*b+56) (Composition.restart before.final last.start)=some after:=ha
  have whole:=Composition.run_join first last _ _ _ before after hb hl
  have ht:(2*C+2)+1+(40*b+56)=budget b C:=by unfold budget;omega
  rw [ht] at whole
  refine ⟨Composition.joinedReceipt before after,whole,?_,?_,?_⟩
  · change after.final.heads=_
    funext i;fin_cases i
    · exact (ah 0).trans (congrFun bhh 0)
    · exact (ah 1).trans (congrFun bhh 1)
    · exact (keep 2 (by decide)).1.trans (congrFun bh 2)
    · exact (ah 2).trans (congrFun bhh 2)
  · change after.final.tapes=_
    funext i;fin_cases i
    · exact (atp 0).trans (congrFun btt 0)
    · exact (atp 1).trans (congrFun btt 1)
    · exact (keep 2 (by decide)).2.trans (congrFun bt 2)
    · exact (atp 2).trans (congrFun btt 2)
  · change before.steps+1+after.steps≤_
    rw [bs,ast]
    unfold budget
    omega

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.AppendReturn
