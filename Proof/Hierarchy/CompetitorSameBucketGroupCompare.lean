import Proof.PCP.ProjectionNormalizationFieldEquality
import Proof.Amplification.RecoveryReadyCalls
import Proof.Hierarchy.CompetitorSameBucketGroupSemantics

/-! A paid comparison of both concatenated occurrence IDs. The old and new
fields, both heads, and the physical rewind log are retained for reuse. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSameBucketGroupCompare
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open RepairSource.ProjectionNormalization CompetitorSameBucketGroup
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine := Rewind.machine FieldEquality.machine
def caps (cap : ℕ) : Fin 4 → ℕ := ![cap,cap,0,cap]
def input (cap : ℕ) (left right : List Bool) (old : Bool) : Fin 4 → List Bool :=
  ![ZeroPadding.pad cap (frame left),ZeroPadding.pad cap (frame right),[old],List.replicate cap false]
def output (cap : ℕ) (left right : List Bool) (old : Bool) : Fin 4 → List Bool :=
  ![ZeroPadding.pad cap (frame left),ZeroPadding.pad cap (frame right),
    [old && decide (left=right)],List.replicate cap false]

theorem compare_ready (cap k : ℕ) (left right : List Bool) (old : Bool)
    (hl : left.length=k) (hr : right.length=k) (hc : 2*k+1≤cap) :
    ReadyRun machine (4*k+4) (input cap left right old) (output cap left right old) := by
  obtain ⟨base,hbase,hbf,hbs⟩ := FieldEquality.equality_run left right [] [] [] [] old
  simp only [List.nil_append,List.append_nil,List.length_nil,Nat.zero_add,hl,hr,max_self] at hbase hbf hbs
  obtain ⟨restored,hrestore,hrf,hrs,_⟩ := Rewind.recorded_run FieldEquality.machine _ _ base hbase 0
    (by intro i; fin_cases i <;> simp [FieldEquality.cfg])
  have he : 0+2*base.steps+2=4*k+4 := by omega
  rw [he] at hrestore hrs
  obtain ⟨r,ha,hfinal,hsteps,_⟩ := ZeroPadding.run_config machine (caps cap) _ _ restored hrestore
  have hin : ZeroPadding.config (caps cap)
      (Rewind.recording (FieldEquality.cfg FieldEquality.machine.start (frame left) (frame right) 0 0 old) 0)=
      initialConfiguration machine (input cap left right old) := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i
      fin_cases i <;> simp [ZeroPadding.config,caps,Rewind.recording,Rewind.config,
        FieldEquality.cfg,initialConfiguration,input,ZeroPadding.pad,Fin.addCases]
  rw [hin] at ha
  refine ⟨r,ha,?_,?_,hsteps.trans hrs⟩
  · rw [hfinal,hrf,hbf,hbs]
    funext i
    fin_cases i <;> simp [ZeroPadding.config,caps,Rewind.finished,Rewind.config,FieldEquality.cfg,output,
      Rewind.Workspace.pad_zeros,max_eq_left hc,Fin.addCases]
  · intro i
    rw [hfinal,hrf]
    fin_cases i <;> rfl

theorem ids_ready (cap m : ℕ) (a b : Entry) (old : Bool)
    (ha : a.row<2^m) (har : a.rightTaggedID<2^m)
    (hb : b.row<2^m) (hbr : b.rightTaggedID<2^m) (hc : 4*m+1≤cap) :
    ReadyRun machine (8*m+4) (input cap (a.ids m) (b.ids m) old)
      ![ZeroPadding.pad cap (frame (a.ids m)),ZeroPadding.pad cap (frame (b.ids m)),
        [old && decide (a.row=b.row ∧ a.rightTaggedID=b.rightTaggedID)],List.replicate cap false] := by
  have h := compare_ready cap (2*m) (a.ids m) (b.ids m) old (ids_length m a) (ids_length m b) (by omega)
  have he : 4*(2*m)+4=8*m+4 := by omega
  rw [he] at h
  simpa only [output,ids_eq_iff m a b ha har hb hbr] using h

end NearCubicWires.RepairOrdinary.CompetitorSameBucketGroupCompare
