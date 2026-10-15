import Proof.CaseAnalysis.CaseTwoSourceBlock
import Proof.MachineModel.GeneratedAmplifierCopy
import Proof.Amplification.RecoveryTseitinReadOnly

/-! The retained PCPP request and the actual input field are unframed,
concatenated, then framed once for the original honest auxiliary machine.
Both logical inputs survive, with every copy and reset charged. -/
namespace NearCubicWires.RepairOrdinary.CloseoutCaseTwo.HonestInput
open LocalBitMultitape RecoveryRootRound RepairSource.RecoveryTseitinReadOnly
  RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def leftSlots : Fin 2→Fin 3:=![0,2]
def rightSlots : Fin 2→Fin 3:=![1,2]
def left:=RecoveryFocus.machine leftSlots GeneratedAmplifier.Copy.machine
def right:=RecoveryFocus.machine rightSlots GeneratedAmplifier.Copy.machine
def raw:=Composition.machine left right
def rawInput (L R : List Bool) : Fin 3→List Bool:=![frame L,frame R,[]]
def rawBudget (L R : List Bool):=(2*L.length+1)+1+(2*R.length+1)

theorem raw_run (L R : List Bool) : ∃ r,run raw (rawBudget L R) (rawInput L R)=some r ∧
    r.steps≤rawBudget L R ∧ r.final.tapes 2=L++R ∧ r.final.heads 2=(L++R).length:=by
  obtain ⟨l,hl,lf,ls⟩:=GeneratedAmplifier.Copy.copy_run [] L [] []
  simp only [List.nil_append,List.append_nil,List.length_nil] at hl lf
  obtain ⟨first,hfirst,_,fs,fh,ft,keep⟩:=RecoveryFocus.dock leftSlots (by decide)
    GeneratedAmplifier.Copy.machine _ (fun _=>0) (rawInput L R) _
    (by intro i;fin_cases i <;>rfl) (by intro i;fin_cases i <;>rfl) l hl
  obtain ⟨r,hr,rf,rs⟩:=GeneratedAmplifier.Copy.copy_run [] R [] L
  simp only [List.nil_append,List.append_nil,List.length_nil] at hr rf
  obtain ⟨last,hlast,_,ss,sh,st,_⟩:=RecoveryFocus.dock rightSlots (by decide)
    GeneratedAmplifier.Copy.machine _ first.final.heads first.final.tapes _
    (by intro i;fin_cases i
        · exact (keep 1 (by decide)).1
        · have h:=fh 1;rw [lf] at h;exact h)
    (by intro i;fin_cases i
        · exact (keep 1 (by decide)).2
        · have h:=ft 1;rw [lf] at h;exact h) r hr
  have whole:=Composition.run_join left right _ _ _ first last hfirst hlast
  refine ⟨_,whole,?_,?_,?_⟩
  · change first.steps+1+last.steps≤rawBudget L R
    rw [fs,ls,ss,rs]
    rfl
  · change last.final.tapes (rightSlots 1)=_
    rw [st,rf]
    rfl
  · change last.final.heads (rightSlots 1)=_
    rw [sh,rf]
    rfl

theorem copy_forward : CursorRestore.NoLeft GeneratedAmplifier.Copy.machine 1:=by
  intro q bits action h
  simp only [GeneratedAmplifier.Copy.machine] at h
  split_ifs at h <;>cases h <;>simp
theorem forward : CursorRestore.NoLeft raw 2:=by
  apply CursorRestore.composition_forward
  · exact CursorRestore.focus_forward leftSlots (by decide) GeneratedAmplifier.Copy.machine 1 copy_forward
  · exact CursorRestore.focus_forward rightSlots (by decide) GeneratedAmplifier.Copy.machine 1 copy_forward
theorem copy_readonly : NoWrite GeneratedAmplifier.Copy.machine 0:=by
  intro q bits action h
  simp only [GeneratedAmplifier.Copy.machine] at h
  split_ifs at h <;>cases h <;>rfl
theorem raw_readonly (i : Fin 2) : NoWrite raw (i.castAdd 1):=by
  fin_cases i
  · exact composition _ _ _ (focus leftSlots (by decide) _ 0 copy_readonly)
      (unselected rightSlots _ 0 (by decide))
  · exact composition _ _ _ (unselected leftSlots _ 1 (by decide))
      (focus rightSlots (by decide) _ 0 copy_readonly)
noncomputable def machine:=AppendOutputFrame.machine raw 2
def input (L R : List Bool) : Fin 7→List Bool:=![frame L,frame R,[],[],[],[],[]]
def budget (L R : List Bool):=2*rawBudget L R+4*(L++R).length+7

theorem honest_input_run (L R : List Bool) : ∃ out,
    ClockJoin.ReadyRun machine (budget L R) (input L R) out ∧
      out 5=frame (L++R) ∧ out 0=frame L ∧ out 1=frame R:=by
  obtain ⟨base,hb,bs,bt,bh⟩:=raw_run L R
  have h0:=run_tape _ _ (raw_readonly 0) _ _ base hb
  have h1:=run_tape _ _ (raw_readonly 1) _ _ base hb
  obtain ⟨r,hr,rt,rh,keep,rs⟩:=PCPPNativeFrame.frame_run raw 2 forward _ _ base hb _ bt bh
  have hi : AppendOutputFrame.input (rawInput L R)=input L R:=by
    funext i;fin_cases i <;>rfl
  rw [hi] at hr
  have ready : ClockJoin.ReadyRun machine (2*base.steps+4*(L++R).length+7) (input L R) r.final.tapes:=
    ⟨r,hr,rfl,rh,rs⟩
  exact ⟨_,ClockJoin.enlarge _ _ _ _ _ ready (by unfold budget;omega),rt,
    (keep 0).trans h0,(keep 1).trans h1⟩

end
end NearCubicWires.RepairOrdinary.CloseoutCaseTwo.HonestInput
