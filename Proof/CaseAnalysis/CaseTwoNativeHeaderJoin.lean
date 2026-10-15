import Proof.PCP.PCPPNativeClauseDescriptorForward
import Proof.Assembly.AppendFrameKernel
import Proof.PCP.PCPPNativeRequestSchema

/-! Print the original native arity/count header from the physically
retained counters, then copy the measured native node/output word once. -/
namespace NearCubicWires.RepairOrdinary.CloseoutCaseTwo.NativeHeaderJoin
open LocalBitMultitape RepairRepresentation RecoveryRootRound RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def frameSlots : Fin 4→Fin 41:=![0,1,39,40]
def headerSlots (j : Fin 35) : Fin 41:=if j=0 then 2 else if j=1 then 3 else ⟨j.val+2,by omega⟩
def copySlots : Fin 2→Fin 41:=![39,20]
theorem header_injective : Function.Injective headerSlots:=by decide
noncomputable def frameProgram:=RecoveryFocus.machine frameSlots AppendFrameKernel.machine
noncomputable def headerProgram:=RecoveryFocus.machine headerSlots PCPPNativeColdHeader.machine
noncomputable def copyProgram:=RecoveryFocus.machine copySlots GeneratedAmplifier.Copy.machine
noncomputable def first:=Composition.machine frameProgram headerProgram
noncomputable def machine:=Composition.machine first copyProgram
def input (domain count : ℕ) (bits : List Bool) (i : Fin 41):=
  if i=0 then bits else if i=1 then List.replicate bits.length true
  else if i=2 then List.replicate domain true else if i=3 then List.replicate count true else []
def budget (domain count length : ℕ):=(4*length+4)+1+PCPPNativeColdHeader.budget domain count+1+(2*length+1)

theorem frame_input (domain count : ℕ) (bits : List Bool) (j : Fin 4) :
    input domain count bits (frameSlots j)=AppendFrameKernel.input bits j:=by
  fin_cases j <;> rfl
theorem header_input (domain count : ℕ) (bits : List Bool) (j : Fin 35) :
    install frameSlots (input domain count bits) (AppendFrameKernel.output bits) (headerSlots j)=
      PCPPNativeColdHeader.data domain count [] j:=by
  rw [install_other frameSlots (input domain count bits) (AppendFrameKernel.output bits) (headerSlots j)
    (by fin_cases j <;> decide)]
  fin_cases j <;> rfl

theorem join_run (domain count : ℕ) (bits : List Bool) :
    ∃ r,run machine (budget domain count bits.length) (input domain count bits)=some r ∧
      r.steps≤budget domain count bits.length ∧
      r.final.tapes 20=natWord domain++natWord count++bits ∧
      r.final.heads 20=(natWord domain++natWord count++bits).length := by
  obtain ⟨a,ar,atp,ah,asteps⟩:=(AppendFrameKernel.ready bits).focus frameSlots (by decide)
    (input domain count bits) (frame_input domain count bits)
  obtain ⟨base,br,bs,bt,bh,_d,_dh,_c,_ch⟩:=PCPPNativeColdHeader.append_run domain count []
  obtain ⟨b,hr,_bf,bst,bheads,btapes,keep⟩:=RecoveryFocus.dock headerSlots header_injective
    PCPPNativeColdHeader.machine _ a.final.heads a.final.tapes (PCPPNativeColdHeader.entry domain count [])
    (by intro j;rw [ah];simp [PCPPNativeColdHeader.entry,PCPPNativeColdHeader.heads])
    (by intro j;rw [atp];exact header_input domain count bits j) base br
  have hfirst:=Composition.run_join frameProgram headerProgram _ _ _ a b ar hr
  let joined:=Composition.joinedReceipt a b
  have h39t : joined.final.tapes 39=frame bits:=by
    change b.final.tapes 39=frame bits
    rw [(keep 39 (by decide)).2,atp]
    exact install_slot frameSlots (by decide) (input domain count bits) (AppendFrameKernel.output bits) 2
  have h39h : joined.final.heads 39=0:=by
    change b.final.heads 39=0
    rw [(keep 39 (by decide)).1,ah]
  have h20t : joined.final.tapes 20=natWord domain++natWord count:=by
    change b.final.tapes (headerSlots 18)=_
    exact (btapes 18).trans (by simpa only [PCPPNativeColdHeader.emitted,List.nil_append] using bt)
  have h20h : joined.final.heads 20=(natWord domain++natWord count).length:=by
    change b.final.heads (headerSlots 18)=_
    exact (bheads 18).trans (by simpa only [PCPPNativeColdHeader.emitted,List.nil_append] using bh)
  obtain ⟨copied,cr,cf,cs⟩:=GeneratedAmplifier.Copy.copy_run [] bits [] (natWord domain++natWord count)
  obtain ⟨last,lr,_lf,lsteps,lh,lt,_lk⟩:=RecoveryFocus.dock copySlots (by decide) GeneratedAmplifier.Copy.machine _
    joined.final.heads joined.final.tapes (GeneratedAmplifier.Copy.cfg 0
      ([]++frame bits++[]) 0 (natWord domain++natWord count))
    (by intro j;fin_cases j
        · exact h39h
        · exact h20h)
    (by intro j;fin_cases j
        · change joined.final.tapes 39=[]++frame bits++[]
          rw [List.nil_append,List.append_nil]
          exact h39t
        · exact h20t) copied cr
  have whole:=Composition.run_join first copyProgram _ _ _ joined last hfirst lr
  refine ⟨Composition.joinedReceipt joined last,whole,?_,?_,?_⟩
  · change a.steps+1+b.steps+1+last.steps≤budget domain count bits.length
    rw [lsteps,cs,bst]
    unfold budget
    omega
  · change last.final.tapes (copySlots 1)=_
    exact (lt 1).trans (by rw [cf];rfl)
  · change last.final.heads (copySlots 1)=_
    exact (lh 1).trans (by rw [cf];rfl)

theorem forward : CursorRestore.NoLeft machine 20:=by
  apply CursorRestore.composition_forward
  · apply CursorRestore.composition_forward
    · exact EquationRowCuts.unselected_forward frameSlots _ 20 (by decide)
    · exact CursorRestore.focus_forward headerSlots header_injective PCPPNativeColdHeader.machine 18
        PCPPNativeClauseDescriptor.header_forward
  · exact CursorRestore.focus_forward copySlots (by decide) GeneratedAmplifier.Copy.machine 1
      PCPPNativeClauseDescriptor.copy_forward

end NearCubicWires.RepairOrdinary.CloseoutCaseTwo.NativeHeaderJoin
