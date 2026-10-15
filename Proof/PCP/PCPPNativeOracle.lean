import Proof.PCP.PCPPNativeResources

/-! The original native oracle descriptor physically supplies its arity and
size. Paid header rewind and template copies retain that SAME descriptor at
head zero for every subsequent query iteration. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeOracleCold
open LocalBitMultitape SourceInterfaces RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def input (bits : List Bool) (i : Fin 40) : List Bool := if i=0 then bits else []
def headerSlots (i : Fin 32) : Fin 40 := i.castAdd 8
def sizeSlots : Fin 5 → Fin 40 := ![20,32,33,34,35]
def widthSlots : Fin 5 → Fin 40 := ![10,36,37,38,39]
noncomputable def header := Rewind.machine PCPPNativeQueryHeader.machine
noncomputable def first := RecoveryFocus.machine headerSlots header
noncomputable def second := RecoveryFocus.machine sizeSlots MatrixTemplateCopy.resetMachine
noncomputable def third := RecoveryFocus.machine widthSlots MatrixTemplateCopy.resetMachine
noncomputable def machine := Composition.machine (Composition.machine first second) third
def budget (R s : ℕ) := 2*PCPPNativeQueryHeader.budget R s+4*s+4*R+28

theorem header_run {R : ℕ} (oracle : BooleanCircuit R) : ∃ out,
    ClockJoin.ReadyRun first (2*PCPPNativeQueryHeader.budget R oracle.size+2)
      (input (PCPPNative.descriptor oracle)) out ∧
    out 0=PCPPNative.descriptor oracle ∧ out 10=UnaryTemplate.tape R ∧
    out 20=UnaryTemplate.tape oracle.size ∧ (∀ i : Fin 40,32 ≤ i.val → out i=[]) := by
  obtain ⟨raw,hr,rs,rt,_,rR,_,rn,_⟩ := PCPPNativeQueryHeader.header_run []
    (PCPPNativeQuery.originalBody oracle++RepairRepresentation.natWord oracle.output.val) R oracle.size
  have he : PCPPNativeQueryHeader.source []
      (PCPPNativeQuery.originalBody oracle++RepairRepresentation.natWord oracle.output.val) R oracle.size=
      PCPPNative.descriptor oracle := by
    rw [PCPPNativeQuery.original_parts]
    simp only [PCPPNativeQueryHeader.source,PCPPNativeQuery.originalHead,List.nil_append,List.append_assoc]
  rw [he] at hr rt
  have hr' : run PCPPNativeQueryHeader.machine (PCPPNativeQueryHeader.budget R oracle.size)
      (fun i => if i=0 then PCPPNative.descriptor oracle else [])=some raw := by
    simpa only [run,initialConfiguration,PCPPNativeQueryHeader.entry,List.length_nil,ite_self] using hr
  obtain ⟨reset,hreset,ht,hh,hs,_⟩ := Rewind.reset_run PCPPNativeQueryHeader.machine _ _ raw hr'
  have small : ClockJoin.ReadyRun header (2*raw.steps+2) _ reset.final.tapes := ⟨reset,hreset,rfl,hh,hs.le⟩
  have enlarged := ClockJoin.enlarge _ _ (2*PCPPNativeQueryHeader.budget R oracle.size+2) _ _ small (by omega)
  have focused := enlarged.focus headerSlots (by decide) (input (PCPPNative.descriptor oracle))
    (by intro i; fin_cases i <;> rfl)
  refine ⟨_,focused,?_,?_,?_,?_⟩
  · exact (install_slot _ (by decide : Function.Injective headerSlots) _ _ 0).trans ((ht 0).trans rt)
  · exact (install_slot _ (by decide : Function.Injective headerSlots) _ _ 10).trans ((ht 10).trans rR)
  · exact (install_slot _ (by decide : Function.Injective headerSlots) _ _ 20).trans ((ht 20).trans rn)
  · intro i hi
    rw [install_other _ _ _ _ (by
      intro j he
      have h := congrArg Fin.val he
      have hj := j.isLt
      change j.val=i.val at h
      omega)]
    have h0 : i≠0 := by intro he; subst i; contradiction
    simp [input,h0]

theorem oracle_run {R : ℕ} (oracle : BooleanCircuit R) : ∃ out,
    ClockJoin.ReadyRun machine (budget R oracle.size) (input (PCPPNative.descriptor oracle)) out ∧
    out 0=PCPPNative.descriptor oracle ∧ out 32=List.replicate oracle.size true ∧
    out 36=List.replicate R true ∧ out 20=UnaryTemplate.tape oracle.size ∧ out 10=UnaryTemplate.tape R := by
  obtain ⟨a,ha,a0,aR,as,afresh⟩ := header_run oracle
  obtain ⟨sized,hs,s0,s1,_,_,sh,ss⟩ := MatrixTemplateCopy.reset_run oracle.size
  have hsize : ClockJoin.ReadyRun MatrixTemplateCopy.resetMachine (4*oracle.size+12)
      (MatrixTemplateCopy.resetInput oracle.size) sized.final.tapes := ⟨sized,hs,rfl,sh,ss.le⟩
  have secondRun := hsize.focus sizeSlots (by decide) a (by
    intro j
    fin_cases j
    · exact as
    all_goals exact afresh _ (by decide))
  let b := install sizeSlots a sized.final.tapes
  have bR : b 10=UnaryTemplate.tape R := (install_other _ _ _ _ (by decide)).trans aR
  have bfresh (i : Fin 40) (hi : 36 ≤ i.val) : b i=[] := by
    dsimp only [b]
    rw [install_other _ _ _ _ (by
      intro j he
      have h := congrArg Fin.val he
      have hj : (sizeSlots j).val ≤ 35 := by fin_cases j <;> decide
      omega)]
    exact afresh i (by omega)
  obtain ⟨width,hw,w0,w1,_,_,wh,ws⟩ := MatrixTemplateCopy.reset_run R
  have hwidth : ClockJoin.ReadyRun MatrixTemplateCopy.resetMachine (4*R+12)
      (MatrixTemplateCopy.resetInput R) width.final.tapes := ⟨width,hw,rfl,wh,ws.le⟩
  have thirdRun := hwidth.focus widthSlots (by decide) b (by
    intro j
    fin_cases j
    · exact bR
    all_goals exact bfresh _ (by decide))
  have joined := ClockJoin.join _ _ _ _ _ _ _ (ClockJoin.join _ _ _ _ _ _ _ ha secondRun) thirdRun
  have hb : (2*PCPPNativeQueryHeader.budget R oracle.size+2)+1+(4*oracle.size+12)+1+(4*R+12)=
      budget R oracle.size := by unfold budget; omega
  rw [hb] at joined
  refine ⟨_,joined,?_,?_,?_,?_,?_⟩
  · exact (install_other _ _ _ _ (by decide)).trans ((install_other _ _ _ _ (by decide)).trans a0)
  · exact (install_other _ _ _ _ (by decide)).trans
      ((install_slot _ (by decide : Function.Injective sizeSlots) _ _ 1).trans s1)
  · exact (install_slot _ (by decide : Function.Injective widthSlots) _ _ 1).trans w1
  · exact (install_other _ _ _ _ (by decide)).trans
      ((install_slot _ (by decide : Function.Injective sizeSlots) _ _ 0).trans s0)
  · exact (install_slot _ (by decide : Function.Injective widthSlots) _ _ 0).trans w0

end NearCubicWires.RepairOrdinary.PCPPNativeOracleCold
