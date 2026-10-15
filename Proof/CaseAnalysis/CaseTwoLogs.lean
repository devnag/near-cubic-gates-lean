import Proof.CaseAnalysis.CaseTwoScalars
import Proof.Hierarchy.HierarchyFixedWord

/-! Pay for the larger rewind-log driver and the fixed tag width after
the original R/B capacity fields. No initialized workspace is assumed. -/
namespace NearCubicWires.RepairOrdinary.CloseoutCaseTwo.ColdLogs
open LocalBitMultitape RecoveryRootRound RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

local instance (D : ℕ) : NeZero (DimensionPolynomial.tapes D):=⟨by dsimp [DimensionPolynomial.tapes];omega⟩
def oldSlots (j : Fin 40) : Fin 57:=j.castAdd 17
def logSlots (j : Fin (DimensionPolynomial.tapes 1)) : Fin 57:=
  if j=0 then 14 else ⟨j.val+39,by have ht:=j.isLt;dsimp [DimensionPolynomial.tapes] at ht;omega⟩
def sixSlots : Fin 2→Fin 57:=![55,56]
theorem old_injective : Function.Injective oldSlots:=by intro i j h;exact Fin.ext (congrArg (fun x : Fin 57=>x.val) h)
theorem log_injective : Function.Injective logSlots:=by decide
def input (R B : ℕ) (i : Fin 57):=if i=0 then List.replicate R true else if i=1 then List.replicate B true else []
noncomputable def first (K : ℕ):=RecoveryFocus.machine oldSlots (ColdScalars.machine K)
noncomputable def second:=RecoveryFocus.machine logSlots (PCPSerializerCapacity.Power.machine 1 16)
noncomputable def third:=RecoveryFocus.machine sixSlots (HierarchyFixedWord.machine (List.replicate 6 true))
noncomputable def machine (K : ℕ):=Composition.machine (Composition.machine (first K) second) third
def budget (K R B : ℕ):=ColdScalars.budget K R B+1+
  PCPSerializerCapacity.Power.budget 1 16 (K*(R+B+1)^4)+1+14

theorem original_input (R B : ℕ) (j : Fin 40) : input R B (oldSlots j)=ColdScalars.input R B j:=by
  fin_cases j <;> rfl

theorem log_input (R B C : ℕ) (out : Fin 40→List Bool) (hc : out 14=List.replicate C true)
    (j : Fin (DimensionPolynomial.tapes 1)) :
    install oldSlots (input R B) out (logSlots j)=DimensionPolynomial.input 1 C j:=by
  by_cases hz : j=0
  · subst j
    change install oldSlots _ out (oldSlots 14)=_
    rw [install_slot _ old_injective,hc]
    rfl
  have hj : j.val≠0:=fun h=>hz (Fin.ext h)
  have hn : ∀ i,oldSlots i≠logSlots j:=by
    intro i he
    have hi:=i.isLt
    have hlval : (logSlots j).val=j.val+39:=by rw [logSlots,if_neg hz]
    have hival : (oldSlots i).val=i.val:=rfl
    have hv:=congrArg Fin.val he
    rw [hival,hlval] at hv
    omega
  rw [install_other _ _ _ _ hn]
  simp [input,logSlots,hz,hj,DimensionPolynomial.input,Fin.ext_iff]

theorem fixed_ready : ClockJoin.ReadyRun (HierarchyFixedWord.machine (List.replicate 6 true)) 14
    (fun _=>[]) (![List.replicate 6 true,List.replicate 6 false] : Fin 2→List Bool):=by
  obtain ⟨r,hr,ht,hh,hs⟩:=HierarchyFixedWord.word_ready (List.replicate 6 true)
  exact ⟨r,by simpa only [List.length_replicate] using hr,by simpa only [List.length_replicate] using ht,
    hh,by simpa only [List.length_replicate] using hs.le⟩

theorem logs_run (K R B : ℕ) : ∃ out,
    ClockJoin.ReadyRun (machine K) (budget K R B) (input R B) out ∧
      out 0=List.replicate R true ∧ out 1=List.replicate B true ∧
      out 14=List.replicate (K*(R+B+1)^4) true ∧ out 29=List.replicate (R+B+1) true ∧
      out 44=List.replicate (16*(K*(R+B+1)^4+1)) true ∧ out 55=List.replicate 6 true:=by
  obtain ⟨a,ha,a0,a1,ac,af⟩:=ColdScalars.scalar_run K R B
  have hfirst:=ha.focus oldSlots old_injective (input R B) (original_input R B)
  obtain ⟨b,hb,bc,bl⟩:=PCPSerializerCapacity.Power.capacity_run 1 16 (K*(R+B+1)^4)
  have hsecond:=hb.focus logSlots log_injective _ (log_input R B _ a ac)
  have hthird:=fixed_ready.focus sixSlots (by decide)
    (install logSlots (install oldSlots (input R B) a) b) (by
      intro j
      rw [install_other logSlots _ _ _ (by fin_cases j <;> decide),
        install_other oldSlots _ _ _ (by fin_cases j <;> decide)]
      fin_cases j <;> rfl)
  have whole:=ClockJoin.join _ _ _ _ _ _ _ (ClockJoin.join _ _ _ _ _ _ _ hfirst hsecond) hthird
  refine ⟨_,whole,?_,?_,?_,?_,?_,?_⟩
  · rw [install_other sixSlots _ _ 0 (by decide),install_other logSlots _ _ 0 (by decide)]
    exact (install_slot oldSlots old_injective _ _ 0).trans a0
  · rw [install_other sixSlots _ _ 1 (by decide),install_other logSlots _ _ 1 (by decide)]
    exact (install_slot oldSlots old_injective _ _ 1).trans a1
  · rw [install_other sixSlots _ _ 14 (by decide)]
    exact (install_slot logSlots log_injective _ _ 0).trans bc
  · rw [install_other sixSlots _ _ 29 (by decide),install_other logSlots _ _ 29 (by decide)]
    exact (install_slot oldSlots old_injective _ _ 29).trans af
  · rw [install_other sixSlots _ _ 44 (by decide)]
    change install logSlots _ b (logSlots (PCPSerializerCapacity.Power.outputSlot 1))=_
    rw [install_slot _ log_injective,bl]
    simp only [pow_one]
  · exact install_slot sixSlots (by decide) _ _ 0

end NearCubicWires.RepairOrdinary.CloseoutCaseTwo.ColdLogs
