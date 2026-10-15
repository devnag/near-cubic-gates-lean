import Proof.CaseAnalysis.HierarchyClockCanonical
import Proof.Hierarchy.HierarchyFromInput
import Proof.Foundations.SourceCore

/-! The original refuter answer alone produces its exact canonical framed
hierarchy clock, with no bound/width input or new arithmetic program. This
feeds the shared Case1/Case2 hierarchy request. -/
namespace NearCubicWires.RepairSource.CloseoutHierarchyClock.Input
open LocalBitMultitape RepairOrdinary RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def tapes (D : Nat):=HierarchyFromInput.tapes D+3
def old (D : Nat) (i : Fin (HierarchyFromInput.tapes D)) : Fin (tapes D):=i.castAdd 3
def fresh (D : Nat) (i : Fin 3) : Fin (tapes D):=i.natAdd (HierarchyFromInput.tapes D)
def slots (D : Nat) (hD : 0<D) : Fin 4→Fin (tapes D):=
  ![old D (HierarchyFromInput.outputTape D hD),fresh D 0,fresh D 1,fresh D 2]
def input (D : Nat) (bits : List Bool) : Fin (tapes D)→List Bool:=
  Fin.addCases (HierarchyFromInput.input D bits) (fun _ : Fin 3=>[])

theorem old_injective (D : Nat) : Function.Injective (old D):=by
  intro a b h
  exact Fin.ext (congrArg (fun i : Fin (tapes D)=>i.val) h)
theorem old_fresh (D : Nat) (i : Fin (HierarchyFromInput.tapes D)) (j : Fin 3) : old D i≠fresh D j:=by
  intro h
  have hv:=congrArg Fin.val h
  have hi:=i.isLt
  change i.val=HierarchyFromInput.tapes D+j.val at hv
  omega
theorem slots_injective (D : Nat) (hD : 0<D) : Function.Injective (slots D hD):=by
  intro a b h
  have hv:=congrArg Fin.val h
  have ho:=(HierarchyFromInput.outputTape D hD).isLt
  fin_cases a <;> fin_cases b <;> simp [slots,old,fresh] at hv ⊢ <;> omega
theorem slots_input (D : Nat) (hD : 0<D) (j : Fin 4) :
    slots D hD j≠old D (HierarchyFromInput.field D 2):=by
  have hn : (HierarchyFromInput.outputTape D hD).val≠2:=by
    unfold HierarchyFromInput.outputTape
    rw [HierarchyFromInput.bound_val]
    split_ifs <;> omega
  intro h
  have hv:=congrArg Fin.val h
  have hl:=HierarchyFromInput.tapes_lower D
  fin_cases j <;> simp [slots,old,fresh,HierarchyFromInput.field] at hv
  · exact hn hv
  all_goals omega

def first (D C : Nat) (hD : 0<D):=RecoveryFocus.machine (old D) (HierarchyFromInput.machine D C hD)
def last (D : Nat) (hD : 0<D):=RecoveryFocus.machine (slots D hD) CloseoutHierarchyClock.machine
def machine (D C : Nat) (hD : 0<D):=Composition.machine (first D C hD) (last D hD)
def budget (D C : Nat) (bits : List Bool):=
  HierarchyFromInput.budget D C bits+1+(8*HierarchyBinary.width C D bits.length+11)

theorem input_run (D C : Nat) (hD : 0<D) (hC : 0<C) (bits : List Bool) :
    ∃ out,ClockJoin.ReadyRun (machine D C hD) (budget D C bits) (input D bits) out ∧
      out (old D (HierarchyFromInput.field D 2))=frame bits ∧
      out (fresh D 1)=frame (C*(bits.length^D+1)).bits:=by
  obtain ⟨r,hr,hbound,_,hx,hh,hs⟩:=HierarchyFromInput.from_input_run D C hD bits
  have hfirst : ClockJoin.ReadyRun (HierarchyFromInput.machine D C hD)
      (HierarchyFromInput.budget D C bits) (HierarchyFromInput.input D bits) r.final.tapes:=⟨r,hr,rfl,hh,hs⟩
  have ha:=hfirst.focus (old D) (old_injective D) (input D bits) (fun i=>Fin.addCases_left i)
  let a:=install (old D) (input D bits) r.final.tapes
  have af (j : Fin 3) : a (fresh D j)=[]:=
    (install_other _ _ _ _ (fun i=>old_fresh D i j)).trans (Fin.addCases_right j)
  obtain ⟨canonical,hc,hout⟩:=CloseoutHierarchyClock.canonical_run
    (HierarchyBinary.width C D bits.length) (C*(bits.length^D+1))
    (Nat.mul_pos hC (by omega)) (HierarchyBinary.bound_fits C D bits.length)
  have hin (j : Fin 4) : a (slots D hD j)=
      CanonicalPositiveOutput.input
        (SignedSortKey.binary (HierarchyBinary.width C D bits.length) (C*(bits.length^D+1))) j:=by
    fin_cases j
    · change install (old D) _ _ (old D (HierarchyFromInput.outputTape D hD))=_
      rw [install_slot _ (old_injective D)]
      exact hbound
    · exact af 0
    · exact af 1
    · exact af 2
  have hb:=hc.focus (slots D hD) (slots_injective D hD) a hin
  refine ⟨_,ClockJoin.join _ _ _ _ _ _ _ ha hb,?_,?_⟩
  · rw [install_other _ _ _ _ (slots_input D hD)]
    exact (install_slot _ (old_injective D) _ _ _).trans hx
  · change install (slots D hD) _ _ (slots D hD 2)=_
    rw [install_slot _ (slots_injective D hD)]
    exact hout

theorem hierarchy_run {k : Nat} (H : OrdinaryHierarchy (fun n=>n^(k+2))) (bits : List Bool) :
    ∃ out,ClockJoin.ReadyRun (machine (k+2) H.coefficient (by omega))
      (budget (k+2) H.coefficient bits) (input (k+2) bits) out ∧
      out (old (k+2) (HierarchyFromInput.field (k+2) 2))=frame bits ∧
      out (fresh (k+2) 1)=frame (H.time bits.length).bits:=
  input_run (k+2) H.coefficient (by omega) H.coefficientPositive bits

end
end NearCubicWires.RepairSource.CloseoutHierarchyClock.Input
