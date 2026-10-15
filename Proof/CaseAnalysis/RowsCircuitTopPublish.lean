import Proof.CaseAnalysis.RowsCircuitCopy

/-! Publish retained top request, support bitmap and count with the existing
paid C-copy. The original description sum keeps its append cursor for the
bottom traversal. No serialized prefix or top field is parsed again. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsCircuitTopPublish
open LocalBitMultitape RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def copySlots (j : Fin 3) : Fin 4→Fin 12:=![(![0,1,4] : Fin 3→Fin 12) j,⟨7+j.val,by omega⟩,5,6]
def sumSlots : Fin 4→Fin 12:=![2,3,10,11]
noncomputable def copy (j : Fin 3):=RecoveryFocus.machine (copySlots j) RecoveryBoundedTapeCopy.machine
noncomputable def copied01:=Composition.machine (copy 0) (copy 1)
noncomputable def copied:=Composition.machine copied01 (copy 2)
noncomputable def describe:=RecoveryFocus.machine sumSlots CloseoutRowsCircuitAppend.unary
noncomputable def machine:=Composition.machine copied describe
def bank (cap a b : ℕ) (sources : Fin 3→List Bool) (done : ℕ) : Fin 12→List Bool:=
  ![sources 0,sources 1,ZeroPadding.pad cap (List.replicate a true),ZeroPadding.pad cap (List.replicate b true),sources 2,
    List.replicate cap true,List.replicate (cap+1) false,
    if 0<done then ZeroPadding.pad cap (sources 0) else List.replicate cap false,
    if 1<done then ZeroPadding.pad cap (sources 1) else List.replicate cap false,
    if 2<done then ZeroPadding.pad cap (sources 2) else List.replicate cap false,[],List.replicate cap false]
def output (cap a b : ℕ) (sources : Fin 3→List Bool):=
  Function.update (bank cap a b sources 3) 10 (List.replicate (a+b) true)
def heads (a b : ℕ):=Function.update (fun _ : Fin 12=>0) 10 (a+b)
def budget (cap : ℕ):=8*cap+20

theorem bank_next (cap a b : ℕ) (sources : Fin 3→List Bool) (j : Fin 3) :
    bank cap a b sources (j.val+1)=Function.update (bank cap a b sources j.val)
      (copySlots j 1) (ZeroPadding.pad cap (sources j)):=by
  fin_cases j <;> funext i <;> fin_cases i <;> simp [bank,copySlots]

theorem copy_run (cap a b : ℕ) (sources : Fin 3→List Bool) (j : Fin 3)
    (hc : (sources j).length≤cap) :
    ClockJoin.ReadyRun (copy j) (2*cap+4) (bank cap a b sources j.val) (bank cap a b sources (j.val+1)):=by
  have inj:Function.Injective (copySlots j):=by fin_cases j <;> decide
  obtain ⟨r,hr,rh,rt,rs⟩:=CloseoutRowsCircuitCopy.copy_focus
    (copySlots j) inj cap (sources j) hc (fun _=>0) (bank cap a b sources j.val)
    (by intro i;rfl)
    (by intro i;fin_cases j <;> fin_cases i <;> simp [copySlots,bank,CloseoutRowsMetadataCopy.input])
  exact ⟨r,hr,rt.trans (bank_next cap a b sources j).symm,by intro i;rw [rh],rs.le⟩

theorem publish_run (cap a b : ℕ) (sources : Fin 3→List Bool)
    (hc : ∀ j,(sources j).length≤cap) (hab : a+b+2≤cap) : ∃ r,
    run machine (budget cap) (bank cap a b sources 0)=some r ∧
      r.steps≤budget cap ∧ r.final.heads=heads a b ∧ r.final.tapes=output cap a b sources:=by
  have first:=ClockJoin.join (copy 0) (copy 1) _ _ _ _ _
    (copy_run cap a b sources 0 (hc 0)) (copy_run cap a b sources 1 (hc 1))
  have all:=ClockJoin.join copied01 (copy 2) _ _ _ _ _ first (copy_run cap a b sources 2 (hc 2))
  obtain ⟨p,hp,pt,ph,ps⟩:=all
  obtain ⟨q,hq,qh,qt,qs⟩:=CloseoutRowsCircuitAppend.unary_focus sumSlots (by decide) cap a b [] hab
    (fun _=>0) (bank cap a b sources 3)
    (by intro i;fin_cases i <;> rfl) (by intro i;fin_cases i <;> rfl)
  have he:Composition.restart p.final describe.start=
      (⟨describe.start,fun _=>0,bank cap a b sources 3⟩ : Configuration 12 5):=by
    apply configuration_ext
    · rfl
    · funext i;exact ph i
    · exact pt
  change runFrom describe _ ⟨describe.start,fun _=>0,bank cap a b sources 3⟩=some q at hq
  rw [←he] at hq
  have whole:=Composition.run_join copied describe _ _ _ p q hp hq
  have hb:((2*cap+4+1+(2*cap+4))+1+(2*cap+4))+1+(2*(a+b)+6)≤budget cap:=by
    unfold budget;omega
  have more:=runFrom_moreFuel machine _
    (budget cap-(((2*cap+4+1+(2*cap+4))+1+(2*cap+4))+1+(2*(a+b)+6))) _
    (Composition.joinedReceipt p q) whole
  rw [Nat.add_sub_of_le hb] at more
  rw [show sumSlots 2=(10 : Fin 12) by rfl] at qh qt
  refine ⟨_,more,?_,?_,?_⟩
  · change p.steps+1+q.steps≤budget cap
    omega
  · change q.final.heads=heads a b
    simpa only [List.nil_append,List.length_replicate,heads] using qh
  · change q.final.tapes=output cap a b sources
    simpa only [List.nil_append,output] using qt

end NearCubicWires.RepairOrdinary.CloseoutRowsCircuitTopPublish
