import Proof.Assembly.RowsPoolWeightArms

/-! The live mask physically selects copy versus literal zero. Both arms
consume the original native integer and leave one shared reusable width
scratch. The coordinate loop uses the retained mask cursor. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsPoolWeight
open LocalBitMultitape RecoveryRootRound RecoveryExecution ExtDecompositionBatch RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def probe : Machine 4 1 where
  descriptionBits:=0
  start:=0
  halted:=fun _=>true
  rule:=fun _ _=>none
def sizes : Fin 3→ℕ:=![1,6,11]
noncomputable def programs : (j : Fin 3)→Machine 4 (sizes j)
  | ⟨0,_⟩=>probe
  | ⟨1,_⟩=>copy
  | ⟨2,_⟩=>replaced
  | ⟨n+3,h⟩=>False.elim (by omega)
def next (j : Fin 3) (_ : Fin (sizes j)) (bits : Fin 4→Bool) : Option (Fin 3):=
  if j=0 then some (if bits 3 then 2 else 1) else none
noncomputable def choice:=RecoveryCalls.machine sizes programs 0 next

theorem probe_run (H : Fin 4→ℕ) (A : Fin 4→List Bool) :
    Step probe 0 H A H A:=by
  obtain ⟨r,hr,hf,_⟩:=(Timed.refl probe (⟨0,H,A⟩ : Configuration 4 1)).run (by rfl)
  exact Step.of_run hr (congrArg Configuration.heads hf) (congrArg Configuration.tapes hf)

private theorem arm_run (j : Fin 3) (hj : j≠0) (fuel : ℕ)
    (H H' : Fin 4→ℕ) (A A' : Fin 4→List Bool)
    (h : Step (programs j) fuel H A H' A')
    (selected : (if readTapeBit (A 3) (H 3) then (2 : Fin 3) else 1)=j) :
    Step choice (fuel+2) H A H' A':=by
  obtain ⟨p,hp,ph,pt,_⟩:=probe_run H A
  have hp':runFrom (programs 0) 0 ⟨(programs 0).start,H,A⟩=some p:=hp
  obtain ⟨u,hu,first⟩:=call_receipt sizes programs 0 next 0 j 0 _ p hp' (by
    change some (if readTapeBit (p.final.tapes 3) (p.final.heads 3) then (2 : Fin 3) else 1)=some j
    rw [pt,ph]
    exact congrArg some selected)
  rw [ph,pt] at first
  obtain ⟨r,hr,rh,rt,_⟩:=h
  obtain ⟨v,hv,last⟩:=stop_receipt sizes programs 0 next j fuel _ r hr (by
    simp only [next,if_neg hj])
  obtain ⟨all,ha,hf,hs⟩:=(first.trans last).run (by
    simp [RecoveryCalls.machine,RecoveryCalls.stopped])
  have hb:u+v≤fuel+2:=by omega
  have more:=runFrom_moreFuel choice (u+v) (fuel+2-(u+v)) _ all ha
  rw [Nat.add_sub_of_le hb] at more
  refine ⟨all,more,?_,?_,hs.le.trans hb⟩
  · rw [hf];exact rh
  · rw [hf];exact rt

def transformed (live : Bool) (z : ℤ) : ℤ:=if live then 0 else z
def choiceBudget (z : ℤ):=DecompositionSource.Fields.cost z+7

theorem choice_run (pre tail backing out mask : List Bool) (mpos : ℕ) (z : ℤ) (live : Bool)
    (hl : readTapeBit mask mpos=live) :
    Step choice (choiceBudget z) (heads pre.length mpos out)
      (data (pre++intWord z++tail) backing out mask)
      (heads (pre.length+(intWord z).length) mpos (out++intWord (transformed live z)))
      (data (pre++intWord z++tail) (DecompositionSource.Fields.saved z backing)
        (out++intWord (transformed live z)) mask):=by
  cases live with
  | false=>
    have h:=arm_run 1 (by decide) _ _ _ _ _ (copy_run pre tail backing out mask mpos z) (by
      change (if readTapeBit mask mpos then (2 : Fin 3) else 1)=1
      rw [hl];rfl)
    exact h.enlarge (by unfold choiceBudget;omega)
  | true=>
    have h:=arm_run 2 (by decide) _ _ _ _ _ (replaced_run pre tail backing out mask mpos z) (by
      change (if readTapeBit mask mpos then (2 : Fin 3) else 1)=2
      rw [hl];rfl)
    have ht:DecompositionSource.Fields.cost z+5+2=choiceBudget z:=by unfold choiceBudget;omega
    rw [ht] at h
    exact h

end NearCubicWires.RepairOrdinary.CloseoutRowsPoolWeight
