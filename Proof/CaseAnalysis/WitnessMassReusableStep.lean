import Proof.CaseAnalysis.WitnessMassPaddedStep

/-! One reusable direct term-mass update, including the paid clear of its
seven normalizer scratch cells under the enclosing parser driver. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.MassReusableStep
open LocalBitMultitape RecoveryRootRound RecoveryExecution SignedSortKey
open CompetitorSumFold
open CompetitorValidity (Estimate)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def old (i : Fin 103) : Fin 105:=i.castAdd 2
def native (i : Fin 94) : Fin 105:=i.castAdd 11
def eraseSlots (i : Fin 9) : Fin 105:=⟨96+i.val,by omega⟩
def first:=RecoveryFocus.machine old MassStep.machine
def last:=RecoveryFocus.machine eraseSlots (RecoveryScratchErase.resetMachine 7)
def machine:=Composition.machine first last
def budget (C B : ℕ):=MassStep.budget B+1+(2*C+4)
def input (C : ℕ) (ambient : Fin 94→List Bool) (nb db : List Bool) : Fin 105→List Bool:=
  Fin.addCases (m:=103) (n:=2) (motive:=fun _=>List Bool)
    (MassPaddedStep.input C ambient nb db) ![List.replicate C true,List.replicate (C+1) false]
theorem old_injective : Function.Injective old:=by
  intro i j h;exact Fin.ext (congrArg (fun k : Fin 105=>k.val) h)
theorem erase_injective : Function.Injective eraseSlots:=by
  intro i j h
  have hv:=congrArg (fun k : Fin 105=>k.val) h
  apply Fin.ext
  change 96+i.val=96+j.val at hv
  omega
theorem old_outside (i : Fin 105) (hi : 103 ≤ i.val) : ∀ j,old j≠i:=by
  intro j h
  have hv:=congrArg (fun k : Fin 105=>k.val) h
  change j.val=i.val at hv
  omega
theorem erase_outside (i : Fin 105) (hi : i.val<96) : ∀ j,eraseSlots j≠i:=by
  intro j h
  have hv:=congrArg (fun k : Fin 105=>k.val) h
  change 96+j.val=i.val at hv
  omega
theorem input_native (C : ℕ) (ambient : Fin 94→List Bool) (nb db : List Bool) (i : Fin 94) :
    input C ambient nb db (native i)=ambient i:=by
  rw [show native i=old (MassPrepare.old i) by rfl,input,old,Fin.addCases_left]
  exact MassPaddedStep.input_native C ambient nb db i
theorem input_num (C : ℕ) (ambient : Fin 94→List Bool) (nb db : List Bool) :
    input C ambient nb db 94=frame nb:=ZeroPadding.pad_zero _
theorem input_den (C : ℕ) (ambient : Fin 94→List Bool) (nb db : List Bool) :
    input C ambient nb db 95=frame db:=ZeroPadding.pad_zero _

theorem step_run (C B b n d : ℕ) (a : Estimate) (source : List Bool)
    (ambient : Fin 94→List Bool) (h : Store B a source ambient)
    (ha : a.Valid B) (hb : b≤B) (hn : n<2^b) (hd : d<2^b) (hpos : 0<d)
    (hc : MassStep.budget B+1≤C)
    (hi : ∀ i,(MassPrepare.input ambient (binary b n) (binary b d) i).length≤C) : ∃ next,
    ClockJoin.ReadyRun machine (budget C B)
      (input C ambient (binary b n) (binary b d)) (input C next (binary b n) (binary b d)) ∧
      Store B (CompetitorRationalNumerators.add a ⟨n,0,d⟩) source next:=by
  obtain ⟨out,hr,hs,hnout,hdout,hbound⟩:=MassPaddedStep.step_run C B b n d a source ambient h ha hb hn hd hpos hc hi
  let start:=input C ambient (binary b n) (binary b d)
  have hf:=hr.focus old old_injective start (by intro i;simp [start,input,old])
  let bank:=install old start out
  have get (i : Fin 103) : bank (old i)=out i:=install_slot old old_injective start out i
  have fresh (i : Fin 105) (hi : 103 ≤ i.val) : bank i=start i:=
    install_other old start out i (old_outside i hi)
  let backing (j : Fin 7):=out ⟨96+j.val,by omega⟩
  obtain ⟨e,er,et,eh,es⟩:=RecoveryScratchErase.erase_ready C (C+1) backing (fun j=>hbound _)
  have eready:ClockJoin.ReadyRun (RecoveryScratchErase.resetMachine 7) (2*C+4)
      (eraseInput C backing) (eraseInput C (fun _ : Fin 7=>List.replicate C false)):=by
    refine ⟨e,er,?_,eh,es.le⟩
    simpa only [eraseInput,max_self] using et
  have ef:=eready.focus eraseSlots erase_injective bank (by
    refine Fin.addCases (m:=8) (n:=1) ?_ ?_
    · intro i
      refine Fin.addCases (m:=7) (n:=1) ?_ ?_ i
      · intro j
        rw [eraseInput,Fin.addCases_left,Fin.addCases_left]
        exact get ⟨96+j.val,by omega⟩
      · intro j;fin_cases j;exact fresh 103 (by decide)
    · intro j;fin_cases j;exact fresh 104 (by decide))
  let final:=install eraseSlots bank (eraseInput C (fun _ : Fin 7=>List.replicate C false))
  let next (i : Fin 94):=final (native i)
  have keep (i : Fin 103) (hi : i.val<96) : final (old i)=out i:=by
    rw [show final=install _ _ _ by rfl,install_other _ _ _ _ (erase_outside _ hi)]
    exact get i
  have eject (j : Fin 9) : final (eraseSlots j)=eraseInput C (fun _ : Fin 7=>List.replicate C false) j:=
    install_slot _ erase_injective _ _ _
  have heq:final=input C next (binary b n) (binary b d):=by
    funext i
    refine Fin.addCases (m:=94) (n:=11) ?_ ?_ i
    · intro j;exact (input_native C next _ _ j).symm
    · intro j;fin_cases j
      · exact ((keep 94 (by decide)).trans hnout).trans (input_num C next _ _).symm
      · exact ((keep 95 (by decide)).trans hdout).trans (input_den C next _ _).symm
      · exact (eject 0).trans (MassPaddedStep.input_scratch C next _ _ 96 (by decide)).symm
      · exact (eject 1).trans (MassPaddedStep.input_scratch C next _ _ 97 (by decide)).symm
      · exact (eject 2).trans (MassPaddedStep.input_scratch C next _ _ 98 (by decide)).symm
      · exact (eject 3).trans (MassPaddedStep.input_scratch C next _ _ 99 (by decide)).symm
      · exact (eject 4).trans (MassPaddedStep.input_scratch C next _ _ 100 (by decide)).symm
      · exact (eject 5).trans (MassPaddedStep.input_scratch C next _ _ 101 (by decide)).symm
      · exact (eject 6).trans (MassPaddedStep.input_scratch C next _ _ 102 (by decide)).symm
      · exact eject 7
      · exact eject 8
  have hall:=ClockJoin.join first last _ _ _ _ _ hf ef
  rw [show install eraseSlots bank (eraseInput C (fun _ : Fin 7=>List.replicate C false))=final by rfl,heq] at hall
  refine ⟨next,hall,?_⟩
  have hn:next=MassPrepare.project out:=by
    funext i
    exact keep (MassPrepare.old i) (by change i.val<96;omega)
  rw [hn]
  exact hs

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.MassReusableStep
