import Proof.CaseAnalysis.WitnessMassScalar
import Proof.CaseAnalysis.WitnessMassTail

/-! Prepare one absolute coefficient directly from the retained checked
binary numerator and denominator. The native addition bank is reused. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.MassPrepare
open LocalBitMultitape RecoveryRootRound RecoveryExecution SignedSortKey
open CompetitorSumFold CompetitorReusableDecision CompetitorRationalDecision
open CompetitorValidity (Estimate)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def old (i : Fin 94) : Fin 103:=i.castAdd 9
def zeroSlots : Fin 5→Fin 103:=![6,96,2,97,98]
def numSlots : Fin 5→Fin 103:=![6,94,3,99,100]
def denSlots : Fin 5→Fin 103:=![84,95,5,101,102]
def clear:=RecoveryFocus.machine old (clearProgram workSlot)
def zero:=RecoveryFocus.machine zeroSlots ClockNormalize.machine
def num:=RecoveryFocus.machine numSlots ClockNormalize.machine
def den:=RecoveryFocus.machine denSlots ClockNormalize.machine
def firstThree:=Composition.machine (Composition.machine clear zero) num
def machine:=Composition.machine firstThree den
def input (ambient : Fin 94→List Bool) (nb db : List Bool) : Fin 103→List Bool:=
  Fin.addCases (m := 94) (n := 9) (motive := fun _=>List Bool)
    ambient ![frame nb,frame db,[],[],[],[],[],[],[]]
def project (bank : Fin 103→List Bool) (i : Fin 94):=bank (old i)
def budget (B : ℕ):=(2*capacity B+4)+1+(4*width B+4)+1+(4*width B+4)+1+(4*B+4)

theorem old_injective : Function.Injective old:=by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin 103=>k.val) h)
theorem old_outside (i : Fin 103) (hi : 94 ≤ i.val) : ∀ j,old j≠i:=by
  intro j h
  have hv:=congrArg (fun k : Fin 103=>k.val) h
  change j.val=i.val at hv
  omega
theorem input_old (ambient : Fin 94→List Bool) (nb db : List Bool) (i : Fin 94) :
    input ambient nb db (old i)=ambient i:=by simp [input,old]

theorem install_project (slot : Fin 5→Fin 103) (hi : Function.Injective slot)
    (w t : Fin 94) (h0 : slot 0=old w) (h2 : slot 2=old t)
    (hx : ∀ j,j≠0→j≠2→94 ≤ (slot j).val)
    (bank : Fin 103→List Bool) (out : Fin 5→List Bool) (ho : out 0=bank (old w)) :
    project (install slot bank out)=Function.update (project bank) t (out 2):=by
  funext i
  by_cases ht:i=t
  · subst i
    rw [Function.update_self]
    exact (congrArg (install slot bank out) h2.symm).trans (install_slot slot hi bank out 2)
  rw [Function.update_of_ne ht]
  by_cases hw:i=w
  · subst i
    exact ((congrArg (install slot bank out) h0.symm).trans (install_slot slot hi bank out 0)).trans ho
  apply install_other
  intro j he
  by_cases hj0:j=0
  · subst j
    rw [h0] at he
    exact hw (old_injective he).symm
  by_cases hj2:j=2
  · subst j
    rw [h2] at he
    exact ht (old_injective he).symm
  have hv:=congrArg (fun k : Fin 103=>k.val) he
  have hj:=hx j hj0 hj2
  change (slot j).val=i.val at hv
  omega

theorem prepare_run (B b n d : ℕ) (a : Estimate) (source : List Bool)
    (ambient : Fin 94→List Bool) (h : Store B a source ambient)
    (hb : b ≤ B) (hn : n<2^b) (hd : d<2^b) : ∃ output,
    ClockJoin.ReadyRun machine (budget B) (input ambient (binary b n) (binary b d)) output ∧
      project output=prepared B ⟨n,0,d⟩ ambient ∧
      output 94=frame (binary b n) ∧ output 95=frame (binary b d):=by
  obtain ⟨c,hc,ch,ct,cs⟩:=clear_run workSlot work_injective
    (fun j=>work_outside j 88 (by decide)) (fun j=>work_outside j 90 (by decide))
    (fun j=>work_outside j 91 (by decide)) (capacity B) 0 ambient h.eraseDriver h.eraseReset
    (fun j=>h.support ⟨(workSlot j).val,(work_range j).1⟩)
  let clean:=cleared (capacity B) workSlot ambient
  have hc0:cfg (clearProgram workSlot).start 0 ambient=
      initialConfiguration (clearProgram workSlot) ambient:=by
    apply configuration_ext
    · rfl
    · funext i;simp only [cfg,heads,initialConfiguration,ite_self]
    · rfl
  rw [hc0] at hc
  have hcr:ClockJoin.ReadyRun (clearProgram workSlot) (2*capacity B+4) ambient clean:=by
    refine ⟨c,hc,ct,?_,cs.le⟩
    intro i
    rw [ch]
    simp only [heads,ite_self]
  let initial:=input ambient (binary b n) (binary b d)
  have hcf:=hcr.focus old old_injective initial (input_old _ _ _)
  let bank0:=install old initial clean
  have p0:project bank0=clean:=by funext i;exact install_slot old old_injective initial clean i
  have fresh (i : Fin 103) (hi : 94 ≤ i.val) : bank0 i=initial i:=
    install_other old initial clean i (old_outside i hi)
  have clean6:clean 6=List.replicate (width B) true:=
    (clear_keep _ _ _ 6 (fun j=>(work_range j).2.2.2.2.1)).trans h.wideWidth
  have clean84:clean 84=List.replicate B true:=
    (clear_keep _ _ _ 84 (fun j=>(work_range j).2.2.2.2.2)).trans h.shortWidth
  have clean2:clean 2=List.replicate (capacity B) false:=clear_cell _ _ _ 2 ⟨0,rfl⟩
  have clean3:clean 3=List.replicate (capacity B) false:=clear_cell _ _ _ 3 ⟨1,rfl⟩
  have clean5:clean 5=List.replicate (capacity B) false:=clear_cell _ _ _ 5 ⟨2,rfl⟩
  obtain ⟨z,hz,z0,z2⟩:=MassScalar.zero_run (capacity B) (width B)
  have hzf:=hz.focus zeroSlots (by decide) bank0 (by
    intro i;fin_cases i
    · exact (congrFun p0 6).trans clean6
    · exact (fresh 96 (by decide)).trans (by rfl)
    · exact (congrFun p0 2).trans clean2
    · exact (fresh 97 (by decide)).trans (by rfl)
    · exact (fresh 98 (by decide)).trans (by rfl))
  let bank1:=install zeroSlots bank0 z
  have p1:project bank1=Function.update clean 2 (ZeroPadding.pad (capacity B) (frame (binary (width B) 0))):=by
    rw [install_project zeroSlots (by decide) 6 2 rfl rfl (by decide) bank0 z
      (z0.trans ((congrFun p0 6).trans clean6).symm),p0,z2]
  have nb1:bank1 94=frame (binary b n):=by
    rw [show bank1=install zeroSlots _ _ by rfl,install_other _ _ _ _ (by decide),fresh 94 (by decide)]
    rfl
  obtain ⟨u,hu,u0,u1,u2⟩:=MassScalar.scalar_run (capacity B) (width B) (binary b n)
    (by simp only [binary_length];unfold width;omega)
  have huf:=hu.focus numSlots (by decide) bank1 (by
    intro i;fin_cases i
    · change project bank1 6=List.replicate (width B) true
      rw [p1,Function.update_of_ne (by decide : (6 : Fin 94)≠2),clean6]
    · exact nb1
    · change project bank1 3=List.replicate (capacity B) false
      rw [p1,Function.update_of_ne (by decide : (3 : Fin 94)≠2),clean3]
    · change bank1 99=[]
      rw [show bank1=install zeroSlots _ _ by rfl,install_other _ _ _ _ (by decide),fresh 99 (by decide)];rfl
    · change bank1 100=[]
      rw [show bank1=install zeroSlots _ _ by rfl,install_other _ _ _ _ (by decide),fresh 100 (by decide)];rfl)
  let bank2:=install numSlots bank1 u
  have u0keep:u 0=bank1 (old 6):=by
    rw [u0]
    exact ((congrFun p1 6).trans (by simpa only [Function.update_of_ne (by decide : (6 : Fin 94)≠2)] using clean6)).symm
  have p2:project bank2=Function.update (project bank1) 3
      (ZeroPadding.pad (capacity B) (frame (binary (width B) n))):=by
    rw [install_project numSlots (by decide) 6 3 rfl rfl (by decide) bank1 u u0keep,u2,binary_value b n hn]
  have db2:bank2 95=frame (binary b d):=by
    rw [show bank2=install numSlots _ _ by rfl,install_other _ _ _ _ (by decide),
      show bank1=install zeroSlots _ _ by rfl,install_other _ _ _ _ (by decide),fresh 95 (by decide)]
    rfl
  have b284:bank2 (old 84)=List.replicate B true:=by
    change project bank2 84=_
    rw [p2,Function.update_of_ne (by decide : (84 : Fin 94)≠3),p1,
      Function.update_of_ne (by decide : (84 : Fin 94)≠2),clean84]
  obtain ⟨v,hv,v0,v1,v2⟩:=MassScalar.scalar_run (capacity B) B (binary b d)
    (by simpa only [binary_length] using hb)
  have hvf:=hv.focus denSlots (by decide) bank2 (by
    intro i;fin_cases i
    · exact b284
    · exact db2
    · change project bank2 5=List.replicate (capacity B) false
      rw [p2,Function.update_of_ne (by decide : (5 : Fin 94)≠3),p1,
        Function.update_of_ne (by decide : (5 : Fin 94)≠2),clean5]
    · change bank2 101=[]
      rw [show bank2=install numSlots _ _ by rfl,install_other _ _ _ _ (by decide),
        show bank1=install zeroSlots _ _ by rfl,install_other _ _ _ _ (by decide),fresh 101 (by decide)];rfl
    · change bank2 102=[]
      rw [show bank2=install numSlots _ _ by rfl,install_other _ _ _ _ (by decide),
        show bank1=install zeroSlots _ _ by rfl,install_other _ _ _ _ (by decide),fresh 102 (by decide)];rfl)
  let bank3:=install denSlots bank2 v
  have p3:project bank3=Function.update (project bank2) 5
      (ZeroPadding.pad (capacity B) (frame (binary B d))):=by
    rw [install_project denSlots (by decide) 84 5 rfl rfl (by decide) bank2 v
      (v0.trans b284.symm),v2,binary_value b d hd]
  refine ⟨bank3,ClockJoin.join firstThree den _ _ _ _ _
    (ClockJoin.join (Composition.machine clear zero) num _ _ _ _ _
      (ClockJoin.join clear zero _ _ _ _ _ hcf hzf) huf) hvf,?_,?_,?_⟩
  · rw [p3,p2,p1]
    funext i
    simp only [prepared,termLoaded_cases,Function.update_apply,Fin.ext_iff]
    split_ifs <;> first | rfl | omega
  · rw [show bank3=install denSlots _ _ by rfl,install_other _ _ _ _ (by decide)]
    exact (install_slot numSlots (by decide) bank1 u 1).trans u1
  · exact (install_slot denSlots (by decide) bank2 v 1).trans v1

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.MassPrepare
