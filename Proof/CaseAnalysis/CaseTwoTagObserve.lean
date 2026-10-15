import Proof.CaseAnalysis.CaseTwoFieldClear
import Proof.CaseAnalysis.CaseTwoTagTest

/-! The same original field producer writes a private native tag buffer.
The actual recovered unary tag is tested before the work bank is erased;
the resulting sentinel flag stays outside that bank. -/
namespace NearCubicWires.RepairOrdinary.CloseoutCaseTwo.TagObserve
open LocalBitMultitape RepairRepresentation OuterPCPRecovery RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def old (i : Fin 23) : Fin 26:=i.castAdd 3
def work (i : Fin 19) : Fin 26:=(FieldClear.work i).castAdd 1
def eraseSlots : Fin 21→Fin 26:=Fin.addCases (m:=19) (n:=2) work ![23,24]
def probeSlots : Fin 2→Fin 26:=![5,25]
theorem old_injective : Function.Injective old:=by
  intro i j h;apply Fin.ext;exact congrArg (fun x : Fin 26=>x.val) h
theorem erase_injective : Function.Injective eraseSlots:=by decide
def heads (out : List Bool) (i : Fin 26):=if i=21 then out.length else 0
def data (C : ℕ) (source : List Bool) (offset : ℕ) (out : List Bool) (flag : Bool) (i : Fin 26):=
  if i=0 then ZeroPadding.pad C (frame source)
  else if i=2 then ZeroPadding.pad C (List.replicate offset true)
  else if i=3 then ZeroPadding.pad C (List.replicate 6 true)
  else if i=21 then out else if i=23 then List.replicate C true
  else if i=24 then List.replicate (C+1) false
  else if i=25 then ZeroPadding.pad C [flag] else List.replicate C false
noncomputable def first:=RecoveryFocus.machine old FieldReady.machine
noncomputable def probe:=RecoveryFocus.machine probeSlots TagTest.machine
noncomputable def last:=RecoveryFocus.machine eraseSlots (RecoveryScratchErase.resetMachine 19)
noncomputable def machine:=Composition.machine (Composition.machine first probe) last
def budget (offset tag C : ℕ):=FieldReady.budget offset 6 tag+2*C+15

theorem tag_run (pre tail : List Bool) (tag : Fin 6) (C : ℕ) (out : List Bool) (flag : Bool)
    (hsource : 2*(pre++orderedNatBits 6 tag.val++tail).length+1≤C)
    (hoffset : pre.length≤C) (hwidth : 6≤C)
    (hbudget : FieldNative.budget pre.length 6 tag.val+1≤C) :
    let source:=pre++orderedNatBits 6 tag.val++tail
    ∃ r,runFrom machine (budget pre.length tag.val C)
      ⟨machine.start,heads out,data C source pre.length out flag⟩=some r ∧
      r.steps≤budget pre.length tag.val C ∧
      r.final.heads=heads (out++natWord tag.val) ∧
      r.final.tapes=data C source pre.length (out++natWord tag.val) (decide (tag.val=5)) := by
  let source:=pre++orderedNatBits 6 tag.val++tail
  obtain ⟨base,hr,hs,h0,h2,h3,h5,h21,hh21,hlocal⟩:=
    FieldReady.field_run pre tail 6 tag.val C out (by have h:=tag.isLt;omega)
      hsource hoffset hwidth hbudget
  obtain ⟨a,ar,_af,ast,ah,atp,keep⟩:=RecoveryFocus.dock old old_injective FieldReady.machine _
    (heads out) (data C source pre.length out flag) (FieldReady.entry C source pre.length 6 out)
    (by intro i;fin_cases i <;> rfl)
    (by intro i;fin_cases i <;>
      simp [data,old,FieldReady.entry,FieldReady.pads,FieldNative.data,ZeroPadding.config,
        Rewind.Workspace.capacities,Rewind.recording,Rewind.config,Fin.addCases,ZeroPadding.pad]) base hr
  have aHeads : a.final.heads=heads (out++natWord tag.val) := by
    funext i
    refine Fin.addCases (m:=23) (n:=3) (fun j=>?_) (fun j=>?_) i
    · change a.final.heads (old j)=heads (out++natWord tag.val) (old j)
      rw [ah j]
      by_cases hj : j=21
      · subst j;exact hh21
      · have he : old j≠21 := by
          intro h;apply hj;exact Fin.ext (congrArg (fun x : Fin 26=>x.val) h)
        simpa only [heads,if_neg he] using (hlocal j hj).1
    · fin_cases j
      · exact (keep 23 (by intro j;have h:=j.isLt;apply Fin.ne_of_val_ne;change j.val≠23;omega)).1
      · exact (keep 24 (by intro j;have h:=j.isLt;apply Fin.ne_of_val_ne;change j.val≠24;omega)).1
      · exact (keep 25 (by intro j;have h:=j.isLt;apply Fin.ne_of_val_ne;change j.val≠25;omega)).1
  have aWork (i : Fin 19) : (a.final.tapes (work i)).length≤C := by
    let j : Fin 23:=⟨(work i).val,by fin_cases i <;> decide⟩
    have hj : old j=work i:=Fin.ext rfl
    rw [←hj,atp j]
    exact (hlocal j (by fin_cases i <;> decide)).2
  have a5 : a.final.tapes 5=ZeroPadding.pad C (List.replicate tag.val true):=(atp 5).trans h5
  have a25 : a.final.tapes 25=ZeroPadding.pad C [flag]:=
    (keep 25 (by intro j;have h:=j.isLt;apply Fin.ne_of_val_ne;change j.val≠25;omega)).2
  obtain ⟨b,br,bh,bt,bs⟩:=(TagTest.ready tag flag C).focus_at probeSlots (by decide)
    a.final.heads a.final.tapes
    (by intro i;fin_cases i;exact a5;exact a25)
    (by intro i;rw [aHeads];fin_cases i <;> rfl)
  have bOther (i : Fin 26) (hi : i≠25) : b.final.tapes i=a.final.tapes i := by
    rw [bt]
    by_cases h5 : i=5
    · subst i
      have h:=install_slot probeSlots (by decide) a.final.tapes
        (![ZeroPadding.pad C (List.replicate tag.val true),ZeroPadding.pad C [decide (tag.val=5)]]) 0
      exact h.trans a5.symm
    · exact install_other probeSlots a.final.tapes _ i (by
        intro j;fin_cases j
        · exact Ne.symm h5
        · exact Ne.symm hi)
  have b25 : b.final.tapes 25=ZeroPadding.pad C [decide (tag.val=5)] := by
    rw [bt]
    exact install_slot probeSlots (by decide) a.final.tapes _ 1
  have bWork (i : Fin 19) : (b.final.tapes (work i)).length≤C := by
    rw [bOther _ (by fin_cases i <;> decide)]
    exact aWork i
  have b23 : b.final.tapes 23=List.replicate C true := by
    rw [bOther 23 (by decide)]
    exact (keep 23 (by intro j;have h:=j.isLt;apply Fin.ne_of_val_ne;change j.val≠23;omega)).2
  have b24 : b.final.tapes 24=List.replicate (C+1) false := by
    rw [bOther 24 (by decide)]
    exact (keep 24 (by intro j;have h:=j.isLt;apply Fin.ne_of_val_ne;change j.val≠24;omega)).2
  obtain ⟨c,cr,ch,ct,cs⟩:=(RecoveryScratchErase.erase_ready C (C+1)
    (fun i=>b.final.tapes (work i)) bWork).focus_at eraseSlots erase_injective b.final.heads b.final.tapes
    (by intro i;fin_cases i <;> first | rfl | exact b23 | exact b24)
    (by intro i;rw [bh,aHeads];fin_cases i <;> rfl)
  have ab:=Composition.run_join first probe _ _ _ a b ar br
  have whole:=Composition.run_join (Composition.machine first probe) last _ _ _
    (Composition.joinedReceipt a b) c ab cr
  have hb : FieldReady.budget pre.length 6 tag.val+1+9+1+(2*C+4)=budget pre.length tag.val C:=by
    unfold budget;omega
  rw [hb] at whole
  refine ⟨Composition.joinedReceipt (Composition.joinedReceipt a b) c,whole,?_,ch.trans (bh.trans aHeads),?_⟩
  · change a.steps+1+b.steps+1+c.steps≤budget pre.length tag.val C
    rw [ast];unfold budget;omega
  · change c.final.tapes=_
    rw [ct]
    apply HierarchyAllocation.install_eq eraseSlots erase_injective
    · intro i;fin_cases i <;> simp [data,eraseSlots,work,FieldClear.work,Fin.addCases]
    · intro i hi
      have hc : ∀ k : Fin 26,(∀ j,eraseSlots j≠k) → k=0 ∨ k=2 ∨ k=3 ∨ k=21 ∨ k=25:=by decide
      rcases hc i hi with rfl|rfl|rfl|rfl|rfl
      · exact ((bOther 0 (by decide)).trans ((atp 0).trans h0)).symm
      · exact ((bOther 2 (by decide)).trans ((atp 2).trans h2)).symm
      · exact ((bOther 3 (by decide)).trans ((atp 3).trans h3)).symm
      · exact ((bOther 21 (by decide)).trans ((atp 21).trans h21)).symm
      · exact b25.symm

end NearCubicWires.RepairOrdinary.CloseoutCaseTwo.TagObserve
