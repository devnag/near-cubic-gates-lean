import Proof.CaseAnalysis.CaseTwoTagReady
import Proof.CaseAnalysis.CaseTwoNativeCopy

/-! Publish a non-sentinel private tag to the native node stream, then
physically erase its temporary buffer and copying scratch for the next row. -/
namespace NearCubicWires.RepairOrdinary.CloseoutCaseTwo.TagPublish
open LocalBitMultitape RepairRepresentation RecoveryRootRound StablePartition.Workspace
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def data (C : ℕ) (source : List Bool) (offset : ℕ) (tagWord out : List Bool) : Fin 28→List Bool:=
  Fin.addCases (m:=27) (n:=1) (TagReady.data C source offset tagWord false) (fun _ : Fin 1=>out)
def heads (out : List Bool) (i : Fin 28):=if i=27 then out.length else 0
def copySlots : Fin 4→Fin 28:=![21,1,27,22]
def clearSlots : Fin 5→Fin 28:=![21,1,25,23,24]
noncomputable def first:=RecoveryFocus.machine copySlots NativeCopy.machine
noncomputable def last:=RecoveryFocus.machine clearSlots (RecoveryScratchErase.resetMachine 3)
noncomputable def machine:=Composition.machine first last
def budget (tag C : ℕ):=NativeCopy.budget tag+2*C+5

theorem pad_false (C : ℕ) (hC : 1≤C) : ZeroPadding.pad C [false]=List.replicate C false:=by
  obtain ⟨k,rfl⟩:=Nat.exists_eq_add_of_le hC
  simp [ZeroPadding.pad,List.replicate_succ,Nat.add_comm]

theorem data_other (C offset : ℕ) (source tagWord oldOut out : List Bool) (j : Fin 28)
    (hj21 : j≠21) (hj27 : j≠27) :
    data C source offset [] out j=data C source offset tagWord oldOut j:=by
  fin_cases j <;> first | contradiction | rfl

theorem publish_run (C offset tag : ℕ) (source out : List Bool)
    (hC : 2*natBitLength tag+3≤C) :
    ∃ r,runFrom machine (budget tag C)
      ⟨machine.start,heads out,data C source offset (natWord tag) out⟩=some r ∧
      r.steps≤budget tag C ∧ r.final.heads=heads (out++natWord tag) ∧
      r.final.tapes=data C source offset [] (out++natWord tag) := by
  obtain ⟨base,hr,ht,hh,hs⟩:=NativeCopy.append_run tag C out hC
  obtain ⟨a,ar,_af,ast,ah,atp,keep⟩:=RecoveryFocus.dock copySlots (by decide) NativeCopy.machine _
    (heads out) (data C source offset (natWord tag) out)
    (⟨NativeCopy.machine.start,NativeCopy.heads out,NativeCopy.input tag C out⟩ : Configuration 4 _)
    (by intro j;fin_cases j <;> rfl)
    (by intro j;fin_cases j <;> simp [data,TagReady.data,TagReady.localData,TagReady.pads,
      TagObserve.data,NativeCopy.input,copySlots,Fin.addCases]) base hr
  have aHeads : a.final.heads=heads (out++natWord tag) := by
    funext i
    by_cases hi : ∃ j,copySlots j=i
    · obtain ⟨j,rfl⟩:=hi
      rw [ah j,hh]
      fin_cases j <;> rfl
    · rw [(keep i (by intro j h;exact hi ⟨j,h⟩)).1]
      have hn : i≠27:=fun h=>hi ⟨2,h.symm⟩
      simp only [heads,if_neg hn]
  have a21 : a.final.tapes 21=ZeroPadding.pad C (natWord tag):=(atp 0).trans (by rw [ht];rfl)
  have a1 : a.final.tapes 1=overlay (UnaryTemplate.tape (natBitLength tag)) (List.replicate C false):=
    (atp 1).trans (by rw [ht];rfl)
  have a27 : a.final.tapes 27=out++natWord tag:=(atp 2).trans (by rw [ht];rfl)
  have a22 : a.final.tapes 22=List.replicate C false:=(atp 3).trans (by rw [ht];rfl)
  have a25 : a.final.tapes 25=ZeroPadding.pad C [false]:=
    (keep 25 (by decide)).2.trans (by simp [data,TagReady.data,TagReady.localData,
      TagReady.pads,TagObserve.data,Fin.addCases])
  let backing : Fin 3→List Bool:=![a.final.tapes 21,a.final.tapes 1,a.final.tapes 25]
  have hb : ∀ j,(backing j).length≤C:=by
    intro j;fin_cases j
    · change (a.final.tapes 21).length≤C
      rw [a21,ZeroPadding.pad_length,PCPPQueryCost.word_length]
      omega
    · change (a.final.tapes 1).length≤C
      rw [a1]
      exact NativeCopy.scratch_bound tag C hC
    · change (a.final.tapes 25).length≤C
      rw [a25,pad_false C (by omega),List.length_replicate]
  have a23 : a.final.tapes 23=List.replicate C true:=
    (keep 23 (by decide)).2.trans (by simp [data,TagReady.data,TagReady.localData,
      TagReady.pads,TagObserve.data,Fin.addCases])
  have a24 : a.final.tapes 24=List.replicate (C+1) false:=
    (keep 24 (by decide)).2.trans (by simp [data,TagReady.data,TagReady.localData,
      TagReady.pads,TagObserve.data,Fin.addCases])
  obtain ⟨b,br,bh,bt,bs⟩:=(RecoveryScratchErase.erase_ready C (C+1) backing hb).focus_at
    clearSlots (by decide) a.final.heads a.final.tapes
    (by intro j;fin_cases j <;> first | rfl | exact a23 | exact a24)
    (by intro j;rw [aHeads];fin_cases j <;> rfl)
  have whole:=Composition.run_join first last _ _ _ a b ar br
  have he : NativeCopy.budget tag+1+(2*C+4)=budget tag C:=by unfold budget;omega
  rw [he] at whole
  refine ⟨Composition.joinedReceipt a b,whole,?_,bh.trans aHeads,?_⟩
  · change a.steps+1+b.steps≤budget tag C
    rw [ast,hs,bs];unfold budget;omega
  · change b.final.tapes=_
    rw [bt]
    apply HierarchyAllocation.install_eq clearSlots (by decide)
    · intro j;fin_cases j <;>
        simp [data,TagReady.data,TagReady.localData,TagReady.pads,TagObserve.data,clearSlots,Fin.addCases]
      · simp [ZeroPadding.pad]
      · exact pad_false C (by omega)
    · intro i hi
      by_cases h27 : i=27
      · subst i;exact a27.symm
      by_cases h22 : i=22
      · subst i
        simpa [data,TagReady.data,TagReady.localData,TagReady.pads,TagObserve.data,Fin.addCases] using a22.symm
      have hi21 : i≠21:=fun h=>hi 0 h.symm
      have hi1 : i≠1:=fun h=>hi 1 h.symm
      rw [(keep i (by intro j;fin_cases j <;> first | exact Ne.symm hi21 | exact Ne.symm hi1 | exact Ne.symm h27 | exact Ne.symm h22)).2]
      exact data_other C offset source (natWord tag) out (out++natWord tag) i hi21 h27

end NearCubicWires.RepairOrdinary.CloseoutCaseTwo.TagPublish
