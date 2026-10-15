import Proof.CaseAnalysis.RowsOriginalClause
import Proof.CaseAnalysis.CaseTwoMetadata
import Proof.CaseAnalysis.CaseTwoVariablePrep

/-! The same native source yields S, then the already decoded original
coordinates produce query templates and the two actual auxiliary flags. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsOriginalClassify
open LocalBitMultitape ExtDecompositionBatch RecoveryRootRound SourceInterfaces RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def headerSlots (i : Fin 56) : Fin 91:=if i.val<19 then ⟨i.val,by omega⟩ else ⟨i.val+27,by omega⟩
theorem header_injective : Function.Injective headerSlots := by
  intro i j h;have hv:=congrArg Fin.val h
  simp only [headerSlots] at hv
  split_ifs at hv <;>dsimp only at hv <;>apply Fin.ext <;>omega

def leftSlots : Fin 6→Fin 91:=![29,55,83,84,85,86]
def rightSlots : Fin 6→Fin 91:=![41,55,87,88,89,90]
def heads : Fin 91→ℕ:=Fin.addCases (m:=46) (n:=45) (motive:=fun _=>ℕ) CloseoutRowsOriginalClause.heads (fun _=>0)
def extra (C : ℕ) : Fin 45→List Bool:=Fin.addCases (m:=37) (n:=8) (motive:=fun _=>List Bool)
  (fun _=>[]) (fun _=>List.replicate C false)
def data (C : ℕ) (A : Fin 46→List Bool) : Fin 91→List Bool:=Fin.addCases (m:=46) (n:=45) (motive:=fun _=>List Bool) A (extra C)
noncomputable def header:=RecoveryFocus.machine headerSlots CloseoutCaseTwo.Metadata.machine
noncomputable def left:=RecoveryFocus.machine leftSlots CloseoutCaseTwo.VariablePrep.machine
noncomputable def right:=RecoveryFocus.machine rightSlots CloseoutCaseTwo.VariablePrep.machine
noncomputable def machine:=Composition.machine (Composition.machine header left) right

theorem prepare_run (index S C : ℕ) : ∃ out,
    Step CloseoutCaseTwo.VariablePrep.machine (CloseoutCaseTwo.VariablePrep.budget index S)
      (fun _=>0) (fun i=>ZeroPadding.pad (if i=1 then 0 else C) (CloseoutCaseTwo.VariablePrep.input index S i))
      (fun _=>0) out ∧ out 0=ZeroPadding.pad C (List.replicate index true) ∧
      out 1=UnaryTemplate.tape S ∧ out 2=ZeroPadding.pad C (UnaryTemplate.tape index) ∧
      out 4=ZeroPadding.pad C [decide (S ≤ index)] := by
  obtain ⟨out,hr,h2,h4,h0,h1⟩:=CloseoutCaseTwo.VariablePrep.prepare_run index S
  obtain ⟨rr,hrr,rt,rh,_⟩:=hr
  have raw:=Step.of_run hrr (funext rh) rt
  refine ⟨_,raw.pad (fun i=>if i=1 then 0 else C),?_,?_,?_,?_⟩
  · change ZeroPadding.pad C (out 0)=_;rw [h0]
  · change ZeroPadding.pad 0 (out 1)=_;rw [h1];exact ZeroPadding.pad_zero _
  · change ZeroPadding.pad C (out 2)=_;rw [h2]
  · change ZeroPadding.pad C (out 4)=_;rw [h4]

theorem run {n0 : ℕ} (r : PCPPRequest n0) (p : PointwisePCPP r.circuit)
    (C a b : ℕ) (A : Fin 46→List Bool)
    (a0 : A 0=pcppOutput r p) (a13 : A 13=UnaryTemplate.tape r.arity)
    (a29 : A 29=ZeroPadding.pad C (List.replicate a true))
    (a41 : A 41=ZeroPadding.pad C (List.replicate b true)) :
    ∃ out,Step machine (CloseoutCaseTwo.Metadata.budget r p+1+
      CloseoutCaseTwo.VariablePrep.budget a p.systematicBits+1+
      CloseoutCaseTwo.VariablePrep.budget b p.systematicBits) heads (data C A) heads out ∧
      (∀ j : Fin 46,out (j.castAdd 45)=A j) ∧
      out 55=UnaryTemplate.tape p.systematicBits ∧
      out 83=ZeroPadding.pad C (UnaryTemplate.tape a) ∧ out 85=ZeroPadding.pad C [decide (p.systematicBits≤a)] ∧
      out 87=ZeroPadding.pad C (UnaryTemplate.tape b) ∧ out 89=ZeroPadding.pad C [decide (p.systematicBits≤b)] := by
  let cache : Fin 19→List Bool:=fun j=>A (j.castAdd 27)
  obtain ⟨base,hbase,_,bh,bkeep,_,_,bs,_,_⟩:=CloseoutCaseTwo.Metadata.metadata_run r p
    PCPPQueryClauseReuse.heads cache rfl rfl a0 a13
  have hhi : ∀ j,heads (headerSlots j)=CloseoutCaseTwo.Metadata.heads PCPPQueryClauseReuse.heads j := by
    intro j;fin_cases j <;>rfl
  have raw:=Step.of_run hbase bh rfl
  have first:=raw.dock headerSlots header_injective heads (data C A) hhi (by intro j;fin_cases j <;>rfl)
  have hh : dockH headerSlots heads (CloseoutCaseTwo.Metadata.heads PCPPQueryClauseReuse.heads)=heads :=
    dockH_existing _ _ _ hhi
  let B:=install headerSlots (data C A) base.final.tapes
  have first':Step header (CloseoutCaseTwo.Metadata.budget r p) heads (data C A) heads B:=first.congr hh rfl
  have sys : B 55=UnaryTemplate.tape p.systematicBits:=
    (install_slot headerSlots header_injective _ _ 28).trans bs
  have indexA : B 29=ZeroPadding.pad C (List.replicate a true):=
    (install_other headerSlots _ _ _ (by decide)).trans a29
  have indexB : B 41=ZeroPadding.pad C (List.replicate b true):=
    (install_other headerSlots _ _ _ (by decide)).trans a41
  have fresh (j : Fin 91) (hj : 83≤j.val) : B j=List.replicate C false := by
    change (install headerSlots (data C A) base.final.tapes) j=_
    rw [install_other headerSlots _ _ _ (by
      intro k he;have hv:=congrArg Fin.val he;have hk:=k.isLt
      simp only [headerSlots] at hv;split_ifs at hv <;>dsimp only at hv <;>omega)]
    have he : j=Fin.natAdd 46 (Fin.natAdd 37 (⟨j.val-83,by omega⟩ : Fin 8)) := by apply Fin.ext;dsimp;omega
    rw [he];simp only [data,extra,Fin.addCases_right]
  obtain ⟨l,hl,l0,l1,l2,l4⟩:=prepare_run a p.systematicBits C
  have second:=hl.dock leftSlots (by decide) heads B (by intro j;fin_cases j <;>rfl) (by
    intro j;fin_cases j
    · exact indexA
    · exact sys.trans (ZeroPadding.pad_zero _).symm
    all_goals exact fresh _ (by decide))
  have lh : dockH leftSlots heads (fun _=>0)=heads:=dockH_existing _ _ _ (by intro j;fin_cases j <;>rfl)
  let D:=install leftSlots B l
  have second':Step left (CloseoutCaseTwo.VariablePrep.budget a p.systematicBits) heads B heads D:=second.congr lh rfl
  obtain ⟨u,hu,u0,u1,u2,u4⟩:=prepare_run b p.systematicBits C
  have third:=hu.dock rightSlots (by decide) heads D (by intro j;fin_cases j <;>rfl) (by
    intro j;fin_cases j
    · exact (install_other leftSlots _ _ _ (by decide)).trans indexB
    · exact (install_slot leftSlots (by decide) _ _ 1).trans (l1.trans (ZeroPadding.pad_zero _).symm)
    all_goals exact (install_other leftSlots _ _ _ (by decide)).trans (fresh _ (by decide)))
  have rh : dockH rightSlots heads (fun _=>0)=heads:=dockH_existing _ _ _ (by intro j;fin_cases j <;>rfl)
  refine ⟨_,(first'.seq second').seq (third.congr rh rfl),?_,?_,?_,?_,?_,?_⟩
  · intro j
    by_cases ja : j=29
    · subst j
      exact (install_other rightSlots _ _ _ (by decide)).trans
        ((install_slot leftSlots (by decide) _ _ 0).trans (l0.trans a29.symm))
    by_cases jb : j=41
    · subst j
      exact (install_slot rightSlots (by decide) _ _ 0).trans (u0.trans a41.symm)
    have leftAway : ∀ k,leftSlots k≠j.castAdd 45 := by
      intro k he;have hv:=congrArg Fin.val he;have hj:=j.isLt
      have neq : j.val≠29:=fun h=>ja (Fin.ext h)
      fin_cases k <;>simp [leftSlots] at hv <;>omega
    have rightAway : ∀ k,rightSlots k≠j.castAdd 45 := by
      intro k he;have hv:=congrArg Fin.val he;have hj:=j.isLt
      have neq : j.val≠41:=fun h=>jb (Fin.ext h)
      fin_cases k <;>simp [rightSlots] at hv <;>omega
    rw [install_other rightSlots _ _ _ rightAway]
    change (install leftSlots B l) _=_
    rw [install_other leftSlots _ _ _ leftAway]
    by_cases small : j.val<19
    · let k : Fin 19:=⟨j.val,small⟩
      have hs : headerSlots (k.castAdd 37)=j.castAdd 45 := by
        apply Fin.ext;simp [headerSlots,k,small]
      change (install headerSlots (data C A) base.final.tapes) _=_
      rw [←hs]
      exact (install_slot headerSlots header_injective _ _ (k.castAdd 37)).trans (bkeep k)
    · change (install headerSlots (data C A) base.final.tapes) _=_
      rw [install_other headerSlots _ _ _ (by
        intro k he;have hv:=congrArg Fin.val he;have hj:=j.isLt
        by_cases hk : k.val<19
        · have eq : k.val=j.val:=by simpa [headerSlots,hk] using hv
          omega
        · have eq : k.val+27=j.val:=by simpa [headerSlots,hk] using hv
          omega)]
      exact Fin.addCases_left j
  · exact (install_slot rightSlots (by decide) _ _ 1).trans u1
  · exact (install_other rightSlots _ _ _ (by decide)).trans ((install_slot leftSlots (by decide) _ _ 2).trans l2)
  · exact (install_other rightSlots _ _ _ (by decide)).trans ((install_slot leftSlots (by decide) _ _ 4).trans l4)
  · exact (install_slot rightSlots (by decide) _ _ 2).trans u2
  · exact (install_slot rightSlots (by decide) _ _ 4).trans u4

end NearCubicWires.RepairOrdinary.CloseoutRowsOriginalClassify
