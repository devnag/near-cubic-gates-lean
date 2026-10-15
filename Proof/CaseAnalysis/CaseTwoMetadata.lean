import Proof.CaseAnalysis.CaseTwoShape
import Proof.PCP.PCPPNativeTemplateRaw

/-! Read the actual PCPP header and copy its actual arity driver. The native
source and the caller's entire cache survive; no dimension is an extra input. -/
namespace NearCubicWires.RepairOrdinary.CloseoutCaseTwo.Metadata
open LocalBitMultitape RepairRepresentation SourceInterfaces RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def shapeSlots (i : Fin 34) : Fin 56:=if i=0 then 0 else ⟨i.val+18,by omega⟩
def rawSlots : Fin 5→Fin 56:=![13,52,53,54,55]
def shape:=RecoveryFocus.machine shapeSlots Shape.machine
def raw:=RecoveryFocus.machine rawSlots PCPPNativeTemplateRaw.machine
def machine:=Composition.machine shape raw
def input (A : Fin 19→List Bool) : Fin 56→List Bool:=Fin.addCases (m:=19) (n:=37) A (fun _=>[])
def heads (H : Fin 19→ℕ) : Fin 56→ℕ:=Fin.addCases (m:=19) (n:=37) H (fun _=>0)
def tail {n0 : ℕ} (r : PCPPRequest n0) (p : PointwisePCPP r.circuit):=
  (PCPPQuerySupport.supportRows r p).flatten++PCPPQuerySupport.clauseTail r p
def budget {n0 : ℕ} (r : PCPPRequest n0) (p : PointwisePCPP r.circuit):=
  Shape.budget p.systematicBits p.auxiliaryBits p.clauseBits+1+(4*r.arity+16)
theorem source_word {n0 : ℕ} (r : PCPPRequest n0) (p : PointwisePCPP r.circuit) :
    Shape.word p.systematicBits p.auxiliaryBits p.clauseBits (tail r p)=pcppOutput r p:=by
  rw [PCPPQuerySupport.output_word]
  simp [Shape.word,tail,PCPPQuerySupport.headerBits,PCPPQueryField.fourBits,
    PCPPQueryField.pairBits,PCPPQueryField.fieldBits,List.append_assoc]
theorem shape_injective : Function.Injective shapeSlots:=by
  intro i j he
  have h:=congrArg Fin.val he
  apply Fin.ext
  by_cases hi : i=0 <;>by_cases hj : j=0
  all_goals simp only [shapeSlots,hi,hj,if_true,if_false,Fin.val_zero,Fin.val_mk] at h
  all_goals first | exact congrArg Fin.val (hi.trans hj.symm) | omega
theorem shape_other (i : Fin 19) (hi : i≠0) : ∀ j,shapeSlots j≠i.castAdd 37:=by
  intro j he
  have hv:=congrArg Fin.val he
  have hb:=i.isLt
  have hi0 : i.val≠0:=fun h=>hi (Fin.ext h)
  by_cases hj : j=0
  · simp only [shapeSlots,hj,if_true,Fin.val_zero,Fin.val_castAdd] at hv
    omega
  · have hj0 : j.val≠0:=fun h=>hj (Fin.ext h)
    simp only [shapeSlots,hj,if_false,Fin.val_mk,Fin.val_castAdd] at hv
    omega
theorem outside_shape (i : Fin 56) (hi : 52 ≤ i.val) : ∀ j,shapeSlots j≠i:=by
  intro j he
  have hv:=congrArg Fin.val he
  have hb:=j.isLt
  by_cases hj : j=0 <;>simp only [shapeSlots,hj,if_true,if_false,Fin.val_zero,Fin.val_mk] at hv <;>omega
theorem new_head (H : Fin 19→ℕ) (i : Fin 56) (hi : 19 ≤ i.val) : heads H i=0:=by
  have he:i=Fin.natAdd 19 (⟨i.val-19,by omega⟩ : Fin 37):=by apply Fin.ext;dsimp;omega
  rw [he];exact Fin.addCases_right _
theorem new_input (A : Fin 19→List Bool) (i : Fin 56) (hi : 19 ≤ i.val) : input A i=[]:=by
  have he:i=Fin.natAdd 19 (⟨i.val-19,by omega⟩ : Fin 37):=by apply Fin.ext;dsimp;omega
  rw [he];exact Fin.addCases_right _
theorem raw_other (j : Fin 19) (hj : j≠13) : ∀ i,rawSlots i≠j.castAdd 37:=by
  intro i he
  have hv:=congrArg Fin.val he
  have hb:=j.isLt
  have hjv : j.val≠13:=fun h=>hj (Fin.ext h)
  fin_cases i <;>simp [rawSlots] at hv <;>omega

theorem metadata_run {n0 : ℕ} (r : PCPPRequest n0) (p : PointwisePCPP r.circuit)
    (H : Fin 19→ℕ) (A : Fin 19→List Bool) (h0 : H 0=0) (h13 : H 13=1)
    (a0 : A 0=pcppOutput r p) (a13 : A 13=UnaryTemplate.tape r.arity) : ∃ out,
    runFrom machine (budget r p) ⟨machine.start,heads H,input A⟩=some out ∧
      out.steps≤budget r p ∧ out.final.heads=heads H ∧
      (∀ j,out.final.tapes (j.castAdd 37)=A j) ∧
      out.final.tapes 52=List.replicate r.arity true ∧ out.final.tapes 53=List.replicate r.arity true ∧
      out.final.tapes 28=UnaryTemplate.tape p.systematicBits ∧
      out.final.tapes 38=UnaryTemplate.tape p.auxiliaryBits ∧
      out.final.tapes 48=UnaryTemplate.tape p.clauseBits:=by
  obtain ⟨sh,hs,sh0,shdims⟩:=Shape.shape_run p.systematicBits p.auxiliaryBits p.clauseBits (tail r p)
  have hw:=source_word r p
  rw [hw] at sh0
  obtain ⟨first,hfirst,fh,ft,fs⟩:=hs.focus_at shapeSlots shape_injective (heads H) (input A)
    (by intro j
        by_cases hj : j=0
        · subst j;change A 0=Shape.word _ _ _ _;rw [hw];exact a0
        · have hj0 : j.val≠0:=fun h=>hj (Fin.ext h)
          rw [new_input A _ (by simp only [shapeSlots,hj,if_false,Fin.val_mk];omega)]
          simp only [Shape.input,SourceHandoff.sourceTapes,hj0,if_false])
    (by intro j
        by_cases hj : j=0
        · subst j;exact h0
        · have hj0 : j.val≠0:=fun h=>hj (Fin.ext h)
          exact new_head H _ (by simp only [shapeSlots,hj,if_false,Fin.val_mk];omega))
  have firstCache (j : Fin 19) : first.final.tapes (j.castAdd 37)=A j:=by
    rw [ft]
    by_cases hj : j=0
    · subst j;exact (install_slot shapeSlots shape_injective _ sh 0).trans (sh0.trans a0.symm)
    · rw [install_other shapeSlots _ _ _ (shape_other j hj)];exact Fin.addCases_left j
  obtain ⟨q,hq,qs,q0,q1,q2,_,qh⟩:=PCPPNativeTemplateRaw.template_run r.arity
  obtain ⟨last,hl,_,ls,lh,lt,keep⟩:=RecoveryFocus.dock rawSlots (by decide)
    PCPPNativeTemplateRaw.machine _ first.final.heads first.final.tapes (PCPPNativeTemplateRaw.entry r.arity)
    (by intro j;rw [fh];fin_cases j
        · exact h13
        all_goals exact new_head H _ (by decide))
    (by intro j;fin_cases j
        · exact (firstCache 13).trans a13
        all_goals
          rw [ft,install_other shapeSlots _ _ _ (outside_shape _ (by decide))]
          exact new_input A _ (by decide)) q hq
  have whole:=Composition.run_join shape raw _ _ _ first last hfirst hl
  refine ⟨_,whole,?_,?_,?_,(lt 1).trans q1,(lt 2).trans q2,?_,?_,?_⟩
  · change first.steps+1+last.steps≤_
    rw [ls,qs]
    unfold budget
    omega
  · change last.final.heads=heads H
    funext j
    by_cases he : ∃ i,rawSlots i=j
    · obtain ⟨i,rfl⟩:=he
      rw [lh,qh]
      fin_cases i
      · exact h13.symm
      all_goals exact (new_head H _ (by decide)).symm
    · rw [(keep j (by intro i hi;exact he ⟨i,hi⟩)).1,fh]
  · intro j
    change last.final.tapes (j.castAdd 37)=_
    by_cases hj : j=13
    · subst j;exact (lt 0).trans (q0.trans a13.symm)
    · rw [(keep _ (raw_other j hj)).2]
      exact firstCache j
  all_goals
    change last.final.tapes _=_
    rw [(keep _ (by decide)).2,ft]
    first
    | exact (install_slot shapeSlots shape_injective _ sh 10).trans (shdims 0)
    | exact (install_slot shapeSlots shape_injective _ sh 20).trans (shdims 1)
    | exact (install_slot shapeSlots shape_injective _ sh 30).trans (shdims 2)

end
end NearCubicWires.RepairOrdinary.CloseoutCaseTwo.Metadata
