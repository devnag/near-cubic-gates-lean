import Proof.CaseAnalysis.RecoveryGrammarPrototypePadded

/-! Static original grammar atoms select retained physical scalars. The
categories occupy disjoint ports, so the checked printer needs no scalar copy. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedGrammarCold
open LocalBitMultitape RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

structure Selection where
  index : Fin 4
  limit : Fin 6
  value : Fin 7
  upper : Fin 3
deriving DecidableEq

def scalarPorts (p : Selection) : Fin 5→Fin 112:=
  ![⟨79+p.index.val,by omega⟩,⟨83+p.limit.val,by omega⟩,
    ⟨89+p.value.val,by omega⟩,⟨96+p.upper.val,by omega⟩,99]
theorem scalarPorts_injective (p : Selection) : Function.Injective (scalarPorts p) := by
  intro i j he
  fin_cases i <;> fin_cases j <;> simp_all [scalarPorts,Fin.ext_iff] <;> omega
theorem scalarPorts_high (p : Selection) (j : Fin 5) : 79 ≤ (scalarPorts p j).val := by
  fin_cases j <;> simp [scalarPorts] <;> omega

def printerSlots (p : Selection) : Fin 84→Fin 112:=
  Fin.addCases (m:=79) (n:=5) (fun j=>j.castAdd 33) (scalarPorts p)
theorem printerSlots_low (p : Selection) (j : Fin 79) :
    printerSlots p (j.castAdd 5)=j.castAdd 33:=by simp only [printerSlots,Fin.addCases_left]
theorem printerSlots_scalar (p : Selection) (j : Fin 5) :
    printerSlots p (RecoveryBoundedGrammarPrototype.scalarSlots j)=scalarPorts p j := by
  fin_cases j <;> rfl
theorem printerSlots_injective (p : Selection) : Function.Injective (printerSlots p) := by
  intro i j
  refine Fin.addCases (m:=79) (n:=5) (fun a=>?_) (fun a=>?_) i <;>
    refine Fin.addCases (m:=79) (n:=5) (fun b=>?_) (fun b=>?_) j
  · intro he
    rw [printerSlots_low,printerSlots_low] at he
    exact congrArg (fun k : Fin 79=>k.castAdd 5) (Fin.castAdd_injective 79 33 he)
  · intro he
    simp only [printerSlots,Fin.addCases_left,Fin.addCases_right] at he
    have hv:=congrArg Fin.val he
    change a.val=(scalarPorts p b).val at hv
    have hb:=scalarPorts_high p b
    exact False.elim (by omega)
  · intro he
    simp only [printerSlots,Fin.addCases_left,Fin.addCases_right] at he
    have hv:=congrArg Fin.val he
    change (scalarPorts p a).val=b.val at hv
    have ha:=scalarPorts_high p a
    exact False.elim (by omega)
  · intro he
    simp only [printerSlots,Fin.addCases_right] at he
    exact congrArg (fun k : Fin 5=>k.natAdd 79) (scalarPorts_injective p he)

noncomputable def printer (p : Selection):=
  RecoveryFocus.machine (printerSlots p) RecoveryBoundedGrammarPrototype.ready

theorem printer_run (p : Selection) (C index value limit upper B : ℕ)
    (H : Fin 112→ℕ) (A : Fin 112→List Bool)
    (hH : ∀ j,H (scalarPorts p j)=0) (hHs : H 75=0) (hHd : H 76=0) (hHl : H 73=0)
    (hA : ∀ j,A (scalarPorts p j)=ZeroPadding.pad B
      (RecoveryBoundedGrammarPrototype.scalarValues C index value limit upper j))
    (hAl : A 73=List.replicate B false) (hAd : A 76=List.replicate B true)
    (hAs : A 75=List.replicate B false)
    (bIndex : 2*index+4≤B) (bLimit : 2*limit+4≤B) (bValue : 2*value+4≤B)
    (bUpper : 2*upper+4≤B) (bC : 2*C+4≤B)
    (bp : (RecoveryBoundedRowReload.word (RecoveryBoundedGrammarPrototype.fields C index value limit upper)).length≤B) :
    ∃ r,runFrom (printer p) (RecoveryBoundedGrammarPrototype.readyBudget C index value limit upper B)
      ⟨(printer p).start,H,A⟩=some r ∧
      r.steps≤RecoveryBoundedGrammarPrototype.readyBudget C index value limit upper B ∧
      r.final.heads=H ∧ r.final.tapes=Function.update A 75 (ZeroPadding.pad B
        (RecoveryBoundedRowReload.word (RecoveryBoundedGrammarPrototype.fields C index value limit upper))) := by
  obtain ⟨a,ar,as,ah,atapes⟩:=RecoveryBoundedGrammarPrototype.padded_ready_run C index value limit upper B
    (fun i=>H (printerSlots p i)) (fun i=>A (printerSlots p i))
    (by
      intro i hi
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl|rfl
      exact hH 0;exact hH 1;exact hH 2;exact hH 3;exact hH 4)
    hHs hHd hHl (by intro j;rw [printerSlots_scalar];exact hA j)
    hAl hAd hAs bIndex bLimit bValue bUpper bC bp
  obtain ⟨r,rr,_,rs,rh,rt,rkeep⟩:=RecoveryFocus.dock (printerSlots p) (printerSlots_injective p)
    RecoveryBoundedGrammarPrototype.ready _ H A _ (by intro j;rfl) (by intro j;rfl) a ar
  refine ⟨r,rr,rs.le.trans as,?_,?_⟩
  · funext i
    by_cases hi : ∃ j,printerSlots p j=i
    · obtain ⟨j,rfl⟩:=hi
      rw [rh j,ah]
    · exact (rkeep i (by intro j he;exact hi ⟨j,he⟩)).1
  · funext i
    by_cases hi : ∃ j,printerSlots p j=i
    · obtain ⟨j,rfl⟩:=hi
      rw [rt j,atapes]
      by_cases hj : j=75
      · subst j;rfl
      · have hp : printerSlots p j≠75 := by
          intro he
          exact hj (printerSlots_injective p (show printerSlots p j=printerSlots p 75 from he))
        simp only [Function.update_of_ne hj,Function.update_of_ne hp]
    · rw [(rkeep i (by intro j he;exact hi ⟨j,he⟩)).2]
      exact (Function.update_of_ne (fun he=>hi ⟨75,he.symm⟩) _ _).symm

end NearCubicWires.RepairOrdinary.RecoveryBoundedGrammarCold
