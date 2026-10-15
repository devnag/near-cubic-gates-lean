import Proof.CaseAnalysis.RecoveryGrammarFoldStep

/-! The retained scalar copies have physical false backing. The original
prototype printer preserves this backing and writes the same reload packet. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedGrammarPrototype
open LocalBitMultitape RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def scalarSlots : Fin 5→Fin 84:=![79,80,81,82,83]
def scalarValues (C index value limit upper : ℕ) : Fin 5→List Bool:=
  ![List.replicate index true,List.replicate limit true,List.replicate value true,
    List.replicate upper true,List.replicate C true]
def scalarCapacity (B : ℕ) (i : Fin 84):=if 79 ≤ i.val then B else 0
def scalarPadded (B : ℕ) (A : Fin 84→List Bool):=fun i=>ZeroPadding.pad (scalarCapacity B i) (A i)

theorem scalar_padding (B : ℕ) (A : Fin 84→List Bool) (values : Fin 5→List Bool)
    (hA : ∀ j,A (scalarSlots j)=ZeroPadding.pad B (values j)) :
    scalarPadded B (install scalarSlots A values)=A := by
  funext i
  by_cases hi : ∃ j,scalarSlots j=i
  · obtain ⟨j,rfl⟩:=hi
    change ZeroPadding.pad (scalarCapacity B (scalarSlots j)) (install scalarSlots A values (scalarSlots j))=_
    rw [install_slot scalarSlots (by decide),hA j]
    have he : scalarCapacity B (scalarSlots j)=B:=by fin_cases j <;> rfl
    rw [he]
  · have hk : i.val<79 := by
      by_contra hn
      have hv : i.val=79 ∨ i.val=80 ∨ i.val=81 ∨ i.val=82 ∨ i.val=83:=by omega
      rcases hv with hv|hv|hv|hv|hv
      all_goals apply hi
      · exact ⟨0,Fin.ext hv.symm⟩
      · exact ⟨1,Fin.ext hv.symm⟩
      · exact ⟨2,Fin.ext hv.symm⟩
      · exact ⟨3,Fin.ext hv.symm⟩
      · exact ⟨4,Fin.ext hv.symm⟩
    change ZeroPadding.pad (scalarCapacity B i) (install scalarSlots A values i)=_
    rw [install_other scalarSlots A values i (by intro j he;exact hi ⟨j,he⟩)]
    simp only [scalarCapacity,show ¬79 ≤ i.val by omega,if_false,ZeroPadding.pad_zero]

theorem scalar_padded_output (B : ℕ) (A : Fin 84→List Bool) (bits : List Bool) :
    scalarPadded B (Function.update A 75 bits)=Function.update (scalarPadded B A) 75 bits := by
  funext i
  by_cases hi : i=75
  · subst i
    change ZeroPadding.pad 0 bits=bits
    exact ZeroPadding.pad_zero _
  · simp only [scalarPadded,Function.update_of_ne hi]

theorem padded_ready_run (C index value limit upper B : ℕ)
    (H : Fin 84→ℕ) (A : Fin 84→List Bool)
    (hH : ∀ i∈([79,80,81,82,83] : List (Fin 84)),H i=0)
    (hHs : H 75=0) (hHd : H 76=0) (hHl : H 73=0)
    (hA : ∀ j,A (scalarSlots j)=ZeroPadding.pad B (scalarValues C index value limit upper j))
    (hAl : A 73=List.replicate B false) (hAd : A 76=List.replicate B true)
    (hAs : A 75=List.replicate B false)
    (bIndex : 2*index+4≤B) (bLimit : 2*limit+4≤B) (bValue : 2*value+4≤B)
    (bUpper : 2*upper+4≤B) (bC : 2*C+4≤B)
    (bp : (RecoveryBoundedRowReload.word (fields C index value limit upper)).length≤B) :
    ∃ r,runFrom ready (readyBudget C index value limit upper B) ⟨ready.start,H,A⟩=some r ∧
      r.steps≤readyBudget C index value limit upper B ∧ r.final.heads=H ∧
      r.final.tapes=Function.update A 75
        (ZeroPadding.pad B (RecoveryBoundedRowReload.word (fields C index value limit upper))) := by
  let logical:=install scalarSlots A (scalarValues C index value limit upper)
  have old (i : Fin 84) (hi : i.val<79) : logical i=A i:=
    install_other scalarSlots A _ i (by
      intro j he
      have hv : 79 ≤ (scalarSlots j).val:=by fin_cases j <;> decide
      rw [he] at hv
      omega)
  have val (j : Fin 5) : logical (scalarSlots j)=scalarValues C index value limit upper j:=
    install_slot scalarSlots (by decide) A _ j
  obtain ⟨p,pr,ps,ph,pt⟩:=ready_run C index value limit upper B H logical hH hHs hHd hHl
    (val 0) (val 1) (val 2) (val 3) (val 4)
    (by rw [old 73 (by decide)];exact hAl)
    (by rw [old 76 (by decide)];exact hAd)
    (by rw [old 75 (by decide)];exact hAs) bIndex bLimit bValue bUpper bC bp
  obtain ⟨r,rr,rf,rs,_⟩:=ZeroPadding.run_config ready (scalarCapacity B) _ _ p pr
  have hp : scalarPadded B logical=A:=scalar_padding B A _ hA
  have hc : ZeroPadding.config (scalarCapacity B) ⟨ready.start,H,logical⟩=
      (⟨ready.start,H,A⟩ : Configuration 84 _) := by
    apply configuration_ext
    · rfl
    · rfl
    · exact hp
  rw [hc] at rr
  refine ⟨r,rr,rs.le.trans ps,?_,?_⟩
  · rw [rf];exact ph
  · rw [rf]
    change scalarPadded B p.final.tapes=_
    rw [pt,scalar_padded_output,hp]

end NearCubicWires.RepairOrdinary.RecoveryBoundedGrammarPrototype
