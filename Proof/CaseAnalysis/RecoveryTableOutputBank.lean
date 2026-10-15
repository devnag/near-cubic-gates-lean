import Proof.CaseAnalysis.RecoveryTableRepeat

/-! The original first-field output selector runs in the table's retained
56-tape bank. Only its graph, output reference and consumed value change. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedTableOutput
open LocalBitMultitape RepairRepresentation
open BoundedOracleStructuralCircuit FinitePredicateCircuit
open RecoveryBoundedSelectorLoop (capacity sourceWord)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots (j : Fin 44) : Fin 56:=j.castAdd 12
theorem slots_injective : Function.Injective slots := by
  intro a b h
  exact Fin.ext (congrArg (fun i : Fin 56=>i.val) h)
noncomputable def machine:=RecoveryFocus.machine slots RecoveryBoundedSelectorReuse.machine
def outputHeads (H : Fin 56→ℕ) (result : List Bool) (i : Fin 56):=if i=20 then result.length else H i
def output (A : Fin 56→List Bool) (current value C : ℕ) (result : List Bool) (i : Fin 56):=
  if i=20 then result else if i=25 then List.replicate current true
  else if i=34 then ZeroPadding.pad C (List.replicate value true) else A i

theorem head_slot (H : Fin 56→ℕ) (out result : List Bool)
    (hH : ∀ j,H (slots j)=RecoveryBoundedSelectorReuse.finalHeads out j) (j : Fin 44) :
    outputHeads H result (slots j)=RecoveryBoundedSelectorReuse.finalHeads result j := by
  have hj:=hH j
  fin_cases j <;> first | rfl | exact hj

theorem tape_slot (A : Fin 56→List Bool) (index base current C D limit total L : ℕ) (out result source : List Bool)
    (hA : ∀ j,A (slots j)=RecoveryBoundedSelectorReuse.finalData index base C D 0 limit total L out source j) (j : Fin 44) :
    output A current total C result (slots j)=RecoveryBoundedSelectorReuse.finalData index current C D total limit total L result source j := by
  have hj:=hA j
  rw [RecoveryBoundedNodeTagSelect.local_data] at hj ⊢
  by_cases h20 : j=20
  · subst j;rfl
  by_cases h25 : j=25
  · subst j;rfl
  by_cases h34 : j=34
  · subst j;rfl
  have hs20 : slots j≠20:=fun h=>h20 (slots_injective h)
  have hs25 : slots j≠25:=fun h=>h25 (slots_injective h)
  have hs34 : slots j≠34:=fun h=>h34 (slots_injective h)
  have hc20 : (j.castAdd 2 : Fin 46)≠20:=fun h=>h20 (Fin.ext (congrArg (fun i : Fin 46=>i.val) h))
  have hc25 : (j.castAdd 2 : Fin 46)≠25:=fun h=>h25 (Fin.ext (congrArg (fun i : Fin 46=>i.val) h))
  have hc34 : (j.castAdd 2 : Fin 46)≠34:=fun h=>h34 (Fin.ext (congrArg (fun i : Fin 46=>i.val) h))
  simp only [output,if_neg hs20,if_neg hs25,if_neg hs34,hj,
    RecoveryBoundedSelectorPair.data,if_neg hc25,if_neg hc34,RecoveryBoundedNodeTagSelect.fixed_override,if_neg hc20]

theorem selector_run {n bound : ℕ} (b : BooleanDAGBuilder (descriptionWidth n bound))
    (row : Fin (bound+1)) (W D L : ℕ) (wires : List (LiveWire b))
    (out tail : List Bool) (H : Fin 56→ℕ) (A : Fin 56→List Bool)
    (hH : ∀ j,H (slots j)=RecoveryBoundedSelectorReuse.finalHeads out j)
    (hA : ∀ j,A (slots j)=RecoveryBoundedSelectorReuse.finalData
      (RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row 6) b.nodes.length (capacity W) D 0
        (OuterPCPRecovery.boundedCircuitFieldLimit n bound) wires.length L out
        (sourceWord (wires.map (fun w=>w.output.val))++tail) j)
    (hi : RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row 6+OuterPCPRecovery.boundedCircuitFieldLimit n bound ≤ W)
    (hp : b.nodes.length+wires.length*(3*OuterPCPRecovery.boundedCircuitFieldLimit n bound+2)+
      3*OuterPCPRecovery.boundedCircuitFieldLimit n bound ≤ W)
    (hg : (compileFirstFieldSelect b row wires).final.nodes.length ≤ W)
    (hc : wires.length ≤ W) (hD : 8388608*(W+1)^3 ≤ D)
    (hL : RecoveryBoundedSelectorFinish.logCapacity W ≤ L) :
    let compiled:=compileFirstFieldSelect b row wires
    let result:=out++compiled.extension.suffix.flatMap PCPPRequestNodeSchema.native
    ∃ r,runFrom machine (RecoveryBoundedSelectorReuse.resetBudget wires.length W) ⟨machine.start,H,A⟩=some r ∧
      r.steps ≤ RecoveryBoundedSelectorReuse.resetBudget wires.length W ∧
      r.final.heads=outputHeads H result ∧ r.final.tapes=output A compiled.output.val wires.length (capacity W) result := by
  let F:=OuterPCPRecovery.boundedCircuitFieldLimit n bound
  have hblock : 6+F ≤ rowWidth n bound:=by unfold rowWidth;omega
  obtain ⟨p,pr,ps,ph,pt⟩:=RecoveryBoundedSelectorReuse.reset_original_run b row 6 F W D L hblock wires out tail hi hp hg hc hD hL
  obtain ⟨r,hr,_,rs,rh,rt,rkeep⟩:=RecoveryFocus.dock slots slots_injective RecoveryBoundedSelectorReuse.machine _ H A
    (RecoveryBoundedSelectorReuse.entry (n:=n) row 6 F W D L b.nodes.length wires.length out
      (sourceWord (wires.map (fun w=>w.output.val))++tail))
    (by rw [RecoveryBoundedSelectorReuse.entry_heads];exact hH)
    (by rw [RecoveryBoundedSelectorReuse.entry_tapes];exact hA) p pr
  refine ⟨r,hr,rs.le.trans ps,?_,?_⟩
  · funext i
    by_cases hi : ∃ j,slots j=i
    · obtain ⟨j,rfl⟩:=hi
      rw [rh j,ph]
      exact (head_slot H out _ hH j).symm
    · rw [(rkeep i (by intro j h;exact hi ⟨j,h⟩)).1]
      have h20 : i≠20:=fun h=>hi ⟨20,h.symm⟩
      simp only [outputHeads,if_neg h20]
  · funext i
    by_cases hi : ∃ j,slots j=i
    · obtain ⟨j,rfl⟩:=hi
      rw [rt j,pt]
      exact (tape_slot A _ _ _ _ _ _ _ _ _ _ _ hA j).symm
    · rw [(rkeep i (by intro j h;exact hi ⟨j,h⟩)).2]
      have h20 : i≠20:=fun h=>hi ⟨20,h.symm⟩
      have h25 : i≠25:=fun h=>hi ⟨25,h.symm⟩
      have h34 : i≠34:=fun h=>hi ⟨34,h.symm⟩
      simp only [output,if_neg h20,if_neg h25,if_neg h34]

end NearCubicWires.RepairOrdinary.RecoveryBoundedTableOutput
