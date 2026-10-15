import Proof.CaseAnalysis.RecoveryClauseLiteralRun

/-! The original clause's existing OR node changes exactly graph20, live
left45 and count25. Its71-bank source and decoder work remain retained. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedClauseOr
open LocalBitMultitape RepairRepresentation RecoveryRootRound
open RecoveryBoundedLiteralDock (slots slots_injective)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine:=RecoveryFocus.machine slots (RecoveryBoundedLiteralNode.machine 3)
def heads (H : Fin 71→ℕ) (result : List Bool):=Function.update H 20 result.length
def data (A : Fin 71→List Bool) (node C : ℕ) (result : List Bool):=
  Function.update (Function.update (Function.update A 20 result) 45 (ZeroPadding.pad C (List.replicate node true)))
    25 (List.replicate (node+1) true)
def graph (left right : ℕ) (out : List Bool):=out++RecoveryBoundedClauseNative.emitted 2 left right

theorem install_update (A : Fin 71→List Bool) (out : Fin 61→List Bool) (j : Fin 61) (value : List Bool) :
    install slots A (Function.update out j value)=Function.update (install slots A out) (slots j) value := by
  funext i
  by_cases hi : i=slots j
  · subst i
    rw [install_slot slots slots_injective,Function.update_self,Function.update_self]
  · rw [Function.update_of_ne hi]
    cases hp : RecoveryFocus.pick slots i with
    | none=>simp only [install,hp]
    | some k=>
      have he:=RecoveryFocus.slot_of_pick slots hp
      have hk : k≠j:=by intro h;subst k;exact hi he.symm
      simp only [install,hp,Function.update_of_ne hk]

theorem node_data (A : Fin 71→List Bool) (node C : ℕ) (result : List Bool) :
    install slots A (RecoveryBoundedLiteralNode.output (fun j=>A (slots j)) 3 node C result)=data A node C result := by
  change install slots A (Function.update (Function.update (Function.update (fun j=>A (slots j)) 20 result)
    45 (ZeroPadding.pad C (List.replicate node true))) 25 (List.replicate (node+1) true))=data A node C result
  rw [install_update,install_update,install_update,install_existing slots A (fun j=>A (slots j)) (by intro j;rfl)]
  rfl

theorem projected_heads (H : Fin 71→ℕ) (result : List Bool) (j : Fin 61) :
    heads H result (slots j)=RecoveryBoundedClauseGate.heads (fun i=>H (slots i)) result j := by
  by_cases hj : j=20
  · subst j;rfl
  · have hn : slots j≠20:=fun he=>hj (Fin.ext (congrArg (fun i : Fin 71=>i.val) he))
    simp only [heads,RecoveryBoundedClauseGate.heads,Function.update_of_ne hj,Function.update_of_ne hn]

theorem data_other (A : Fin 71→List Bool) (node C : ℕ) (result : List Bool) (i : Fin 71)
    (h20 : i≠20) (h25 : i≠25) (h45 : i≠45) : data A node C result i=A i := by
  simp only [data,Function.update_of_ne h20,Function.update_of_ne h25,Function.update_of_ne h45]

end NearCubicWires.RepairOrdinary.RecoveryBoundedClauseOr
