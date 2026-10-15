import Proof.CaseAnalysis.RecoverySuppliers
import Proof.CaseAnalysis.RecoveryGraphOriginal

/-! The original graph1664 bank is intact. Supplier old0..157 aliases its
accepted scalar insertion, while all supplier private work is disjoint. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedColdSourceGraph
open LocalBitMultitape RepairSource RepairSource.ProjectionNormalization RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section
variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)

def tapes (k d : ℕ):=1664+RecoveryBoundedColdSuppliers.tapes source k d
def graphSlots (k d : ℕ) (i : Fin 1664) : Fin (tapes source k d):=
  i.castAdd (RecoveryBoundedColdSuppliers.tapes source k d)
def supplierSlots (k d : ℕ) (i : Fin (RecoveryBoundedColdSuppliers.tapes source k d)) : Fin (tapes source k d):=
  if h : i.val < 158 then graphSlots source k d (RecoveryBoundedColdGraph.slots ⟨i.val,h⟩)
  else i.natAdd 1664
def hierarchyPort (k d : ℕ):=supplierSlots source k d (RecoveryBoundedColdSuppliers.hierarchyPort source k d)
def wPort (k d : ℕ):=supplierSlots source k d (RecoveryBoundedColdSuppliers.wPort source k d)
def input (k d : ℕ) (word : List Bool) (W : ℕ) (i : Fin (tapes source k d)):=
  if i=hierarchyPort source k d then word else if i=wPort source k d then List.replicate W true else []

theorem graph_injective (k d : ℕ) : Function.Injective (graphSlots source k d):=Fin.castAdd_injective _ _
theorem graph_fresh (k d : ℕ) (i : Fin 1664) (j : Fin (RecoveryBoundedColdSuppliers.tapes source k d)) :
    graphSlots source k d i≠j.natAdd 1664:=by
  intro he
  have hi:=i.isLt
  have hv:=congrArg Fin.val he
  change i.val=1664+j.val at hv
  omega
theorem supplier_injective (k d : ℕ) : Function.Injective (supplierSlots source k d):=by
  intro i j he
  dsimp only [supplierSlots] at he
  split_ifs at he with hi hj
  · exact Fin.ext (congrArg (fun z : Fin 158=>z.val)
      (RecoveryBoundedColdGraph.injective (graph_injective source k d he)))
  · exact False.elim (graph_fresh source k d _ _ he)
  · exact False.elim (graph_fresh source k d _ _ he.symm)
  · exact Fin.ext (by have hv:=congrArg Fin.val he;simp only [Fin.val_natAdd] at hv;omega)

theorem supplier_old (k d : ℕ) (i : Fin 158) :
    supplierSlots source k d (RecoveryBoundedColdSuppliers.old source k d i)=
      graphSlots source k d (RecoveryBoundedColdGraph.slots i):=by
  simp only [supplierSlots,show (RecoveryBoundedColdSuppliers.old source k d i).val < 158 from i.isLt,dif_pos]
  rfl
theorem supplier_fresh (k d : ℕ) (i : Fin (RecoveryBoundedColdSuppliers.tapes source k d))
    (hi : 158 ≤ i.val) : supplierSlots source k d i=i.natAdd 1664:=by
  simp only [supplierSlots,dif_neg (by omega : ¬ i.val < 158)]
theorem hierarchy_fresh (k d : ℕ) : hierarchyPort source k d=
    (RecoveryBoundedColdSuppliers.hierarchyPort source k d).natAdd 1664:=
  supplier_fresh source k d _ (by rw [RecoveryBoundedColdSuppliers.hierarchy_value])
theorem w_fresh (k d : ℕ) : wPort source k d=
    (RecoveryBoundedColdSuppliers.wPort source k d).natAdd 1664:=
  supplier_fresh source k d _ (Nat.le_of_lt (RecoveryBoundedColdSuppliers.base_large source k))
theorem inputs_distinct (k d : ℕ) : hierarchyPort source k d≠wPort source k d:=by
  intro he
  have h:=supplier_injective source k d he
  have hv:=congrArg Fin.val h
  rw [RecoveryBoundedColdSuppliers.hierarchy_value] at hv
  change 158=RecoveryBoundedColdSuppliers.base source k at hv
  have hb:=RecoveryBoundedColdSuppliers.base_large source k
  omega

theorem input_supplier (k d : ℕ) (word : List Bool) (W : ℕ)
    (i : Fin (RecoveryBoundedColdSuppliers.tapes source k d)) :
    input source k d word W (supplierSlots source k d i)=RecoveryBoundedColdSuppliers.input source k d word W i:=by
  by_cases hi : i=RecoveryBoundedColdSuppliers.hierarchyPort source k d
  · subst i
    simp only [input,hierarchyPort,if_true,RecoveryBoundedColdSuppliers.input,
      RecoveryBoundedColdSuppliers.hierarchy_value]
  have hih : supplierSlots source k d i≠hierarchyPort source k d:=fun he=>hi (supplier_injective source k d he)
  have hiv : i.val≠158:=fun he=>hi (Fin.ext (he.trans (RecoveryBoundedColdSuppliers.hierarchy_value source k d).symm))
  by_cases hw : i=RecoveryBoundedColdSuppliers.wPort source k d
  · subst i
    simp only [input,if_neg hih,wPort,if_true,RecoveryBoundedColdSuppliers.input,if_neg hiv]
    rw [if_pos (show (RecoveryBoundedColdSuppliers.wPort source k d).val=RecoveryBoundedColdSuppliers.base source k from rfl)]
  have hiw : supplierSlots source k d i≠wPort source k d:=fun he=>hw (supplier_injective source k d he)
  have hiwv : i.val≠RecoveryBoundedColdSuppliers.base source k:=fun he=>hw (Fin.ext he)
  simp only [input,if_neg hih,if_neg hiw,RecoveryBoundedColdSuppliers.input,if_neg hiv,if_neg hiwv]

theorem input_graph (k d : ℕ) (word : List Bool) (W : ℕ) (i : Fin 1664) :
    input source k d word W (graphSlots source k d i)=[]:=by
  have hi : graphSlots source k d i≠hierarchyPort source k d:=by
    rw [hierarchy_fresh]
    exact graph_fresh source k d i _
  have hw : graphSlots source k d i≠wPort source k d:=by
    rw [w_fresh]
    exact graph_fresh source k d i _
  simp only [input,if_neg hi,if_neg hw]

theorem supplier_away_graph (k d : ℕ) (i : Fin 1664)
    (hi : ∀ j,RecoveryBoundedColdGraph.slots j≠i) :
    ∀ j,supplierSlots source k d j≠graphSlots source k d i:=by
  intro j he
  dsimp only [supplierSlots] at he
  split_ifs at he with hj
  · exact hi _ (graph_injective source k d he)
  · exact graph_fresh source k d i j he.symm

end
end NearCubicWires.RepairOrdinary.RecoveryBoundedColdSourceGraph
