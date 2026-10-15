import Proof.CaseAnalysis.CloseoutRecoveryGrammarBank
import Proof.MachineModel.OrdinaryMatrixBucketRootPower

/-! The physically reloaded prototype is exactly the original unary
worker's padded input, including its original graph and actual count ports. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedGrammarBank
open LocalBitMultitape RecoveryRootRound
open RecoveryBoundedGrammarWorker (paddedData capacity)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def logicalReady (fields : Fin 78→List Bool) (node B : ℕ) (out stack packet source : List Bool):=
  RecoveryBoundedRowReload.loaded fields B (logicalBase node B out stack packet source)

theorem port_capacity (B : ℕ) (i : Fin 78) (hi : i∈RecoveryBoundedRowReload.ports) : capacity B i=B := by
  simp only [RecoveryBoundedRowReload.ports,List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

theorem logical_ready_padding (fields : Fin 78→List Bool) (node B : ℕ) (out stack packet source : List Bool) :
    paddedData B (logicalReady fields node B out stack packet source)=ready fields node B out stack packet source := by
  funext i
  change ZeroPadding.pad (capacity B i) (RecoveryBoundedRowReload.loaded fields B
    (logicalBase node B out stack packet source) i)=_
  rw [RecoveryBoundedRowReload.loaded_apply,ready,RecoveryBoundedRowReload.loaded_apply]
  by_cases hi : i∈RecoveryBoundedRowReload.ports
  · simp only [if_pos hi]
    rw [port_capacity B i hi]
    exact MatrixBucketRootPower.pad_pad B B _ (Nat.le_refl _)
  · simp only [if_neg hi]
    exact congrFun (logical_padding node B out stack packet source) i

theorem padded_install {t : ℕ} (slots : Fin t→Fin 78) (hinj : Function.Injective slots)
    (B : ℕ) (A : Fin 78→List Bool) (data : Fin t→List Bool) :
    paddedData B (install slots A data)=install slots (paddedData B A)
      (fun j=>ZeroPadding.pad (capacity B (slots j)) (data j)) := by
  funext i
  by_cases hi : ∃ j,slots j=i
  · obtain ⟨j,rfl⟩:=hi
    change ZeroPadding.pad _ (install slots A data (slots j))=_
    rw [install_slot slots hinj,install_slot slots hinj]
  · have hnone : ∀ j,slots j≠i:=by intro j he;exact hi ⟨j,he⟩
    change ZeroPadding.pad _ (install slots A data i)=_
    rw [install_other slots A data i hnone,install_other slots _ _ i hnone]
    rfl

theorem unary_ports (C D index node value limit upper B : ℕ) (out stack packet source : List Bool)
    (hC : C+1≤B) (hD : D≤B) (j : Fin 37) :
    ZeroPadding.pad (capacity B (RecoveryBoundedGrammarUnary.slots j))
      (RecoveryBoundedUnaryReuse.data index node C D value limit false out j)=
      ready (RecoveryBoundedGrammarPrototype.fields C index value limit upper)
        node B out stack packet source (RecoveryBoundedGrammarUnary.slots j) := by
  have hp (bits : List Bool) : ZeroPadding.pad B (ZeroPadding.pad C bits)=ZeroPadding.pad B bits:=
    MatrixBucketRootPower.pad_pad C B bits (by omega)
  have hc : ZeroPadding.pad B (List.replicate C false)=List.replicate B false:=
    RecoveryBoundedSelectorLoop.pad_erased B C (by omega)
  have hc1 : ZeroPadding.pad B (List.replicate (C+1) false)=List.replicate B false:=
    RecoveryBoundedSelectorLoop.pad_erased B (C+1) hC
  have hd : ZeroPadding.pad B (List.replicate D false)=List.replicate B false:=
    RecoveryBoundedSelectorLoop.pad_erased B D hD
  have hz : ZeroPadding.pad B []=List.replicate B false:=by simp [ZeroPadding.pad]
  have hf : ZeroPadding.pad B [false]=List.replicate B false:=RecoveryBoundedSelectorLoop.pad_false B (by omega)
  fin_cases j <;>
    simp [RecoveryBoundedGrammarUnary.slots,capacity,ready,RecoveryBoundedRowReload.loaded_apply,
      RecoveryBoundedRowReload.ports,RecoveryBoundedGrammarPrototype.fields,base,
      RecoveryBoundedUnaryReuse.data,RecoveryBoundedUnaryReuse.baseData,RecoveryBoundedNativeFold.oldData,
      RecoveryBoundedNativeFold.values,PCPPNativeClauseBank.data,Fin.addCases,hp,hc,hc1,hd,hz,hf]

noncomputable def unaryInput (C D index node value limit upper B : ℕ) (out stack packet source : List Bool):=
  install RecoveryBoundedGrammarUnary.slots
    (logicalReady (RecoveryBoundedGrammarPrototype.fields C index value limit upper) node B out stack packet source)
    (RecoveryBoundedUnaryReuse.data index node C D value limit false out)

theorem unary_padding (C D index node value limit upper B : ℕ) (out stack packet source : List Bool)
    (hC : C+1≤B) (hD : D≤B) :
    paddedData B (unaryInput C D index node value limit upper B out stack packet source)=
      ready (RecoveryBoundedGrammarPrototype.fields C index value limit upper) node B out stack packet source := by
  rw [unaryInput,padded_install _ RecoveryBoundedGrammarUnary.slots_injective,logical_ready_padding]
  apply install_existing
  intro j
  exact (unary_ports C D index node value limit upper B out stack packet source hC hD j).symm

end NearCubicWires.RepairOrdinary.RecoveryBoundedGrammarBank
