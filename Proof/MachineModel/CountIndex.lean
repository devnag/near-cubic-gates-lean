import Proof.CaseAnalysis.RowsCountBinary
import Proof.MachineModel.ClockScalarFields
import Proof.Amplification.RecoveryListPredecessor

/-! A positive physical incidence counter produces the fixed-width last-row
index. The conversion is paid in the raw monomial count, not table capacity. -/
namespace NearCubicWires.ExtIncidence.CountIndex
open LocalBitMultitape RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairOrdinary.SignedSortKey RepairOrdinary.RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def old (i : Fin 10) : Fin 15:=i.castAdd 5
def scalarSlots : Fin 5→Fin 15:=![10,5,11,12,13]
def predSlots : Fin 3→Fin 15:=![11,12,14]
theorem old_injective : Function.Injective old:=by
  intro i j h;exact Fin.ext (congrArg (fun x : Fin 15=>x.val) h)
noncomputable def count:=RecoveryFocus.machine old MatrixDimensionBinary.resetMachine
noncomputable def scalar:=RecoveryFocus.machine scalarSlots ClockNormalize.machine
noncomputable def pred:=RecoveryFocus.machine predSlots RecoveryListPredecessor.machine
noncomputable def first:=Composition.machine count scalar
noncomputable def machine:=Composition.machine first pred
def input (w M : ℕ) (i : Fin 15) : List Bool:=
  if i=0 then List.replicate M true else if i=10 then List.replicate w true else []
def budget (w M : ℕ):=16*M^2+72*M+8*w+42

theorem index_run (w M : ℕ) (hM : 0<M) (hw : M<2^w) : ∃ out,
    ClockJoin.ReadyRun machine (budget w M) (input w M) out ∧
      out 1=List.replicate M true ∧ out 10=List.replicate w true ∧
      out 11=frame (binary w (M-1)) := by
  obtain ⟨a,ha,a1,_a2,_a3,a5,_a8,ah,ast⟩:=MatrixDimensionBinary.reset_run M hM
  have ca : ClockJoin.ReadyRun MatrixDimensionBinary.resetMachine (16*M^2+72*M+32)
      (MatrixDimensionBinary.resetInput M) a.final.tapes:=⟨a,ha,rfl,ah,ast⟩
  have cr:=ca.focus old old_injective (input w M) (by intro i;fin_cases i <;> rfl)
  let A:=install old (input w M) a.final.tapes
  have fresh (i : Fin 15) (hi : 10 ≤ i.val) : A i=input w M i:=by
    apply install_other
    intro j hj
    have hv : j.val=i.val:=congrArg (fun x : Fin 15=>x.val) hj
    have hjb:=j.isLt
    omega
  have hlen : (binary (natBitLength M) M).length≤w:=by
    rw [binary_length]
    have h:=Nat.log_lt_of_lt_pow (by omega : M≠0) hw
    change Nat.log 2 M+1≤w
    omega
  obtain ⟨b,hb,b0,_b1,b2,b3,_b4,bh,bst⟩:=ClockScalarFields.scalar_run w
    (binary (natBitLength M) M) hlen
  have bv:=binary_value (natBitLength M) M (Nat.lt_pow_succ_log_self (by decide) M)
  rw [bv] at b2
  have cb : ClockJoin.ReadyRun ClockNormalize.machine (4*w+4)
      (ClockNormalize.input w (binary (natBitLength M) M)) b.final.tapes:=⟨b,hb,rfl,bh,bst.le⟩
  have sr:=cb.focus scalarSlots (by decide) A (by
    intro i;fin_cases i
    · exact fresh 10 (by decide)
    · exact (install_slot old old_injective _ _ 5).trans a5
    all_goals exact fresh _ (by decide))
  let B:=install scalarSlots A b.final.tapes
  have hpred : RecoveryListPredecessor.result (binary w M) true=binary w (M-1):=by
    have hv:=RecoveryListPredecessor.predecessor_value (binary w M) (by rw [binary_value w M hw];omega)
    have he:=BoundedCounter.binary_of_value (RecoveryListPredecessor.result (binary w M) true)
    simpa only [RecoveryListPredecessor.result_length,binary_length,binary_value w M hw,hv] using he.symm
  have pc:=RecoveryListPredecessor.predecessor_ready (binary w M) true 0
  rw [binary_length,hpred,binary_value w M hw] at pc
  have pr:=pc.focus predSlots (by decide) B (by
    intro i;fin_cases i
    · exact (install_slot scalarSlots (by decide) _ _ 2).trans b2
    · exact (install_slot scalarSlots (by decide) _ _ 3).trans b3
    · exact (install_other scalarSlots A _ 14 (by decide)).trans (fresh 14 (by decide)))
  have prClock : ClockJoin.ReadyRun pred (4*w+4) B
      (install predSlots B ![frame (binary w (M-1)),[decide (M≠0)],
        List.replicate (max 0 (2*w+1)) false]) := by
    obtain ⟨r,hr,rt,rh,rs⟩:=pr
    exact ⟨r,hr,rt,rh,rs.le⟩
  have whole:=ClockJoin.join first pred _ _ _ _ _
    (ClockJoin.join count scalar _ _ _ _ _ cr sr) prClock
  have ht : (16*M^2+72*M+32+1+(4*w+4))+1+(4*w+4)=budget w M:=by unfold budget;omega
  rw [ht] at whole
  refine ⟨_,whole,?_,?_,install_slot predSlots (by decide) _ _ 0⟩
  · exact (install_other predSlots B _ 1 (by decide)).trans
      ((install_other scalarSlots A _ 1 (by decide)).trans ((install_slot old old_injective _ _ 1).trans a1))
  · exact (install_other predSlots B _ 10 (by decide)).trans
      ((install_slot scalarSlots (by decide) _ _ 0).trans b0)

end NearCubicWires.ExtIncidence.CountIndex
