import Proof.CaseAnalysis.CommonProgramOneFields
import Proof.CaseAnalysis.CommonProgramTwoAliases
import Proof.CaseAnalysis.CommonProgramRecoveryFresh
import Proof.CaseAnalysis.CommonProgramRecoveredQuery

/-! Case1's selected heads are zero after actual recovery even though
unrelated recovery heads can remain displaced. -/
namespace NearCubicWires.RepairSource.CloseoutCommonProgram
open LocalBitMultitape RepairOrdinary OrdinaryOracleCompose
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

private theorem four_heads (f : Fin 4→ℕ) (h0 : f 0=0) (h1 : f 1=0)
    (h2 : f 2=0) (h3 : f 3=0) : ∀ j,f j=0:=by
  intro j
  fin_cases j
  · exact h0
  · exact h1
  · exact h2
  · exact h3

theorem recovered_hierarchy (p : Parameters) (bits : List Bool)
    (out : Fin (prefixProgram p).base.tapeCount→List Bool) (padding : ℕ)
    (final : (recovery p).Config) :
    let w:=RecoveryBoundedCold.sharedLocal (source p) p.k p.degree 0
    (recovered p bits out padding final).tapes (lift0 p (word0 p))=final.tapes w ∧
      (recovered p bits out padding final).heads (lift0 p (word0 p))=final.heads w:=by
  let w:=RecoveryBoundedCold.sharedLocal (source p) p.k p.degree 0
  have hslot : recoverySlot p w=lift0 p (word0 p):=recovery_inputs p 0
  have away : w≠RecoveryBoundedCold.queryPort (source p) p.k p.degree:=
    fun he=>(by decide : (0 : Fin 3)≠2)
      (RecoveryBoundedCold.sharedLocal_injective (source p) p.k p.degree he)
  exact ⟨(congrArg (recovered p bits out padding final).tapes hslot.symm).trans
      (recovered_word p bits out padding final w away),
    (congrArg (recovered p bits out padding final).heads hslot.symm).trans
      (recovered_heads p bits out padding final w)⟩

theorem one_recovered_heads (p : Parameters) (bits : List Bool)
    (out : Fin (prefixProgram p).base.tapeCount→List Bool) (padding : ℕ)
    (final : (recovery p).Config)
    (ha : out ⟨0,(prefixProgram p).base.twoTapes.trans_lt' (by decide)⟩=frame bits)
    (hw : final.heads (RecoveryBoundedCold.sharedLocal (source p) p.k p.degree 0)=0)
    (hq : final.heads (RecoveryBoundedCold.queryPort (source p) p.k p.degree)=0) :
    ∀ i,(recovered p bits out padding final).heads (oneSlot p i)=0:=by
  let c:=recovered p bits out padding final
  have fields : ∀ j,c.heads (oneSlot p (oneLocal p j))=0:=
    four_heads (fun j=>c.heads (oneSlot p (oneLocal p j)))
      ((congrArg c.heads (one_word p)).trans ((recovered_hierarchy p bits out padding final).2.trans hw))
      ((congrArg c.heads (one_address p)).trans (recovered_address p bits out padding final ha).1)
      ((congrArg c.heads (one_query p)).trans (recovered_query_head p bits out padding final hq))
      ((congrArg c.heads (one_output p)).trans (recovered_output p bits out padding final).1)
  apply one_entry_heads p c.heads
  · intro j
    have hslot:=congrArg (lift3 p)
      (CloseoutCommonPortBank.shared_slot (oneLocal p) (oneShared p) (one_local_injective p) j)
    exact (congrArg c.heads hslot.symm).trans (fields j)
  · intro i
    have boundary : n1 p ≤ (lift3 p (i.natAdd (n2 p))).val:=
      (Nat.le_add_right (n1 p) 28).trans (Nat.le_add_right (n2 p) i.val)
    exact (recovered_fresh p bits out padding final _ boundary).1

end
end NearCubicWires.RepairSource.CloseoutCommonProgram
