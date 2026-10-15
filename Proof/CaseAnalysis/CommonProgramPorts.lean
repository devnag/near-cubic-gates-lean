import Proof.CaseAnalysis.CommonProgram

/-! The shared physical header has five distinct ports. Its numeric order
proves every small shared-bank injection without expanding worker states. -/
namespace NearCubicWires.RepairSource.CloseoutCommonProgram
open LocalBitMultitape RepairOrdinary OrdinaryOracleCompose
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

private theorem value_injective {a b : ℕ} (f : Fin a→Fin b)
    (hf : ∀ i,(f i).val=i.val) : Function.Injective f:=by
  intro i j he
  exact Fin.ext ((hf i).symm.trans ((congrArg Fin.val he).trans (hf j)))
private theorem indexed_injective {a b c : ℕ} (f : Fin a→Fin b) (g : Fin c→Fin a)
    (s : Fin c→Fin b) (hf : Function.Injective f) (hg : Function.Injective g)
    (he : ∀ i,s i=f (g i)) : Function.Injective s:=by
  intro i j hij
  exact hg (hf ((he i).symm.trans (hij.trans (he j))))
private theorem cast_two (a b c : ℕ) :
    Function.Injective (fun i : Fin a=>(i.castAdd b).castAdd c):=
  (Fin.castAdd_injective (a+b) c).comp (Fin.castAdd_injective a b)
private theorem cast_three (a b c d : ℕ) :
    Function.Injective (fun i : Fin a=>((i.castAdd b).castAdd c).castAdd d):=
  (Fin.castAdd_injective (a+b+c) d).comp (cast_two a b c)
private theorem cast_four (a b c d e : ℕ) :
    Function.Injective (fun i : Fin a=>(((i.castAdd b).castAdd c).castAdd d).castAdd e):=
  (Fin.castAdd_injective (a+b+c+d) e).comp (cast_three a b c d)

def header (p : Parameters) : Fin 5→Fin (n0 p):=
  ![address0 p,query0 p,capacity0 p,word0 p,output0 p]

theorem query_capacity (p : Parameters) : (query0 p).val<(capacity0 p).val:=by
  have h:=CloseoutCommonPrefix.first_bound (work p) p.refuter p.k
    (CloseoutCommonPrefix.query (work p) p.refuter)
  change (query0 p).val<1+CloseoutCommonPrefix.base (work p) p.refuter at h
  change (query0 p).val<1+CloseoutCommonPrefix.base (work p) p.refuter+25
  omega

theorem capacity_word (p : Parameters) : (capacity0 p).val<(word0 p).val:=by
  have hb:=HierarchyFromInput.tapes_lower (p.k+2)
  have hf : (CloseoutHierarchyRequest.fresh p.k 0).val≠2:=by
    change CloseoutHierarchyClock.Input.tapes (p.k+2)+0≠2
    unfold CloseoutHierarchyClock.Input.tapes
    omega
  have hw : (CloseoutCommonPrepare.hierarchySlot p.k).val=
      27+(CloseoutHierarchyRequest.fresh p.k 0).val:=by
    simp only [CloseoutCommonPrepare.hierarchySlot,CloseoutCommonPrepare.requestSlots,
      CloseoutHierarchyRequest.Shared.bank,if_neg hf,Fin.val_natAdd]
  have h0:(CloseoutCommonPrepare.hierarchySlot p.k).val≠0:=by omega
  have h1:(CloseoutCommonPrepare.hierarchySlot p.k).val≠1:=by omega
  change 1+CloseoutCommonPrefix.base (work p) p.refuter+25<
    (CloseoutCommonPrefix.prepareSlots (work p) p.refuter p.k
      (CloseoutCommonPrepare.hierarchySlot p.k)).val
  simp only [CloseoutCommonPrefix.prepareSlots,if_neg h0,if_neg h1]
  omega

theorem header_injective (p : Parameters) : Function.Injective (header p):=by
  apply StrictMono.injective
  apply Fin.strictMono_iff_lt_succ.mpr
  intro i
  fin_cases i
  · change 0<(prefixProgram p).queryTape.val
    have h:=(prefixProgram p).queryFresh
    omega
  · exact query_capacity p
  · exact capacity_word p
  · exact (CloseoutCommonPrefix.prepareSlots (work p) p.refuter p.k
      (CloseoutCommonPrepare.hierarchySlot p.k)).isLt

theorem lift0_injective (p : Parameters) : Function.Injective (lift0 p):=
  value_injective (lift0 p) (fun _=>rfl)
theorem lift1_injective (p : Parameters) : Function.Injective (lift1 p):=by
  unfold lift1
  exact cast_four (n1 p) 28 (on p) (tn p) 2
theorem lift2_injective (p : Parameters) : Function.Injective (lift2 p):=by
  unfold lift2
  exact cast_three (n2 p) (on p) (tn p) 2
theorem lift3_injective (p : Parameters) : Function.Injective (lift3 p):=by
  unfold lift3
  exact cast_two (n3 p) (tn p) 2
theorem prefix_injective (p : Parameters) : Function.Injective (prefixSlot p):=
  (lift0_injective p).comp (Fin.castAdd_injective _ _)

theorem recovery_shared_injective (p : Parameters) : Function.Injective (recoveryShared p):=by
  have hi : Function.Injective (![3,2,1] : Fin 3→Fin 5):=by decide
  exact indexed_injective (header p) _ (recoveryShared p) (header_injective p) hi
    (by intro i;fin_cases i <;>rfl)
theorem recovery_injective (p : Parameters) : Function.Injective (recoverySlot p):=
  (lift1_injective p).comp (CloseoutCommonPortBank.injective _ _ (recovery_shared_injective p))
theorem recovery_query (p : Parameters) : recoverySlot p (recovery p).queryTape=(ports p).queryTape:=by
  change lift1 p (recoveryBank p (RecoveryBoundedCold.sharedLocal (source p) p.k p.degree 2))=_
  rw [recoveryBank,CloseoutCommonPortBank.shared_slot _ _
    (RecoveryBoundedCold.sharedLocal_injective (source p) p.k p.degree)]
  rfl

theorem clear_shared_injective (p : Parameters) : Function.Injective (clearShared p):=by
  have hi : Function.Injective (![0,1] : Fin 2→Fin 5):=by decide
  exact indexed_injective (fun j=>(header p j).castAdd (rn p)) _ (clearShared p)
    ((Fin.castAdd_injective (n0 p) (rn p)).comp (header_injective p)) hi
    (by intro i;fin_cases i <;>rfl)
theorem clear_injective (p : Parameters) : Function.Injective (clearSlot p):=
  (lift2_injective p).comp (CloseoutCommonPortBank.injective _ _ (clear_shared_injective p))
theorem one_shared_injective (p : Parameters) : Function.Injective (oneShared p):=by
  have hi : Function.Injective (![3,0,1,4] : Fin 4→Fin 5):=by decide
  exact indexed_injective (fun j=>((header p j).castAdd (rn p)).castAdd 28) _ (oneShared p)
    ((Fin.castAdd_injective (n1 p) 28).comp
      ((Fin.castAdd_injective (n0 p) (rn p)).comp (header_injective p))) hi
    (by intro i;fin_cases i <;>rfl)
theorem one_injective (p : Parameters) : Function.Injective (oneSlot p):=
  (lift3_injective p).comp (CloseoutCommonPortBank.injective _ _ (one_shared_injective p))

end
end NearCubicWires.RepairSource.CloseoutCommonProgram
