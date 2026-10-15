import Proof.Hierarchy.CompetitorSameBucketGroupBlocks

/-! The SAME grouping machine produces the exact dense P/N bank from a
sorted typed source. Coverage and final cell totals justify every cycle;
capacity/template initialization is still an explicit cold-parent task. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSameBucketGroupMachine
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey RadixSemantics
open CompetitorSameBucketGroup
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def emptyStore : Store := ⟨[],[],[],false,false,false,0,0⟩

theorem dense_meaning (w u p m : ℕ) (es : List Entry)
    (hd : ∀ e∈es,Domain u e) (hm : 2*u≤2^m)
    (hs : es.Pairwise (fun a b => value (word (a.record p m))≤value (word (b.record p m))))
    (coverage : ∀ row col : Fin u,∃ e∈es,e.row=row.val ∧ e.rightTaggedID=u+col.val)
    (hbits : ∀ e∈es,e.coefficient.natAbs<2^p)
    (hf : ∀ row col : Fin u,positive (atCell row.val (u+col.val) es)<2^w ∧
      negative (atCell row.val (u+col.val) es)<2^w) :
    FitsAll w p m emptyStore es ∧ scanWord w p m emptyStore es=dense w u es := by
  have hflat := sorted_groups_flatten u p m es hd hm hs
  have member (g : List Entry) (hg : g∈groups u es) (e : Entry) (he : e∈g) : e∈es := by
    rw [← hflat]
    exact List.mem_flatten.mpr ⟨g,hg,he⟩
  have hsame : ∀ g∈groups u es,∀ a∈g,∀ b∈g,a.ids m=b.ids m := by
    intro g hg a ha b hb
    obtain ⟨hr,hc⟩ := group_same u es g hg a ha b hb
    simp only [Entry.ids,hr,hc]
  have hapart : (groups u es).Pairwise (fun g h => ∀ a∈g,∀ b∈h,a.ids m≠b.ids m) := by
    apply (groups_strict u es).imp_of_mem
    intro g h hg hh hab a ha b hb heq
    have hda := hd a (member g hg a ha)
    have hdb := hd b (member h hh b hb)
    unfold Domain at hda hdb
    obtain ⟨hr,hc⟩ := (ids_eq_iff m a b (by omega) (by omega) (by omega) (by omega)).mp heq
    rcases hab a ha b hb with h|⟨_,h⟩ <;> omega
  have h := blocks_scan w p m (groups u es) emptyStore (groups_nonempty u es coverage) hsame hapart
    (by simpa only [hflat] using hbits) (groups_fit w u es hf)
    (by intro _;exact ⟨rfl,rfl⟩) (by intro h;cases h)
  rw [hflat] at h
  refine ⟨h.1,?_⟩
  rw [dense_groups]
  change scanWord w p m emptyStore es=(groups u es).flatMap (blockWord w)
  simpa only [pendingWord,emptyStore,Bool.false_eq_true,↓reduceIte,List.nil_append] using h.2

def streamBudget (cap w p m : ℕ) (es : List Entry) := es.length*cycleBound cap w p m+(24*w+27)

theorem dense_run (cap w u p m : ℕ) (es : List Entry)
    (hpw : p≤w) (hc : 8*m+3≤cap) (ha : 4*w+3≤cap)
    (hd : ∀ e∈es,Domain u e) (hm : 2*u≤2^m)
    (hs : es.Pairwise (fun a b => value (word (a.record p m))≤value (word (b.record p m))))
    (coverage : ∀ row col : Fin u,∃ e∈es,e.row=row.val ∧ e.rightTaggedID=u+col.val)
    (hbits : ∀ e∈es,e.coefficient.natAbs<2^p)
    (hf : ∀ row col : Fin u,positive (atCell row.val (u+col.val) es)<2^w ∧
      negative (atCell row.val (u+col.val) es)<2^w) :
    ∃ r,runFrom machine (streamBudget cap w p m es)
        (boundary 0 cap w p m 0 (stream p m es) [] emptyStore)=some r ∧
      r.final.heads=heads (fields p m es).length (dense w u es).length ∧
      r.final.tapes=(scanStore p m emptyStore es).tapes cap w p m (stream p m es) (dense w u es) ∧
      r.steps ≤ streamBudget cap w p m es := by
  obtain ⟨hfit,hword⟩ := dense_meaning w u p m es hd hm hs coverage hbits hf
  obtain ⟨n,hn,h⟩ := loop_run cap w p m [] [] es emptyStore
    (by simp [Valid,emptyStore]) hpw hc ha hfit
  simp only [List.length_nil,List.nil_append,hword] at h
  obtain ⟨r,hr,hfinal,hsteps⟩ := h.run (by simp [machine,RecoveryCalls.machine,RecoveryCalls.stopped])
  have hrun := runFrom_moreFuel machine n (streamBudget cap w p m es-n) _ r hr
  have hbudget : n+(streamBudget cap w p m es-n)=streamBudget cap w p m es := by
    unfold streamBudget
    omega
  rw [hbudget] at hrun
  refine ⟨r,hrun,?_,?_,?_⟩
  · rw [hfinal]
    rfl
  · rw [hfinal]
    rfl
  · rw [hsteps]
    exact hn

end NearCubicWires.RepairOrdinary.CompetitorSameBucketGroupMachine
