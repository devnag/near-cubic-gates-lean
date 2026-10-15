import Proof.PCP.PCPPQueryPrepare

/-! A counted scan of the explicit clause pairs. Each preceding pair is
skipped once, with its physical width scratch reused; the selected pair is
copied verbatim. The index sentinel is restored without a second count. -/
namespace NearCubicWires.RepairOrdinary.PCPPQueryClauseRows
open LocalBitMultitape RecoveryExecution RepairSource.VerifierDecoding PCPPQueryField
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def stream (rows : List (ℕ×ℕ)) := (rows.map (fun p => pairBits p.1 p.2)).flatten
def savedRows (rows : List (ℕ×ℕ)) (backing : List Bool) :=
  rows.foldl (fun old p => saved p.2 (saved p.1 old)) backing
noncomputable def skip := RepeatMachine.machine (pair false) (fun _ _ => true)
noncomputable def cfg (phase : Fin 5) (source : List Bool) (pos : ℕ)
    (backing out : List Bool) (total driver : ℕ) :=
  RepeatMachine.cfg phase (store (s:=8) 0 source pos backing out) total driver

theorem pair_cost (a b : ℕ) : pairCost a b=(pairBits a b).length+5 := by
  simp [pairCost,fieldCost,pairBits]; omega

theorem remaining (pre : List Bool) (rows : List (ℕ×ℕ)) (tail backing out : List Bool)
    (total pos : ℕ) (hn : pos+rows.length=total) :
    Timed skip ((stream rows).length+7*rows.length+total+3)
      (cfg 0 (pre++stream rows++tail) pre.length backing out total (pos+1))
      (cfg 3 (pre++stream rows++tail) (pre.length+(stream rows).length)
        (savedRows rows backing) out total 1) := by
  induction rows generalizing pre backing pos with
  | nil =>
    have hp : pos=total := by simpa using hn
    subst pos
    simpa only [skip,cfg,stream,savedRows,List.map_nil,List.flatten_nil,List.foldl_nil,
      List.append_nil,List.length_nil,Nat.mul_zero,Nat.zero_add,Nat.add_zero]
      using RepeatMachine.exhaust (pair false) (fun _ _ => true)
        (store (s:=8) 0 (pre++tail) pre.length backing out) total
  | cons row rows ih =>
    obtain ⟨r,hr,hf,hs⟩ := pair_run false pre (stream rows++tail) backing out row.1 row.2
    simp only [selected,Bool.false_eq_true,↓reduceIte,List.append_nil] at hf
    have hstep := RepeatMachine.iteration (pair false) (fun _ _ => true)
      (store 0 (pre++pairBits row.1 row.2++(stream rows++tail)) pre.length backing out)
      total pos r (by rfl) (by simp only [List.length_cons] at hn; omega) hr
    rw [hf,hs,pair_cost] at hstep
    have htail := ih (pre++pairBits row.1 row.2) (saved row.2 (saved row.1 backing)) (pos+1)
      (by simp only [List.length_cons] at hn; omega)
    have hsource : (pre++pairBits row.1 row.2)++stream rows++tail=
        pre++pairBits row.1 row.2++(stream rows++tail) := by simp [List.append_assoc]
    have hmid : cfg 0 (pre++pairBits row.1 row.2++(stream rows++tail))
        (pre.length+(pairBits row.1 row.2).length) (saved row.2 (saved row.1 backing)) out total (pos+2)=
      cfg 0 ((pre++pairBits row.1 row.2)++stream rows++tail)
        (pre++pairBits row.1 row.2).length (saved row.2 (saved row.1 backing)) out total ((pos+1)+1) := by
      rw [hsource,List.length_append]
    change Timed skip ((pairBits row.1 row.2).length+5+2)
      (cfg 0 (pre++pairBits row.1 row.2++(stream rows++tail)) pre.length backing out total (pos+1))
      (cfg 0 (pre++pairBits row.1 row.2++(stream rows++tail))
        (pre.length+(pairBits row.1 row.2).length) (saved row.2 (saved row.1 backing)) out total (pos+2)) at hstep
    rw [hmid] at hstep
    have hall := hstep.trans htail
    have htime : (pairBits row.1 row.2).length+5+2+
        ((stream rows).length+7*rows.length+total+3)=
        (stream (row::rows)).length+7*(row::rows).length+total+3 := by
      simp [stream]; omega
    rw [htime] at hall
    simpa only [stream,List.map_cons,List.flatten_cons,List.append_assoc,List.length_append,
      savedRows,List.foldl_cons,Nat.add_assoc] using hall

theorem skip_run (pre : List Bool) (rows : List (ℕ×ℕ)) (tail backing out : List Bool) :
    ∃ r,runFrom skip ((stream rows).length+8*rows.length+3)
      (cfg 0 (pre++stream rows++tail) pre.length backing out rows.length 1)=some r ∧
      r.final=cfg 3 (pre++stream rows++tail) (pre.length+(stream rows).length)
        (savedRows rows backing) out rows.length 1 ∧
      r.steps=(stream rows).length+8*rows.length+3 := by
  have h := remaining pre rows tail backing out rows.length 0 (by omega)
  have ht : (stream rows).length+7*rows.length+rows.length+3=(stream rows).length+8*rows.length+3 := by omega
  rw [ht] at h
  exact h.run (by simp [skip,cfg,RepeatMachine.machine,RepeatMachine.cfg,controlConfig,RepeatMachine.phaseCode])

def copy : Machine 4 8 := TapeEmbedding.machine 1 (pair true)
noncomputable def machine := Composition.machine skip copy
def budget (rows : List (ℕ×ℕ)) (a b : ℕ) := (stream rows).length+8*rows.length+(pairBits a b).length+9

theorem pair_lookup_run (pre : List Bool) (rows : List (ℕ×ℕ)) (tail backing out : List Bool) (a b : ℕ) :
    ∃ r,runFrom machine (budget rows a b)
      (Composition.leftConfig 8 (cfg 0 (pre++stream rows++pairBits a b++tail) pre.length backing out rows.length 1))=some r ∧
      r.final.tapes 0=pre++stream rows++pairBits a b++tail ∧
      r.final.heads 0=pre.length+(stream rows).length+(pairBits a b).length ∧
      r.final.tapes 2=out++pairBits a b ∧ r.final.heads 2=(out++pairBits a b).length ∧
      r.final.tapes 3=CompareMachine.word rows.length ∧ r.final.heads 3=1 ∧
      r.steps=budget rows a b := by
  let source := pre++stream rows++pairBits a b++tail
  obtain ⟨first,hfirst,hff,hfs⟩ := skip_run pre rows (pairBits a b++tail) backing out
  have hsource : pre++stream rows++(pairBits a b++tail)=source := by simp [source,List.append_assoc]
  rw [hsource] at hfirst hff
  obtain ⟨last,hl,hlf,hls⟩ := pair_run true (pre++stream rows) tail (savedRows rows backing) out a b
  simp only [selected,↓reduceIte] at hlf
  have he := TapeEmbedding.run_embed (pair true) (fun _ : Fin 1 => 1)
    (fun _ => CompareMachine.word rows.length) _ _ last hl
  have hi : TapeEmbedding.config (fun _ : Fin 1 => 1) (fun _ => CompareMachine.word rows.length)
      (store (s:=8) 0 source (pre++stream rows).length (savedRows rows backing) out)=
      Composition.restart first.final copy.start := by
    rw [hff,List.length_append]
    apply configuration_ext <;> rfl
  change runFrom copy (pairCost a b)
    (TapeEmbedding.config (fun _ : Fin 1 => 1) (fun _ => CompareMachine.word rows.length)
      (store (s:=8) 0 source (pre++stream rows).length (savedRows rows backing) out))=_ at he
  rw [hi] at he
  have hj := Composition.run_join skip copy _ _ _ first
    (TapeEmbedding.receipt (fun _ : Fin 1 => 1) (fun _ => CompareMachine.word rows.length) last) hfirst he
  have ht : (stream rows).length+8*rows.length+3+1+pairCost a b=budget rows a b := by
    rw [pair_cost]; unfold budget; omega
  rw [ht] at hj
  refine ⟨Composition.joinedReceipt first
    (TapeEmbedding.receipt (fun _ : Fin 1 => 1) (fun _ => CompareMachine.word rows.length) last),hj,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals first
    | (change first.steps+1+last.steps=_; rw [hfs,hls]; exact ht)
    | (simp only [Composition.joinedReceipt,Composition.rightConfig,TapeEmbedding.receipt];
        rw [hlf]; simp [TapeEmbedding.config,store,Fin.addCases,List.length_append,Nat.add_assoc])

end NearCubicWires.RepairOrdinary.PCPPQueryClauseRows
