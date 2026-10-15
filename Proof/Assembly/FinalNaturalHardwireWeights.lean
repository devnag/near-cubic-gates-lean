import Proof.Assembly.RowsPoolWeightLoop
import Proof.CaseAnalysis.FinalSupplierRowInput

/-!
A.12.1 hardwires every live assignment before printing the residual table.
This is the actual native weight-stream worker: copy residual coordinates,
skip live coordinates, and consume one retained membership bit per weight.
It uses the existing scalar intWord copy/skip workers and mask advance.
The signed target accumulation and the enclosing exact-child loop are separate
remaining producers; no encoded polynomial or prepared row input is supplied.
-/
namespace NearCubicWires.RepairSource.CloseoutFinal.C10NaturalHardwireWeights
open LocalBitMultitape RepairOrdinary RecoveryRootRound RecoveryExecution ExtDecompositionBatch RepairRepresentation
open RepairOrdinary.CloseoutRowsPoolWeight
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def sizes : Fin 3→ℕ:=![1,6,6]
noncomputable def programs : (j : Fin 3)→Machine 4 (sizes j)
  | ⟨0,_⟩=>probe
  | ⟨1,_⟩=>copy
  | ⟨2,_⟩=>skip
  | ⟨n+3,h⟩=>False.elim (by omega)
def next (j : Fin 3) (_ : Fin (sizes j)) (bits : Fin 4→Bool) : Option (Fin 3):=
  if j=0 then some (if bits 3 then 2 else 1) else none
noncomputable def choice:=RecoveryCalls.machine sizes programs 0 next

private theorem arm_run (j : Fin 3) (hj : j≠0) (fuel : ℕ)
    (H H' : Fin 4→ℕ) (A A' : Fin 4→List Bool)
    (h : Step (programs j) fuel H A H' A')
    (selected : (if readTapeBit (A 3) (H 3) then (2 : Fin 3) else 1)=j) :
    Step choice (fuel+2) H A H' A':=by
  obtain ⟨p,hp,ph,pt,_⟩:=probe_run H A
  have hp':runFrom (programs 0) 0 ⟨(programs 0).start,H,A⟩=some p:=hp
  obtain ⟨u,hu,first⟩:=call_receipt sizes programs 0 next 0 j 0 _ p hp' (by
    change some (if readTapeBit (p.final.tapes 3) (p.final.heads 3) then (2 : Fin 3) else 1)=some j
    rw [pt,ph]
    exact congrArg some selected)
  rw [ph,pt] at first
  obtain ⟨r,hr,rh,rt,_⟩:=h
  obtain ⟨v,hv,last⟩:=stop_receipt sizes programs 0 next j fuel _ r hr (by
    simp only [next,if_neg hj])
  obtain ⟨all,ha,hf,hs⟩:=(first.trans last).run (by
    simp [RecoveryCalls.machine,RecoveryCalls.stopped])
  have hb:u+v≤fuel+2:=by omega
  have more:=runFrom_moreFuel choice (u+v) (fuel+2-(u+v)) _ all ha
  rw [Nat.add_sub_of_le hb] at more
  refine ⟨all,more,?_,?_,hs.le.trans hb⟩
  · rw [hf];exact rh
  · rw [hf];exact rt

def emit (live : Bool) (z : ℤ) : List Bool := if live then [] else intWord z
def choiceBudget (z : ℤ):=DecompositionSource.Fields.cost z+2

theorem choice_run (pre tail backing out mask : List Bool) (mpos : ℕ) (z : ℤ) (live : Bool)
    (hl : readTapeBit mask mpos=live) :
    Step choice (choiceBudget z) (heads pre.length mpos out)
      (data (pre++intWord z++tail) backing out mask)
      (heads (pre.length+(intWord z).length) mpos (out++emit live z))
      (data (pre++intWord z++tail) (DecompositionSource.Fields.saved z backing)
        (out++emit live z) mask):=by
  cases live with
  | false=>
    have h:=arm_run 1 (by decide) _ _ _ _ _ (copy_run pre tail backing out mask mpos z) (by
      change (if readTapeBit mask mpos then (2 : Fin 3) else 1)=1
      rw [hl];rfl)
    exact h.enlarge (by unfold choiceBudget;omega)
  | true=>
    have h:=arm_run 2 (by decide) _ _ _ _ _ (skip_run pre tail backing out mask mpos z) (by
      change (if readTapeBit mask mpos then (2 : Fin 3) else 1)=2
      rw [hl];rfl)
    have ht:RowNativeFieldSkip.cost z+2=choiceBudget z:=by
      unfold choiceBudget RowNativeFieldSkip.cost DecompositionSource.Fields.cost
      omega
    rw [ht] at h
    simpa only [emit,ite_true,List.append_nil] using h

noncomputable def body:=Composition.machine choice advance
def bodyBudget (z : ℤ):=DecompositionSource.Fields.cost z+4

theorem body_run (pre tail backing out mpre mtail : List Bool) (z : ℤ) (live : Bool) :
    Step body (bodyBudget z) (heads pre.length mpre.length out)
      (data (pre++intWord z++tail) backing out (mpre++live::mtail))
      (heads (pre.length+(intWord z).length) (mpre.length+1) (out++emit live z))
      (data (pre++intWord z++tail) (DecompositionSource.Fields.saved z backing)
        (out++emit live z) (mpre++live::mtail)):=by
  have selected:=choice_run pre tail backing out (mpre++live::mtail) mpre.length z live
    (Streaming.read_append mpre mtail live)
  have h:=selected.seq (advance_run (pre++intWord z++tail) (DecompositionSource.Fields.saved z backing)
    (out++emit live z) (mpre++live::mtail)
    (pre.length+(intWord z).length) mpre.length)
  have ht:choiceBudget z+1+1=bodyBudget z:=by unfold choiceBudget bodyBudget;omega
  rw [ht] at h
  exact h

theorem body_budget (z : ℤ) : bodyBudget z=(intWord z).length+7:=by
  simp [bodyBudget,DecompositionSource.Fields.cost,DecompositionSource.intWord_length,
    natBitLength,intBitLength]

def emitted (xs : List Item) : List Bool := xs.flatMap (fun x => emit x.2 x.1)

noncomputable def loop:=RepeatMachine.machine body (fun _ _=>true)
noncomputable def cfg (phase : Fin 5) (source : List Bool) (pos : ℕ)
    (backing out membership : List Bool) (mpos total driver : ℕ):=
  RepeatMachine.cfg phase (⟨body.start,heads pos mpos out,data source backing out membership⟩) total driver

theorem remaining (xs : List Item) (pre tail backing out mpre mtail : List Bool)
    (total pos : ℕ) (hn : pos+xs.length=total) :
    ∃ time≤(word xs).length+9*xs.length+total+3,Timed loop time
      (cfg 0 (pre++word xs++tail) pre.length backing out (mpre++mask xs++mtail) mpre.length total (pos+1))
      (cfg 3 (pre++word xs++tail) (pre.length+(word xs).length) (saved xs backing)
        (out++emitted xs) (mpre++mask xs++mtail) (mpre.length+xs.length) total 1):=by
  induction xs generalizing pre backing out mpre pos with
  | nil=>
    have he:pos=total:=by simpa using hn
    subst pos
    refine ⟨total+3,by simp [word],?_⟩
    simpa [cfg,loop,word,mask,emitted,saved] using RepeatMachine.exhaust body (fun _ _=>true)
      (⟨body.start,heads pre.length mpre.length out,data (pre++tail) backing out (mpre++mtail)⟩) total
  | cons x xs ih=>
    obtain ⟨r,hr,rh,rt,rs⟩:=body_run pre (word xs++tail) backing out mpre (mask xs++mtail) x.1 x.2
    have one:=RepeatMachine.iteration body (fun _ _=>true)
      ⟨body.start,heads pre.length mpre.length out,
        data (pre++intWord x.1++(word xs++tail)) backing out (mpre++x.2::(mask xs++mtail))⟩
      total pos r rfl (by simp only [List.length_cons] at hn;omega) hr
    simp only [↓reduceIte] at one
    rw [RowOccurrenceLoop.cfg_eq 0 r.final
      (⟨body.start,heads (pre.length+(intWord x.1).length) (mpre.length+1)
        (out++emit x.2 x.1),
        data (pre++intWord x.1++(word xs++tail)) (DecompositionSource.Fields.saved x.1 backing)
          (out++emit x.2 x.1) (mpre++x.2::(mask xs++mtail))⟩)
      total (pos+2) rh rt] at one
    obtain ⟨t,ht,rest⟩:=ih (pre++intWord x.1) (DecompositionSource.Fields.saved x.1 backing)
      (out++emit x.2 x.1) (mpre++[x.2]) (pos+1)
      (by simp only [List.length_cons] at hn;omega)
    have hp:(pre++intWord x.1).length=pre.length+(intWord x.1).length:=List.length_append
    have hm:(mpre++[x.2]).length=mpre.length+1:=by simp
    simp only [cfg,List.append_assoc,List.singleton_append,hp,hm,show pos+1+1=pos+2 by omega] at rest
    simp only [List.append_assoc,List.cons_append] at one rest
    have all:=one.trans rest
    refine ⟨r.steps+2+t,?_,?_⟩
    · rw [body_budget] at rs
      simp only [word,List.flatMap_cons,List.length_append,List.length_cons] at ht ⊢
      omega
    · simpa only [loop,cfg,word,mask,emitted,saved,List.flatMap_cons,List.map_cons,List.foldl_cons,
        List.length_append,List.length_cons,List.append_assoc,List.cons_append,Nat.add_assoc,
        Nat.add_comm 1 xs.length] using all

def loopBudget (xs : List Item):=(word xs).length+10*xs.length+3

theorem weights_run (xs : List Item) (pre tail backing out mpre mtail : List Bool) :
    ∃ r,runFrom loop (loopBudget xs)
      (cfg 0 (pre++word xs++tail) pre.length backing out (mpre++mask xs++mtail) mpre.length xs.length 1)=some r ∧
      r.final=cfg 3 (pre++word xs++tail) (pre.length+(word xs).length) (saved xs backing)
        (out++emitted xs) (mpre++mask xs++mtail) (mpre.length+xs.length) xs.length 1 ∧
      r.steps≤loopBudget xs:=by
  obtain ⟨t,ht,h⟩:=remaining xs pre tail backing out mpre mtail xs.length 0 (by omega)
  obtain ⟨r,hr,hf,hs⟩:=h.run (by simp [loop,cfg,RepeatMachine.machine,RepeatMachine.cfg,
    controlConfig,RepeatMachine.phaseCode])
  have hb:t≤loopBudget xs:=by unfold loopBudget;omega
  have more:=runFrom_moreFuel loop t (loopBudget xs-t) _ r hr
  rw [Nat.add_sub_of_le hb] at more
  exact ⟨r,more,hf,hs.le.trans hb⟩

open SupplierPipeline SupplierEstimator

/-- The source gate is read in its existing native coordinate order. -/
def gateItems {q : ℕ} (g : ExactThresholdGate q) (live : Finset (Fin q)) : List Item :=
  List.ofFn (fun i => (g.weight i, decide (i ∈ live)))

def weightWord {q : ℕ} (g : ExactThresholdGate q) : List Bool :=
  (List.ofFn g.weight).flatMap intWord

theorem gateItems_word {q : ℕ} (g : ExactThresholdGate q) (live : Finset (Fin q)) :
    word (gateItems g live) = weightWord g := by
  simp [word,gateItems,weightWord,List.ofFn_eq_map,List.flatMap_map]

theorem gateItems_mask {q : ℕ} (g : ExactThresholdGate q) (live : Finset (Fin q)) :
    mask (gateItems g live) = List.ofFn (fun i => decide (i ∈ live)) := by
  simp [mask,gateItems,List.ofFn_eq_map,List.map_map,Function.comp_def]

private theorem emitted_filter {q : ℕ} (g : ExactThresholdGate q) (live : Finset (Fin q))
    (xs : List (Fin q)) :
    emitted (xs.map (fun i => (g.weight i, decide (i ∈ live)))) =
      (xs.filter (fun i => decide (i ∉ live))).flatMap (fun i => intWord (g.weight i)) := by
  induction xs with
  | nil => rfl
  | cons i xs ih =>
    by_cases hi : i ∈ live <;> simpa [emitted,emit,hi] using ih

theorem residual_order {q : ℕ} (live : Finset (Fin q)) :
    (List.finRange q).filter (fun i => decide (i ∉ live)) = liveᶜ.sort := by
  apply ((List.sortedLT_finRange q).pairwise.filter _).sortedLT.eq_of_mem_iff
    liveᶜ.sortedLT_sort
  intro i
  simp

/-- The deleted-coordinate output is exactly the weight block consumed by
`C10SupplierRowInput.pool`, including its increasing complement enumeration. -/
theorem gateItems_emitted {q : ℕ} (g : ExactThresholdGate q) (live : Finset (Fin q))
    (y : BitInput live.card) :
    emitted (gateItems g live) = weightWord (C10SupplierRowInput.hardwire live g y) := by
  rw [gateItems,List.ofFn_eq_map,emitted_filter,residual_order]
  rw [weightWord,List.ofFn_eq_map]
  change liveᶜ.sort.flatMap (fun i => intWord (g.weight i)) =
    ((List.finRange liveᶜ.card).map
      (fun i => g.weight (liveᶜ.orderEmbOfFin rfl i))).flatMap intWord
  rw [← Finset.listMap_orderEmbOfFin_finRange liveᶜ rfl]
  simp only [List.flatMap_map]

/-- Actual source-native gate receipt. The retained signed target remains at
the source cursor for the separately paid frozen-score/target worker. -/
theorem hardwire_weights_run {q : ℕ} (g : ExactThresholdGate q) (live : Finset (Fin q))
    (y : BitInput live.card) (pre tail backing out mpre mtail : List Bool) :
    ∃ r,runFrom loop (loopBudget (gateItems g live))
      (cfg 0 (pre++exactWord g++tail) pre.length backing out
        (mpre++List.ofFn (fun i => decide (i ∈ live))++mtail) mpre.length q 1)=some r ∧
      r.final=cfg 3 (pre++exactWord g++tail) (pre.length+(weightWord g).length)
        (saved (gateItems g live) backing)
        (out++weightWord (C10SupplierRowInput.hardwire live g y))
        (mpre++List.ofFn (fun i => decide (i ∈ live))++mtail) (mpre.length+q) q 1 ∧
      r.steps≤(weightWord g).length+10*q+3 := by
  have h := weights_run (gateItems g live) pre (intWord g.target++tail) backing out mpre mtail
  rw [gateItems_word,gateItems_mask,gateItems_emitted g live y] at h
  have hlen : (gateItems g live).length=q := List.length_ofFn
  simpa only [loopBudget,gateItems_word,hlen,exactWord,weightWord,
    List.append_assoc] using h

end NearCubicWires.RepairSource.CloseoutFinal.C10NaturalHardwireWeights
