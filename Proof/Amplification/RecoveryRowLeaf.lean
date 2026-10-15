import Proof.Amplification.RecoveryRowLeafTapes

namespace NearCubicWires.RepairOrdinary.RecoveryRowLeaf
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryClauseState
open RepairSource.RecoveryOracle
open RecoveryClauseEvaluation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def forceState (s : State) : State := {s with result:=true}

theorem force_core (s : State) (e : Extra) :
    RecoveryClauseEvaluation.tapes (forceState s) e=
      Function.update (RecoveryClauseEvaluation.tapes s e) 27 [true] := by
  funext i
  by_cases hi : i=27
  · subst i; simp [forceState]
  · rw [Function.update_of_ne hi]
    by_cases hj : i=41
    · subst i; rfl
    · symm
      apply boundary_routing _ _ ?_ ?_ i hi hj
      · intro j h
        rw [tapes_left,tapes_left]
        exact boundary_state_other 1 s {e with aggregate:=true} j h
      · intro j _
        rw [tapes_right,tapes_right]
        rfl

theorem force_layout (s : State) (e : Extra) (kind : List Bool) (flags : Fin 3→Bool) :
    Function.update (tapes (RecoveryClauseEvaluation.tapes s e) kind flags) 27 [true]=
      tapes (RecoveryClauseEvaluation.tapes (forceState s) e) kind flags := by
  rw [force_core]
  funext i
  refine Fin.addCases (m:=42) (n:=4) (motive:=fun j=>
    Function.update (tapes (RecoveryClauseEvaluation.tapes s e) kind flags) 27 [true] j=
      tapes (Function.update (RecoveryClauseEvaluation.tapes s e) 27 [true]) kind flags j) ?_ ?_ i
  · intro j
    by_cases hj : j=27
    · subst j; simp [tapes,Fin.addCases]
    · have h : j.castAdd 4≠27 := by intro h; exact hj (Fin.ext (congrArg (fun x : Fin 46=>x.val) h))
      simp [tapes,h,hj]
  · intro j
    have h : j.natAdd 42≠27 := by intro h; have hv:=congrArg Fin.val h; simp at hv; omega
    simp [tapes,h]

noncomputable def sizes : Fin 3→Nat :=
  ![Fintype.card (RecoveryCalls.Control RecoveryRowKind.sizes),
    Fintype.card (RecoveryCalls.Control RecoveryClauseEvaluation.sizes),2]
noncomputable def programs : (j : Fin 3)→Machine 46 (sizes j)
  | ⟨0,_⟩=>kindMachine
  | ⟨1,_⟩=>clauseMachine
  | ⟨2,_⟩=>force
  | ⟨n+3,h⟩=>False.elim (by omega)
def next (j : Fin 3) (_ : Fin (sizes j)) (scanned : Fin 46→Bool) : Option (Fin 3) :=
  if j.val=0 then if scanned 44 then some 1 else some 2 else none
noncomputable def machine := RecoveryCalls.machine sizes programs 0 next

def leafWordCheck (s : State) (e : Extra) (kind word : List Bool) : Bool :=
  if RadixSemantics.value kind=1 then clauseWordCheck s e word else true

structure LeafResult (s : State) (e : Extra) (kind word : List Bool) where
  state : State
  extra : Extra
  stateValid : state.Valid
  extraValid : extra.Valid state word
  width : state.bits.length=s.bits.length
  count : extra.binaryCount=e.binaryCount
  committed : extra.committed=e.committed
  cap : extra.cap=e.cap
  answer : state.result=leafWordCheck s e kind word

def kindFlags (kind : List Bool) : Fin 3→Bool := fun i=>decide (RadixSemantics.value kind=i.val)

theorem leaf_trace (s : State) (e : Extra) (kind word : List Bool) (flags : Fin 3→Bool)
    (hs : s.Valid) (he : e.Valid s word) (hk : kind.length ≤ s.bits.length) :
    ∃ n output,n ≤ 8388608*(s.bits.length+1)^2 ∧ output 27=[leafWordCheck s e kind word] ∧
      Timed machine n (initialConfiguration machine (tapes (RecoveryClauseEvaluation.tapes s e) kind flags))
        (RecoveryCalls.stopped sizes (fun _=>0) output) ∧
      (leafWordCheck s e kind word=true → ∃ out : LeafResult s e kind word,
        output=tapes (RecoveryClauseEvaluation.tapes out.state out.extra)
          (RecoveryRowKind.after kind) (kindFlags kind)) := by
  have hkind := kind_ready s e word kind flags he hk
  have htime : RecoveryRowKind.time kind=12*kind.length+17 := by unfold RecoveryRowKind.time; omega
  by_cases hleaf : RadixSemantics.value kind=1
  · have h0 := hkind.call sizes programs 0 next 0 1 (by
      intro q; simp [next,tapes,extra,Fin.addCases,readTapeBit,hleaf])
    obtain ⟨r,hr,hn,hh,ht,hreturn⟩ := clause_run s e word hs he
    have hready := (ready_of_run RecoveryClauseEvaluation.machine _ _ r hr hh).embed
      (extra (RecoveryRowKind.after kind) (kindFlags kind))
    have h1 := hready.stop sizes programs 0 next 1 (by intro q; rfl)
    have h := h0.trans h1
    refine ⟨RecoveryRowKind.time kind+1+(r.steps+1),
      tapes r.final.tapes (RecoveryRowKind.after kind) (kindFlags kind),?_,?_,h,?_⟩
    · rw [htime]
      nlinarith only [hn,hk]
    · change r.final.tapes 27=[leafWordCheck s e kind word]
      simpa only [leafWordCheck,if_pos hleaf] using ht
    · intro hc
      have hclause : clauseWordCheck s e word=true := by simpa [leafWordCheck,hleaf] using hc
      obtain ⟨out,hout⟩ := hreturn hclause
      refine ⟨⟨out.state,out.extra,out.stateValid,out.extraValid,out.width,out.count,
        out.committed,out.cap,?_⟩,?_⟩
      · simpa only [leafWordCheck,if_pos hleaf] using out.answer
      · rw [hout]
  · have h0 := hkind.call sizes programs 0 next 0 2 (by
      intro q; simp [next,tapes,extra,Fin.addCases,readTapeBit,hleaf])
    have hforce := force_ready (tapes (RecoveryClauseEvaluation.tapes s e)
      (RecoveryRowKind.after kind) (kindFlags kind)) s.result rfl
    rw [force_layout] at hforce
    have h1 := hforce.stop sizes programs 0 next 2 (by intro q; rfl)
    have h := h0.trans h1
    refine ⟨RecoveryRowKind.time kind+1+(1+1),
      tapes (RecoveryClauseEvaluation.tapes (forceState s) e)
        (RecoveryRowKind.after kind) (kindFlags kind),?_,?_,h,?_⟩
    · rw [htime]
      nlinarith only [hk]
    · simp [tapes,Fin.addCases,forceState,leafWordCheck,hleaf]
    · intro _
      refine ⟨⟨forceState s,e,hs,?_,rfl,rfl,rfl,rfl,?_⟩,rfl⟩
      · exact ⟨he.source,he.row,he.counter,he.count,he.committed,he.cap,he.prefixBound,he.reset⟩
      · simp [forceState,leafWordCheck,hleaf]

theorem leaf_run (s : State) (e : Extra) (kind word : List Bool) (flags : Fin 3→Bool)
    (hs : s.Valid) (he : e.Valid s word) (hk : kind.length ≤ s.bits.length) :
    ∃ r,run machine (8388608*(s.bits.length+1)^2)
        (tapes (RecoveryClauseEvaluation.tapes s e) kind flags)=some r ∧
      r.steps ≤ 8388608*(s.bits.length+1)^2 ∧ (∀ i,r.final.heads i=0) ∧
      r.final.tapes 27=[leafWordCheck s e kind word] ∧
      (leafWordCheck s e kind word=true → ∃ out : LeafResult s e kind word,
        r.final.tapes=tapes (RecoveryClauseEvaluation.tapes out.state out.extra)
          (RecoveryRowKind.after kind) (kindFlags kind)) := by
  obtain ⟨n,output,hn,ht,h,hreturn⟩ := leaf_trace s e kind word flags hs he hk
  obtain ⟨r,hr,hf,hsteps⟩ := h.run (by simp [machine,RecoveryCalls.machine,RecoveryCalls.stopped])
  have hm := run_moreFuel machine n (8388608*(s.bits.length+1)^2-n) _ r hr
  rw [Nat.add_sub_of_le hn] at hm
  refine ⟨r,hm,hsteps.le.trans hn,?_,?_,?_⟩
  · intro i; simp [hf,RecoveryCalls.stopped]
  · simpa [hf,RecoveryCalls.stopped] using ht
  · intro ht
    obtain ⟨out,he⟩ := hreturn ht
    exact ⟨out,by simpa [hf,RecoveryCalls.stopped] using he⟩

end NearCubicWires.RepairOrdinary.RecoveryRowLeaf
