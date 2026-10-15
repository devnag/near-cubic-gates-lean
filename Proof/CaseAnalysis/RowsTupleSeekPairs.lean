import Proof.CaseAnalysis.RowsTupleSeekPair
import Proof.Supplier.RowOccurrenceLoop

/-! One physical bottom-count driver advances the native and declared
support streams together, including the empty bottom list. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsTupleSeek
open LocalBitMultitape RecoveryExecution RecoveryRootRound ExtDecompositionBatch
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

abbrev GatePair := List Bool × List Bool
def nativeWord (gs : List GatePair) := gs.flatMap (fun g=>frame g.1)
def supportWord (gs : List GatePair) := gs.flatMap (fun g=>frame g.2)
def pairCost (g : GatePair) := 2*g.1.length+2*g.2.length+3
def pairsCost (gs : List GatePair) := (gs.map pairCost).sum+3*gs.length+3
noncomputable def pairsMachine (keep : Bool) := RepeatMachine.machine (pairMachine keep) (fun _ _=>true)
noncomputable def pairEntry (keep : Bool) (ns ss : List Bool) (np sp : ℕ) (native support : List Bool) :=
  (⟨(pairMachine keep).start,pairHeads np sp native support,pairData ns ss native support⟩ : Configuration 4 6)
noncomputable def pairsCfg (keep : Bool) (phase : Fin 5) (ns ss : List Bool) (np sp : ℕ)
    (native support : List Bool) (total cursor : ℕ) :=
  RepeatMachine.cfg phase (pairEntry keep ns ss np sp native support) total cursor

theorem pairs_remaining (keep : Bool) (gs : List GatePair)
    (np nt sp st native support : List Bool) (total done : ℕ) (hn : done+gs.length=total) :
    ∃ time ≤ (gs.map pairCost).sum+2*gs.length+total+3,
      Timed (pairsMachine keep) time
        (pairsCfg keep 0 (np++nativeWord gs++nt) (sp++supportWord gs++st)
          np.length sp.length native support total (done+1))
        (pairsCfg keep 3 (np++nativeWord gs++nt) (sp++supportWord gs++st)
          (np.length+(nativeWord gs).length) (sp.length+(supportWord gs).length)
          (native++selected keep (nativeWord gs)) (support++selected keep (supportWord gs)) total 1) := by
  induction gs generalizing np sp native support done with
  | nil=>
    have hd : done=total := by simpa using hn
    subst done
    refine ⟨total+3,by simp,?_⟩
    simpa [pairsMachine,pairsCfg,nativeWord,supportWord,selected] using
      RepeatMachine.exhaust (pairMachine keep) (fun _ _=>true)
        (pairEntry keep (np++nt) (sp++st) np.length sp.length native support) total
  | cons g gs ih=>
    obtain ⟨r,hr,rh,rt,rs⟩ := pair_run keep np g.1 (nativeWord gs++nt)
      sp g.2 (supportWord gs++st) native support
    have hstep := RepeatMachine.iteration (pairMachine keep) (fun _ _=>true)
      (pairEntry keep (np++frame g.1++(nativeWord gs++nt)) (sp++frame g.2++(supportWord gs++st))
        np.length sp.length native support) total done r (by rfl)
        (by simp only [List.length_cons] at hn;omega) hr
    simp only [↓reduceIte] at hstep
    rw [RowOccurrenceLoop.cfg_eq 0 r.final
      (pairEntry keep (np++frame g.1++(nativeWord gs++nt)) (sp++frame g.2++(supportWord gs++st))
        (np.length+(frame g.1).length) (sp.length+(frame g.2).length)
        (native++selected keep (frame g.1)) (support++selected keep (frame g.2))) total (done+2) rh rt] at hstep
    obtain ⟨time,ht,tailRun⟩ := ih (np++frame g.1) (sp++frame g.2)
      (native++selected keep (frame g.1)) (support++selected keep (frame g.2)) (done+1)
      (by simp only [List.length_cons] at hn;omega)
    simp only [List.length_append,List.append_assoc] at hstep tailRun
    rw [show done+1+1=done+2 by omega] at tailRun
    have all := hstep.trans tailRun
    refine ⟨r.steps+2+time,?_,?_⟩
    · simp only [List.map_cons,List.sum_cons,List.length_cons,pairCost] at *
      omega
    · cases keep <;> simpa only [pairsMachine,pairsCfg,nativeWord,supportWord,List.flatMap_cons,
        List.length_append,List.append_assoc,Nat.add_assoc,selected,Bool.false_eq_true,↓reduceIte,List.append_nil] using all

theorem pairs_run (keep : Bool) (gs : List GatePair) (np nt sp st native support : List Bool) :
    ∃ r,runFrom (pairsMachine keep) (pairsCost gs)
      (pairsCfg keep 0 (np++nativeWord gs++nt) (sp++supportWord gs++st)
        np.length sp.length native support gs.length 1)=some r ∧
      r.final=pairsCfg keep 3 (np++nativeWord gs++nt) (sp++supportWord gs++st)
        (np.length+(nativeWord gs).length) (sp.length+(supportWord gs).length)
        (native++selected keep (nativeWord gs)) (support++selected keep (supportWord gs)) gs.length 1 ∧
      r.steps ≤ pairsCost gs := by
  obtain ⟨time,hb,tr⟩ := pairs_remaining keep gs np nt sp st native support gs.length 0 (by omega)
  have hbound : time ≤ pairsCost gs := by unfold pairsCost;omega
  obtain ⟨r,hr,rf,rs⟩ := tr.run
    (by simp [pairsMachine,pairsCfg,RepeatMachine.machine,RepeatMachine.cfg,controlConfig,RepeatMachine.phaseCode])
  have more := runFrom_moreFuel (pairsMachine keep) time (pairsCost gs-time) _ r hr
  rw [Nat.add_sub_of_le hbound] at more
  exact ⟨r,more,rf,by omega⟩

end NearCubicWires.RepairOrdinary.CloseoutRowsTupleSeek
