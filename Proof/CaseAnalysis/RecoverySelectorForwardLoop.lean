import Proof.CaseAnalysis.RecoverySelectorForwardState

/-! The original selector's forward guarded heads are executed by the existing
physical repeat controller, retaining the shared reference stream. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedSelectorLoop
open LocalBitMultitape SourceInterfaces RepairRepresentation Composition RecoveryExecution
open BoundedOracleStructuralCircuit FinitePredicateCircuit RecoveryBoundedNative RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def forwardMachine:=RepeatMachine.machine machine (fun _ _=>true)
noncomputable def configuration {n bound : ℕ} (phase : Fin 5) (row : Fin (bound+1))
    (start limit W D : ℕ) (a : State) (source : List Bool) (total driver : ℕ) :=
  RepeatMachine.cfg phase (a.entry (n:=n) row start limit W D source) total driver

private theorem cfg_data {t s : ℕ} (phase : Fin 5) (c d : Configuration t s) (total driver : ℕ)
    (hh : c.heads=d.heads) (ht : c.tapes=d.tapes) :
    RepeatMachine.cfg phase c total driver=RepeatMachine.cfg phase d total driver := by
  apply configuration_ext
  · rfl
  · simp only [RepeatMachine.cfg,controlConfig,TapeEmbedding.config,hh]
  · simp only [RepeatMachine.cfg,controlConfig,TapeEmbedding.config,ht]

theorem forward_run {n bound : ℕ} (count W D total : ℕ)
    (row : Fin (bound+1)) (start limit : ℕ) (hblock : start+limit ≤ rowWidth n bound)
    (b : BooleanDAGBuilder (descriptionWidth n bound)) (a : State) (wires : List (LiveWire b))
    (tail : List Bool) (hlen : wires.length=count) (hb : a.position=b.nodes.length)
    (htotal : a.value+count=total)
    (hi : RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start+limit ≤ W)
    (hp : a.position+count*(3*limit+2)+3*limit ≤ W) (hv : total ≤ W)
    (hD : 8388608*(W+1)^3 ≤ D) :
    ∃ r,runFrom forwardMachine (count*(stepBudget W+2)+total+3)
      (configuration (n:=n) 0 row start limit W D a
        (a.skipped++sourceWord (wires.map (fun w=>w.output.val))++tail) total (a.value+1))=some r ∧
      r.final=configuration (n:=n) 3 row start limit W D
        (a.iterate row start limit hblock (wires.map (fun w=>w.output.val)))
        (a.skipped++sourceWord (wires.map (fun w=>w.output.val))++tail) total 1 ∧
      r.steps ≤ count*(stepBudget W+2)+total+3 := by
  induction count generalizing b a with
  | zero=>
    have hw : wires=[] := by simpa using hlen
    subst wires
    have hoff : a.value=total := by omega
    obtain ⟨r,hr,rf,rs⟩:=(RepeatMachine.exhaust machine (fun _ _=>true)
      (a.entry (n:=n) row start limit W D (a.skipped++sourceWord []++tail)) total).run
      (by simp [RepeatMachine.machine,RepeatMachine.cfg,controlConfig,RepeatMachine.phaseCode])
    refine ⟨r,?_,rf,?_⟩
    · simpa only [forwardMachine,configuration,hoff,Nat.zero_mul,Nat.zero_add,List.map_nil] using hr
    · simpa only [Nat.zero_mul,Nat.zero_add] using rs.le
  | succ count ih=>
    cases wires with
    | nil=>simp at hlen
    | cons wire wires=>
      have hlen' : wires.length=count := by simpa using hlen
      let source:=a.skipped++sourceWord ((wire::wires).map (fun w=>w.output.val))++tail
      let next:=a.next row start limit hblock wire.output.val
      let built:=head b (unaryEqualsExpr row start limit a.value hblock) wire
      have sourceEq : a.skipped++frame (List.replicate wire.output.val true)++
          (sourceWord (wires.map (fun w=>w.output.val))++tail)=source := by
        simp only [source,sourceWord,List.map_cons,List.flatMap_cons,List.append_assoc]
      obtain ⟨first,hfirst,fs,fh,ft⟩:=state_run b row start limit W D a
        (sourceWord (wires.map (fun w=>w.output.val))++tail) wire hblock hb hi (by omega) (by omega) hD
      rw [sourceEq] at hfirst fh ft
      have hiteration:=RepeatMachine.iteration machine (fun _ _=>true)
        (a.entry (n:=n) row start limit W D source) total a.value first rfl (by omega) hfirst
      change Timed forwardMachine (first.steps+2)
        (configuration (n:=n) 0 row start limit W D a source total (a.value+1))
        (RepeatMachine.cfg 0 first.final total (a.value+2)) at hiteration
      rw [cfg_data 0 first.final (next.entry (n:=n) row start limit W D source) total (a.value+2) fh ft] at hiteration
      have hn:=next_bounds row start limit hblock wire.output.val a
      have hnPos : next.position=built.final.nodes.length := next_position b row start limit a wire hblock hb
      have hnBound : next.position+count*(3*limit+2)+3*limit ≤ W := by
        dsimp only [next]
        simp only [Nat.add_mul,Nat.one_mul] at hp
        omega
      obtain ⟨last,hl,lf,ls⟩:=ih built.final next (liftLiveWires built.extension wires)
        (by simpa only [liftLiveWires_length] using hlen') hnPos
        (by dsimp only [next,State.next]; omega) hnBound
      have nextSource : next.skipped++sourceWord ((liftLiveWires built.extension wires).map (fun w=>w.output.val))++tail=source := by
        rw [raw_lift]
        change (a.skipped++frame (List.replicate wire.output.val true))++sourceWord (wires.map (fun w=>w.output.val))++tail=source
        simpa only [List.append_assoc] using sourceEq
      rw [nextSource] at hl lf
      have he : a.value+2=next.value+1 := rfl
      rw [he] at hiteration
      change runFrom forwardMachine _ (configuration (n:=n) 0 row start limit W D next source total (next.value+1))=some last at hl
      rcases hiteration with ⟨space,hprefix⟩
      obtain ⟨r,hr,rf,rs,_⟩:=hprefix.followedBy last hl
      have hbudget : first.steps+2+(count*(stepBudget W+2)+total+3) ≤
          (count+1)*(stepBudget W+2)+total+3 := by
        simp only [Nat.add_mul,Nat.one_mul]
        omega
      have more:=runFrom_moreFuel forwardMachine _
        ((count+1)*(stepBudget W+2)+total+3-(first.steps+2+(count*(stepBudget W+2)+total+3))) _ r hr
      rw [Nat.add_sub_of_le hbudget] at more
      refine ⟨r,more,?_,?_⟩
      · rw [rf,lf,raw_lift]
        rfl
      · rw [rs]
        omega

end NearCubicWires.RepairOrdinary.RecoveryBoundedSelectorLoop
