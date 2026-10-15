import Proof.CaseAnalysis.RecoveryAddressState

/-! Execute all original address children using the actual repeat driver,
retaining their native prefix and the reverse-OR reference stack. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedAddress
open LocalBitMultitape SourceInterfaces RepairRepresentation Composition RecoveryExecution
open BoundedOracleStructuralCircuit FinitePredicateCircuit RecoveryBoundedNative RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def forwardMachine:=RepeatMachine.machine body (fun _ _=>true)
noncomputable def configuration {n bound : ℕ} (phase : Fin 5) (row : Fin (bound+1))
    (start limit W D : ℕ) (a : State) (source : List Bool) (total driver : ℕ):=
  RepeatMachine.cfg phase (a.entry (n:=n) row start limit W D source) total driver

private theorem cfg_data {t s : ℕ} (phase : Fin 5) (c d : Configuration t s) (total driver : ℕ)
    (hh : c.heads=d.heads) (ht : c.tapes=d.tapes) :
    RepeatMachine.cfg phase c total driver=RepeatMachine.cfg phase d total driver := by
  apply configuration_ext
  · rfl
  · simp only [RepeatMachine.cfg,controlConfig,TapeEmbedding.config,hh]
  · simp only [RepeatMachine.cfg,controlConfig,TapeEmbedding.config,ht]

theorem forward_run {n bound : ℕ} (W D total : ℕ) (row : Fin (bound+1)) (start limit : ℕ)
    (hblock : start+limit ≤ rowWidth n bound) (b : BooleanDAGBuilder (descriptionWidth n bound))
    (a : State) (bits tail : List Bool) (hb : a.position=b.nodes.length) (htotal : a.value+bits.length=total)
    (hi : RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start+limit ≤ W)
    (hp : a.position+bits.length*(3*limit+1)+3*limit ≤ W) (hv : total ≤ W)
    (hD : RecoveryBoundedNativeUnaryJoin.budget limit (RecoveryBoundedSelectorLoop.capacity W) ≤ D) :
    ∃ r,runFrom forwardMachine (bits.length*(stepBudget W+2)+total+3)
      (configuration (n:=n) 0 row start limit W D a (a.skipped++bits++tail) total (a.value+1))=some r ∧
      r.final=configuration (n:=n) 3 row start limit W D (a.iterate row start limit hblock bits)
        (a.skipped++bits++tail) total 1 ∧ r.steps ≤ bits.length*(stepBudget W+2)+total+3 := by
  induction bits generalizing b a with
  | nil=>
    have hoff : a.value=total := by simpa using htotal
    obtain ⟨r,hr,rf,rs⟩:=(RepeatMachine.exhaust body (fun _ _=>true)
      (a.entry (n:=n) row start limit W D (a.skipped++[]++tail)) total).run
      (by simp [RepeatMachine.machine,RepeatMachine.cfg,controlConfig,RepeatMachine.phaseCode])
    refine ⟨r,?_,rf,?_⟩
    · simpa only [forwardMachine,configuration,hoff,List.length_nil,Nat.zero_mul,Nat.zero_add] using hr
    · simpa only [List.length_nil,Nat.zero_mul,Nat.zero_add] using rs.le
  | cons bit bits ih=>
    let source:=a.skipped++(bit::bits)++tail
    let next:=a.next row start limit hblock bit
    let built:=compileExpr b (if bit then unaryEqualsExpr row start limit a.value hblock else .const false)
    have sourceEq : a.skipped++bit::(bits++tail)=source := by simp only [source,List.cons_append,List.append_assoc]
    obtain ⟨first,hfirst,fs,fh,ft⟩:=state_run b row start limit W D a bit (bits++tail) hblock hb hi (by omega) (by omega) hD
    rw [sourceEq] at hfirst fh ft
    have hiteration:=RepeatMachine.iteration body (fun _ _=>true)
      (a.entry (n:=n) row start limit W D source) total a.value first rfl (by simp only [List.length_cons] at htotal;omega) hfirst
    change Timed forwardMachine (first.steps+2)
      (configuration (n:=n) 0 row start limit W D a source total (a.value+1))
      (RepeatMachine.cfg 0 first.final total (a.value+2)) at hiteration
    rw [cfg_data 0 first.final (next.entry (n:=n) row start limit W D source) total (a.value+2) fh ft] at hiteration
    have hn:=next_bound row start limit hblock bit a
    have hnPos : next.position=built.final.nodes.length:=next_position b row start limit a bit hblock hb
    have hnBound : next.position+bits.length*(3*limit+1)+3*limit ≤ W := by
      dsimp only [next]
      simp only [List.length_cons,Nat.add_mul,Nat.one_mul] at hp
      omega
    obtain ⟨last,hl,lf,ls⟩:=ih built.final next hnPos
      (by dsimp only [next,State.next];simp only [List.length_cons] at htotal;omega) hnBound
    have nextSource : next.skipped++bits++tail=source := by
      change (a.skipped++[bit])++bits++tail=source
      simp only [source,List.append_assoc,List.singleton_append]
    rw [nextSource] at hl lf
    have he : a.value+2=next.value+1 := rfl
    rw [he] at hiteration
    change runFrom forwardMachine _ (configuration (n:=n) 0 row start limit W D next source total (next.value+1))=some last at hl
    rcases hiteration with ⟨space,hprefix⟩
    obtain ⟨r,hr,rf,rs,_⟩:=hprefix.followedBy last hl
    have hbudget : first.steps+2+(bits.length*(stepBudget W+2)+total+3) ≤
        (bit::bits).length*(stepBudget W+2)+total+3 := by
      simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
      omega
    have more:=runFrom_moreFuel forwardMachine _
      ((bit::bits).length*(stepBudget W+2)+total+3-(first.steps+2+(bits.length*(stepBudget W+2)+total+3))) _ r hr
    rw [Nat.add_sub_of_le hbudget] at more
    refine ⟨r,more,?_,?_⟩
    · rw [rf,lf]
      rfl
    · rw [rs]
      omega

end NearCubicWires.RepairOrdinary.RecoveryBoundedAddress
