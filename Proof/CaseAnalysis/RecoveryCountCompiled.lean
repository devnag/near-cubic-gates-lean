import Proof.CaseAnalysis.RecoveryCountFinish

/-! The complete original bounded count compiler: ascending literal count
cases, followed by the existing terminal false and reverse OR. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedCountUniform
open LocalBitMultitape Composition SourceInterfaces RepairSource CanonicalRecoveryLanguage
open RepairSource.ProjectionNormalization RepairSource.VerifierDecoding BoundedOracleStructuralCircuit FinitePredicateCircuit
open RecoveryBoundedClauseList (stackWord)
open RecoveryBoundedSelectorLoop (capacity)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace FinalJoin
def machine {s t : ℕ} (first : Machine 153 s) (last : Machine 153 t):=Composition.machine first last
theorem endpoint {s : ℕ} (m : Machine 153 s) (u : ℕ) (c d : Configuration 153 s)
    (hc : c.control=m.start)
    (hp : ∃ r,runFrom m u c=some r ∧ r.final=d ∧ r.steps≤u) :
    ∃ r,runFrom m u ⟨m.start,c.heads,c.tapes⟩=some r ∧ r.steps≤u ∧
      r.final.heads=d.heads ∧ r.final.tapes=d.tapes := by
  obtain ⟨r,rr,rf,rs⟩:=hp
  have he : (⟨m.start,c.heads,c.tapes⟩ : Configuration 153 s)=c := by
    apply configuration_ext
    · exact hc.symm
    · rfl
    · rfl
  exact ⟨r,he ▸ rr,rs,congrArg Configuration.heads rf,congrArg Configuration.tapes rf⟩

theorem endpoints {s t : ℕ} (first : Machine 153 s) (last : Machine 153 t)
    (u v : ℕ) (H H' H'' : Fin 153→ℕ) (A A' A'' : Fin 153→List Bool)
    (hp : ∃ p,runFrom first u ⟨first.start,H,A⟩=some p ∧ p.steps≤u ∧ p.final.heads=H' ∧ p.final.tapes=A')
    (hq : ∃ q,runFrom last v ⟨last.start,H',A'⟩=some q ∧ q.steps≤v ∧ q.final.heads=H'' ∧ q.final.tapes=A'') :
    ∃ r,runFrom (machine first last) (u+1+v) ⟨(machine first last).start,H,A⟩=some r ∧
      r.steps≤u+1+v ∧ r.final.heads=H'' ∧ r.final.tapes=A'' := by
  obtain ⟨p,pr,ps,ph,pt⟩:=hp
  obtain ⟨q,qr,qs,qh,qt⟩:=hq
  have qr' : runFrom last v (restart p.final last.start)=some q := by
    change runFrom last v ⟨last.start,p.final.heads,p.final.tapes⟩=some q
    rw [ph,pt]
    exact qr
  exact ⟨joinedReceipt p q,Composition.run_join first last _ _ _ p q pr qr',
    Nat.add_le_add (Nat.add_le_add_right ps 1) qs,qh,qt⟩

theorem indexed {s t : ℕ} {ι : Type} (first : Machine 153 s) (last : Machine 153 t)
    (u v : ℕ) (initial : Configuration 153 s) (middle : ι → Configuration 153 s)
    (H : ι→Fin 153→ℕ) (A : ι→Fin 153→List Bool) (hs : initial.control=first.start)
    (hp : ∃ i,∃ r,runFrom first u initial=some r ∧ r.final=middle i ∧ r.steps≤u)
    (hq : ∀ i,∃ r,runFrom last v ⟨last.start,(middle i).heads,(middle i).tapes⟩=some r ∧
      r.steps≤v ∧ r.final.heads=H i ∧ r.final.tapes=A i) :
    ∃ i,∃ r,runFrom (machine first last) (u+1+v)
      ⟨(machine first last).start,initial.heads,initial.tapes⟩=some r ∧
      r.steps≤u+1+v ∧ r.final.heads=H i ∧ r.final.tapes=A i := by
  obtain ⟨i,hi⟩:=hp
  exact ⟨i,endpoints first last u v _ _ _ _ _ _ (endpoint first u initial (middle i) hs hi) (hq i)⟩
end FinalJoin

noncomputable def compiledMachine:=FinalJoin.machine scanMachine RecoveryBoundedCountNativeFold.machine
def compiledBudget (B W R bound : ℕ):=scanBudget B W R bound+1+
  RecoveryBoundedGrammarFold.budget false bound (capacity W)

variable {p : RawProjectionPCP} {R Q : ℕ} {hr : p.width≤R} {hq : p.queries≤Q}
variable {n bound : ℕ} {x : BitInput n}

theorem compiled_run (z : Resources p R Q hr hq (bound:=bound) x)
    (b : BooleanDAGBuilder (descriptionWidth R bound)) (stack : List Bool) (extra : Fin 12→List Bool)
    (hb : 0<bound)
    (rawWidth : extra 0=RecoveryBoundedGrammarScalarAdd.unary z.base.B (rowWidth R bound))
    (rawQ : extra 3=RecoveryBoundedGrammarScalarAdd.unary z.base.B Q)
    (rawClauses : extra 4=RecoveryBoundedGrammarScalarAdd.unary z.base.B (Codec.clauses p).length)
    (rawR : extra 5=RecoveryBoundedGrammarScalarAdd.unary z.base.B (R+1))
    (hS : stack.length+(bound+z.base.W)*(2*z.base.W+1)≤z.base.S)
    (hP : stack.length+(bound+2^R+1)*(2*z.base.W+1)≤z.P)
    (hFinal : (compileCountCases (compactProjectionPCP (p.normalized R Q hr hq)) x b
      (List.finRange bound)).final.nodes.length≤z.base.G) :
    ∃ f : Forward z b (List.finRange bound), ∃ r,
      runFrom compiledMachine (compiledBudget z.base.B z.base.W R bound)
        ⟨compiledMachine.start,scanHeads (z.heads b stack) 1,scanData (z.bank b 0 stack extra) bound⟩=some r ∧
      r.steps≤compiledBudget z.base.B z.base.W R bound ∧
      r.final.heads=(z.foldResult f.next stack f.refs extra).heads ∧
      r.final.tapes=(z.foldResult f.next stack f.refs extra).tapes := by
  have first:=scan_run z b stack extra rawWidth rawQ rawClauses rawR hS hP hFinal
  have joined:=FinalJoin.indexed scanMachine RecoveryBoundedCountNativeFold.machine
    (scanBudget z.base.B z.base.W R bound) (RecoveryBoundedGrammarFold.budget false bound (capacity z.base.W))
    (Driver.configuration RecoveryBoundedCountPipeline.machine 0 z b 0 stack extra 1)
    (fun f : Forward z b (List.finRange bound)=>Driver.configuration RecoveryBoundedCountPipeline.machine 3
      z f.next bound (stack++stackWord f.refs) extra 1)
    (fun f=>(z.foldResult f.next stack f.refs extra).heads)
    (fun f=>(z.foldResult f.next stack f.refs extra).tapes) rfl first
    (fun f=>by
      simpa only [Driver.configuration_heads,Driver.configuration_tapes] using z.finish_run b stack extra f hb hFinal)
  simpa only [compiledMachine,compiledBudget,Driver.configuration_heads,Driver.configuration_tapes] using joined

private theorem suffix_last {q : ℕ} (nodes result : List (BooleanNode q)) (refs : List ℕ) (output : ℕ)
    (hg : result=nodes++RecoveryBoundedCounts.anySuffix nodes.length refs)
    (ho : output=nodes.length+refs.length) : result.length=output+1 := by
  rw [hg,ho,List.length_append,RecoveryBoundedCounts.anySuffix_length]
  omega

theorem Forward.output_last (z : Resources p R Q hr hq (bound:=bound) x)
    (b : BooleanDAGBuilder (descriptionWidth R bound)) (f : Forward z b (List.finRange bound)) :
    (compileCountCases (compactProjectionPCP (p.normalized R Q hr hq)) x b (List.finRange bound)).final.nodes.length=
      (compileCountCases (compactProjectionPCP (p.normalized R Q hr hq)) x b (List.finRange bound)).output.val+1 := by
  exact suffix_last f.next.nodes _ f.refs _ f.spine.original.1 f.spine.original.2

end NearCubicWires.RepairOrdinary.RecoveryBoundedCountUniform
