import Proof.Assembly.BranchPhases
import Proof.CaseAnalysis.FinalUnaryAddress

/-! Exact live-clause consumer. The actual source-count loop visits only
indices below its source count; no saturated/idle execution is required.
Unrelated ambient heads are preserved (the prologue counter need not be zero).
The site execution and restored clean cache remain explicit obligations. -/
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 120000
set_option warningAsError true
namespace LiveClauseSites
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary
open RepairRepresentation SourceInterfaces RepairSource.VerifierDecoding RecoveryRootRound
open RepairSource.CloseoutFinal
open CloseoutFinalC10UnaryAddressRounds
noncomputable section

variable {B : Nat} (cache : Fin 19 → Fin B) (hi : Function.Injective cache)

def moving (H : Fin B → Nat) : Fin B → Nat :=
 fun i => if i=cache 13 ∨ i=cache 14 then 1 else H i

def right := DecompositionCountPosition.move (fun i : Fin B =>
 if i=cache 13 ∨ i=cache 14 then .right else .stay)
def left := DecompositionCountPosition.move (fun i : Fin B =>
 if i=cache 13 ∨ i=cache 14 then .left else .stay)

theorem position (H : Fin B → Nat) (A : Fin B → List Bool)
 (hH : ∀ j, H (cache j)=0) :
 Step (right cache) 1 H A (moving cache H) A ∧
 Step (left cache) 1 (moving cache H) A H A := by
 have hr := DecompositionCountPosition.move_run
   (fun i : Fin B => if i=cache 13 ∨ i=cache 14 then .right else .stay) H A
 have hl := DecompositionCountPosition.move_run
   (fun i : Fin B => if i=cache 13 ∨ i=cache 14 then .left else .stay) (moving cache H) A
 obtain ⟨rr,hrr,rrf,_⟩ := hr
 obtain ⟨rl,hrl,rlf,_⟩ := hl
 constructor
 · apply Step.of_run hrr ?_ (congrArg Configuration.tapes rrf)
   rw [rrf]; funext i
   by_cases h : i=cache 13 ∨ i=cache 14
   · have hz : H i=0 := by rcases h with h|h <;> subst i <;> apply hH
     simp [HeadMove.apply, moving, h, hz]
   · simp [HeadMove.apply, moving, h]
 · apply Step.of_run hrl ?_ (congrArg Configuration.tapes rlf)
   rw [rlf]; funext i
   by_cases h : i=cache 13 ∨ i=cache 14
   · have hz : H i=0 := by rcases h with h|h <;> subst i <;> apply hH
     simp [HeadMove.apply, moving, h, hz]
   · simp [HeadMove.apply, moving, h]

include hi in
theorem moving_cache (H : Fin B → Nat) (hH : ∀ j, H (cache j)=0) (j : Fin 19) :
 moving cache H (cache j)=PCPPQueryClauseReuse.heads j := by
 simp only [moving, hi.eq_iff, hH, PCPPQueryClauseReuse.heads]

/-- Same syntax as the selected branch's complete per-clause program. -/
def program {ss : Nat} (terminal : Fin B) (site : Machine B ss) :=
 let slots : Fin 4 → Fin B := ![cache 14,terminal,cache 1,cache 2]
 let test := RecoveryFocus.machine slots CloseoutRowsGateArityCheck.machine
 let clear := C10LengthGate.branch (cache 2) (cache 1) (CloseoutRowsOriginalSwitch.stop B)
 let query := RecoveryFocus.machine cache PCPPQueryClauseReuse.machine
 let advance := RecoveryFocus.machine cache CloseoutFinalC10RequestAtCursor.advance
 let live := Composition.machine (right cache)
   (Composition.machine query (Composition.machine (left cache)
     (Composition.machine site (Composition.machine (right cache)
       (Composition.machine advance (left cache))))))
 Composition.machine test (CloseoutRowsOriginalSwitch.machine clear live (cache 1))

theorem fuel_bound (j M Q S : Nat) :
 (2*min j M+6)+1+((1+1+(Q+1+(1+1+(S+1+(1+1+((2*j+2)+1+(1)))))))+2) ≤ 4*j+Q+S+21 := by
 have h := Nat.min_le_left j M
 omega

include hi in
theorem run_generic {ss : Nat} (terminal : Fin B) (hdisjoint : ∀ j,cache j≠terminal)
 (source packet : List Bool) (arity j M C Q : Nat) (hj : j<M) (hcap : j+3≤C)
 (raw : Step PCPPQueryClauseReuse.machine Q PCPPQueryClauseReuse.heads
   (PCPPQueryIndexPadding.clauseData source arity j C [])
   PCPPQueryClauseReuse.heads (PCPPQueryIndexPadding.clauseData source arity j C packet))
 (site : Machine B ss) (siteFuel : Nat)
 (H H' : Fin B → Nat) (A A' : Fin B → List Bool)
 (hH : ∀ j,H (cache j)=0) (hH' : ∀ j,H' (cache j)=0) (hterminal : H terminal=0)
 (hcount : A terminal=List.replicate M true)
 (hcache : ∀ i,A (cache i)=PCPPQueryIndexPadding.clauseData source arity j C [] i)
 (hsite : Step site siteFuel H
   (install cache A (PCPPQueryIndexPadding.clauseData source arity j C packet)) H' A')
 (hrestored : ∀ i,A' (cache i)=PCPPQueryIndexPadding.clauseData source arity j C [] i) :
 Step (program cache terminal site) (4*j+Q+siteFuel+21)
   H A H' (install cache A' (PCPPQueryIndexPadding.clauseData source arity (j+1) C [])) := by
 classical
 let queried := PCPPQueryIndexPadding.clauseData source arity j C packet
 let AQ := install cache A queried
 let next := PCPPQueryIndexPadding.clauseData source arity (j+1) C []
 let AN := install cache A' next
 let ts : Fin 4 → Fin B := ![cache 14,terminal,cache 1,cache 2]
 have htinj : Function.Injective ts := by
   intro i k hik
   change (![cache 14,terminal,cache 1,cache 2] : Fin 4 → Fin B) i =
     (![cache 14,terminal,cache 1,cache 2] : Fin 4 → Fin B) k at hik
   clear * - hi hdisjoint hik
   fin_cases i <;> fin_cases k <;> dsimp at hik ⊢
   all_goals first | rfl | exact False.elim (hdisjoint _ hik) | exact False.elim (hdisjoint _ hik.symm) | exact False.elim (by have := hi hik; contradiction)
 have hts : ∀ i,H (ts i)=0 := by
   intro i; fin_cases i <;> simp [ts,hH,hterminal]
 have hta : ∀ i,A (ts i)=testInput j M C i := by
   intro i; fin_cases i
   · exact hcache 14
   · exact hcount
   · exact hcache 1
   · exact hcache 2
 have ho : testOutput j M C=testInput j M C := by
   have hne : j≠M := Nat.ne_of_lt hj
   funext i; fin_cases i <;> dsimp [testOutput,testInput]
   rw [decide_eq_false hne]
   exact pad_replicate_false C 1 (by omega)
 have test := (terminal_test j M C (by omega)).dock ts htinj H A hts hta
 rw [ho,dockH_existing ts H _ hts,install_existing ts A _ hta] at test
 have flag : readTapeBit (A (cache 1)) (H (cache 1))=false := by
   rw [hH,hcache]
   simp [PCPPQueryIndexPadding.clauseData,PCPPQueryClauseReuse.data,readTapeBit]
 have query := raw.dock cache hi (moving cache H) A (moving_cache cache hi H hH) hcache
 rw [dockH_existing cache (moving cache H) _ (moving_cache cache hi H hH)] at query
 have inc := (CloseoutFinalC10RequestAtCursor.advance_step source arity j C hcap).dock
   cache hi (moving cache H') A' (moving_cache cache hi H' hH') hrestored
 rw [dockH_existing cache (moving cache H') _ (moving_cache cache hi H' hH')] at inc
 have incLeft := inc.seq (position cache H' AN hH').2
 have restored := (position cache H' A' hH').1.seq incLeft
 have call := hsite.seq restored
 have leftCall := (position cache H AQ hH).2.seq call
 have queryCall := query.seq leftCall
 have live := (position cache H A hH).1.seq queryCall
 have switch := CloseoutRowsOriginalSwitch.false_run
   (C10LengthGate.branch (cache 2) (cache 1) (CloseoutRowsOriginalSwitch.stop B))
   _ (cache 1) live flag
 have result := test.seq switch
 exact result.enlarge (fuel_bound j M Q siteFuel)

include hi in
theorem run {ss : Nat} (terminal : Fin B) (hdisjoint : ∀ j,cache j≠terminal)
 (a : PointwisePCPPAlgorithm) (rq : PCPPRequest a.minimumArity)
 (ci : Fin (2^(a.output rq).clauseBits)) (site : Machine B ss) (siteFuel : Nat)
 (H H' : Fin B → Nat) (A A' : Fin B → List Bool)
 (hH : ∀ j,H (cache j)=0) (hH' : ∀ j,H' (cache j)=0) (hterminal : H terminal=0)
 (hcount : A terminal=List.replicate (2^(a.output rq).clauseBits) true)
 (hcache : ∀ j,A (cache j)=PCPPQueryIndexPadding.clauseData
   (pcppOutput rq (a.output rq)) rq.arity ci.val
   (PCPPQueryCachedBounds.capacity a (rq.circuit.size+rq.arity)) [] j)
 (hsite : Step site siteFuel H
   (install cache A (PCPPQueryIndexPadding.clauseData
     (pcppOutput rq (a.output rq)) rq.arity ci.val
     (PCPPQueryCachedBounds.capacity a (rq.circuit.size+rq.arity))
     (natListWord [literalIndex ((a.output rq).clauses ci).left,
       literalIndex ((a.output rq).clauses ci).right]))) H' A')
 (hrestored : ∀ j,A' (cache j)=PCPPQueryIndexPadding.clauseData
   (pcppOutput rq (a.output rq)) rq.arity ci.val
   (PCPPQueryCachedBounds.capacity a (rq.circuit.size+rq.arity)) [] j) :
 Step (program cache terminal site)
   (4*ci.val+PCPPQueryCachedBounds.callBudget a (rq.circuit.size+rq.arity)+siteFuel+21)
   H A H' (install cache A' (PCPPQueryIndexPadding.clauseData
     (pcppOutput rq (a.output rq)) rq.arity (ci.val+1)
     (PCPPQueryCachedBounds.capacity a (rq.circuit.size+rq.arity)) [])) := by
 obtain ⟨qr,hqr,hqt,hqh,hqs⟩ := PCPPQueryIndexPadding.clause_run a rq ci
 rw [PCPPQueryIndexPadding.clause_entry] at hqr
 exact run_generic cache hi terminal hdisjoint _ _ _ _ _ _ _ ci.isLt
   (CloseoutFinalC10RequestAtCursor.next_index_fits a rq ci)
   ⟨qr,hqr,hqh,hqt,hqs⟩ site siteFuel H H' A A' hH hH' hterminal hcount hcache hsite hrestored

attribute [local irreducible] P1TopDown.WorkspaceSelectedAdmission.originalTapes
 P1TopDown.WorkspaceSelectedEntry.size

theorem selected_program (sources : RepairSource.EightSources) {gamma : Real}
 (p : RepairSource.CloseoutFinal.Parameters sources gamma) (k r scratch : Nat)
 (site : Bool → CloseoutRowsOriginalSchedule.Phase → Σ s,
 Machine (P1TopDown.ControllerSelectedContinuation.bodyTapes sources p k r scratch) s)
 (mode : Bool) (ph : CloseoutRowsOriginalSchedule.Phase) :
 (SelectedBranchPhases.clause sources p k r scratch site mode ph).2 =
 program (SelectedBranchPhases.cache sources p k r scratch mode)
   ⟨SelectedBranchPhases.offset sources p k r+53,
     by have := SelectedBranchPhases.fresh_lt sources p k r scratch; omega⟩
   (site mode ph).2 := rfl

end
end LiveClauseSites
