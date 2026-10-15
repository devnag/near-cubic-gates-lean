import Proof.MachineModel.RoundState

/-! Ordered repetition of the same cleaned occurrence body. The actual unary
occurrence driver advances and returns; no output cache is an input premise. -/
namespace NearCubicWires.ExtDecompositionBatch
open LocalBitMultitape RepairOrdinary RepairRepresentation ExecutableInterfaces
open RepairOrdinary.DecompositionSource RepairOrdinary.RecoveryRootRound SupplierPipeline
open RepairOrdinary.CloseoutRowsCircuitBottom RepairOrdinary.RecoveryExecution
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
variable (a : DecompositionAlgorithm)

noncomputable def loopStore (C q pos : ℕ) (source c1 c2 c3 : List Bool) :=
  (⟨(cleanRound a).start,loopInH a pos c1 c2 c3,loopInA a C q source c1 c2 c3⟩ : Configuration (CT a) _)
noncomputable def occurrenceLoop:=RepeatMachine.machine (cleanRound a) (fun _ _=>true)
noncomputable def loopCfg (phase : Fin 5) (C q pos : ℕ) (source c1 c2 c3 : List Bool) (total driver : ℕ) :=
  RepeatMachine.cfg phase (loopStore a C q pos source c1 c2 c3) total driver

def requestStream {q : ℕ} (occ : List (SupportedNormalizedGate q)):=occ.flatMap (fun g=>frame (nativeWord g))
def roundSum {q : ℕ} (C : ℕ) (occ : List (SupportedNormalizedGate q)):=
  (occ.map (fun g=>roundCost a C g+2)).sum

theorem B_cons {q : ℕ} (g : SupportedNormalizedGate q) (occ : List (SupportedNormalizedGate q)) :
    B a (g::occ)=(children a g).length+B a occ := by simp [B,GS]

theorem remaining (C q : ℕ) (occ : List (SupportedNormalizedGate q))
    (pre rest c1 c2 c3 : List Bool) (total pos : ℕ) (hn : pos+occ.length=total)
    (hC : ∀ g∈occ,bodyCost a q g<C) :
    ∃ n,n≤roundSum a C occ+total+3 ∧
      Timed (occurrenceLoop a) n
        (loopCfg a 0 C q pre.length (pre++requestStream occ++rest) c1 c2 c3 total (pos+1))
        (loopCfg a 3 C q (pre.length+(requestStream occ).length) (pre++requestStream occ++rest)
          (c1++(counts a occ).flatMap natWord) (c2++(GS a occ).flatMap exactWord)
          (c3++List.replicate (B a occ) true) total 1) := by
  induction occ generalizing pre c1 c2 c3 pos with
  | nil =>
    have hp:pos=total:=by simpa only [List.length_nil,Nat.add_zero] using hn
    subst pos
    refine ⟨total+3,by simp [roundSum],?_⟩
    simpa only [occurrenceLoop,loopCfg,requestStream,List.flatMap_nil,List.append_nil,counts,List.map_nil,
      GS,B,List.length_nil,List.replicate_zero,Nat.add_zero] using
      RepeatMachine.exhaust (cleanRound a) (fun _ _=>true)
        (loopStore a C q pre.length (pre++rest) c1 c2 c3) total
  | cons g occ ih =>
    obtain ⟨r,hr,hh,ht,hs⟩:=round_run a C q g pre (requestStream occ++rest) c1 c2 c3
      (hC g (by simp))
    have hb:=RepeatMachine.iteration (cleanRound a) (fun _ _=>true)
      (loopStore a C q pre.length (pre++frame (nativeWord g)++(requestStream occ++rest)) c1 c2 c3)
      total pos r rfl (by simp only [List.length_cons] at hn;omega) hr
    have endCfg : RepeatMachine.cfg 0 r.final total (pos+2)=
        loopCfg a 0 C q (pre.length+(frame (nativeWord g)).length)
          (pre++frame (nativeWord g)++(requestStream occ++rest))
          (c1++natWord (children a g).length) (c2++(children a g).flatMap exactWord)
          (c3++List.replicate (children a g).length true) total ((pos+1)+1) := by
      apply configuration_ext
      · rfl
      · simp only [RepeatMachine.cfg,controlConfig,TapeEmbedding.config,hh,loopCfg,loopStore]
      · simp only [RepeatMachine.cfg,controlConfig,TapeEmbedding.config,ht,loopCfg,loopStore]
    change Timed (occurrenceLoop a) (r.steps+2)
      (loopCfg a 0 C q pre.length (pre++frame (nativeWord g)++(requestStream occ++rest)) c1 c2 c3 total (pos+1))
      (RepeatMachine.cfg 0 r.final total (pos+2)) at hb
    rw [endCfg] at hb
    obtain ⟨n,nb,tail⟩:=ih (pre++frame (nativeWord g))
      (c1++natWord (children a g).length) (c2++(children a g).flatMap exactWord)
      (c3++List.replicate (children a g).length true) (pos+1)
      (by simp only [List.length_cons] at hn;omega) (fun x hx=>hC x (by simp [hx]))
    have sourceEq : (pre++frame (nativeWord g))++requestStream occ++rest=
        pre++frame (nativeWord g)++(requestStream occ++rest) := by simp only [List.append_assoc]
    rw [sourceEq,List.length_append] at tail
    have all:=hb.trans tail
    refine ⟨r.steps+2+n,?_,?_⟩
    · simp only [roundSum,List.map_cons,List.sum_cons] at nb ⊢
      omega
    · simpa only [requestStream,List.flatMap_cons,List.length_append,counts_cons,GS_cons,
        List.flatMap_append,B_cons,List.replicate_add,List.append_assoc,Nat.add_assoc] using all

end NearCubicWires.ExtDecompositionBatch
