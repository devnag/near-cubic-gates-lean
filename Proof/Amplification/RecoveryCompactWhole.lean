import Proof.Amplification.RecoveryCompactMaterializeExact

/-! Whole cold materialization from the original two input tapes. The
retained rejecting flag gates the complete493-tape allocation, and success
keeps the exact source-vector equality needed by canonical completeness. -/
namespace NearCubicWires.RepairOrdinary.RecoveryColdCompact
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryColdView
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def prefixProgram := TapeEmbedding.machine 155 RecoveryColdMarker.coldProgram
def input (bits word : List Bool) := bankInput (RecoveryColdMarker.input bits word)
noncomputable def coldProgram := RecoveryGatedSequence.machine prefixProgram materializeProgram 277
def coldBudget (bits word : List Bool) := RecoveryColdMarker.coldBudget bits word+
  materializeBudget bits word (limit bits) (limit bits)+2
def Ready (bits word : List Bool) (H : Fin 493→Nat) (A : Fin 493→List Bool) : Prop :=
  ∃ (h : Fin 338→Nat) (a : Fin 338→List Bool),∃ n innerBits m outerBits,
    RecoveryColdMarker.Ready bits word h a ∧ n≤limit bits ∧ m≤limit bits ∧
    (fun j=>a (sourceSlots j))=sourceTapes bits word innerBits outerBits n m ∧
    H=finishHeads (bankHeads h) ∧
    A=finishTapes (stage34 bits word innerBits outerBits n m (bankInput a))

theorem prefix_run (bits word : List Bool) :
    ∃ bit,∃ (base : ExecutionReceipt 338 (RecoveryColdFront.stateCount RecoveryColdMarker.coldProgram)),
      run RecoveryColdMarker.coldProgram (RecoveryColdMarker.coldBudget bits word)
        (RecoveryColdMarker.input bits word)=some base ∧
      ∃ r,run prefixProgram (RecoveryColdMarker.coldBudget bits word) (input bits word)=some r ∧
        r.final.heads=liftedHeads base.final.heads ∧ r.final.tapes=bankInput base.final.tapes ∧
        r.final.heads 277=0 ∧ r.final.tapes 277=[bit] ∧
        (bit=true → RecoveryColdMarker.Ready bits word base.final.heads base.final.tapes) := by
  obtain ⟨bit,base,hbase,_,hh,ht,hgood⟩ := RecoveryColdMarker.cold_run bits word
  let r := TapeEmbedding.receipt (fun _ : Fin 155=>0) (fun _=>[]) base
  have hr := TapeEmbedding.run_embed RecoveryColdMarker.coldProgram (fun _ : Fin 155=>0)
    (fun _=>[]) (RecoveryColdMarker.coldBudget bits word) _ base hbase
  have hi : TapeEmbedding.config (fun _ : Fin 155=>0) (fun _=>[])
      (initialConfiguration RecoveryColdMarker.coldProgram (RecoveryColdMarker.input bits word))=
        initialConfiguration prefixProgram (input bits word) := by
    apply configuration_ext
    · rfl
    · funext i
      refine Fin.addCases (m:=338) (n:=155) (motive:=fun j=>
        (TapeEmbedding.config (fun _ : Fin 155=>0) (fun _=>[])
          (initialConfiguration RecoveryColdMarker.coldProgram (RecoveryColdMarker.input bits word))).heads j=0)
        (by intro j; simp only [TapeEmbedding.config,Fin.addCases_left,initialConfiguration])
        (by intro j; simp only [TapeEmbedding.config,Fin.addCases_right]) i
    · rfl
  rw [hi] at hr
  exact ⟨bit,base,hbase,r,hr,rfl,rfl,hh,ht,hgood⟩

theorem cold_run (bits word : List Bool) :
    ∃ bit,∃ r,run coldProgram (coldBudget bits word) (input bits word)=some r ∧
      r.steps≤coldBudget bits word ∧ r.final.heads 277=0 ∧ r.final.tapes 277=[bit] ∧
      (bit=true → Ready bits word r.final.heads r.final.tapes) := by
  obtain ⟨bit,base,_,first,hfirst,hfh,hft,hh,ht,hgood⟩ := prefix_run bits word
  cases hb : bit with
  | false=>
    have hfalse : first.final.tapes 277=[false] := ht.trans (congrArg (fun b=>[b]) hb)
    obtain ⟨r,hr,hs,hrh,hrt⟩ := initial_reject prefixProgram materializeProgram 277
      (RecoveryColdMarker.coldBudget bits word) _ first hfirst hh hfalse
    have hle : RecoveryColdMarker.coldBudget bits word+1≤coldBudget bits word := by
      unfold coldBudget; omega
    have hm := run_moreFuel coldProgram (RecoveryColdMarker.coldBudget bits word+1)
      (coldBudget bits word-(RecoveryColdMarker.coldBudget bits word+1)) _ r hr
    rw [Nat.add_sub_of_le hle] at hm
    refine ⟨false,r,hm,hs.trans hle,?_,?_,?_⟩
    · rw [hrh]; exact hh
    · rw [hrt]; exact hfalse
    · intro hf
      exact False.elim (Bool.false_ne_true hf)
  | true=>
    have hready := hgood hb
    have htrue : first.final.tapes 277=[true] := ht.trans (congrArg (fun b=>[b]) hb)
    obtain ⟨n,innerBits,m,outerBits,hn,hm,hsource,last,hlast,hlh,hlt,_⟩ :=
      materialize_exact bits word base.final.heads base.final.tapes hready
    have hbound : materializeBudget bits word n m≤
        materializeBudget bits word (limit bits) (limit bits) := by
      unfold materializeBudget bankBudget
      omega
    have hmore := runFrom_moreFuel materializeProgram (materializeBudget bits word n m)
      (materializeBudget bits word (limit bits) (limit bits)-materializeBudget bits word n m) _ last hlast
    rw [Nat.add_sub_of_le hbound,←hfh,←hft] at hmore
    obtain ⟨r,hr,hs,hrh,hrt⟩ := initial_accept prefixProgram materializeProgram 277
      (RecoveryColdMarker.coldBudget bits word) (materializeBudget bits word (limit bits) (limit bits))
      _ first last hfirst hh htrue hmore
    refine ⟨true,r,hr,hs,?_,?_,?_⟩
    · rw [hrh,hlh]
      change base.final.heads 277=0
      exact (congrFun hfh.symm 277).trans hh
    · rw [hrt,hlt]
      change finishTapes (stage34 bits word innerBits outerBits n m (bankInput base.final.tapes))
        ((277 : Fin 336).castAdd 157)=[true]
      rw [retained]
      exact (congrFun hft.symm 277).trans htrue
    · intro _
      exact ⟨base.final.heads,base.final.tapes,n,innerBits,m,outerBits,
        hready,hn,hm,hsource,hrh.trans hlh,hrt.trans hlt⟩

end NearCubicWires.RepairOrdinary.RecoveryColdCompact
