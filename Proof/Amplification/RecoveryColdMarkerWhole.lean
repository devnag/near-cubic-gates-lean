import Proof.Amplification.RecoveryMarkerLayout

/-! The actual cold front gates all marker broadcasts. Malformed witnesses
stop with the original false flag; success retains every prepared raw/table
input and supplies the native marker bank on fresh tapes. -/
namespace NearCubicWires.RepairOrdinary.RecoveryColdMarker
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryColdView
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def prefixProgram := TapeEmbedding.machine 59 RecoveryColdFront.machine
def input (bits word : List Bool) := lift (RecoveryColdFront.input bits word)
noncomputable def coldProgram := RecoveryGatedSequence.machine prefixProgram bankProgram 277
def coldBudget (bits word : List Bool) := RecoveryColdFront.budget bits word+bankBudget bits+2
def Ready (bits word : List Bool) (H : Fin 338→Nat) (A : Fin 338→List Bool) : Prop :=
  ∃ (h : Fin 279→Nat) (a : Fin 279→List Bool),
    RecoveryColdFront.Prepared bits word h a ∧ H=heads h ∧ A=stage6 bits a

theorem prefix_run (bits word : List Bool) :
    ∃ bit,∃ (base : ExecutionReceipt 279 (RecoveryColdFront.stateCount RecoveryColdFront.machine)),
      run RecoveryColdFront.machine (RecoveryColdFront.budget bits word)
        (RecoveryColdFront.input bits word)=some base ∧
      ∃ r,run prefixProgram (RecoveryColdFront.budget bits word) (input bits word)=some r ∧
        r.final.heads=heads base.final.heads ∧ r.final.tapes=lift base.final.tapes ∧
        r.final.heads 277=0 ∧ r.final.tapes 277=[bit] ∧
        (bit=true → RecoveryColdFront.Prepared bits word base.final.heads base.final.tapes) := by
  obtain ⟨bit,base,hbase,_,hh,ht,hgood⟩ := RecoveryColdFront.front_run bits word
  let r := TapeEmbedding.receipt (fun _ : Fin 59=>0) (fun _=>[]) base
  have hr := TapeEmbedding.run_embed RecoveryColdFront.machine (fun _ : Fin 59=>0)
    (fun _=>[]) (RecoveryColdFront.budget bits word) _ base hbase
  have hi : TapeEmbedding.config (fun _ : Fin 59=>0) (fun _=>[])
      (initialConfiguration RecoveryColdFront.machine (RecoveryColdFront.input bits word))=
        initialConfiguration prefixProgram (input bits word) := by
    apply configuration_ext
    · rfl
    · funext i
      refine Fin.addCases (m:=279) (n:=59) (motive:=fun j=>
        (TapeEmbedding.config (fun _ : Fin 59=>0) (fun _=>[])
          (initialConfiguration RecoveryColdFront.machine (RecoveryColdFront.input bits word))).heads j=0)
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
    obtain ⟨r,hr,hs,hrh,hrt⟩ := initial_reject prefixProgram bankProgram 277
      (RecoveryColdFront.budget bits word) _ first hfirst hh hfalse
    have hle : RecoveryColdFront.budget bits word+1≤coldBudget bits word := by
      unfold coldBudget; omega
    have hm := run_moreFuel coldProgram (RecoveryColdFront.budget bits word+1)
      (coldBudget bits word-(RecoveryColdFront.budget bits word+1)) _ r hr
    rw [Nat.add_sub_of_le hle] at hm
    refine ⟨false,r,hm,hs.trans hle,?_,?_,?_⟩
    · rw [hrh]; exact hh
    · rw [hrt]; exact hfalse
    · intro hf
      exact False.elim (Bool.false_ne_true hf)
  | true=>
    have hready := hgood hb
    have htrue : first.final.tapes 277=[true] := ht.trans (congrArg (fun b=>[b]) hb)
    obtain ⟨last,hlast,hlh,hlt,_⟩ := bank_run bits base.final.heads base.final.tapes
      (sources bits word base.final.heads base.final.tapes hready)
    rw [←hfh,←hft] at hlast
    obtain ⟨r,hr,hs,hrh,hrt⟩ := initial_accept prefixProgram bankProgram 277
      (RecoveryColdFront.budget bits word) (bankBudget bits) _ first last hfirst hh htrue hlast
    refine ⟨true,r,hr,hs,?_,?_,?_⟩
    · rw [hrh,hlh]
      have h0 : (heads base.final.heads) 277=first.final.heads 277 := congrFun hfh.symm 277
      exact h0.trans hh
    · rw [hrt,hlt]
      change stage6 bits base.final.tapes ((277 : Fin 279).castAdd 59)=[true]
      rw [retained]
      have h0 : base.final.tapes 277=first.final.tapes 277 := congrFun hft.symm 277
      exact h0.trans htrue
    · intro _
      exact ⟨base.final.heads,base.final.tapes,hready,hrh.trans hlh,hrt.trans hlt⟩

end NearCubicWires.RepairOrdinary.RecoveryColdMarker
