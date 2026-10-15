import Proof.Amplification.RecoveryViewPrepared

/-! The actual cold raw-view bank producer. Malformed valuation syntax
halts at its physical false gate; successful syntax supplies the native
reader bank from the original code/witness input and blank workspace. -/
namespace NearCubicWires.RepairOrdinary.RecoveryColdView
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open RepairSource.VerifierDecoding
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def coldProgram := RecoveryGatedSequence.machine prefixProgram preparedProgram 30
def coldBudget (bits word : List Bool) :=
  RecoveryColdValuation.resumedBudget bits word+bankBudget bits+4

def Ready (bits word : List Bool) (heads : Fin 100→Nat) (tapes : Fin 100→List Bool) : Prop :=
  ∃ table tail count a,
    readList (limit bits) (readEntry (width bits)) word=some (table,tail) ∧
    count≤limit bits ∧ tail=word.drop (count*(width bits+2)+1) ∧
    Sources bits a ∧ a 23=frame word ∧ a 31=CompareMachine.word count ∧
    heads=bootHeads (2*(count*(width bits+2)+1)) ∧ tapes=bootTapes bits a

theorem cold_run (bits word : List Bool) :
    ∃ r,run coldProgram (coldBudget bits word) (input bits word)=some r ∧
      r.steps≤coldBudget bits word ∧ r.final.heads 30=0 ∧
      r.final.tapes 30=[(readList (limit bits) (readEntry (width bits)) word).isSome] ∧
      ((readList (limit bits) (readEntry (width bits)) word).isSome=true →
        Ready bits word r.final.heads r.final.tapes) := by
  obtain ⟨first,hfirst,hfh,hft,hgood⟩ := prefix_run bits word
  cases hp : readList (limit bits) (readEntry (width bits)) word with
  | none=>
    have hfalse : first.final.tapes 30=[false] := by simpa only [hp,Option.isSome_none] using hft
    obtain ⟨r,hr,_,hh,ht⟩ := initial_reject prefixProgram preparedProgram 30
      (RecoveryColdValuation.resumedBudget bits word) _ first hfirst hfh hfalse
    have hle : RecoveryColdValuation.resumedBudget bits word+1≤coldBudget bits word := by
      unfold coldBudget
      omega
    have hm := run_moreFuel coldProgram (RecoveryColdValuation.resumedBudget bits word+1)
      (coldBudget bits word-(RecoveryColdValuation.resumedBudget bits word+1)) _ r hr
    rw [Nat.add_sub_of_le hle] at hm
    refine ⟨r,hm,runFrom_steps_le coldProgram (coldBudget bits word) _ r hm,?_,?_,?_⟩
    · rw [hh]
      exact hfh
    · rw [ht]
      exact hfalse
    · simp only [Option.isSome_none,Bool.false_eq_true,IsEmpty.forall_iff]
  | some pair=>
    obtain ⟨table,tail⟩ := pair
    obtain ⟨count,hc,htail,hheads,hsrc,hs,hcount⟩ := hgood table tail hp
    have htrue : first.final.tapes 30=[true] := by simpa only [hp,Option.isSome_some] using hft
    obtain ⟨last,hlast,hlh,hlt⟩ := prepared_run bits (2*(count*(width bits+2)+1)) first.final.tapes hsrc
    rw [←hheads] at hlast
    obtain ⟨r,hr,_,hrh,hrt⟩ := initial_accept prefixProgram preparedProgram 30
      (RecoveryColdValuation.resumedBudget bits word) (bankBudget bits+2) _ first last hfirst hfh htrue hlast
    have he : RecoveryColdValuation.resumedBudget bits word+(bankBudget bits+2)+2=coldBudget bits word := by
      unfold coldBudget
      omega
    rw [he] at hr
    refine ⟨r,hr,runFrom_steps_le coldProgram (coldBudget bits word) _ r hr,?_,?_,?_⟩
    · rw [hrh,hlh]
      rfl
    · rw [hrt,hlt,(boot_retained bits first.final.tapes).2.1]
      exact htrue
    · intro _
      exact ⟨table,tail,count,first.final.tapes,hp,hc,htail,hsrc,hs,hcount,hrh.trans hlh,hrt.trans hlt⟩

theorem ready_native {s : Nat} (bits word : List Bool) (heads : Fin 100→Nat)
    (tapes : Fin 100→List Bool) (h : Ready bits word heads tapes) (q : Fin s) :
    ∃ count,count≤limit bits ∧ tapes 23=frame word ∧ tapes 31=CompareMachine.word count ∧
      ZeroPadding.config (nativeCaps bits) ⟨q,(fun j=>heads (viewSlots j)),(fun j=>tapes (viewSlots j))⟩=
        RecoveryRawViewEnd.cfg (view bits word (2*(count*(width bits+2)+1))) 0 q := by
  obtain ⟨table,tail,count,a,_,hc,_,ha,hs,hn,hh,ht⟩ := h
  refine ⟨count,hc,?_,?_,?_⟩
  · rw [ht,(boot_retained bits a).1]
    exact hs
  · rw [ht,(boot_retained bits a).2.2]
    exact hn
  · rw [hh,ht]
    exact boot_native_layout bits word _ a ha hs q

end NearCubicWires.RepairOrdinary.RecoveryColdView
