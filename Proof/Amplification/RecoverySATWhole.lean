import Proof.Amplification.RecoverySATEntry

/-! Whole cold RawSAT allocation. The actual valuation gate precedes all
copies; successful execution retains the original raw-view input bank. -/
namespace NearCubicWires.RepairOrdinary.RecoveryColdSAT
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open RepairSource.VerifierDecoding
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
open RecoveryColdView
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def coldProgram := RecoveryGatedSequence.machine prefixProgram bankProgram 30
def coldBudget (bits word : List Bool) := RecoveryColdView.coldBudget bits word+bankBudget bits word+2
def Ready (bits word : List Bool) (h : Fin 172→Nat) (a : Fin 172→List Bool) : Prop :=
  ∃ pos b,Sources bits word b ∧
    RecoveryColdView.Ready bits word (fun j=>heads pos (j.castAdd 72)) (fun j=>b (j.castAdd 72)) ∧
    h=heads pos ∧ a=stage9 bits word b

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
    obtain ⟨r,hr,_,hh,ht⟩ := initial_reject prefixProgram bankProgram 30
      (RecoveryColdView.coldBudget bits word) _ first hfirst hfh hfalse
    have hle : RecoveryColdView.coldBudget bits word+1≤coldBudget bits word := by
      unfold coldBudget
      omega
    have hm := run_moreFuel coldProgram (RecoveryColdView.coldBudget bits word+1)
      (coldBudget bits word-(RecoveryColdView.coldBudget bits word+1)) _ r hr
    rw [Nat.add_sub_of_le hle] at hm
    refine ⟨r,hm,runFrom_steps_le coldProgram (coldBudget bits word) _ r hm,?_,?_,?_⟩
    · rw [hh]
      exact hfh
    · rw [ht]
      exact hfalse
    · simp only [Option.isSome_none,Bool.false_eq_true,IsEmpty.forall_iff]
  | some pair=>
    obtain ⟨table,tail⟩ := pair
    obtain ⟨pos,hheads,hsrc,hview⟩ := hgood table tail hp
    have htrue : first.final.tapes 30=[true] := by simpa only [hp,Option.isSome_some] using hft
    obtain ⟨last,hlast,hlh,hlt,_⟩ := bank_run bits word pos first.final.tapes hsrc
    rw [←hheads] at hlast
    obtain ⟨r,hr,_,hrh,hrt⟩ := initial_accept prefixProgram bankProgram 30
      (RecoveryColdView.coldBudget bits word) (bankBudget bits word) _ first last hfirst hfh htrue hlast
    refine ⟨r,hr,runFrom_steps_le coldProgram (coldBudget bits word) _ r hr,?_,?_,?_⟩
    · rw [hrh,hlh]
      rfl
    · rw [hrt,hlt,low_retained bits word first.final.tapes 30 (by decide)]
      exact htrue
    · intro _
      rw [hheads] at hview
      exact ⟨pos,first.final.tapes,hsrc,hview,hrh.trans hlh,hrt.trans hlt⟩

theorem ready_view (bits word : List Bool) (h : Fin 172→Nat) (a : Fin 172→List Bool)
    (hr : Ready bits word h a) :
    RecoveryColdView.Ready bits word (fun j=>h (j.castAdd 72)) (fun j=>a (j.castAdd 72)) := by
  obtain ⟨pos,b,_,hb,hh,ht⟩ := hr
  rw [hh,ht,low_tapes]
  exact hb

theorem ready_sat {s : Nat} (bits word : List Bool) (h : Fin 172→Nat) (a : Fin 172→List Bool)
    (hr : Ready bits word h a) (q : Fin s) :
    ZeroPadding.config (caps bits word) ⟨q,(fun j=>h (satSlots j)),(fun j=>a (satSlots j))⟩=
      (state bits word).cfg q := by
  obtain ⟨pos,b,hb,_,hh,ht⟩ := hr
  rw [hh,ht]
  exact bank_native bits word pos b hb q

theorem ready_retained (bits word : List Bool) (h : Fin 172→Nat) (a : Fin 172→List Bool)
    (hr : Ready bits word h a) :
    a 1=frame word ∧ a 24=CompareMachine.word word.length ∧
      a 14=CompareMachine.word (width bits+1) := by
  obtain ⟨pos,b,hb,_,_,ht⟩ := hr
  rw [ht,low_retained bits word b 1 (by decide),low_retained bits word b 24 (by decide),
    low_retained bits word b 14 (by decide)]
  exact ⟨hb.source,hb.length,hb.increment⟩

end NearCubicWires.RepairOrdinary.RecoveryColdSAT
