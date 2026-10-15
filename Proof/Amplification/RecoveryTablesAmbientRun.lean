import Proof.Amplification.RecoveryTablesAmbientRetained

/-! Actual table materialization from the retained scanner and nine blank
tapes. The entry consumes only the existing source/width/cap tapes. -/
namespace NearCubicWires.RepairOrdinary.RecoveryColdTablesAmbient
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def Produced (width cap : Nat) (word : List Bool) (k : Nat)
    (h : Fin 270→Nat) (a : Fin 270→List Bool) (H : Fin 279→Nat) (A : Fin 279→List Bool) : Prop :=
  ∃ n innerBits m outerBits logged,n ≤ cap ∧ m ≤ cap ∧
    readCount cap (word.drop k)=some (n,innerBits) ∧
    readCount cap (innerBits.drop (4*width*n))=some (m,outerBits) ∧
    logged ≤ RecoveryColdTables.budget width cap word ∧
    H=(RecoveryFocus.config slots (heads h) (tapes a)
      (RecoveryColdTables.restored word innerBits outerBits n m width cap logged)).heads ∧
    A=(RecoveryFocus.config slots (heads h) (tapes a)
      (RecoveryColdTables.restored word innerBits outerBits n m width cap logged)).tapes

theorem accepted_parses (width cap : Nat) (word : List Bool) (k : Nat)
    (h : RecoveryColdTables.answer width cap word k=true) :
    ∃ n innerBits m outerBits,readCount cap (word.drop k)=some (n,innerBits) ∧
      readCount cap (innerBits.drop (4*width*n))=some (m,outerBits) := by
  cases hp : readCount cap (word.drop k) with
  | none=>simp [RecoveryColdTables.answer,hp] at h
  | some pair=>
    rcases pair with ⟨n,innerBits⟩
    have hi : (readCount cap (innerBits.drop (4*width*n))).isSome=true := by
      simpa only [RecoveryColdTables.answer,hp,Option.any_some] using h
    cases hq : readCount cap (innerBits.drop (4*width*n)) with
    | none=>simp [hq] at hi
    | some pair=>exact ⟨n,innerBits,pair.1,pair.2,rfl,hq⟩

theorem ambient_run (word : List Bool) (k width cap : Nat) (h : Fin 270→Nat) (a : Fin 270→List Bool)
    (ha : Sources word k width cap h a) :
    ∃ r,runFrom program (RecoveryColdTables.resetBudget width cap word)
        ⟨program.start,heads h,tapes a⟩=some r ∧
      r.steps ≤ RecoveryColdTables.resetBudget width cap word ∧ r.final.heads 277=0 ∧
      r.final.tapes 277=[RecoveryColdTables.answer width cap word k] ∧
      (RecoveryColdTables.answer width cap word k=true →
        Produced width cap word k h a r.final.heads r.final.tapes) := by
  obtain ⟨base,hr,hb,hh,ht,_,hready⟩ := RecoveryColdTables.reset_run width cap word k
  obtain ⟨r,hrun,hfinal,hsteps⟩ := RecoveryFocus.run_config slots slots_injective
    RecoveryColdTables.resetProgram (heads h) (tapes a) _ _ base hr
  rw [input_layout word k width cap h a ha] at hrun
  have hpick : RecoveryFocus.pick slots (277 : Fin 279)=some 10 :=
    RecoveryFocus.pick_slot slots slots_injective 10
  refine ⟨r,hrun,hsteps.le.trans hb,?_,?_,?_⟩
  · rw [hfinal]; simpa only [RecoveryFocus.config,hpick] using hh
  · rw [hfinal]; simpa only [RecoveryFocus.config,hpick] using ht
  · intro hgood
    obtain ⟨n,innerBits,m,outerBits,hp1,hp2⟩ := accepted_parses width cap word k hgood
    obtain ⟨hn,hm,logged,hlog,hout⟩ := hready n innerBits m outerBits hp1 hp2
    exact ⟨n,innerBits,m,outerBits,logged,hn,hm,hp1,hp2,hlog,
      by rw [hfinal,hout],by rw [hfinal,hout]⟩

noncomputable def coldProgram := Composition.machine ambientBoot program
def coldBudget (width cap : Nat) (word : List Bool) := RecoveryColdTables.resetBudget width cap word+2

theorem cold_run (word : List Bool) (k width cap : Nat) (h : Fin 270→Nat) (a : Fin 270→List Bool)
    (ha : Sources word k width cap h a) :
    ∃ r,runFrom coldProgram (coldBudget width cap word)
        ⟨coldProgram.start,coldHeads h,coldTapes a⟩=some r ∧
      r.steps ≤ coldBudget width cap word ∧ r.final.heads 277=0 ∧
      r.final.tapes 277=[RecoveryColdTables.answer width cap word k] ∧
      (RecoveryColdTables.answer width cap word k=true →
        Produced width cap word k h a r.final.heads r.final.tapes) := by
  obtain ⟨first,hfirst,hh,ht,_⟩ := boot_ambient h a
  obtain ⟨last,hlast,_,hlh,hlt,hready⟩ := ambient_run word k width cap h a ha
  have hi : Composition.restart first.final program.start=
      (⟨program.start,heads h,tapes a⟩ : Configuration 279 _) := by
    apply configuration_ext
    · rfl
    · exact hh
    · exact ht
  rw [←hi] at hlast
  have hj := Composition.run_join ambientBoot program 1 (RecoveryColdTables.resetBudget width cap word)
    _ first last hfirst hlast
  rw [show 1+1+RecoveryColdTables.resetBudget width cap word=coldBudget width cap word by unfold coldBudget; omega] at hj
  let r := Composition.joinedReceipt first last
  exact ⟨r,hj,runFrom_steps_le coldProgram (coldBudget width cap word) _ r hj,hlh,hlt,hready⟩

theorem produced_retained (word : List Bool) (k width cap : Nat) (h : Fin 270→Nat) (a : Fin 270→List Bool)
    (ha : Sources word k width cap h a) (H : Fin 279→Nat) (A : Fin 279→List Bool)
    (hp : Produced width cap word k h a H A) :
    (fun i : Fin 172=>H (i.castAdd 107))=(fun i=>h (i.castAdd 98)) ∧
      (fun i : Fin 172=>A (i.castAdd 107))=(fun i=>a (i.castAdd 98)) := by
  obtain ⟨n,innerBits,m,outerBits,logged,_,_,_,_,_,hh,ht⟩ := hp
  rw [hh,ht]
  exact restored_retained word innerBits outerBits k n m width cap logged h a ha

end NearCubicWires.RepairOrdinary.RecoveryColdTablesAmbient
