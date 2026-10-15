import Proof.CaseAnalysis.CloseoutRowsIntegerColdLoop

/-! One complete cold ordinary canonical-IntList decoder and native source
producer. Every driver, traversal, allocation, signed field and rewind is
executed; its verdict agrees with the public decoder on every raw input. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsIntegerCold
open LocalBitMultitape RecoveryRootRound RadixSemantics CloseoutWitness
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine:=Composition.machine prepare finish
def budget (bits : List Bool):=prepareBudget bits+1+finishBudget bits

theorem restart_ready {t s u : ℕ} (c : Configuration t s) (p : Machine t u)
    (tapes : Fin t→List Bool) (hh : ∀ i,c.heads i=0) (ht : c.tapes=tapes) :
    Composition.restart c p.start=initialConfiguration p tapes:=by
  apply configuration_ext
  · rfl
  · funext i;exact hh i
  · exact ht

theorem result_fields (bits : List Bool) :
    (loopResult bits).tapes (213 : Fin 221)=produced bits ∧
      (loopResult bits).heads (213 : Fin 221)=(produced bits).length ∧
      (loopResult bits).tapes (219 : Fin 221)=
        [CloseoutRowsIntegerLoop.validity (CloseoutRowsCanonicalFlag.flag bits)
          (Reencode.fields bits) (Reencode.fields bits).length] ∧
      (loopResult bits).tapes (220 : Fin 221)=CompareMachine.word (Reencode.fields bits).length:=by
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem validity_iff (bits : List Bool)
    (hcanonical : CloseoutRowsCanonicalFlag.flag bits=true ↔
      ∃ codes,CanonicalBinary.encodeBalancedList codes=value bits) :
    CloseoutRowsIntegerLoop.validity (CloseoutRowsCanonicalFlag.flag bits)
        (Reencode.fields bits) (Reencode.fields bits).length=true ↔
      (CanonicalBinary.decodeIntList (value bits)).isSome:=by
  have hfields:=CloseoutRowsIntegerLoop.validity_true (Reencode.fields bits)
  simp only [CloseoutRowsIntegerLoop.validity,Bool.true_and] at hfields
  rw [CloseoutRowsIntegerLoop.validity,Bool.and_eq_true,hcanonical,hfields,
    ←CloseoutRowsIntegerList.checks_iff]
  rfl

theorem native_run (bits : List Bool) : ∃ actual,
    run machine (budget bits) (input bits)=some actual ∧ actual.steps≤budget bits ∧
      actual.final.tapes 213=produced bits ∧ actual.final.heads 213=(produced bits).length ∧
      (readTapeBit (actual.final.tapes 219) 0=true ↔
        (CanonicalBinary.decodeIntList (value bits)).isSome) ∧
      actual.final.tapes 220=CompareMachine.word (Reencode.fields bits).length ∧
      (∀ values,CanonicalBinary.decodeIntList (value bits)=some values →
        actual.final.tapes 213=values.flatMap RepairRepresentation.intWord ∧
          actual.final.tapes 220=CompareMachine.word values.length):=by
  obtain ⟨prepared,hp,hinput,hcanonical⟩:=prepare_run bits
  obtain ⟨a,ha,atapes,aheads,asteps⟩:=hp
  obtain ⟨b,hb,bsteps,btapes,bheads⟩:=finish_run bits prepared hinput
  have hi:=restart_ready a.final finish prepared aheads atapes
  have hb':runFrom finish (finishBudget bits) (Composition.restart a.final finish.start)=some b:=by
    rw [hi]
    exact hb
  have h:=Composition.run_join prepare finish _ _ _ a b ha hb'
  have ho:b.final.tapes 213=produced bits:=
    (btapes 213).trans (result_fields bits).1
  have hc:b.final.tapes 220=CompareMachine.word (Reencode.fields bits).length:=
    (btapes 220).trans (result_fields bits).2.2.2
  refine ⟨_,h,?_,ho,(bheads 213).trans (result_fields bits).2.1,?_,hc,?_⟩
  · change a.steps+1+b.steps≤budget bits
    unfold budget
    omega
  · change readTapeBit (b.final.tapes (loopSlots 219)) 0=true ↔_
    rw [btapes,(result_fields bits).2.2.1]
    exact validity_iff bits hcanonical
  · intro values hv
    have hcheck:CloseoutRowsIntegerList.checks bits:=
      (CloseoutRowsIntegerList.checks_iff bits).mpr (Option.isSome_iff_exists.mpr ⟨values,hv⟩)
    obtain ⟨zs,_,hz,hcount,hout⟩:=CloseoutRowsIntegerList.typed_of_checks bits hcheck
    have he:zs=values:=Option.some.inj (hz.symm.trans hv)
    subst zs
    exact ⟨ho.trans hout,hc.trans (congrArg CompareMachine.word hcount.symm)⟩

end NearCubicWires.RepairOrdinary.CloseoutRowsIntegerCold
