import Proof.Amplification.RecoveryMarkerHandoffPrepared

namespace NearCubicWires.RepairOrdinary.RecoveryMarkerHandoff
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open RepairSource.RecoveryOracle CompactCertificate CompactCertificate.Serialization
open private decodeClauseCodes from StatementSupport
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def flatState (x : CheckState) : RecoveryRowRoot.State := ⟨x.inner,x.innerTotal,x.outer.key⟩
def flatSlots (i : Fin 70) : Fin 212 := if i.val<69 then ⟨57+i.val,by omega⟩ else 211
theorem flat_injective : Function.Injective flatSlots := by
  intro i j h
  have hv := congrArg Fin.val h
  unfold flatSlots at hv
  split at hv <;> split at hv <;> apply Fin.ext <;> dsimp at hv <;> omega
noncomputable def flatMachine := RecoveryFocus.machine flatSlots RecoveryRowRoot.wholeMachine

open private focus_configuration from Proof.Amplification.RecoveryValuationStreamTapes

theorem flat_config {s : Nat} (marker : MarkerState) (x : CheckState) (q : Fin s) :
    RecoveryFocus.config flatSlots (heads x) (tapes marker x) ((flatState x).cfg q)=cfg marker x q := by
  apply focus_configuration flatSlots flat_injective
  · rfl
  · intro j; fin_cases j <;> rfl
  · intro j; fin_cases j <;> rfl
  · intro i _; rfl
  · intro i _; rfl

theorem flat_run (marker : MarkerState) (x : CheckState) (limit : Nat)
    (word innerBits outerBits innerPre outerPre : List Bool)
    (hx : RecoveryNestedTable.Prepared x limit word innerBits outerBits innerPre outerPre)
    (table : FiniteValuation.Table) (rest : List Bool)
    (hp : readList x.inner.base.extra.cap (readEntry x.inner.base.state.bits.length) word=some (table,rest)) :
    ∃ r,runFrom flatMachine (RecoveryRowRoot.wholeBudget x.inner.base.state.bits.length limit x.innerTotal)
        (cfg marker x flatMachine.start)=some r ∧
      r.steps ≤ RecoveryRowRoot.wholeBudget x.inner.base.state.bits.length limit x.innerTotal ∧
      r.final.heads 107=0 ∧ r.final.tapes 107=[RecoveryRowRoot.wholeAnswer (flatState x) word innerBits] ∧
      (r.final.tapes 107=[true] → ∃ codes,CanonicalBinary.decodeBalancedList (RadixSemantics.value x.outer.key)=some codes ∧
        compactMeaning ⟨decodeClauseCodes codes,RadixSemantics.value x.inner.base.extra.committed,
          RadixSemantics.value x.inner.base.extra.binaryCount⟩) := by
  have hv : (flatState x).Valid word innerBits := ⟨hx.innerValid,hx.outerValid.2.trans hx.copiedWidth⟩
  obtain ⟨base,hr,hb,hh,ht,hmeaning⟩ := RecoveryRowRoot.whole_root_run limit word innerBits innerPre
    (flatState x) hv hx.innerZero hx.innerBound hx.innerSource hx.innerPos hx.innerCapacity
  obtain ⟨r,hrun,hf,hs⟩ := RecoveryFocus.run_config flatSlots flat_injective RecoveryRowRoot.wholeMachine
    (heads x) (tapes marker x) _ _ base hr
  rw [flat_config] at hrun
  have ht' : r.final.tapes 107=[RecoveryRowRoot.wholeAnswer (flatState x) word innerBits] := by
    rw [hf]
    change (RecoveryFocus.config flatSlots (heads x) (tapes marker x) base.final).tapes (flatSlots 50)=_
    simp only [RecoveryFocus.config,RecoveryFocus.pick_slot flatSlots flat_injective]
    exact ht
  refine ⟨r,hrun,hs.le.trans hb,?_,ht',?_⟩
  · rw [hf]
    change (RecoveryFocus.config flatSlots (heads x) (tapes marker x) base.final).heads (flatSlots 50)=0
    simp only [RecoveryFocus.config,RecoveryFocus.pick_slot flatSlots flat_injective]
    exact hh
  · intro ha
    have he : RecoveryRowRoot.wholeAnswer (flatState x) word innerBits=true := List.singleton_inj.mp (ht'.symm.trans ha)
    obtain ⟨codes,hd,hc⟩ := hmeaning he
    change codes.all (RecoveryRowStructure.tableLeafPredicate x.inner word)=true at hc
    rw [RecoveryNestedTable.valuation_predicate x word table rest hp,clause_codes_check] at hc
    exact ⟨codes,hd,FiniteValuation.check_sound _ table hc⟩

end NearCubicWires.RepairOrdinary.RecoveryMarkerHandoff
