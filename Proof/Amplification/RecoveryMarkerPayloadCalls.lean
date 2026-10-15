import Proof.Amplification.RecoveryMarkerFlatCall

/-! Both selected payload callees share the same physical answer slot and
one valuation parse, with a common cubic encoded-width execution bound. -/
namespace NearCubicWires.RepairOrdinary.RecoveryMarkerHandoff
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open RepairSource.RecoveryOracle CompactCertificate CompactCertificate.Serialization
open private decodeClauseCodes from StatementSupport
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def nestedMachine := RecoveryBankPair.rightMachine (t:=57) RecoveryNestedTable.machine
def payloadBudget (width : Nat) := 134217728*(width+1)^3
def payloadMeaning (x : CheckState) (flat : Bool) : Prop :=
  ∃ codes,(if flat then CanonicalBinary.decodeBalancedList (RadixSemantics.value x.outer.key)
    else BalancedCNFSATEncoding.decodeNestedBalancedCNFPayload (RadixSemantics.value x.outer.key))=some codes ∧
      compactMeaning ⟨decodeClauseCodes codes,RadixSemantics.value x.inner.base.extra.committed,
        RadixSemantics.value x.inner.base.extra.binaryCount⟩

theorem flat_budget (width limit total : Nat) (hl : limit ≤ 3*(width+1)) (ht : total ≤ limit) :
    RecoveryRowRoot.wholeBudget width limit total ≤ payloadBudget width := by
  have h := RecoveryNestedTable.budgets_le width limit total total hl ht ht
  unfold RecoveryRowRoot.wholeBudget RecoveryRowRoot.rootBudget payloadBudget
  unfold RecoveryOuterRoot.wholeBudget RecoveryOuterRoot.rootBudget at h
  omega

theorem right_answer_run {t u s : Nat} (p : Machine u s) (b bound : Nat)
    (lh : Fin t→Nat) (lt : Fin t→List Bool) (rh : Fin u→Nat) (rt : Fin u→List Bool)
    (slot : Fin u) (answer : Bool) (P : Prop) (hbound : b ≤ bound)
    (hbase : ∃ base,runFrom p b ⟨p.start,rh,rt⟩=some base ∧ base.steps ≤ bound ∧
      base.final.heads slot=0 ∧ base.final.tapes slot=[answer] ∧
      (base.final.tapes slot=[true] → P)) :
    ∃ r,runFrom (RecoveryBankPair.rightMachine (t:=t) p) bound
        (RecoveryBankPair.cfg lh lt rh rt p.start)=some r ∧ r.steps ≤ bound ∧
      r.final.heads (slot.natAdd t)=0 ∧ r.final.tapes (slot.natAdd t)=[answer] ∧
      (r.final.tapes (slot.natAdd t)=[true] → P) := by
  obtain ⟨base,hr,hb,hh,ht,hsound⟩ := hbase
  obtain ⟨r,hrun,hsteps,hf⟩ := RecoveryBankPair.right_run p b ⟨p.start,rh,rt⟩ base hr lh lt
  have hm := runFrom_moreFuel (RecoveryBankPair.rightMachine (t:=t) p) b (bound-b) _ r hrun
  rw [Nat.add_sub_of_le hbound] at hm
  have ht' : r.final.tapes (slot.natAdd t)=[answer] := by
    rw [hf]
    simpa only [RecoveryBankPair.cfg,Fin.addCases_right] using ht
  refine ⟨r,hm,hsteps.le.trans hb,?_,ht',?_⟩
  · rw [hf]
    simpa only [RecoveryBankPair.cfg,Fin.addCases_right] using hh
  · intro ha
    exact hsound (ht.trans (ht'.symm.trans ha))

theorem nested_run (marker : MarkerState) (x : CheckState) (limit : Nat)
    (word innerBits outerBits innerPre outerPre : List Bool)
    (hx : RecoveryNestedTable.Prepared x limit word innerBits outerBits innerPre outerPre)
    (hl : limit ≤ 3*(x.inner.base.state.bits.length+1))
    (table : FiniteValuation.Table) (rest : List Bool)
    (hp : readList x.inner.base.extra.cap (readEntry x.inner.base.state.bits.length) word=some (table,rest)) :
    ∃ r,runFrom nestedMachine (payloadBudget x.inner.base.state.bits.length) (cfg marker x nestedMachine.start)=some r ∧
      r.steps ≤ payloadBudget x.inner.base.state.bits.length ∧
      r.final.heads 107=0 ∧ r.final.tapes 107=[RecoveryNestedTable.answer x word innerBits outerBits] ∧
      (r.final.tapes 107=[true] → payloadMeaning x false) := by
  exact right_answer_run RecoveryNestedTable.machine (RecoveryNestedTable.budget x limit)
    (payloadBudget x.inner.base.state.bits.length) (fun _ : Fin 57=>0) marker.tapes
    (x.cfg (0 : Fin 1)).heads (x.cfg (0 : Fin 1)).tapes 50 (RecoveryNestedTable.answer x word innerBits outerBits)
    (payloadMeaning x false) (RecoveryNestedTable.budget_le x limit word innerBits outerBits innerPre outerPre hx hl)
    (RecoveryNestedTable.nested_meaning_run x limit word innerBits outerBits innerPre outerPre hx hl table rest hp)

theorem flat_bounded_run (marker : MarkerState) (x : CheckState) (limit : Nat)
    (word innerBits outerBits innerPre outerPre : List Bool)
    (hx : RecoveryNestedTable.Prepared x limit word innerBits outerBits innerPre outerPre)
    (hl : limit ≤ 3*(x.inner.base.state.bits.length+1))
    (table : FiniteValuation.Table) (rest : List Bool)
    (hp : readList x.inner.base.extra.cap (readEntry x.inner.base.state.bits.length) word=some (table,rest)) :
    ∃ r,runFrom flatMachine (payloadBudget x.inner.base.state.bits.length) (cfg marker x flatMachine.start)=some r ∧
      r.steps ≤ payloadBudget x.inner.base.state.bits.length ∧
      r.final.heads 107=0 ∧ r.final.tapes 107=[RecoveryRowRoot.wholeAnswer (flatState x) word innerBits] ∧
      (r.final.tapes 107=[true] → payloadMeaning x true) := by
  obtain ⟨r,hr,hb,hh,ht,hsound⟩ := flat_run marker x limit word innerBits outerBits innerPre outerPre hx table rest hp
  have hbound := flat_budget x.inner.base.state.bits.length limit x.innerTotal hl hx.innerBound
  have hm := runFrom_moreFuel flatMachine (RecoveryRowRoot.wholeBudget x.inner.base.state.bits.length limit x.innerTotal)
    (payloadBudget x.inner.base.state.bits.length-RecoveryRowRoot.wholeBudget x.inner.base.state.bits.length limit x.innerTotal) _ r hr
  rw [Nat.add_sub_of_le hbound] at hm
  exact ⟨r,hm,hb.trans hbound,hh,ht,hsound⟩

end NearCubicWires.RepairOrdinary.RecoveryMarkerHandoff
