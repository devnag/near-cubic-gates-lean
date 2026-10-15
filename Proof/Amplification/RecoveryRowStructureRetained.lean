import Proof.Amplification.RecoveryRowStructureAcceptance

namespace NearCubicWires.RepairOrdinary.RecoveryRowStructure
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryRowStream
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
open RepairSource.RecoveryOracle.BalancedCertificate
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem children_retained (x : Children) (pair bits : List Bool) :
    (childrenOutput x pair bits).base.state.bits=x.base.state.bits ∧
    (childrenOutput x pair bits).base.kind=x.base.kind ∧
    (childrenOutput x pair bits).base.extra=x.base.extra ∧
    (childrenOutput x pair bits).base.source=x.base.source ∧
    (childrenOutput x pair bits).base.pos=x.base.pos ∧
    (childrenOutput x pair bits).total=x.total ∧
    (childrenOutput x pair bits).copyCapacity=x.copyCapacity ∧
    (childrenOutput x pair bits).lookupCapacity=x.lookupCapacity := by
  unfold childrenOutput leftOutput
  split
  · unfold rightOutput
    split <;> exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  · exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

def Retains (out x : Children) : Prop :=
  out.base.state.bits=x.base.state.bits ∧ out.base.kind=x.base.kind ∧
  out.base.extra=x.base.extra ∧ out.base.source=x.base.source ∧ out.base.pos=x.base.pos ∧
  out.total=x.total ∧ out.copyCapacity=x.copyCapacity ∧ out.lookupCapacity=x.lookupCapacity

theorem retains_trans (a b c : Children) (h : Retains a b) (k : Retains b c) : Retains a c :=
  ⟨h.1.trans k.1,h.2.1.trans k.2.1,h.2.2.1.trans k.2.2.1,h.2.2.2.1.trans k.2.2.2.1,
    h.2.2.2.2.1.trans k.2.2.2.2.1,h.2.2.2.2.2.1.trans k.2.2.2.2.2.1,
    h.2.2.2.2.2.2.1.trans k.2.2.2.2.2.2.1,h.2.2.2.2.2.2.2.trans k.2.2.2.2.2.2.2⟩

theorem retains_front (x : Children) : Retains (structureFront x) x := by
  unfold Retains structureFront frontOutput
  split <;> exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem retains_zero (x : Children) : Retains ({x with base:=zeroOutput x.base} : Children) x :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem retains_one (x : Children) (child : List Bool) : Retains ({x with base:=oneOutput x.base child} : Children) x := by
  dsimp only [Retains,oneOutput,countClassified,payloadCompared,setValid,setCount,setFlag]
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem structure_retained (x : Children) (bits : List Bool) :
    (structureOutput x bits).base.state.bits=x.base.state.bits ∧
    (structureOutput x bits).base.kind=x.base.kind ∧
    (structureOutput x bits).base.extra=x.base.extra ∧
    (structureOutput x bits).base.source=x.base.source ∧
    (structureOutput x bits).base.pos=x.base.pos ∧
    (structureOutput x bits).total=x.total ∧
    (structureOutput x bits).copyCapacity=x.copyCapacity ∧
    (structureOutput x bits).lookupCapacity=x.lookupCapacity := by
  change Retains (structureOutput x bits) x
  unfold structureOutput
  split
  · split
    · exact retains_trans _ (structureFront x) x (retains_zero (structureFront x)) (retains_front x)
    · split
      · exact retains_trans _ (structureFront x) x (retains_one (structureFront x) (pairWord x.base)) (retains_front x)
      · exact retains_trans _ (structureFront x) x (children_retained (structureFront x) (pairWord x.base) bits) (retains_front x)
  · exact retains_front x

theorem structure_leaf_check (x : Children) (bits word : List Bool) :
    RecoveryRowLeaf.leafWordCheck (structureOutput x bits).base.state (structureOutput x bits).base.extra
      (structureOutput x bits).base.kind word=
    RecoveryRowLeaf.leafWordCheck x.base.state x.base.extra x.base.kind word := by
  have h := structure_retained x bits
  unfold RecoveryRowLeaf.leafWordCheck RecoveryClauseEvaluation.clauseWordCheck
  rw [h.1,h.2.1,h.2.2.1]

theorem structure_run_checked (x : Children) (word bits : List Bool) (rows : List Row) (rest : List Bool)
    (hx : x.Valid word bits) (hw : x.base.code.length=x.base.state.bits.length)
    (hk : x.base.kind.length=x.base.state.bits.length) (hc : x.base.count.length=x.base.state.bits.length)
    (hp : readMany (readRow x.bank.row.width) x.total bits=some (rows,rest))
    (hrows : checkFrom [] rows=true) :
    ∃ r,runFrom structureMachine (structureTime x) (x.cfg structureMachine.start)=some r ∧
      r.final=(structureOutput x bits).cfg r.final.control ∧ r.steps≤ structureTime x ∧
      (structureOutput x bits).Valid word bits ∧
      (structureOutput x bits).base.valid=unpairCheck rows (dataRow x.base) := by
  obtain ⟨r,hr,hf,hs,hv⟩ := structure_run x word bits rows rest hx hw hk hc hp
  exact ⟨r,hr,hf,hs,hv,(structure_answer x bits rows rest hp).trans (check_eq rows (dataRow x.base) hrows)⟩

end NearCubicWires.RepairOrdinary.RecoveryRowStructure
