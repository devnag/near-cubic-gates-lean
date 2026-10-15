import Proof.Amplification.RecoveryRowStructureChildrenGraph

/-! Complete right-child tail of the paired-row checker: copy the actual
retained right key, run the second prior-row lookup, and either reject the
missing child or execute the three-count relation. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRowStructure
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryRowStream RadixSemantics
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
open RepairSource.RecoveryOracle.BalancedCertificate
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def rightFound (x : Children) (key bits : List Bool) := bankOutput (bankKey x key) bits
def rightOutput (x : Children) (key bits : List Bool) :=
  if (rightFound x key bits).bank.found then childrenCounted (rightFound x key bits)
  else childrenRejected (rightFound x key bits)
def rightTime (x : Children) (key : List Bool) := (8*key.length+8)+1+bankTime x+1+(4*x.base.count.length+5)

theorem right_output_valid (x : Children) (key word bits : List Bool) (hx : (rightFound x key bits).Valid word bits) :
    (rightOutput x key bits).Valid word bits := by
  unfold rightOutput
  split <;> exact hx

theorem right_trace (x : Children) (key word bits : List Bool) (rows : List Row) (rest : List Bool)
    (hx : x.Valid word bits) (hw : key.length=x.base.state.bits.length)
    (hsource : x.base.state.fields 0=frame key)
    (hp : readMany (readRow x.bank.row.width) x.total bits=some (rows,rest))
    (hcount : x.base.count.length=x.base.state.bits.length) (hleft : x.base.code.length=x.base.state.bits.length) :
    ∃ n≤rightTime x key,Timed childrenMachine n (childrenCfg x 4) (childrenStop (rightOutput x key bits)) ∧
      (rightOutput x key bits).Valid word bits := by
  obtain ⟨copied,hr0,hf0,_,hv0⟩ := key_copy_run false x key word bits 0 hx hw (by change x.base.state.fields 0=ZeroPadding.pad 0 (frame key); simpa using hsource)
  obtain ⟨n0,hb0,h0⟩ := children_call 4 5 x (bankKey x key) (8*key.length+8) copied hr0 hf0 (by rfl)
  obtain ⟨looked,hr1,hf1,_,hv1,_,_⟩ := bank_run (bankKey x key) word bits rows rest hv0 hp
  cases ha : (rightFound x key bits).bank.found
  · obtain ⟨n1,hb1,h1⟩ := children_call 5 7 (bankKey x key) (rightFound x key bits) (bankTime x) looked hr1 hf1 (by
      rw [hf1]
      change (if (rightFound x key bits).bank.found then some (6 : Fin 8) else some 7)=some 7
      rw [ha]; rfl)
    obtain ⟨n2,hb2,h2⟩ := children_reject_tail (rightFound x key bits)
    refine ⟨n0+n1+n2,by unfold rightTime; omega,?_,?_⟩
    · simpa only [rightOutput,ha,Bool.false_eq_true,if_false] using (h0.trans h1).trans h2
    · exact right_output_valid x key word bits hv1
  · obtain ⟨n1,hb1,h1⟩ := children_call 5 6 (bankKey x key) (rightFound x key bits) (bankTime x) looked hr1 hf1 (by
      rw [hf1]
      change (if (rightFound x key bits).bank.found then some (6 : Fin 8) else some 7)=some 6
      rw [ha]; rfl)
    obtain ⟨n2,hb2,h2⟩ := children_count_tail (rightFound x key bits) word bits hv1 hcount hleft
    refine ⟨n0+n1+n2,by change n2≤4*x.base.count.length+5 at hb2; unfold rightTime; omega,?_,?_⟩
    · simpa only [rightOutput,ha,if_true] using (h0.trans h1).trans h2
    · exact right_output_valid x key word bits hv1

theorem lookupOr_option (rows : List Row) (key old : Nat) :
    RecoveryRowLookupTable.lookupOr rows key old=(RecoveryRowLookupTable.lookupCount rows key).getD old := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
    by_cases he : key=row.code <;> simp [RecoveryRowLookupTable.lookupOr,RecoveryRowLookupTable.lookupCount,he,ih]

theorem lookupFound_option (rows : List Row) (key : Nat) :
    rows.any (fun row=>decide (key=row.code))=(RecoveryRowLookupTable.lookupCount rows key).isSome := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
    by_cases he : key=row.code <;> simp [RecoveryRowLookupTable.lookupCount,he,ih]

end NearCubicWires.RepairOrdinary.RecoveryRowStructure
