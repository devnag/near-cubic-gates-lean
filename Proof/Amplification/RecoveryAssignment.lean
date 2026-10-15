import Proof.Amplification.RecoveryAssignmentTable

/-! Complete physical finite-valuation assignment lookup. The same bounded
witness table is parsed, malformed counts/rows reject, and the binary prefix
selector consumes its actual fallback result. Every call return is paid. -/
namespace NearCubicWires.RepairOrdinary.RecoveryAssignment
open LocalBitMultitape RecoveryExecution RecoveryRootRound RadixSemantics RecoveryValuationStream
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
open RepairSource.RecoveryOracle RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def sizes : Fin 2→Nat := ![Fintype.card (RecoveryCalls.Control RecoveryValuationCount.graphSizes),
  Fintype.card (RecoveryCalls.Control RecoveryPrefixAssignment.sizes)]
noncomputable def programs : (j : Fin 2) → Machine 14 (sizes j)
  | ⟨0,_⟩=>tableMachine
  | ⟨1,_⟩=>selectorMachine
  | ⟨n+2,h⟩=>False.elim (by omega)
def next (j : Fin 2) (_ : Fin (sizes j)) (bits : Fin 14→Bool) : Option (Fin 2) :=
  if j.val=0 then if bits 7 then some 1 else none else none
noncomputable def machine := RecoveryCalls.machine sizes programs 0 next

def cost (d : Data) (cap : Nat) (binaryCount committed : List Bool) (guard : Bool) : Nat :=
  RecoveryValuationCount.limit d.width cap+
    RecoveryPrefixAssignment.cost (prefixData d binaryCount committed guard)+2

theorem assignment_run (d : Data) (pre word : List Bool) (cap : Nat)
    (binaryCount committed : List Bool) (guard : Bool)
    (hs : d.source=pre++frame word) (hp : d.pos=pre.length)
    (hi : d.index.length=d.width) (hb : d.row.length≤2*(d.width+1)+1)
    (hw : binaryCount.length=d.index.length) (hc : 2*binaryCount.length+3≤d.capacity)
    (hbit : RecoveryCommittedBit.rawCost d.index committed≤d.capacity)
    (hfound : d.found=false) (hvalue : d.value=false) :
    ∃ r,runFrom machine (cost d cap binaryCount committed guard)
        (cfg d 0 cap binaryCount committed guard machine.start)=some r ∧
      r.steps≤cost d cap binaryCount committed guard ∧ r.final.heads 7=0 ∧
      r.final.tapes 7=[(readList cap (readEntry d.width) word).isSome] ∧
      ∀ table tail,readList cap (readEntry d.width) word=some (table,tail) →
        r.final.heads 5=0 ∧ r.final.tapes 5=
          [FiniteValuation.assignment (value committed) (value binaryCount) table (value d.index)] := by
  obtain ⟨r0,hr0,_,hh0,hv0,hout0⟩ := table_run d pre word cap binaryCount committed guard
    hs hp hi hb (by omega) hfound hvalue
  cases hparse : readList cap (readEntry d.width) word with
  | none =>
    obtain ⟨n0,hn0,h0⟩ := stop_receipt sizes programs 0 next 0 _ _ r0 hr0 (by
      simp [next,Configuration.scanned,hh0,hv0,hparse,readTapeBit,List.getD])
    change Timed machine n0 (cfg d 0 cap binaryCount committed guard machine.start)
      (RecoveryCalls.stopped sizes r0.final.heads r0.final.tapes) at h0
    obtain ⟨r,hr,hf,ht⟩ := h0.run (by simp [RecoveryCalls.machine,RecoveryCalls.stopped,machine])
    have hn : n0≤cost d cap binaryCount committed guard := by unfold cost; omega
    have hm := runFrom_moreFuel machine n0 (cost d cap binaryCount committed guard-n0) _ r hr
    rw [Nat.add_sub_of_le hn] at hm
    refine ⟨r,hm,ht.le.trans hn,?_,?_,?_⟩
    · simpa only [hf,RecoveryCalls.stopped] using hh0
    · simpa only [hf,RecoveryCalls.stopped,hparse] using hv0
    · intro table tail he
      contradiction
  | some pair =>
    rcases pair with ⟨table,tail⟩
    obtain ⟨count,out,_,_,hindex,_,hcapacity,_,hvalid,hlookup,hout⟩ := hout0 table tail hparse
    obtain ⟨n0,hn0,h0⟩ := call_receipt sizes programs 0 next 0 1 _ _ r0 hr0 (by
      simp [next,Configuration.scanned,hh0,hv0,hparse,readTapeBit,List.getD])
    rw [hout] at h0
    change Timed machine n0 (cfg d 0 cap binaryCount committed guard machine.start)
      (cfg out count cap binaryCount committed guard (RecoveryCalls.code sizes 1 selectorMachine.start)) at h0
    obtain ⟨r1,hr1,_,hh5,hv5,hh7,hv7⟩ := selector_run out count cap binaryCount committed guard
      (by rw [hindex]; exact hw) (by rw [hcapacity]; exact hc)
      (by rw [hindex,hcapacity]; exact hbit)
    obtain ⟨n1,hn1,h1⟩ := stop_receipt sizes programs 0 next 1 _ _ r1 hr1 (by rfl)
    change Timed machine n1
      (cfg out count cap binaryCount committed guard (RecoveryCalls.code sizes 1 selectorMachine.start))
      (RecoveryCalls.stopped sizes r1.final.heads r1.final.tapes) at h1
    have hall := h0.trans h1
    have hn : n0+n1≤cost d cap binaryCount committed guard := by
      have he : RecoveryPrefixAssignment.cost (prefixData out binaryCount committed guard)=
          RecoveryPrefixAssignment.cost (prefixData d binaryCount committed guard) := by
        simp [RecoveryPrefixAssignment.cost,prefixData,hindex]
      rw [he] at hn1
      unfold cost
      omega
    obtain ⟨r,hr,hf,ht⟩ := hall.run (by simp [RecoveryCalls.machine,RecoveryCalls.stopped,machine])
    have hm := runFrom_moreFuel machine (n0+n1)
      (cost d cap binaryCount committed guard-(n0+n1)) _ r hr
    rw [Nat.add_sub_of_le hn] at hm
    refine ⟨r,hm,ht.le.trans hn,?_,?_,?_⟩
    · simpa only [hf,RecoveryCalls.stopped] using hh7
    · simpa only [hf,RecoveryCalls.stopped,hvalid,Option.isSome_some] using hv7
    · intro table' tail' he
      have hpairs : (table,tail)=(table',tail') := Option.some.inj he
      cases hpairs
      refine ⟨?_,?_⟩
      · simpa only [hf,RecoveryCalls.stopped] using hh5
      · simpa only [hf,RecoveryCalls.stopped,hindex,hlookup,FiniteValuation.assignment] using hv5

end NearCubicWires.RepairOrdinary.RecoveryAssignment
