import Proof.Amplification.RecoveryMarkerLayout

/-! The exact selected compact-checker input, with one shared valuation and
the two actual table suffixes. Its three lookup workspaces use the existing
quadratic erase capacity; no larger true driver is allocated. -/
namespace NearCubicWires.RepairOrdinary.RecoveryColdCompact
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryColdView
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def data (bits word table : List Bool) : RecoveryRowStream.Data :=
  ⟨RecoveryColdSAT.clause bits,RecoveryColdSAT.valuation bits word,
    [],[],[],fun _=>false,frame table,0,false⟩
def lookup (bits table : List Bool) : RecoveryRowLookupStream.Data :=
  ⟨⟨frame table,0,width bits,fun _=>[],false⟩,
    RecoveryColdHeader.zeroWord bits,RecoveryColdHeader.zeroWord bits,
    false,false,false,2*width bits+1,4*width bits+3⟩
def children (bits word table : List Bool) : RecoveryRowStructure.Children :=
  ⟨data bits word table,lookup bits table,2*width bits+1,0,erase bits⟩
def state (bits word innerBits outerBits : List Bool) (innerTotal outerTotal : Nat) :
    RecoveryNestedTable.State :=
  ⟨children bits word innerBits,innerTotal,
    ⟨⟨children bits word outerBits,lookup bits innerBits,innerTotal,erase bits⟩,
      outerTotal,RecoveryColdHeader.zeroWord bits⟩⟩

theorem lookup_capacity (bits : List Bool) :
    limit bits*(RecoveryRowLookupStream.budget (width bits)+3)+5≤erase bits := by
  have hw : limit bits≤3*width bits := by
    change 3*(max 1 bits.length+1)≤3*(max 1 bits.length+2)
    omega
  have hmul := Nat.mul_le_mul_right (32*width bits+53) hw
  change limit bits*(32*width bits+53)+5≤8192*(width bits+1)^2
  nlinarith

theorem data_valid (bits word table : List Bool) : (data bits word table).Valid word :=
  ⟨(RecoveryColdSAT.valid bits word).1,(RecoveryColdSAT.valid bits word).2.1,
    Nat.zero_le _,Nat.zero_le _,Nat.zero_le _⟩

theorem lookup_valid (bits table : List Bool) : (lookup bits table).Valid := by
  exact ⟨(fun _=>Nat.zero_le _),RecoveryColdHeader.zero_length bits,
    (RecoveryColdHeader.zero_length bits).le,Nat.le_refl _,Nat.le_refl _⟩

theorem lookup_inv (bits table : List Bool) :
    RecoveryRowLookupTable.Inv (width bits) ⟨lookup bits table,table⟩ :=
  ⟨lookup_valid bits table,rfl,[],rfl,rfl⟩

theorem children_valid (bits word table : List Bool) :
    (children bits word table).Valid word table := by
  have hcap := lookup_capacity bits
  have hw : (RecoveryColdHeader.zeroWord bits).length=width bits := RecoveryColdHeader.zero_length bits
  refine ⟨data_valid bits word table,?_,rfl,RecoveryColdHeader.zero_length bits,?_,?_⟩
  · change RecoveryRowLookupTable.Inv (RecoveryColdHeader.zeroWord bits).length
      ⟨lookup bits table,table⟩
    rw [hw]
    exact lookup_inv bits table
  · change 2*(RecoveryColdHeader.zeroWord bits).length+1≤2*width bits+1
    rw [hw]
  · change 0*(RecoveryRowLookupStream.budget (width bits)+3)+5≤erase bits
    omega

theorem prepared (bits word innerBits outerBits : List Bool) (innerTotal outerTotal : Nat)
    (hi : innerTotal≤limit bits) (ho : outerTotal≤limit bits) :
    RecoveryNestedTable.Prepared (state bits word innerBits outerBits innerTotal outerTotal)
      (limit bits) word innerBits outerBits [] [] := by
  have hw : (RecoveryColdHeader.zeroWord bits).length=width bits := RecoveryColdHeader.zero_length bits
  have hc := lookup_capacity bits
  refine ⟨children_valid bits word innerBits,⟨?_,rfl⟩,rfl,rfl,hi,ho,rfl,rfl,rfl,rfl,rfl,rfl,?_,?_⟩
  · refine ⟨children_valid bits word outerBits,?_⟩
    refine ⟨data_valid bits word outerBits,?_,rfl,hw,?_,?_⟩
    · change RecoveryRowLookupTable.Inv (RecoveryColdHeader.zeroWord bits).length
        ⟨lookup bits innerBits,innerBits⟩
      rw [hw]
      exact lookup_inv bits innerBits
    · change 2*(RecoveryColdHeader.zeroWord bits).length+1≤2*width bits+1
      rw [hw]
    · change innerTotal*(RecoveryRowLookupStream.budget (width bits)+3)+5≤erase bits
      exact (Nat.add_le_add_right (Nat.mul_le_mul_right _ hi) 5).trans hc
  all_goals
    change limit bits*(RecoveryRowLookupStream.budget (RecoveryColdHeader.zeroWord bits).length+3)+5≤erase bits
    rw [hw]
    exact hc

end NearCubicWires.RepairOrdinary.RecoveryColdCompact
