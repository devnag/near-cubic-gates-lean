import Proof.Amplification.RecoveryMarkerAtomAccepted

/-! Exact original-code equations for actual marker clause loads and
accepted literal shapes. The zero case is interpreted through its flag,
never through the wrapped predecessor word. -/
namespace NearCubicWires.RepairOrdinary.RecoveryMarker
open LocalBitMultitape RecoveryMarkerClause RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def outerCode (x : State) := value x.outer.bits

theorem load_flag (x : State) : (loaded x).outer.flag=decide (outerCode x≠0) := by
  unfold loaded
  split
  · exact RecoveryThreeCellReader.after_flag x.outer 0
  · exact RecoveryThreeCellReader.after_flag x.outer 0

theorem load_codes (x : State) (hp : (loaded x).outer.flag=true) :
    RecoveryMarkerAtom.inputCode (loaded x)=(Nat.unpair (outerCode x-1)).1 ∧
      outerCode (loaded x)=(Nat.unpair (outerCode x-1)).2 := by
  have hz : outerCode x≠0 := by rw [load_flag,decide_eq_true_eq] at hp; exact hp
  change value x.outer.bits≠0 at hz
  rw [loaded,if_neg hz]
  constructor
  · exact RecoveryCellStore.head_value x.outer.bits hz
  · exact RecoveryThreeCellReader.after_value x.outer 0 hz

theorem load_rebuild (x : State) (hp : (loaded x).outer.flag=true) :
    Nat.pair (RecoveryMarkerAtom.inputCode (loaded x)) (outerCode (loaded x))+1=outerCode x := by
  obtain ⟨hh,ht⟩ := load_codes x hp
  rw [hh,ht,Nat.pair_unpair]
  have hz : outerCode x≠0 := by rw [load_flag,decide_eq_true_eq] at hp; exact hp
  exact Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hz)

theorem empty_flag (x : State) : (emptyStep x).inner.data.flag=decide (RecoveryMarkerAtom.inputCode x≠0) :=
  RecoveryThreeCellReader.after_flag x.inner.data 0

theorem encode_tag (tag index : Nat) (ht : tag≤1) :
    Encodable.encode (decide (tag≠0),index)=Nat.pair tag index := by
  cases tag with
  | zero=>rfl
  | succ tag=>
    have hz : tag=0 := by omega
    subst tag
    rfl

theorem atom_singleton (which : Fin 3) (x : State) (ha : RecoveryMarkerAtom.answer which x=true)
    (hm : which.val≠1) :
    RecoveryMarkerAtom.inputCode x=Encodable.encode
      [(decide (RecoveryMarkerAtom.literalTag x≠0),RecoveryMarkerAtom.literalValue x)] := by
  have hs := RecoveryMarkerAtom.accepted_shape which x ha
  have hr := RecoveryMarkerAtom.code_rebuild x hs.1
  rw [hs.2.2.2 hm] at hr
  rw [←hr,Encodable.encode_list_cons]
  rw [encode_tag _ _ hs.2.1]
  rfl

theorem committed_tag (x : State) (ha : RecoveryMarkerAtom.answer 1 x=true) : RecoveryMarkerAtom.literalTag x=0 := by
  have hs := RecoveryMarkerAtom.accepted_shape 1 x ha
  have h := hs.2.2.1
  change (!(decide (RecoveryMarkerAtom.literalTag x≠0)))=true at h
  by_cases hz : RecoveryMarkerAtom.literalTag x=0
  · exact hz
  · simp [hz] at h

theorem count_tag (x : State) (ha : RecoveryMarkerAtom.answer 2 x=true) : RecoveryMarkerAtom.literalTag x=1 := by
  have hs := RecoveryMarkerAtom.accepted_shape 2 x ha
  have hz : RecoveryMarkerAtom.literalTag x≠0 := by
    have h := hs.2.2.1
    change decide (RecoveryMarkerAtom.literalTag x≠0)=true at h
    exact of_decide_eq_true h
  omega

theorem prefix_clause (x : State) (h1 : RecoveryMarkerAtom.answer 1 x=true)
    (h2 : RecoveryMarkerAtom.answer 2 (RecoveryMarkerAtom.output 1 x)=true) :
    RecoveryMarkerAtom.inputCode x=Encodable.encode
      [(false,RecoveryMarkerAtom.literalValue x),
        (true,RecoveryMarkerAtom.literalValue (RecoveryMarkerAtom.output 1 x))] := by
  have hs := RecoveryMarkerAtom.accepted_shape 1 x h1
  have hr := RecoveryMarkerAtom.code_rebuild x hs.1
  have ht := RecoveryMarkerAtom.committed_tail x h1
  have hn := atom_singleton 2 (RecoveryMarkerAtom.output 1 x) h2 (by decide)
  rw [count_tag _ h2] at hn
  rw [committed_tag x h1,←ht,hn] at hr
  rw [←hr,Encodable.encode_list_cons]
  rfl

end NearCubicWires.RepairOrdinary.RecoveryMarker
