import Proof.Amplification.RecoveryCertificateBounds

/-! Flat bounded parsing primitives for the selected NP certificate. All list
counts are explicitly capped; scalar fields have one fixed original width.
This is the concrete bit codec, not a claim of ordinary execution. -/
namespace NearCubicWires.RepairSource.RecoveryOracle.CompactCertificate.Serialization
open RepairOrdinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

abbrev Parser (α : Type) := List Bool → Option (α×List Bool)
def readField (width : Nat) : Parser Nat := fun bits =>
  if width≤bits.length then some (RadixSemantics.value (bits.take width),bits.drop width) else none
def readBit : Parser Bool
  | [] => none
  | bit::rest => some (bit,rest)
def readCount : Nat → Parser Nat
  | _,[] => none
  | _,false::rest => some (0,rest)
  | 0,true::_ => none
  | limit+1,true::rest => (readCount limit rest).map fun pair => (pair.1+1,pair.2)
def readMany {α : Type} (read : Parser α) : Nat → Parser (List α)
  | 0,bits => some ([],bits)
  | count+1,bits => do
      let (item,rest) ← read bits
      let (items,tail) ← readMany read count rest
      some (item::items,tail)
def readList {α : Type} (limit : Nat) (read : Parser α) : Parser (List α) := fun bits => do
  let (count,rest) ← readCount limit bits
  readMany read count rest
def packList {α : Type} (pack : α → List Bool) (values : List α) : List Bool :=
  List.replicate values.length true++[false]++values.flatMap pack

theorem readField_pack (width value : Nat) (hv : value<2^width) (suffix : List Bool) :
    readField width (SignedSortKey.binary width value++suffix)=some (value,suffix) := by
  have hn : (SignedSortKey.binary width value).length=width := SignedSortKey.binary_length width value
  have hle : width≤(SignedSortKey.binary width value++suffix).length := by simp
  rw [readField,if_pos hle]
  have ht : (SignedSortKey.binary width value++suffix).take width=SignedSortKey.binary width value := by
    conv_lhs => arg 1; rw [← hn]
    exact List.take_left
  have hd : (SignedSortKey.binary width value++suffix).drop width=suffix := by
    conv_lhs => arg 1; rw [← hn]
    exact List.drop_left
  rw [ht,hd,SignedSortKey.binary_value width value hv]

theorem readCount_pack (limit count : Nat) (hc : count≤limit) (suffix : List Bool) :
    readCount limit (List.replicate count true++false::suffix)=some (count,suffix) := by
  induction count generalizing limit with
  | zero => simp [readCount]
  | succ count ih =>
    cases limit with
    | zero => omega
    | succ limit =>
      simp only [List.replicate_succ,List.cons_append,readCount,ih limit (by omega),Option.map_some]

theorem readMany_pack {α : Type} (read : Parser α) (pack : α → List Bool)
    (values : List α) (hp : ∀ item∈values,∀ suffix,read (pack item++suffix)=some (item,suffix))
    (suffix : List Bool) : readMany read values.length (values.flatMap pack++suffix)=some (values,suffix) := by
  induction values with
  | nil => rfl
  | cons item rest ih =>
    have hh := hp item (by simp) (rest.flatMap pack++suffix)
    have ht := ih (by intro i hi; exact hp i (by simp [hi]))
    simp only [List.length_cons,List.flatMap_cons,List.append_assoc,readMany,hh]
    change (do let (items,tail) ← readMany read rest.length (rest.flatMap pack++suffix)
               some (item::items,tail))=_
    rw [ht]
    rfl

theorem readList_pack {α : Type} (limit : Nat) (read : Parser α) (pack : α → List Bool)
    (values : List α) (hlen : values.length≤limit)
    (hp : ∀ item∈values,∀ suffix,read (pack item++suffix)=some (item,suffix))
    (suffix : List Bool) : readList limit read (packList pack values++suffix)=some (values,suffix) := by
  unfold readList packList
  rw [List.append_assoc,List.append_assoc]
  change (do
    let (count,rest) ← readCount limit (List.replicate values.length true++false::(values.flatMap pack++suffix))
    readMany read count rest)=_
  rw [readCount_pack limit values.length hlen]
  exact readMany_pack read pack values hp suffix

theorem packList_length {α : Type} (pack : α → List Bool) (values : List α) (width : Nat)
    (hp : ∀ item∈values,(pack item).length=width) :
    (packList pack values).length=(width+1)*values.length+1 := by
  have h : (values.flatMap pack).length=width*values.length := by
    induction values with
    | nil => simp
    | cons item rest ih =>
      have hh := hp item (by simp)
      have ht := ih (by intro i hi; exact hp i (by simp [hi]))
      simp only [List.flatMap_cons,List.length_append,hh,ht,List.length_cons]
      ring
  simp only [packList,List.length_append,List.length_replicate,List.length_singleton,h]
  ring

end NearCubicWires.RepairSource.RecoveryOracle.CompactCertificate.Serialization
