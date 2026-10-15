import Proof.Amplification.RecoveryAssignmentCounterErase
import Proof.Amplification.RecoveryBoundedWordPrefix

/-! Bounded lookahead of the serialized shared table. Copying this prefix
preserves the parsed table on every word, including malformed witnesses. -/
namespace NearCubicWires.RepairSource.RecoveryOracle.CompactCertificate.Serialization
open RepairOrdinary RepairOrdinary.RecoveryValuationStream RepairOrdinary.RecoveryValuationTable
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem readCount_take (cap limit : Nat) (word : List Bool) (hl : cap+1≤limit) :
    readCount cap (word.take limit)=
      (readCount cap word).map (fun pair=>(pair.1,pair.2.take (limit-pair.1-1))) := by
  induction cap generalizing limit word with
  | zero =>
    cases limit with
    | zero => omega
    | succ limit => cases word with
      | nil => rfl
      | cons bit rest => cases bit <;> rfl
  | succ cap ih =>
    cases limit with
    | zero => omega
    | succ limit =>
      cases word with
      | nil => rfl
      | cons bit rest =>
        cases bit with
        | false => rfl
        | true =>
          simp only [List.take_succ_cons,readCount]
          rw [ih limit rest (by omega)]
          cases h : readCount cap rest with
          | none => rfl
          | some pair =>
            rcases pair with ⟨count,tail⟩
            simp only [Option.map_some]
            have he : limit-count-1=limit+1-(count+1)-1 := by omega
            rw [he]

theorem readEntry_take (width limit : Nat) (word : List Bool) (hl : width+1≤limit) :
    readEntry width (word.take limit)=
      (readEntry width word).map (fun pair=>(pair.1,pair.2.take (limit-(width+1)))) := by
  by_cases hw : width<word.length
  · have htake : width<(word.take limit).length := by simp only [List.length_take]; omega
    rw [readEntry_full width _ htake,readEntry_full width word hw]
    simp only [Option.map_some,List.take_take,show min width limit=width by omega]
    have hi : (word.take limit)[width]?=word[width]? := by simp [show width<limit by omega]
    rw [hi,List.drop_take]
  · have hshort : (word.take limit).length≤width := by simp only [List.length_take]; omega
    rw [readEntry_short width _ (by omega),readEntry_short width word (by omega)]
    rfl

theorem readMany_take (width count limit : Nat) (word : List Bool) (hl : count*(width+1)≤limit) :
    readMany (readEntry width) count (word.take limit)=
      (readMany (readEntry width) count word).map
        (fun pair=>(pair.1,pair.2.take (limit-count*(width+1)))) := by
  induction count generalizing limit word with
  | zero => simp [readMany]
  | succ count ih =>
    have hwidth : width+1≤limit := by nlinarith
    cases hp : readEntry width word with
    | none =>
      have ht : readEntry width (word.take limit)=none := by rw [readEntry_take width limit word hwidth,hp]; rfl
      rw [readMany_head_none _ count _ ht,readMany_head_none _ count _ hp]
      rfl
    | some pair =>
      rcases pair with ⟨entry,tail⟩
      have ht : readEntry width (word.take limit)=some (entry,tail.take (limit-(width+1))) := by
        rw [readEntry_take width limit word hwidth,hp]; rfl
      rw [readMany_head_some _ count _ _ _ ht,readMany_head_some _ count _ _ _ hp]
      rw [ih (limit-(width+1)) tail (by
        have he : (count+1)*(width+1)=count*(width+1)+(width+1) := by ring
        omega)]
      have he : limit-(width+1)-count*(width+1)=limit-(count+1)*(width+1) := by
        have hmul : (count+1)*(width+1)=count*(width+1)+(width+1) := by ring
        rw [hmul]
        omega
      rw [he]
      cases readMany (readEntry width) count tail with
      | none => rfl
      | some pair => cases pair; rfl

theorem readList_take_table (width cap limit : Nat) (word : List Bool)
    (hl : cap*(width+2)+1≤limit) :
    (readList cap (readEntry width) (word.take limit)).map Prod.fst=
      (readList cap (readEntry width) word).map Prod.fst := by
  have hc : cap+1≤limit := by nlinarith
  cases hp : readCount cap word with
  | none =>
    have ht : readCount cap (word.take limit)=none := by rw [readCount_take cap limit word hc,hp]; rfl
    rw [RecoveryValuationCount.readList_count_none width cap _ ht,
      RecoveryValuationCount.readList_count_none width cap _ hp]
  | some pair =>
    rcases pair with ⟨count,tail⟩
    have hcount := (RecoveryCertificateCount.readCount_some cap count word tail hp).1
    have ht : readCount cap (word.take limit)=some (count,tail.take (limit-count-1)) := by
      rw [readCount_take cap limit word hc,hp]; rfl
    rw [RecoveryValuationCount.readList_count_some width cap count _ _ ht,
      RecoveryValuationCount.readList_count_some width cap count _ _ hp]
    have hmul := Nat.mul_le_mul_right (width+2) hcount
    rw [readMany_take width count (limit-count-1) tail (by
      have hsum : count*(width+1)+count+1≤limit := by nlinarith
      omega)]
    cases readMany (readEntry width) count tail with
    | none => rfl
    | some pair => cases pair; rfl

end NearCubicWires.RepairSource.RecoveryOracle.CompactCertificate.Serialization
