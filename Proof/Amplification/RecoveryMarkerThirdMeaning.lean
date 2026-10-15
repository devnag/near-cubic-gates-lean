import Proof.Amplification.RecoveryMarkerPrefixMeaning

/-! The optional third clause has exactly the original legacy marker
shape. Its absence retains the prepared zero prefix fields; its presence
supplies the actual saved committed/count words. -/
namespace NearCubicWires.RepairOrdinary.RecoveryMarker
open LocalBitMultitape RecoveryMarkerClause RadixSemantics RecoveryMarkerMetadata
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

abbrev TailWords := Option (List Bool×List Bool)
def tailClauses : TailWords→EncodedCNF
  | none=>[]
  | some (committed,count)=>[[(false,value committed),(true,value count)]]
def installTail (fields : Fields) : TailWords→Fields
  | none=>fields
  | some (committed,count)=>{fields with committed:=frame committed,count:=frame count}
def TailFits (width : Nat) : TailWords→Prop
  | none=>True
  | some (committed,count)=>committed.length=width ∧ count.length=width

theorem third_accepted (x : State) (hx : x.Valid) (ha : (thirdOutput x).inner.present=true) :
    ∃ tail : TailWords,TailFits x.width tail ∧ outerCode x=Encodable.encode (tailClauses tail) ∧
      read (thirdOutput x)=installTail (read x) tail := by
  cases hp : (loaded x).outer.flag
  · have hz : outerCode x=0 := by
      rw [load_flag] at hp
      by_cases hz : outerCode x=0
      · exact hz
      · simp [hz] at hp
    refine ⟨none,True.intro,?_,?_⟩
    · exact hz
    · have ho : thirdOutput x=RecoveryMarkerFlags.answered (loaded x) true := by
        simp only [thirdOutput,hp,Bool.false_eq_true,ite_false]
      rw [ho,read_answered,read_loaded]
      rfl
  · have ho : thirdOutput x=prefixOutput (loaded x) := by simp only [thirdOutput,hp,ite_true]
    rw [ho] at ha ⊢
    obtain ⟨committed,count,hc,hn,hclause,htail,hfields⟩ := prefix_accepted (loaded x) ha
    have hw := loaded_width x hx
    have hcode := load_rebuild x hp
    rw [hclause,htail] at hcode
    refine ⟨some (committed,count),⟨hc.trans hw,hn.trans hw⟩,?_,?_⟩
    · change outerCode x=Encodable.encode [[(false,value committed),(true,value count)]]
      rw [←hcode,Encodable.encode_list_cons]
      rfl
    · rw [hfields,read_loaded]
      rfl

end NearCubicWires.RepairOrdinary.RecoveryMarker
