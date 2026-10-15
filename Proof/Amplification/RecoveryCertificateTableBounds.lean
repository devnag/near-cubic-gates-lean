import Proof.Amplification.RecoveryAllCodeCertificate

/-! Bounds for the actual flat table certificate, including the shared inner
table of nested payloads. Empty chunks pay one row each. -/
namespace NearCubicWires.RepairSource.RecoveryOracle.CompactCertificate
open CanonicalBinary BalancedCNFSATEncoding BalancedCertificate
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def RowFits (code width : Nat) (row : Row) : Prop :=
  row.code≤code ∧ row.payload≤code ∧ row.count≤width ∧ row.kind≤2

theorem balanced_member_le (values : List Nat) (value : Nat) (hm : value∈values) :
    value≤encodeBalancedList values := by
  induction values using encodeBalancedList.induct with
  | case1 => simp at hm
  | case2 item =>
    have he := List.mem_singleton.mp hm
    subst value
    simpa only [encodeBalancedList] using Nat.right_le_pair 1 item
  | case3 first second rest values leftLength left right ihleft ihright =>
    have happ : left++right=values := by simp [left,right]
    have hm' : value∈left++right := by rw [happ]; exact hm
    rw [encodeBalancedList.eq_def]
    change value≤Nat.pair 2 (Nat.pair (encodeBalancedList left) (encodeBalancedList right))
    rcases List.mem_append.mp hm' with hl|hr
    · exact (ihleft hl).trans ((Nat.left_le_pair _ _).trans (Nat.right_le_pair _ _))
    · exact (ihright hr).trans ((Nat.right_le_pair _ _).trans (Nat.right_le_pair _ _))

theorem decoded_member_le {code : Nat} {values : List Nat} (hd : decodeBalancedList code=some values)
    (value : Nat) (hm : value∈values) : value≤code :=
  (balanced_member_le values value hm).trans_eq (encodeBalancedList_of_decode hd)

theorem bounded_rootCheck (P : Nat → Bool) {code : Nat} {values : List Nat}
    (hd : decodeBalancedList code=some values) (hp : values.all P=true) :
    ∃ rows,rootCheck P rows code=true ∧ rows.length≤2*natBitLength code+1 ∧
      ∀ row∈rows,RowFits code (natBitLength code) row := by
  obtain ⟨w⟩ := exists_witness values
  have he : w.root.code=code := w.rootCode.trans (encodeBalancedList_of_decode hd)
  have hn := decoded_balanced_length hd
  refine ⟨w.rows,?_,by have hl:=w.lengthBound; omega,?_⟩
  · rw [← encodeBalancedList_of_decode hd]
    exact witness_rootCheck values w P hp
  · intro row hm
    exact ⟨(w.codeBound row hm).trans_eq he,(w.payloadBound row hm).trans_eq he,
      (w.countBound row hm).trans hn,w.kindBound row hm⟩

theorem bounded_chunk_tables (P : Nat → Bool) (chunks : List Nat)
    (hh : ∀ chunk∈chunks,∃ codes,decodeBalancedList chunk=some codes ∧ codes.all P=true) :
    ∃ rows,checkFrom [] rows=true ∧ rows.all (leafCheck P)=true ∧ chunks.all (hasRoot rows)=true ∧
      rows.length≤2*(chunks.map natBitLength).sum+chunks.length ∧
      ∀ row∈rows,∃ chunk∈chunks,RowFits chunk (natBitLength chunk) row := by
  induction chunks with
  | nil => exact ⟨[],rfl,rfl,rfl,by simp,by simp⟩
  | cons chunk rest ih =>
    obtain ⟨codes,hd,hp⟩ := hh chunk (by simp)
    obtain ⟨head,hhc,hsize,hfields⟩ := bounded_rootCheck P hd hp
    simp only [rootCheck,Bool.and_eq_true] at hhc
    obtain ⟨tail,ht,hl,hr,hbound,htfields⟩ := ih (by intro c hc; exact hh c (by simp [hc]))
    refine ⟨head++tail,?_,by simp [hhc.1.2,hl],?_,?_,?_⟩
    · rw [check_append]
      simp only [List.nil_append,hhc.1.1,Bool.true_and]
      exact check_mono [] head tail (by simp) ht
    · rw [List.all_cons,Bool.and_eq_true]
      constructor
      · simp only [hasRoot,List.any_append,hhc.2,Bool.true_or]
      · rw [List.all_eq_true] at hr ⊢
        intro c hc
        simp only [hasRoot,List.any_append]
        rw [show tail.any (fun row => row.code==c)=true from hr c hc]
        exact Bool.or_true _
    · simp only [List.length_append,List.map_cons,List.sum_cons,List.length_cons]
      omega
    · intro row hm
      rcases List.mem_append.mp hm with hm|hm
      · exact ⟨chunk,by simp,hfields row hm⟩
      · obtain ⟨c,hc,hf⟩ := htfields row hm
        exact ⟨c,by simp [hc],hf⟩

theorem bounded_nestedCheck (P : Nat → Bool) {payload : Nat} {codes : List Nat}
    (hd : decodeNestedBalancedCNFPayload payload=some codes) (hp : codes.all P=true) :
    ∃ inner outer,nestedCheck P inner outer payload=true ∧
      inner.length≤3*natBitLength payload ∧ outer.length≤2*natBitLength payload+1 ∧
      ∀ row∈inner++outer,RowFits payload (natBitLength payload) row := by
  cases hh : decodeBalancedList payload with
  | none => simp [decodeNestedBalancedCNFPayload,hh] at hd
  | some chunks =>
    have hchunks : decodeBalancedClauseChunks chunks=some codes := by
      simpa [decodeNestedBalancedCNFPayload,hh] using hd
    obtain ⟨inner,hi,hl,hr,hs,hf⟩ :=
      bounded_chunk_tables P chunks ((chunks_predicate_iff P chunks).mpr ⟨codes,hchunks,hp⟩)
    obtain ⟨outer,ho,hos,hof⟩ := bounded_rootCheck (hasRoot inner) hh hr
    have hb := decoded_balanced_atoms_bits hh
    have hn := decoded_balanced_length hh
    refine ⟨inner,outer,by simp [nestedCheck,hi,hl,ho],by omega,hos,?_⟩
    intro row hm
    rcases List.mem_append.mp hm with hm|hm
    · obtain ⟨chunk,hc,hfields⟩ := hf row hm
      have hc' := decoded_member_le hh chunk hc
      exact ⟨hfields.1.trans hc',hfields.2.1.trans hc',
        hfields.2.2.1.trans (RawSyntaxCertificate.width_mono hc'),hfields.2.2.2⟩
    · exact hof row hm

end NearCubicWires.RepairSource.RecoveryOracle.CompactCertificate
