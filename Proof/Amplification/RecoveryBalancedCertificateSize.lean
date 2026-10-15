import Proof.Amplification.RecoveryBalancedCertificate

/-! Completeness and encoded-length bounds for the prior-row certificate.
Every canonical list has a table of at most twice its leaf count plus one;
all code and payload fields are bounded by the enclosing code. -/
namespace NearCubicWires.RepairSource.RecoveryOracle.BalancedCertificate
open CanonicalBinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

structure Witness (values : List Nat) where
  rows : List Row
  root : Row
  member : root∈rows
  checked : checkFrom [] rows=true
  rootCode : root.code=encodeBalancedList values
  rootCount : root.count=values.length
  lengthBound : rows.length≤2*values.length+1
  positiveBound : 0<values.length → rows.length+1≤2*values.length
  codeBound : ∀ row∈rows,row.code≤root.code
  payloadBound : ∀ row∈rows,row.payload≤root.code
  countBound : ∀ row∈rows,row.count≤values.length
  kindBound : ∀ row∈rows,row.kind≤2
  leafSupport : ∀ row∈rows,row.kind=1 → row.payload∈values

theorem exists_witness (values : List Nat) : Nonempty (Witness values) := by
  induction values using encodeBalancedList.induct with
  | case1 =>
    let root : Row := ⟨0,0,0,0⟩
    refine ⟨⟨[root],root,by simp,?_,?_,rfl,by simp,by simp,?_,?_,?_,?_,?_⟩⟩
    · rfl
    · simp [root,encodeBalancedList]
    all_goals intro row hr; simp only [List.mem_singleton] at hr; subst row; decide
  | case2 value =>
    let root : Row := ⟨1,Nat.pair 1 value,1,value⟩
    refine ⟨⟨[root],root,by simp,?_,?_,rfl,by simp,by simp,?_,?_,?_,?_,?_⟩⟩
    · simp [checkFrom,unpairCheck,root]
    · simp [root,encodeBalancedList]
    · intro row hr; simp only [List.mem_singleton] at hr; subst row; exact Nat.le_refl _
    · intro row hr; simp only [List.mem_singleton] at hr; subst row; exact Nat.right_le_pair _ _
    · intro row hr; simp only [List.mem_singleton] at hr; subst row; exact Nat.le_refl _
    · intro row hr; simp only [List.mem_singleton] at hr; subst row; change 1≤2; omega
    · intro row hr _; simp only [List.mem_singleton] at hr; subst row; simp [root]
  | case3 first second rest values leftLength left right ihleft ihright =>
    obtain ⟨lw⟩ := ihleft
    obtain ⟨rw⟩ := ihright
    have hvalues : (first::second::rest).length=values.length := rfl
    have happ : left++right=values := by simp [left,right]
    have hn : values.length≥2 := by simp [values]
    have hl : left.length=(values.length+1)/2 := by simp [left,leftLength]; omega
    have hr : right.length=values.length-(values.length+1)/2 := by simp [right,leftLength]
    have hpositive : 0<right.length ∧ 0<left.length := by omega
    have hbalance : left.length=right.length ∨ left.length=right.length+1 := by omega
    have hsum : left.length+right.length=values.length := by rw [← List.length_append,happ]
    let root : Row := ⟨2,Nat.pair 2 (Nat.pair lw.root.code rw.root.code),lw.root.count+rw.root.count,0⟩
    let rows := lw.rows++rw.rows++[root]
    have hcode : root.code=encodeBalancedList values := by
      dsimp [root]
      rw [lw.rootCode,rw.rootCode,← encode_append left right hpositive.1 hbalance,happ]
    have hcount : root.count=values.length := by simp [root,lw.rootCount,rw.rootCount,hsum]
    have hleft : lw.root.code≤root.code := (Nat.left_le_pair _ _).trans (Nat.right_le_pair _ _)
    have hright : rw.root.code≤root.code := (Nat.right_le_pair _ _).trans (Nat.right_le_pair _ _)
    have hlocal : unpairCheck (lw.rows++rw.rows) root=true := by
      rw [unpairCheck_eq]
      simp only [localCheck,root,show (2:Nat)≠0 by decide,show (2:Nat)≠1 by decide,
        ↓reduceIte,List.any_eq_true]
      refine ⟨lw.root,List.mem_append_left _ lw.member,rw.root,List.mem_append_right _ rw.member,?_⟩
      simp [lw.rootCount,rw.rootCount,hbalance,hpositive.1]
    have hrightCheck : checkFrom lw.rows rw.rows=true :=
      check_mono [] lw.rows rw.rows (by simp) rw.checked
    have hcheck : checkFrom [] rows=true := by
      dsimp [rows]
      rw [check_append,check_append]
      simp only [List.nil_append,lw.checked,hrightCheck,checkFrom,hlocal,Bool.and_true]
    have hleftSize := lw.positiveBound hpositive.2
    have hrightSize := rw.positiveBound hpositive.1
    have hrows : rows.length=lw.rows.length+rw.rows.length+1 := by simp [rows,Nat.add_assoc]
    refine ⟨⟨rows,root,by simp [rows],hcheck,hcode,hcount,?_,?_,?_,?_,?_,?_,?_⟩⟩
    · rw [hrows]; omega
    · intro _; rw [hrows]; omega
    · intro row hm
      rcases List.mem_append.mp hm with hm|hm
      · rcases List.mem_append.mp hm with hm|hm
        · exact (lw.codeBound row hm).trans hleft
        · exact (rw.codeBound row hm).trans hright
      · exact (List.mem_singleton.mp hm) ▸ Nat.le_refl _
    · intro row hm
      rcases List.mem_append.mp hm with hm|hm
      · rcases List.mem_append.mp hm with hm|hm
        · exact (lw.payloadBound row hm).trans hleft
        · exact (rw.payloadBound row hm).trans hright
      · rw [List.mem_singleton.mp hm]; exact Nat.zero_le _
    · intro row hm
      rcases List.mem_append.mp hm with hm|hm
      · rcases List.mem_append.mp hm with hm|hm
        · exact (lw.countBound row hm).trans (by omega)
        · exact (rw.countBound row hm).trans (by omega)
      · rw [List.mem_singleton.mp hm,hcount]
    · intro row hm
      rcases List.mem_append.mp hm with hm|hm
      · rcases List.mem_append.mp hm with hm|hm
        · exact lw.kindBound row hm
        · exact rw.kindBound row hm
      · rw [List.mem_singleton.mp hm]
    · intro row hm hk
      rcases List.mem_append.mp hm with hm|hm
      · have hmem : row.payload∈left++right := by
          rcases List.mem_append.mp hm with hm|hm
          · exact List.mem_append_left _ (lw.leafSupport row hm hk)
          · exact List.mem_append_right _ (rw.leafSupport row hm hk)
        rw [happ] at hmem
        exact hmem
      · rw [List.mem_singleton.mp hm] at hk
        change (2:Nat)=1 at hk
        omega

theorem certificate_iff (code : Nat) :
    (∃ rows root,checkFrom [] rows=true ∧ root∈rows ∧ root.code=code) ↔
      ∃ values,decodeBalancedList code=some values := by
  constructor
  · rintro ⟨rows,root,hcheck,hmem,hcode⟩
    obtain ⟨values,hv,_⟩ := check_sound [] rows (by simp) hcheck root (by simpa using hmem)
    refine ⟨values,?_⟩
    rw [← hcode,← hv]
    exact decodeBalancedList_encode values
  · rintro ⟨values,hdecode⟩
    obtain ⟨w⟩ := exists_witness values
    exact ⟨w.rows,w.root,w.checked,w.member,w.rootCode.trans (encodeBalancedList_of_decode hdecode)⟩

theorem bounded_certificate {code : Nat} {values : List Nat}
    (hd : decodeBalancedList code=some values) :
    ∃ rows root,checkFrom [] rows=true ∧ root∈rows ∧ root.code=code ∧
      rows.length≤2*natBitLength code+1 ∧
      ∀ row∈rows,row.code≤code ∧ row.payload≤code ∧ row.count≤natBitLength code ∧ row.kind≤2 := by
  obtain ⟨w⟩ := exists_witness values
  have he : w.root.code=code := w.rootCode.trans (encodeBalancedList_of_decode hd)
  have hn := decoded_balanced_length hd
  refine ⟨w.rows,w.root,w.checked,w.member,he,by have h:=w.lengthBound; omega,?_⟩
  intro row hm
  exact ⟨(w.codeBound row hm).trans_eq he,(w.payloadBound row hm).trans_eq he,
    (w.countBound row hm).trans hn,w.kindBound row hm⟩

end NearCubicWires.RepairSource.RecoveryOracle.BalancedCertificate
