import Proof.Amplification.RecoveryBalancedCertificateSize

namespace NearCubicWires.RepairSource.RecoveryOracle.BalancedCertificate
open CanonicalBinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def MeaningWith (P : Nat → Bool) (row : Row) : Prop :=
  ∃ values : List Nat,encodeBalancedList values=row.code ∧ values.length=row.count ∧ values.all P=true

def leafCheck (P : Nat → Bool) (row : Row) : Bool := if row.kind=1 then P row.payload else true
def rootCheck (P : Nat → Bool) (rows : List Row) (code : Nat) : Bool :=
  checkFrom [] rows && rows.all (leafCheck P) && rows.any (fun row => row.code==code)

theorem local_sound_with (P : Nat → Bool) (prior : List Row) (row : Row)
    (hp : ∀ entry∈prior,MeaningWith P entry) (hc : unpairCheck prior row=true)
    (hleaf : leafCheck P row=true) : MeaningWith P row := by
  rw [unpairCheck_eq] at hc
  unfold localCheck at hc
  split at hc
  · simp only [Bool.and_eq_true,beq_iff_eq] at hc
    exact ⟨[],by simpa [encodeBalancedList] using hc.1.symm,by simpa using hc.2.symm,rfl⟩
  · split at hc
    · rename_i hkind
      simp only [Bool.and_eq_true,beq_iff_eq] at hc
      refine ⟨[row.payload],?_,by simpa using hc.2.symm,?_⟩
      · have h := congrArg (fun p : Nat×Nat => Nat.pair p.1 p.2) hc.1
        simpa [encodeBalancedList] using h.symm
      · simpa [leafCheck,hkind] using hleaf
    · split at hc
      · simp only [List.any_eq_true,Bool.and_eq_true,beq_iff_eq,Bool.or_eq_true,decide_eq_true_eq,and_assoc] at hc
        obtain ⟨left,hl,right,hr,hpair,hcount,hbalance,hpositive⟩ := hc
        obtain ⟨lv,hlc,hln,hlp⟩ := hp left hl
        obtain ⟨rv,hrc,hrn,hrp⟩ := hp right hr
        refine ⟨lv++rv,?_,by simp [hln,hrn,hcount],by simp [hlp,hrp]⟩
        rw [encode_append lv rv (by omega) (by omega),hlc,hrc]
        have h := congrArg (fun p : Nat×Nat => Nat.pair p.1 p.2) hpair
        simpa using h.symm
      · contradiction

theorem rows_sound_with (P : Nat → Bool) (prior rows : List Row)
    (hp : ∀ entry∈prior,MeaningWith P entry) (hc : checkFrom prior rows=true)
    (hl : rows.all (leafCheck P)=true) : ∀ entry∈prior++rows,MeaningWith P entry := by
  induction rows generalizing prior with
  | nil => simpa using hp
  | cons row rest ih =>
    simp only [checkFrom,Bool.and_eq_true] at hc
    simp only [List.all_cons,Bool.and_eq_true] at hl
    have hn : ∀ entry∈prior++[row],MeaningWith P entry := by
      intro entry he
      rcases List.mem_append.mp he with hm|hm
      · exact hp entry hm
      · simpa using List.mem_singleton.mp hm ▸ local_sound_with P prior row hp hc.1 hl.1
    simpa [List.append_assoc] using ih (prior++[row]) hn hc.2 hl.2

theorem rootCheck_sound (P : Nat → Bool) (rows : List Row) (code : Nat)
    (hc : rootCheck P rows code=true) : ∃ values,decodeBalancedList code=some values ∧ values.all P=true := by
  simp only [rootCheck,Bool.and_eq_true,List.any_eq_true,beq_iff_eq] at hc
  obtain ⟨root,hmem,hcode⟩ := hc.2
  obtain ⟨values,hv,_,hp⟩ := rows_sound_with P [] rows (by simp) hc.1.1 hc.1.2 root (by simpa using hmem)
  refine ⟨values,?_,hp⟩
  rw [← hcode,← hv]
  exact decodeBalancedList_encode values

theorem witness_rootCheck (values : List Nat) (w : Witness values) (P : Nat → Bool)
    (hp : values.all P=true) : rootCheck P w.rows (encodeBalancedList values)=true := by
  simp only [rootCheck,Bool.and_eq_true]
  refine ⟨⟨w.checked,?_⟩,?_⟩
  · rw [List.all_eq_true]
    intro row hm
    unfold leafCheck
    split
    · rename_i hkind
      exact List.all_eq_true.mp hp _ (w.leafSupport row hm hkind)
    · rfl
  · rw [List.any_eq_true]
    exact ⟨w.root,w.member,by simp [w.rootCode]⟩

theorem rootCheck_iff (P : Nat → Bool) (code : Nat) :
    (∃ rows,rootCheck P rows code=true) ↔ ∃ values,decodeBalancedList code=some values ∧ values.all P=true := by
  constructor
  · rintro ⟨rows,hc⟩; exact rootCheck_sound P rows code hc
  · rintro ⟨values,hd,hp⟩
    obtain ⟨w⟩ := exists_witness values
    refine ⟨w.rows,?_⟩
    rw [← encodeBalancedList_of_decode hd]
    exact witness_rootCheck values w P hp

end NearCubicWires.RepairSource.RecoveryOracle.BalancedCertificate
