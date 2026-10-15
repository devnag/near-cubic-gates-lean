import Proof.PCP.PCPTraversal

/-! The whole cold balanced serializer, including the empty input, the sole
fresh raw output copy, and its fixed polynomial time bound. -/
namespace NearCubicWires.RepairOrdinary.PCPTraversal
open LocalBitMultitape RecoveryExecution RecoveryRootRound PCPSerializerMass
open RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def bodyBudget (B : ℕ) :=
  400*(B+1)*(PCPPairReusable.capacity B+1)+20*(B+1)^5+30

theorem whole_budget (B M : ℕ) (hm : M≤B) : entryFuel B M+bodyBudget B≤budget B := by
  have hp : 1≤(B+1)^10 := Nat.one_le_pow 10 _ (by omega)
  have hc : PCPPairReusable.capacity B+1≤131073*(B+1)^10 := by
    unfold PCPPairReusable.capacity
    omega
  have hb : 400*(B+1)*(PCPPairReusable.capacity B+1)≤52429200*(B+1)^11 := by
    calc
      _≤400*(B+1)*(131073*(B+1)^10) := by gcongr
      _=52429200*(B+1)^11 := by ring
  have h11 : (B+1)^11≤(B+1)^12 := pow_le_pow_right₀ (by omega) (by omega)
  have h5 : (B+1)^5≤(B+1)^12 := pow_le_pow_right₀ (by omega) (by omega)
  have hB : B+1≤(B+1)^12 := by
    calc
      B+1=(B+1)^1 := by simp
      _≤(B+1)^12 := pow_le_pow_right₀ (by omega) (by omega)
  change (16643239936*(B+1)^11+2*M+12)+
    (400*(B+1)*(PCPPairReusable.capacity B+1)+20*(B+1)^5+30)≤1000000000000*(B+1)^12
  omega

theorem body_run (B : ℕ) (pre : List Bool) (fields : List (List Bool)) (suffix : List Bool)
    (tapes : Fin 128 → List Bool) (hm : mass fields≤B)
    (st : Stable (PCPPairReusable.capacity B) (pre++FieldList.stream fields++suffix)
      (RepairSource.VerifierDecoding.CompareMachine.word fields.length) pre.length [] [false] []
      (coldHeads pre.length) tapes)
    (count : CountAt (PCPPairReusable.capacity B) fields.length tapes) :
    ∃ fuel≤bodyBudget B,∃ out,
      Timed machine fuel (atCall 0 (coldHeads pre.length) tapes)
        (RecoveryCalls.stopped sizes (coldHeads (pre.length+(FieldList.stream fields).length)) out) ∧
      out 77=ZeroPadding.pad (PCPPairReusable.capacity B) (frame (code fields).bits) ∧
      out 78=(code fields).bits ∧ out 0=pre++FieldList.stream fields++suffix ∧
      out 2=RepairSource.VerifierDecoding.CompareMachine.word fields.length ∧
      WorkBound (PCPPairReusable.capacity B) out := by
  let cap := PCPPairReusable.capacity B
  have hn : fields.length≤B := (mass_bounds fields).1.trans hm
  have hreserve := capacity_reserves B
  have hc : 3≤cap := by omega
  have hframeCap : frameBound B≤cap := by
    have hp : (B+1)^5≤(B+1)^10 := pow_le_pow_right₀ (by omega) (by omega)
    unfold frameBound cap PCPPairReusable.capacity
    omega
  have hfr := (bounded_frame fields B hm).trans hframeCap
  have hbits := bounded_code fields B hm
  have hmain : 400*(cap+1)≤400*(B+1)*(cap+1) := by
    apply Nat.mul_le_mul_right
    omega
  by_cases hz : fields.length=0
  · have he : fields=[] := List.length_eq_zero_iff.mp hz
    subst fields
    obtain ⟨middle,hpath,hstable,hresult⟩ := stable_empty cap pre.length
      (pre++FieldList.stream []++suffix) (RepairSource.VerifierDecoding.CompareMachine.word 0)
      [] [false] [] (coldHeads pre.length) tapes st count (by omega)
    obtain ⟨n,hnFinal,out,hfinal,hfield,hraw,hsource,hcount,hwork⟩ := final_path cap pre.length
      (pre++FieldList.stream []++suffix) (RepairSource.VerifierDecoding.CompareMachine.word 0)
      [] [false] [] [] (coldHeads pre.length) middle hstable (by simpa using hc.trans' (by decide : 1≤3)) hresult
    obtain ⟨m,hmStart,hstart⟩ := hpath
    have hcode : (code []).bits=[] := by simp [code,values,CanonicalBinary.encodeBalancedList]
    refine ⟨m+n,?_,out,?_,?_,?_,hsource,hcount,hwork⟩
    · change m+n≤400*(B+1)*(cap+1)+20*(B+1)^5+30
      simp only [List.length_nil] at hnFinal
      omega
    · exact hstart.trans hfinal
    · simpa only [hcode] using hfield
    · simpa only [hcode] using hraw
  · have hpos : 0<fields.length := by omega
    obtain ⟨h,t,hpath,hstable,hresult⟩ := subtree_run B fields.length fields rfl hpos hm
      pre suffix (RepairSource.VerifierDecoding.CompareMachine.word fields.length)
      [] [false] [] (coldHeads pre.length) tapes st count
      (by have he := Nat.mul_le_mul_right (frameBound B) hn; simpa only [List.length_nil,Nat.zero_add] using he.trans (by omega))
      (by change 0+3*fields.length≤cap; omega)
      (by change 1+2*fields.length≤cap; omega)
    obtain ⟨z,hz⟩ := hstable.continuation.zeros
    have ht : t 81=List.replicate (z+1) false := by
      simpa only [List.replicate_succ,List.singleton_append] using hz
    have hreturn := return_empty_path z h t ht hstable.continuation.head
    obtain ⟨n,hnFinal,out,hfinal,hfield,hraw,hsource,hcount,hwork⟩ := final_path cap
      (pre.length+(FieldList.stream fields).length) (pre++FieldList.stream fields++suffix)
      (RepairSource.VerifierDecoding.CompareMachine.word fields.length) [] [false] [] (code fields).bits
      h t hstable (by simpa only [frame_length] using hfr) hresult
    obtain ⟨m,hmStart,hstart⟩ := hpath.trans hreturn
    have hsub : subtreeBudget cap fields.length≤400*B*(cap+1) := by
      unfold subtreeBudget
      apply Nat.mul_le_mul_right
      omega
    have he : 400*(B+1)*(cap+1)=400*B*(cap+1)+400*(cap+1) := by ring
    refine ⟨m+n,?_,out,?_,hfield,hraw,hsource,hcount,hwork⟩
    · change m+n≤400*(B+1)*(cap+1)+20*(B+1)^5+30
      rw [he]
      dsimp only [cap] at hmStart hsub hnFinal ⊢
      omega
    · have hp := hstart.trans hfinal
      rw [hstable.root_heads] at hp
      exact hp

theorem cold_timed (pre : List Bool) (fields : List (List Bool)) (suffix : List Bool) :
    ∃ fuel≤budget (mass fields),∃ out,
      Timed machine fuel (entry (pre++FieldList.stream fields++suffix) pre.length fields.length)
        (RecoveryCalls.stopped sizes (coldHeads (pre.length+(FieldList.stream fields).length)) out) ∧
      out 77=ZeroPadding.pad (PCPPairReusable.capacity (mass fields)) (frame (code fields).bits) ∧
      out 78=(code fields).bits ∧ out 0=pre++FieldList.stream fields++suffix ∧
      out 2=RepairSource.VerifierDecoding.CompareMachine.word fields.length ∧
      WorkBound (PCPPairReusable.capacity (mass fields)) out := by
  obtain ⟨n,hn,tapes,hentry,hstable,hcount⟩ := cold_stable pre fields suffix
  obtain ⟨m,hm,out,hbody,hfield,hraw,hsource,hcountWord,hwork⟩ :=
    body_run (mass fields) pre fields suffix tapes le_rfl hstable hcount
  exact ⟨n+m,(Nat.add_le_add hn hm).trans (whole_budget _ _ (mass_bounds fields).1),out,
    hentry.trans hbody,hfield,hraw,hsource,hcountWord,hwork⟩

theorem cold_run (pre : List Bool) (fields : List (List Bool)) (suffix : List Bool) :
    ∃ receipt,runFrom machine (budget (mass fields))
        (entry (pre++FieldList.stream fields++suffix) pre.length fields.length)=some receipt ∧
      receipt.final.tapes 77=ZeroPadding.pad (PCPPairReusable.capacity (mass fields)) (frame (code fields).bits) ∧
      receipt.final.tapes 78=(code fields).bits ∧
      receipt.final.tapes 0=pre++FieldList.stream fields++suffix ∧
      receipt.final.tapes 2=RepairSource.VerifierDecoding.CompareMachine.word fields.length ∧
      receipt.final.heads=coldHeads (pre.length+(FieldList.stream fields).length) ∧
      WorkBound (PCPPairReusable.capacity (mass fields)) receipt.final.tapes ∧
      receipt.steps≤budget (mass fields) := by
  obtain ⟨n,hn,out,hpath,hfield,hraw,hsource,hcount,hwork⟩ := cold_timed pre fields suffix
  obtain ⟨r,hr,hfinal,hs⟩ := hpath.run (by simp [machine,RecoveryCalls.machine,RecoveryCalls.stopped])
  have hrun := runFrom_moreFuel machine n (budget (mass fields)-n) _ r hr
  have he : n+(budget (mass fields)-n)=budget (mass fields) := by omega
  rw [he] at hrun
  refine ⟨r,hrun,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [hfinal]; exact hfield
  · rw [hfinal]; exact hraw
  · rw [hfinal]; exact hsource
  · rw [hfinal]; exact hcount
  · rw [hfinal]; rfl
  · rw [hfinal]; exact hwork
  · omega

end NearCubicWires.RepairOrdinary.PCPTraversal
