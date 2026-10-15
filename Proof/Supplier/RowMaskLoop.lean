import Proof.Supplier.RowMaskBody

/-! A selected incidence mask is consumed once. Its selected positions are
appended in order and its population is added to the physical count tape. -/
namespace NearCubicWires.RepairOrdinary.RowMaskLoop
open LocalBitMultitape RecoveryExecution RowMaskBodyParts Streaming RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def word : ℕ→List Bool→List Bool
  | _,[]=>[]
  | j,b::bs=>RowMaskBody.emitted b j++word (j+1) bs
noncomputable def machine := RepeatMachine.machine RowMaskBody.machine (fun _ _=>true)
noncomputable def cfg (phase : Fin 5) (source : List Bool) (pos j count : ℕ) (out : List Bool)
    (total driver : ℕ) :=
  RepeatMachine.cfg phase (RowMaskBodyParts.cfg RowMaskBody.machine.start source pos j count out) total driver

theorem remaining (total j : ℕ) (bits : List Bool) (pre tail out : List Bool) (count : ℕ)
    (hj : j+bits.length=total) :
    ∃ n,n≤bits.length*(4*total+20)+total+3 ∧
      Timed machine n (cfg 0 (pre++bits++tail) pre.length j count out total (j+1))
        (cfg 3 (pre++bits++tail) (pre.length+bits.length) total (count+bits.count true)
          (out++word j bits) total 1) := by
  induction bits generalizing j pre out count with
  | nil =>
    have he : j=total := by simpa using hj
    subst j
    refine ⟨total+3,by simp,?_⟩
    simpa only [List.nil_append,List.append_nil,List.length_nil,List.count_nil,Nat.add_zero,word,machine,cfg] using
      RepeatMachine.exhaust RowMaskBody.machine (fun _ _=>true)
        (RowMaskBodyParts.cfg RowMaskBody.machine.start (pre++tail) pre.length total count out) total
  | cons bit bits ih =>
    obtain ⟨r,hr,rh,rt,rs⟩ := RowMaskBody.body_run pre (bits++tail) bit j count out
    have ht := RepeatMachine.iteration RowMaskBody.machine (fun _ _=>true)
      (RowMaskBodyParts.cfg RowMaskBody.machine.start (pre++bit::(bits++tail)) pre.length j count out)
      total j r (by rfl) (by simp only [List.length_cons] at hj; omega) hr
    simp only [↓reduceIte] at ht
    have he := RowOccurrenceLoop.cfg_eq 0 r.final
      (RowMaskBodyParts.cfg RowMaskBody.machine.start (pre++bit::(bits++tail)) (pre.length+1)
        (j+1) (count+bit.toNat) (out++RowMaskBody.emitted bit j)) total (j+2) rh rt
    rw [he] at ht
    obtain ⟨n,hn,htail⟩ := ih (j+1) (pre++[bit]) (out++RowMaskBody.emitted bit j) (count+bit.toNat)
      (by simp only [List.length_cons] at hj; omega)
    have hsource : (pre++[bit])++bits++tail=pre++bit::(bits++tail) := by simp [List.append_assoc]
    simp only [List.length_append,List.length_cons,List.length_nil,hsource] at htail
    have hdri : j+1+1=j+2 := by omega
    rw [hdri] at htail
    have whole := ht.trans htail
    refine ⟨r.steps+2+n,?_,?_⟩
    · simp only [List.length_cons] at hj ⊢
      nlinarith
    · have hc : count+bit.toNat+bits.count true=count+(bit::bits).count true := by
        cases bit <;> simp [Nat.add_comm,Nat.add_left_comm]
      have hpos : pre.length+1+bits.length=pre.length+(bit::bits).length := by simp; omega
      simpa only [machine,cfg,word,hc,hpos,List.cons_append,List.append_assoc] using whole

theorem mask_run (pre bits tail out : List Bool) (count : ℕ) :
    ∃ r,runFrom machine (bits.length*(4*bits.length+21)+3)
      (cfg 0 (pre++bits++tail) pre.length 0 count out bits.length 1)=some r ∧
      r.final=cfg 3 (pre++bits++tail) (pre.length+bits.length) bits.length (count+bits.count true)
        (out++word 0 bits) bits.length 1 ∧ r.steps≤bits.length*(4*bits.length+21)+3 := by
  obtain ⟨n,hn,h⟩ := remaining bits.length 0 bits pre tail out count (by simp)
  have hbound : n≤bits.length*(4*bits.length+21)+3 := by nlinarith
  obtain ⟨r,hr,rf,rs⟩ := h.run
    (by simp [machine,cfg,RepeatMachine.machine,RepeatMachine.cfg,controlConfig,RepeatMachine.phaseCode])
  have more := runFrom_moreFuel machine n (bits.length*(4*bits.length+21)+3-n) _ r hr
  rw [Nat.add_sub_of_le hbound] at more
  exact ⟨r,more,rf,rs.le.trans hbound⟩

end NearCubicWires.RepairOrdinary.RowMaskLoop
