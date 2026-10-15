import Proof.CaseAnalysis.RowsCircuitReturnHeads
import Proof.CaseAnalysis.RowsCircuitResourceRun

/-! The actual retained count and top payload are appended between two
paid inner-gate clears. The same native prefix is retained, and the next
bottom traversal receives a genuinely cleared gate workspace. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsCircuitNativePrepare
open LocalBitMultitape RecoveryRootRound RepairRepresentation
open CloseoutRowsCircuitNativePrefix CloseoutRowsCircuitGateErase
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def first:=Composition.machine CloseoutRowsCircuitGateErase.machine CloseoutRowsCircuitNativePrefix.machine
noncomputable def machine:=Composition.machine first CloseoutRowsCircuitGateErase.machine
def budget (C n : ℕ) (bits : List Bool):=(2*C+4)+1+CloseoutRowsCircuitNativePrefix.budget C n bits+1+(2*C+4)

theorem gate_at (C : ℕ) (A : Fin 1703 → List Bool) (i : Fin 1703)
    (hi : 639 ≤ i.val ∧ i.val ≤ 1687 ∧ i.val≠1674) :
    CloseoutRowsCircuitGateErase.output C A i=List.replicate C false:=by
  let j:Fin 1048:=⟨if i.val<1674 then i.val-639 else i.val-640,by split_ifs <;> omega⟩
  have he:CloseoutRowsCircuitAllocate.gate j=i:=by
    apply Fin.ext
    rw [CloseoutRowsCircuitAllocate.gate_val]
    dsimp only [j]
    split_ifs <;> omega
  rw [←he]
  exact output_gate C A j

theorem gate_heads (H : Fin 1703 → ℕ)
    (hh : ∀ j,H (CloseoutRowsCircuitGateErase.slots j)=0) (i : Fin 1703)
    (hi : 639 ≤ i.val ∧ i.val ≤ 1687 ∧ i.val≠1674) : H i=0:=by
  let j:Fin 1050:=⟨if i.val<1674 then i.val-639 else i.val-640,by split_ifs <;> omega⟩
  have he:CloseoutRowsCircuitGateErase.slots j=i:=by
    apply Fin.ext
    rw [CloseoutRowsCircuitGateErase.slots_val]
    dsimp only [j]
    split_ifs <;> omega
  rw [←he];exact hh j

private theorem together {t a b : ℕ} (p : Machine t a) (q : Machine t b) (fp fq : ℕ)
    (H H' H'' : Fin t → ℕ) (A B D : Fin t → List Bool)
    (r : ExecutionReceipt t a) (s : ExecutionReceipt t b)
    (hp : runFrom p fp ⟨p.start,H,A⟩=some r) (ph : r.final.heads=H') (pt : r.final.tapes=B) (ps : r.steps ≤ fp)
    (hq : runFrom q fq ⟨q.start,H',B⟩=some s) (qh : s.final.heads=H'') (qt : s.final.tapes=D) (qs : s.steps ≤ fq) :
    ∃ run,runFrom (Composition.machine p q) (fp+1+fq) ⟨(Composition.machine p q).start,H,A⟩=some run ∧
      run.steps ≤ fp+1+fq ∧ run.final.heads=H'' ∧ run.final.tapes=D:=by
  have he:Composition.restart r.final q.start=⟨q.start,H',B⟩:=configuration_ext rfl ph pt
  rw [←he] at hq
  refine ⟨Composition.joinedReceipt r s,Composition.run_join p q _ _ _ r s hp hq,?_,qh,qt⟩
  change r.steps+1+s.steps ≤ fp+1+fq;omega

theorem prepare_run (C n : ℕ) (bits out : List Bool) (H : Fin 1703 → ℕ)
    (A : Fin 1703 → List Bool) (hn : n ≤ C) (hc : EquationHeaderAppend.budget n+1 ≤ C)
    (hb : 2*bits.length+1 ≤ C)
    (hh : ∀ j,H (CloseoutRowsCircuitGateErase.slots j)=0)
    (bound : ∀ j,(A (CloseoutRowsCircuitAllocate.gate j)).length ≤ C)
    (hpub : H 1702=0 ∧ H 1701=0 ∧ H 1696=0 ∧ H 1688=out.length)
    (driver : A 1694=List.replicate C true) (log : A 1695=List.replicate (C+1) false)
    (count : A 1702=ZeroPadding.pad C (List.replicate n true))
    (top : A 1701=ZeroPadding.pad C (frame bits))
    (native : A 1688=out) (scratch : A 1696=List.replicate C false) : ∃ B r,
    runFrom machine (budget C n bits) ⟨machine.start,H,A⟩=some r ∧
      r.steps ≤ budget C n bits ∧
      r.final.heads=Function.update H 1688 (out++natWord n++frame bits).length ∧ r.final.tapes=B ∧
      B 1688=out++natWord n++frame bits ∧ B 1696=List.replicate C false ∧
      B 1694=List.replicate C true ∧ B 1695=List.replicate (C+1) false ∧
      (∀ j,B (CloseoutRowsCircuitAllocate.gate j)=List.replicate C false) ∧
      (∀ i,(i.val<639 ∨ 1687 < i.val ∨ i.val=1674) → i≠1694 → i≠1695 → i≠1688 → i≠1696 → B i=A i):=by
  obtain ⟨r0,h0,r0h,r0t,r0s⟩:=erase_run C H A hh bound driver log
  let A0:=CloseoutRowsCircuitGateErase.output C A
  have copyH:∀ i,H (copySlots i)=0:=by
    intro i;fin_cases i
    · exact hpub.1
    · exact gate_heads H hh 639 (by decide)
    · exact hh 1048
    · exact hh 1049
  have copyT:∀ i,A0 (copySlots i)=CloseoutRowsMetadataCopy.input (ZeroPadding.pad C (List.replicate n true)) C i:=by
    intro i;fin_cases i
    · exact (output_other C A 1702 (by decide)).trans count
    · exact gate_at C A 639 (by decide)
    · exact output_driver C A
    · exact output_log C A
  have headerH:∀ i,H (headerSlots i)=CloseoutRowsCircuitCountHeader.heads out i:=by
    intro i
    by_cases h17:i.val=17
    · simp only [headerSlots,if_pos h17,CloseoutRowsCircuitCountHeader.heads];exact hpub.2.2.2
    by_cases h18:i.val=18
    · simp only [headerSlots,if_neg h17,if_pos h18,CloseoutRowsCircuitCountHeader.heads];exact hpub.2.2.1
    simp only [CloseoutRowsCircuitCountHeader.heads,if_neg h17]
    apply gate_heads H hh
    rw [header_val,if_neg h17,if_neg h18]
    omega
  have headerT:∀ i,(Function.update A0 639 (ZeroPadding.pad C (List.replicate n true))) (headerSlots i)=
      CloseoutRowsCircuitCountHeader.input C n out i:=by
    intro i
    by_cases h17:i.val=17
    · simp only [headerSlots,if_pos h17,CloseoutRowsCircuitCountHeader.input,
        Function.update_of_ne (by decide : (1688 : Fin 1703)≠639)]
      exact (output_other C A 1688 (by decide)).trans native
    by_cases h0:i.val=0
    · have he:i=0:=Fin.ext h0;subst i;exact Function.update_self _ _ _
    simp only [CloseoutRowsCircuitCountHeader.input,if_neg h17,if_neg h0]
    by_cases h18:i.val=18
    · simp only [headerSlots,if_neg h17,if_pos h18,Function.update_of_ne (by decide : (1696 : Fin 1703)≠639)]
      exact (output_other C A 1696 (by decide)).trans scratch
    have hne:headerSlots i≠639:=by
      intro h;have hv:=congrArg Fin.val h
      rw [header_val,if_neg h17,if_neg h18] at hv;omega
    rw [Function.update_of_ne hne]
    apply gate_at
    rw [header_val,if_neg h17,if_neg h18]
    omega
  obtain ⟨P,r1,h1,r1s,r1h,r1t,pnative,pscratch,pbound,pkeep⟩:=prefix_run C n bits out H A0 hn hc hb
    copyH copyT headerH headerT hpub.2.1 ((output_other C A 1701 (by decide)).trans top)
  let H1:=Function.update H 1688 (out++natWord n++frame bits).length
  have hh1:∀ j,H1 (CloseoutRowsCircuitGateErase.slots j)=0:=by
    intro j
    rw [show H1=Function.update H _ _ by rfl,Function.update_of_ne (by
      intro h;have hv:=congrArg Fin.val h;rw [slots_val] at hv;split_ifs at hv <;> omega)]
    exact hh j
  have small:∀ j,(P (CloseoutRowsCircuitAllocate.gate j)).length ≤ C:=by
    intro j
    by_cases hit:∃ k,headerSlots k=CloseoutRowsCircuitAllocate.gate j
    · obtain ⟨k,hk⟩:=hit
      rw [←hk]
      exact pbound k (by
        intro h17
        have hv:=congrArg Fin.val hk
        rw [header_val,if_pos h17] at hv
        have gr:=CloseoutRowsCircuitAllocate.gate_range j
        omega)
    · rw [pkeep _ (by simpa only [not_exists] using hit)]
      change (CloseoutRowsCircuitGateErase.output C A (CloseoutRowsCircuitAllocate.gate j)).length ≤ C
      rw [output_gate,List.length_replicate]
  have outsideHeader (i : Fin 1703) (hi : 1688 < i.val) (hlog : i≠1696) : ∀ j,headerSlots j≠i:=by
    intro j h;have hv:=congrArg Fin.val h
    rw [header_val] at hv
    split_ifs at hv <;> omega
  have pd:P 1694=List.replicate C true:=by
    rw [pkeep _ (outsideHeader 1694 (by decide) (by decide))]
    exact output_driver C A
  have pl:P 1695=List.replicate (C+1) false:=by
    rw [pkeep _ (outsideHeader 1695 (by decide) (by decide))]
    exact output_log C A
  obtain ⟨r2,h2,r2h,r2t,r2s⟩:=erase_run C H1 P hh1 small pd pl
  obtain ⟨r01,h01,s01,h01h,h01t⟩:=together CloseoutRowsCircuitGateErase.machine CloseoutRowsCircuitNativePrefix.machine
    _ _ H H H1 A A0 P r0 r1 h0 r0h r0t r0s.le h1 r1h r1t r1s
  obtain ⟨r,hr,rs,rh,rt⟩:=together first CloseoutRowsCircuitGateErase.machine _ _ H H1 H1 A P
    (CloseoutRowsCircuitGateErase.output C P) r01 r2 h01 h01h h01t s01 h2 r2h r2t r2s.le
  refine ⟨_,r,hr,rs,rh,rt,?_,?_,output_driver C P,output_log C P,output_gate C P,?_⟩
  · exact (output_other C P 1688 (by decide)).trans pnative
  · exact (output_other C P 1696 (by decide)).trans pscratch
  · intro i hi hd hl ho hs
    have outsideGate: (i.val<639 ∨ 1687 < i.val ∨ i.val=1674) ∧ i.val≠1694 ∧ i.val≠1695:=
      ⟨hi,fun h=>hd (Fin.ext h),fun h=>hl (Fin.ext h)⟩
    rw [output_other C P i outsideGate,pkeep i (by
      intro j h
      have hv:=congrArg Fin.val h
      rw [header_val] at hv
      split_ifs at hv <;> omega)]
    exact output_other C A i outsideGate

end NearCubicWires.RepairOrdinary.CloseoutRowsCircuitNativePrepare
