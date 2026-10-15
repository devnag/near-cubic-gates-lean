import Proof.CaseAnalysis.RowsCircuitCountHeader

/-! Publish the actual retained-count header and the already checked top
payload before the original bottom traversal. The native output is an
existing prefix with a logical append cursor; padding is never emitted. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsCircuitNativePrefix
open LocalBitMultitape RecoveryRootRound RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def copySlots : Fin 4 → Fin 1703 := ![1702,639,1694,1695]
def headerSlots (i : Fin 19) : Fin 1703 :=
  if i.val=17 then 1688 else if i.val=18 then 1696 else ⟨639+i.val,by omega⟩
def frameSlots : Fin 3 → Fin 1703 := ![1701,1688,1696]
noncomputable def countCopy := RecoveryFocus.machine copySlots RecoveryBoundedTapeCopy.machine
noncomputable def header := RecoveryFocus.machine headerSlots CloseoutRowsCircuitCountHeader.machine
noncomputable def top := RecoveryFocus.machine frameSlots CompetitorFrameAppend.machine
noncomputable def first := Composition.machine countCopy header
noncomputable def machine := Composition.machine first top
def budget (C n : ℕ) (bits : List Bool) :=
  (2*C+4)+1+CloseoutRowsCircuitCountHeader.budget n+1+(4*bits.length+3)

theorem header_val (i : Fin 19) : (headerSlots i).val=
    if i.val=17 then 1688 else if i.val=18 then 1696 else 639+i.val:=by
  simp only [headerSlots];split_ifs <;> rfl
theorem header_injective : Function.Injective headerSlots:=by
  intro i j h
  have hv:=congrArg Fin.val h
  rw [header_val,header_val] at hv
  split_ifs at hv <;> apply Fin.ext <;> omega

theorem copy_count (C n : ℕ) (H : Fin 1703 → ℕ) (A : Fin 1703 → List Bool)
    (hn : n≤C) (hh : ∀ i,H (copySlots i)=0)
    (ht : ∀ i,A (copySlots i)=CloseoutRowsMetadataCopy.input
      (ZeroPadding.pad C (List.replicate n true)) C i) :
    PCPOuter.Exact countCopy (2*C+4) H A H
      (Function.update A 639 (ZeroPadding.pad C (List.replicate n true))):=by
  have hc:(ZeroPadding.pad C (List.replicate n true)).length=C:=by
    rw [ZeroPadding.pad_length,List.length_replicate,Nat.max_eq_left hn]
  have run:=CloseoutRowsCircuitCopy.copy_focus copySlots (by decide) C
    (ZeroPadding.pad C (List.replicate n true)) hc.le H A hh ht
  have hp:ZeroPadding.pad C (ZeroPadding.pad C (List.replicate n true))=
      ZeroPadding.pad C (List.replicate n true):=by
    rw [ZeroPadding.pad,hc,Nat.sub_self,List.replicate_zero,List.append_nil]
  rw [hp] at run
  exact run

private theorem header_heads (H : Fin 1703 → ℕ) (out next : List Bool)
    (hh : ∀ i,H (headerSlots i)=CloseoutRowsCircuitCountHeader.heads out i)
    (after : Fin 1703 → ℕ)
    (selected : ∀ i,after (headerSlots i)=CloseoutRowsCircuitCountHeader.heads next i)
    (outside : ∀ i,(∀ j,headerSlots j≠i) → after i=H i) :
    after=Function.update H 1688 next.length:=by
  apply Function.eq_update_iff.mpr
  refine ⟨selected 17,?_⟩
  intro i hi
  by_cases hs:∃ j,headerSlots j=i
  · obtain ⟨j,rfl⟩:=hs
    have hj:j.val≠17:=by intro h;apply hi;unfold headerSlots;rw [if_pos h]
    rw [selected,hh]
    simp only [CloseoutRowsCircuitCountHeader.heads,if_neg hj]
  · exact outside i (by simpa only [not_exists] using hs)

theorem header_focus (C n : ℕ) (out : List Bool) (H : Fin 1703 → ℕ)
    (A : Fin 1703 → List Bool) (hn : n≤C) (hc : EquationHeaderAppend.budget n+1≤C)
    (hh : ∀ i,H (headerSlots i)=CloseoutRowsCircuitCountHeader.heads out i)
    (ht : ∀ i,A (headerSlots i)=CloseoutRowsCircuitCountHeader.input C n out i) :
    ∃ B r,runFrom header (CloseoutRowsCircuitCountHeader.budget n)
        ⟨header.start,H,A⟩=some r ∧ r.steps≤CloseoutRowsCircuitCountHeader.budget n ∧
      r.final.heads=Function.update H 1688 (out++natWord n).length ∧ r.final.tapes=B ∧
      B 1688=out++natWord n ∧ B 1696=List.replicate C false ∧
      (∀ j : Fin 19,j.val≠17 → (B (headerSlots j)).length≤C) ∧
      (∀ i : Fin 1703,(∀ j,headerSlots j≠i) → B i=A i):=by
  obtain ⟨base,hb,bs,bh,bo,_bn,bl,bound⟩:=CloseoutRowsCircuitCountHeader.header_run C n out hn hc
  obtain ⟨r,hr,_rf,rs,rh,rt,keep⟩:=RecoveryFocus.dock headerSlots header_injective
    CloseoutRowsCircuitCountHeader.machine _ H A _ hh ht base hb
  refine ⟨r.final.tapes,r,hr,rs ▸ bs,?_,rfl,?_,?_,?_,?_⟩
  · apply header_heads H out (out++natWord n) hh r.final.heads
    · intro j;rw [rh,bh]
    · intro i hi;exact (keep i hi).1
  · exact (rt 17).trans bo
  · exact (rt 18).trans bl
  · intro j hj;rw [rt];exact bound j hj
  · intro i hi;exact (keep i hi).2

private theorem joined {t a b : ℕ} (p : Machine t a) (q : Machine t b) (fp fq : ℕ)
    (H H' H'' : Fin t → ℕ) (A B D : Fin t → List Bool)
    (first : ExecutionReceipt t a) (last : ExecutionReceipt t b)
    (hp : runFrom p fp ⟨p.start,H,A⟩=some first)
    (ph : first.final.heads=H') (pt : first.final.tapes=B) (ps : first.steps≤fp)
    (hq : runFrom q fq ⟨q.start,H',B⟩=some last)
    (qh : last.final.heads=H'') (qt : last.final.tapes=D) (qs : last.steps≤fq) :
    ∃ r,runFrom (Composition.machine p q) (fp+1+fq)
        ⟨(Composition.machine p q).start,H,A⟩=some r ∧
      r.steps≤fp+1+fq ∧ r.final.heads=H'' ∧ r.final.tapes=D:=by
  have he:Composition.restart first.final q.start=⟨q.start,H',B⟩:=configuration_ext rfl ph pt
  have hlast:runFrom q fq (Composition.restart first.final q.start)=some last:=by rw [he];exact hq
  refine ⟨Composition.joinedReceipt first last,Composition.run_join p q fp fq _ first last hp hlast,?_,qh,qt⟩
  change first.steps+1+last.steps≤fp+1+fq
  omega

theorem prefix_run (C n : ℕ) (bits out : List Bool) (H : Fin 1703 → ℕ)
    (A : Fin 1703 → List Bool) (hn : n≤C) (hc : EquationHeaderAppend.budget n+1≤C)
    (hb : 2*bits.length+1≤C)
    (copyH : ∀ i,H (copySlots i)=0)
    (copyT : ∀ i,A (copySlots i)=CloseoutRowsMetadataCopy.input
      (ZeroPadding.pad C (List.replicate n true)) C i)
    (headerH : ∀ i,H (headerSlots i)=CloseoutRowsCircuitCountHeader.heads out i)
    (headerT : ∀ i,(Function.update A 639 (ZeroPadding.pad C (List.replicate n true)))
      (headerSlots i)=CloseoutRowsCircuitCountHeader.input C n out i)
    (topH : H 1701=0) (topT : A 1701=ZeroPadding.pad C (frame bits)) :
    ∃ B r,runFrom machine (budget C n bits) ⟨machine.start,H,A⟩=some r ∧
      r.steps≤budget C n bits ∧
      r.final.heads=Function.update H 1688 (out++natWord n++frame bits).length ∧
      r.final.tapes=B ∧
      B 1688=out++natWord n++frame bits ∧ B 1696=List.replicate C false ∧
      (∀ j : Fin 19,j.val≠17 → (B (headerSlots j)).length≤C) ∧
      (∀ i : Fin 1703,(∀ j,headerSlots j≠i) → B i=A i):=by
  let A1:=Function.update A 639 (ZeroPadding.pad C (List.replicate n true))
  obtain ⟨copied,cp,ch,ct,cs⟩:=copy_count C n H A hn copyH copyT
  obtain ⟨B,wrote,wp,ws,wh,wt,bout,blog,bsmall,bkeep⟩:=header_focus C n out H A1 hn hc headerH headerT
  obtain ⟨p,hp,ps,ph,pt⟩:=joined countCopy header (2*C+4) (CloseoutRowsCircuitCountHeader.budget n)
    H H (Function.update H 1688 (out++natWord n).length) A A1 B copied wrote
    cp ch ct cs.le wp wh wt ws
  have outsideTop:∀ j,headerSlots j≠1701:=by
    intro j he;have hv:=congrArg Fin.val he
    rw [header_val] at hv;split_ifs at hv <;> omega
  have btop:B 1701=ZeroPadding.pad C (frame bits):=by
    rw [bkeep _ outsideTop]
    exact (Function.update_of_ne (by decide) _ _).trans topT
  have last:=CloseoutRowsCircuitAppend.frame_focus frameSlots (by decide) C bits (out++natWord n) hb
    (Function.update H 1688 (out++natWord n).length) B (by
      intro i;fin_cases i
      · exact (Function.update_of_ne (by decide) _ _).trans topH
      · exact Function.update_self _ _ _
      · exact (Function.update_of_ne (by decide) _ _).trans (headerH 18)) (by
      intro i;fin_cases i
      · exact btop
      · exact bout
      · exact blog)
  obtain ⟨q,hq,qh,qt,qs⟩:=last
  obtain ⟨r,hr,rs,rh,rt⟩:=joined first top _ (4*bits.length+3) H
    (Function.update H 1688 (out++natWord n).length)
    (Function.update (Function.update H 1688 (out++natWord n).length) 1688
      (out++natWord n++frame bits).length)
    A B (Function.update B 1688 (out++natWord n++frame bits)) p q
    hp ph pt ps hq qh qt qs.le
  rw [Function.update_idem] at rh
  refine ⟨_,r,hr,rs,rh,rt,Function.update_self _ _ _,?_,?_,?_⟩
  · exact (Function.update_of_ne (by decide) _ _).trans blog
  · intro j hj
    have he:headerSlots j≠1688:=by
      intro h;have hv:=congrArg Fin.val h
      rw [header_val] at hv;split_ifs at hv <;> omega
    rw [Function.update_of_ne he]
    exact bsmall j hj
  · intro i hi
    have ho:i≠1688:=Ne.symm (hi 17)
    have hc:i≠639:=Ne.symm (hi 0)
    rw [Function.update_of_ne ho,bkeep i hi]
    exact Function.update_of_ne hc _ _

end NearCubicWires.RepairOrdinary.CloseoutRowsCircuitNativePrefix
