import Proof.CaseAnalysis.RecoveryRowPacketRun

/-! The original prototype writer runs in paid false backing, then rewinds
its actual output stream for the existing fifteen-field loader. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedRowPacketAppend
open LocalBitMultitape Composition RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def capacity (P : ℕ) (i : Fin 88):=if i=75 then P else 0
def padded (P : ℕ) (A : Fin 88→List Bool):=fun i=>ZeroPadding.pad (capacity P i) (A i)

theorem padded_output (P : ℕ) (A : Fin 88→List Bool) (bits : List Bool) :
    padded P (outputData A bits)=outputData A (ZeroPadding.pad P bits) := by
  funext i
  by_cases hi : i=75
  · subst i;rfl
  · simp only [padded,capacity,if_neg hi,outputData,Function.update_of_ne hi,ZeroPadding.pad_zero]

theorem Appends.padded_run {s fuel : ℕ} {p : Machine 88 s} {H : Fin 88→ℕ}
    {A : Fin 88→List Bool} {out result : List Bool} (h : Appends p fuel H A out result) (P : ℕ) :
    ∃ r,runFrom p fuel ⟨p.start,outputHeads H out,outputData A (ZeroPadding.pad P out)⟩=some r ∧
      r.steps≤fuel ∧ r.final.heads=outputHeads H result ∧
      r.final.tapes=outputData A (ZeroPadding.pad P result) := by
  obtain ⟨p0,pr,ps,ph,pt⟩:=h
  obtain ⟨r,rr,rf,rs,_⟩:=ZeroPadding.run_config p (capacity P) _ _ p0 pr
  have hi : ZeroPadding.config (capacity P) ⟨p.start,outputHeads H out,outputData A out⟩=
      (⟨p.start,outputHeads H out,outputData A (ZeroPadding.pad P out)⟩ : Configuration 88 s) := by
    apply configuration_ext
    · rfl
    · rfl
    · exact padded_output P A out
  rw [hi] at rr
  refine ⟨r,rr,rs.le.trans ps,?_,?_⟩
  · rw [rf];exact ph
  · rw [rf]
    change padded P p0.final.tapes=_
    rw [pt,padded_output]

def rewindSlots : Fin 3→Fin 88:=![75,76,73]
noncomputable def rewind:=RecoveryFocus.machine rewindSlots CompetitorRecordRewind.machine
noncomputable def ready:=Composition.machine machine rewind
def readyBudget (C F R count Q clauses B : ℕ):=budget C F R count Q clauses+1+(2*B+2)

theorem rewind_run (H : Fin 88→ℕ) (A : Fin 88→List Bool) (source : List Bool) (B pos : ℕ)
    (hHs : H 75=pos) (hHd : H 76=0) (hHl : H 73=0)
    (hAs : A 75=source) (hAd : A 76=List.replicate B true) (hAl : A 73=List.replicate B false)
    (hp : pos≤B) :
    ∃ r,runFrom rewind (2*B+2) ⟨rewind.start,H,A⟩=some r ∧ r.steps≤2*B+2 ∧
      r.final.heads=Function.update H 75 0 ∧ r.final.tapes=A := by
  obtain ⟨p,pr,ps,pf⟩:=RecoveryBoundedQueryRewind.padded_run source B pos hp
  obtain ⟨r,rr,_,rs,rh,rt,rkeep⟩:=RecoveryFocus.dock rewindSlots (by decide)
    CompetitorRecordRewind.machine _ H A (RecoveryBoundedQueryRewind.padded 0 source pos B)
    (by intro j;fin_cases j;exact hHs;exact hHd;exact hHl)
    (by intro j;fin_cases j;exact hAs;exact hAd;exact hAl) p pr
  refine ⟨r,rr,rs.le.trans ps.le,?_,?_⟩
  · funext i
    by_cases hi : ∃ j,rewindSlots j=i
    · obtain ⟨j,rfl⟩:=hi
      rw [rh j,pf]
      fin_cases j
      · rfl
      · change 0=Function.update H 75 0 76
        rw [Function.update_of_ne (by decide)]
        exact hHd.symm
      · change 0=Function.update H 75 0 73
        rw [Function.update_of_ne (by decide)]
        exact hHl.symm
    · rw [(rkeep i (by intro j he;exact hi ⟨j,he⟩)).1]
      exact (Function.update_of_ne (fun he=>hi ⟨0,he.symm⟩) _ _).symm
  · funext i
    by_cases hi : ∃ j,rewindSlots j=i
    · obtain ⟨j,rfl⟩:=hi
      rw [rt j,pf]
      fin_cases j;exact hAs.symm;exact hAd.symm;exact hAl.symm
    · exact (rkeep i (by intro j he;exact hi ⟨j,he⟩)).2

theorem ready_run (C D F L R count Q clauses B : ℕ)
    (H : Fin 88→ℕ) (A : Fin 88→List Bool)
    (h : Loaded (values C F R count Q clauses) B H A) (hfit : 6+F≤C)
    (hHs : H 75=0) (hHd : H 76=0)
    (hAd : A 76=List.replicate B true) (hAs : A 75=List.replicate B false)
    (bp : (RecoveryBoundedRowReload.word (RecoveryBoundedRowPrototype.fields C D F L R count Q clauses)).length≤B) :
    ∃ r,runFrom ready (readyBudget C F R count Q clauses B) ⟨ready.start,H,A⟩=some r ∧
      r.steps≤readyBudget C F R count Q clauses B ∧ r.final.heads=H ∧
      r.final.tapes=Function.update A 75
        (ZeroPadding.pad B (RecoveryBoundedRowReload.word
          (RecoveryBoundedRowPrototype.fields C D F L R count Q clauses))) := by
  let word:=RecoveryBoundedRowReload.word (RecoveryBoundedRowPrototype.fields C D F L R count Q clauses)
  have p0:=packet_run C D F L R count Q clauses B [] H A h hfit
  obtain ⟨p,pr,ps,ph,pt⟩:=p0.padded_run B
  have hInput : outputData A (ZeroPadding.pad B [])=A := by
    change Function.update A 75 (ZeroPadding.pad B [])=A
    have he : ZeroPadding.pad B []=List.replicate B false:=by simp [ZeroPadding.pad]
    rw [he,←hAs]
    exact Function.update_eq_self 75 A
  have hHeads : outputHeads H []=H := by
    change Function.update H 75 0=H
    rw [←hHs]
    exact Function.update_eq_self 75 H
  rw [hInput,hHeads] at pr
  rw [List.nil_append] at ph pt
  have keep (i : Fin 88) (hi : i≠75) : outputData A (ZeroPadding.pad B word) i=A i :=
    Function.update_of_ne hi _ _
  obtain ⟨q,qr,qs,qh,qt⟩:=rewind_run (outputHeads H word) (outputData A (ZeroPadding.pad B word))
    (ZeroPadding.pad B word) B word.length rfl
    (by rw [show outputHeads H word 76=H 76 from Function.update_of_ne (by decide) _ _];exact hHd)
    (by rw [show outputHeads H word 73=H 73 from Function.update_of_ne (by decide) _ _];exact h.scratch_head)
    rfl (by rw [keep 76 (by decide)];exact hAd) (by rw [keep 73 (by decide)];exact h.scratch_tape) bp
  have qr' : runFrom rewind (2*B+2) (restart p.final rewind.start)=some q := by
    change runFrom _ _ ⟨_,p.final.heads,p.final.tapes⟩=some q
    rw [ph,pt]
    exact qr
  have whole:=Composition.run_join machine rewind _ _ _ p q pr qr'
  refine ⟨joinedReceipt p q,whole,?_,?_,qt⟩
  · change p.steps+1+q.steps≤readyBudget C F R count Q clauses B
    unfold readyBudget
    omega
  · change q.final.heads=H
    rw [qh]
    change Function.update (Function.update H 75 word.length) 75 0=H
    rw [Function.update_idem,←hHs]
    exact Function.update_eq_self 75 H

end NearCubicWires.RepairOrdinary.RecoveryBoundedRowPacketAppend
