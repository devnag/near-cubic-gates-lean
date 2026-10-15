import Proof.CaseAnalysis.RowsCircuitArithmeticDock
import Proof.CaseAnalysis.RowsCircuitCapsRetained

/-! Full circuit resource tail: copy actual measured counters, recover the
original mode description, compare both original policy caps, and retain
all public fields. No policy-sized workspace is allocated. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsCircuitResourceRun
open LocalBitMultitape RecoveryRootRound CloseoutRowsGatePairHeads
open CloseoutRowsCircuitResourceCopies CloseoutRowsCircuitArithmeticDock
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def first (threshold : Bool):=Composition.machine CloseoutRowsCircuitResourceCopies.machine (stage threshold).2
noncomputable def machine (threshold : Bool):=Composition.machine (first threshold) (CloseoutRowsCircuitCaps.machine threshold)
def budget (threshold : Bool) (C D n wire L W : ℕ):=
  (6*C+14)+1+CloseoutRowsCircuitArithmeticDock.budget threshold D n+1+
    CloseoutRowsCircuitCaps.budget (amount threshold D n) wire L W

private theorem together {t a b : ℕ} (p : Machine t a) (q : Machine t b) (fp fq : ℕ)
    (H : Fin t → ℕ) (A B D : Fin t → List Bool) (hp : ReadyAt p fp H A B) (hq : ReadyAt q fq H B D) :
    ReadyAt (Composition.machine p q) (fp+1+fq) H A D:=by
  obtain ⟨r,hr,rt,rh,rs⟩:=hp
  obtain ⟨s,hs,st,sh,ss⟩:=hq
  have he:Composition.restart r.final q.start=RecoveryCalls.restarted q H B:=configuration_ext rfl rh rt
  rw [←he] at hs
  refine ⟨Composition.joinedReceipt r s,Composition.run_join p q _ _ _ r s hr hs,st,sh,?_⟩
  change r.steps+1+s.steps ≤ fp+1+fq
  omega

theorem resource_run (threshold : Bool) (C D n wire L W : ℕ)
    (H : Fin 1703 → ℕ) (A : Fin 1703 → List Bool)
    (hc : 32*(D+n+wire+3) ≤ C) (hn : threshold=true → n+1 ≤ D)
    (heads : ∀ i,(639 ≤ i.val ∧ i.val ≤ 664) ∨ i=1689 ∨ i=622 ∨ i=1690 ∨
      i=1694 ∨ i=1695 ∨ i=1698 ∨ i=1699 ∨ i=1700 → H i=0)
    (fresh : ∀ i,639 ≤ i.val ∧ i.val ≤ 664 → A i=List.replicate C false)
    (hD : A 1689=List.replicate D true) (hnat : A 622=List.replicate n true)
    (hw : A 1690=List.replicate wire true)
    (hL : A 1699=List.replicate L true) (hW : A 1698=List.replicate W true)
    (driver : A 1694=List.replicate C true) (log : A 1695=List.replicate (C+1) false) : ∃ out,
    ReadyAt (machine threshold) (budget threshold C D n wire L W) H A out ∧
      (readTapeBit (out 1700) 0=true ↔ amount threshold D n ≤ L ∧ wire ≤ W) ∧
      (∀ i,H i=0 → (A i).length ≤ C → (out i).length ≤ C) ∧
      (∀ i,(i.val<639 ∨ 665 ≤ i.val) → i≠1700 → out i=A i):=by
  let values:Fin 3 → ℕ:=![D,n,wire]
  have small:∀ i,values i ≤ C:=by intro i;fin_cases i <;> simp [values] <;> omega
  obtain ⟨r,hr,rh,rt,rs⟩:=copies_run C values A H small
    (by intro j i;apply heads;fin_cases j <;> fin_cases i <;> simp [CloseoutRowsCircuitResourceCopies.slots,sources,targets])
    (by intro i;fin_cases i;exact hD;exact hnat;exact hw)
    (by intro i;exact fresh _ (by fin_cases i <;> decide)) driver log
  let B:=bank C values A 3
  have copied:ReadyAt CloseoutRowsCircuitResourceCopies.machine (6*C+14) H A B:=⟨r,hr,rt,rh,rs.le⟩
  have bkeep (i : Fin 1703) (h0 : i≠639) (h1 : i≠640) (h2 : i≠660) : B i=A i:=by
    simp only [B,bank,h0,h1,h2,false_and,if_false]
  have bsmall (i : Fin 1703) (ha : (A i).length ≤ C) : (B i).length ≤ C:=by
    by_cases h0:i=639
    · subst i;simp [B,bank,values,ZeroPadding.pad_length];omega
    by_cases h1:i=640
    · subst i;simp [B,bank,values,ZeroPadding.pad_length];omega
    by_cases h2:i=660
    · subst i;simp [B,bank,values,ZeroPadding.pad_length];omega
    rw [bkeep i h0 h1 h2];exact ha
  obtain ⟨mid,arith,value,arSmall,arKeep⟩:=arithmetic_run threshold C D n H B (by omega) hn
    (by intro i hi;apply heads;exact Or.inl (by omega))
    (by simp [B,bank,values]) (by simp [B,bank,values]) (by
      intro i hi
      rw [bkeep i (by intro h;subst i;norm_num at hi) (by intro h;subst i;norm_num at hi)
        (by intro h;subst i;norm_num at hi)]
      exact fresh i (by omega))
  have keep (i : Fin 1703) (hi : 665 ≤ i.val) : mid i=A i:=by
    rw [arKeep i (Or.inr (by omega)),bkeep i (by intro h;subst i;norm_num at hi)
      (by intro h;subst i;norm_num at hi) (by intro h;subst i;norm_num at hi)]
  have remaining (i : Fin 1703) (hi : 655 ≤ i.val ∧ i.val ≤ 664) (hnw : i≠660) :
      mid i=List.replicate C false:=by
    rw [arKeep i (Or.inr hi.1),bkeep i (by intro h;subst i;norm_num at hi)
      (by intro h;subst i;norm_num at hi) hnw]
    exact fresh i (by omega)
  have wireValue:mid 660=ZeroPadding.pad C (List.replicate wire true):=by
    rw [arKeep 660 (Or.inr (by decide))]
    simp [B,bank,values]
  have amountBound:amount threshold D n ≤ D+n+2:=by
    unfold amount;split_ifs <;> have hd:=Nat.div_le_self (D-(n+1)) 2
    · omega
    · exact Nat.div_le_self _ _
  obtain ⟨out,caps,verdict,capW,capL,support,unchanged⟩:=CloseoutRowsCircuitCapsRetained.retained_run
    threshold C (amount threshold D n) wire L W H mid (by omega)
    (by intro i;apply heads;cases threshold <;> fin_cases i <;> simp [CloseoutRowsCircuitCaps.descriptionSlots])
    (by intro i;apply heads;fin_cases i <;> simp [CloseoutRowsCircuitCaps.wireSlots])
    (heads 1700 (by simp))
    (by
      intro i;fin_cases i
      · exact value
      · change mid 1699=ZeroPadding.pad 0 (List.replicate L true)
        rw [ZeroPadding.pad_zero];exact (keep 1699 (by decide)).trans hL
      · change mid 656=ZeroPadding.pad C []
        simpa [ZeroPadding.pad] using remaining 656 (by decide) (by decide)
      · change mid 657=ZeroPadding.pad C []
        simpa [ZeroPadding.pad] using remaining 657 (by decide) (by decide)
      · change mid 658=ZeroPadding.pad C []
        simpa [ZeroPadding.pad] using remaining 658 (by decide) (by decide)
      · change mid 659=ZeroPadding.pad C []
        simpa [ZeroPadding.pad] using remaining 659 (by decide) (by decide)
)
    (by
      intro i;fin_cases i
      · exact wireValue
      · change mid 1698=ZeroPadding.pad 0 (List.replicate W true)
        rw [ZeroPadding.pad_zero];exact (keep 1698 (by decide)).trans hW
      · change mid 661=ZeroPadding.pad C []
        simpa [ZeroPadding.pad] using remaining 661 (by decide) (by decide)
      · change mid 662=ZeroPadding.pad C []
        simpa [ZeroPadding.pad] using remaining 662 (by decide) (by decide)
      · change mid 663=ZeroPadding.pad C []
        simpa [ZeroPadding.pad] using remaining 663 (by decide) (by decide)
      · change mid 664=ZeroPadding.pad C []
        simpa [ZeroPadding.pad] using remaining 664 (by decide) (by decide)
)
  have all:=together (first threshold) (CloseoutRowsCircuitCaps.machine threshold) _ _ H _ _ _
    (together CloseoutRowsCircuitResourceCopies.machine (stage threshold).2 _ _ H _ _ _ copied arith) caps
  refine ⟨out,all,verdict,?_,?_⟩
  · intro i hi ha
    exact support i hi (arSmall i (bsmall i ha))
  · intro i hi hflag
    by_cases hWslot:i=1698
    · subst i;exact capW.trans (keep 1698 (by decide))
    by_cases hLslot:i=1699
    · subst i;exact capL.trans (keep 1699 (by decide))
    rw [unchanged i (by
      intro j h
      cases threshold <;> fin_cases j <;> simp [CloseoutRowsCircuitCaps.descriptionSlots] at h
      all_goals first | (exact hLslot h.symm) | (have hv:=congrArg Fin.val h;omega))
      (by
        intro j h;fin_cases j <;> simp [CloseoutRowsCircuitCaps.wireSlots] at h
        all_goals first | (exact hWslot h.symm) | (have hv:=congrArg Fin.val h;omega))
      (by
        intro j h;fin_cases j <;> simp [CloseoutRowsCircuitCaps.flagSlots] at h
        all_goals first | (exact hflag h.symm) | (have hv:=congrArg Fin.val h;omega))]
    rw [arKeep i (by omega),bkeep i (by intro h;subst i;norm_num at hi)
      (by intro h;subst i;norm_num at hi) (by intro h;subst i;norm_num at hi)]

end NearCubicWires.RepairOrdinary.CloseoutRowsCircuitResourceRun
