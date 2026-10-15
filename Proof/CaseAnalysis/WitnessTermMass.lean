import Proof.CaseAnalysis.WitnessTermReset

/-! A checked term's retained numerator and denominator are the actual
mass operands. No coefficient record is serialized, copied, or reparsed. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.TermMass
open LocalBitMultitape RecoveryRootRound SignedSortKey CompetitorSumFold
open CompetitorValidity (Estimate)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots (i : Fin 105) : Fin 826:=⟨if i.val<94 then 725+i.val else
  if i.val=94 then 690 else if i.val=95 then 693 else if i.val<103 then 723+i.val
  else if i.val=103 then 720 else 721,by split_ifs <;> omega⟩
theorem slots_injective : Function.Injective slots:=by
  intro i j h
  have hv:=congrArg Fin.val h
  dsimp only [slots] at hv
  split_ifs at hv <;> apply Fin.ext <;> omega
def tail (P : ℕ) (ambient : Fin 94→List Bool) : Fin 101→List Bool:=
  Fin.addCases (m:=94) (n:=7) (motive:=fun _=>List Bool) ambient (fun _=>List.replicate P false)
def data (P : ℕ) (terms : Fin 725→List Bool) (ambient : Fin 94→List Bool) : Fin 826→List Bool:=
  Fin.addCases (m:=725) (n:=101) (motive:=fun _=>List Bool) terms (tail P ambient)
def heads (position : ℕ) : Fin 826→ℕ:=
  Fin.addCases (m:=725) (n:=101) (motive:=fun _=>ℕ) (TermRead.heads position) (fun _=>0)
noncomputable def machine:=RecoveryFocus.machine slots MassReusableStep.machine

theorem native_slot (i : Fin 94) : slots (i.castAdd 11)=(i.castAdd 7).natAdd 725:=by
  apply Fin.ext
  change (if i.val<94 then 725+i.val else _) = 725+i.val
  rw [if_pos i.isLt]
theorem input_slots (P : ℕ) (terms : Fin 725→List Bool) (ambient : Fin 94→List Bool)
    (nb db : List Bool)
    (hn : terms 690=ZeroPadding.pad P (frame nb))
    (hd : terms 693=ZeroPadding.pad P (frame db))
    (hp : terms 720=List.replicate P true) (he : terms 721=List.replicate (P+1) false) :
    ∀ i,data P terms ambient (slots i)=MassOperands.input P ambient nb db i:=by
  intro i
  refine Fin.addCases (m:=94) (n:=11) ?_ ?_ i
  · intro j
    rw [native_slot,data,Fin.addCases_right,tail,Fin.addCases_left]
    exact (MassOperands.input_native P ambient nb db j).symm
  · intro j
    fin_cases j
    · exact hn.trans (MassOperands.input_num P ambient nb db).symm
    · exact hd.trans (MassOperands.input_den P ambient nb db).symm
    all_goals first
      | (change List.replicate P false=ZeroPadding.pad 0 (ZeroPadding.pad P []);simp [ZeroPadding.pad])
      | (change terms 720=ZeroPadding.pad 0 (List.replicate P true);rw [ZeroPadding.pad_zero];exact hp)
      | (change terms 721=ZeroPadding.pad 0 (List.replicate (P+1) false);rw [ZeroPadding.pad_zero];exact he)
theorem heads_slots (position : ℕ) (i : Fin 105) : heads position (slots i)=0:=by
  refine Fin.addCases (m:=94) (n:=11) ?_ ?_ i
  · intro j;rw [native_slot,heads,Fin.addCases_right]
  · intro j;fin_cases j <;> rfl
theorem data_outside (P : ℕ) (terms : Fin 725→List Bool) (a b : Fin 94→List Bool)
    (i : Fin 826) (hi : ∀ j,slots j≠i) : data P terms a i=data P terms b i:=by
  revert hi
  refine Fin.addCases (m:=725) (n:=101) ?_ ?_ i
  · intro j _;simp only [data,Fin.addCases_left]
  · intro j
    refine Fin.addCases (m:=94) (n:=7) ?_ ?_ j
    · intro k hk;exact (hk (k.castAdd 11) (native_slot k)).elim
    · intro k _;simp only [data,Fin.addCases_right,tail]

theorem mass_run (P B b position : ℕ) (q : ℚ) (a : Estimate) (source : List Bool)
    (terms : Fin 725→List Bool) (ambient : Fin 94→List Bool)
    (hstore : Store B a source ambient) (ha : a.Valid B) (hb : b≤B)
    (hn : q.num.natAbs<2^b) (hd : q.den<2^b)
    (hnum : terms 690=ZeroPadding.pad P (frame (binary b q.num.natAbs)))
    (hden : terms 693=ZeroPadding.pad P (frame (binary b q.den)))
    (hp : terms 720=List.replicate P true) (he : terms 721=List.replicate (P+1) false)
    (hcap : MassStep.budget B+1≤P)
    (hi : ∀ i,(MassPrepare.input ambient (binary b q.num.natAbs) (binary b q.den) i).length≤P) :
    ∃ next result,runFrom machine (MassReusableStep.budget P B)
      ⟨machine.start,heads position,data P terms ambient⟩=some result ∧
      result.steps≤MassReusableStep.budget P B ∧ result.final.heads=heads position ∧
      result.final.tapes=data P terms next ∧
      Store B (CompetitorRationalNumerators.add a (Mass.magnitude q)) source next:=by
  classical
  obtain ⟨next,⟨base,hr,ht,hh,hs⟩,hnext⟩:=MassOperands.step_run P B b q.num.natAbs q.den a source ambient
    hstore ha hb hn hd q.pos hcap hi
  obtain ⟨r,hrun,_rf,rs,rh,rt,keep⟩:=RecoveryFocus.dock slots slots_injective MassReusableStep.machine _
    (heads position) (data P terms ambient) _ (heads_slots position)
    (input_slots P terms ambient _ _ hnum hden hp he) base hr
  have out (i : Fin 105) : r.final.tapes (slots i)=MassOperands.input P next (binary b q.num.natAbs) (binary b q.den) i:=by
    rw [rt,ht]
  refine ⟨next,r,hrun,rs ▸ hs,?_,?_,hnext⟩
  · funext i
    by_cases hslot:∃ j,slots j=i
    · obtain ⟨j,rfl⟩:=hslot
      rw [rh,hh,heads_slots]
    · exact (keep i (by simpa using hslot)).1
  · funext i
    by_cases hslot:∃ j,slots j=i
    · obtain ⟨j,rfl⟩:=hslot
      exact (out j).trans (input_slots P terms next _ _ hnum hden hp he j).symm
    · exact ((keep i (by simpa using hslot)).2).trans
        (data_outside P terms ambient next i (by simpa using hslot))

end NearCubicWires.RepairOrdinary.CloseoutWitness.TermMass
