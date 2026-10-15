import Proof.PCP.PCPPRequestSource

/-! The native emitter reads one actual three-field oracle node into bounded
unary indices. The source stream is consumed once and retained exactly. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeNodeRead
open LocalBitMultitape RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots (i : Fin 3) (j : Fin 11) : Fin 31 :=
  if j=0 then 0 else ⟨j.val+10*i.val,by omega⟩
def outputSlot (i : Fin 3) := slots i 10
noncomputable def field (i : Fin 3) := RecoveryFocus.machine (slots i) PCPPQueryNatural.machine
noncomputable def machine := Composition.machine (Composition.machine (field 0) (field 1)) (field 2)
def source (pre tail : List Bool) (a b c : ℕ) := pre++natWord a++natWord b++natWord c++tail
def budget (a b c : ℕ) := PCPPQueryNatural.budget a+1+PCPPQueryNatural.budget b+1+PCPPQueryNatural.budget c
noncomputable def entry (word : List Bool) (pos : ℕ) :=
  (⟨machine.start,(fun i => if i=0 then pos else 0),(fun i => if i=0 then word else [])⟩ : Configuration 31 _)

theorem slots_injective (i : Fin 3) : Function.Injective (slots i) := by
  intro j k h
  apply Fin.ext
  have hv := congrArg Fin.val h
  simp only [slots] at hv
  split_ifs at hv <;> simp_all only [Fin.ext_iff]
  all_goals omega

theorem slots_nonzero (i : Fin 3) (j : Fin 11) (hj : j≠0) : slots i j≠0 := by
  intro h
  have hv := congrArg Fin.val h
  have hjv : j.val≠0 := fun he => hj (Fin.ext he)
  simp only [slots,hj,ite_false] at hv
  change j.val+10*i.val=0 at hv
  omega

theorem other_bank (i k : Fin 3) (hik : i≠k) (j : Fin 11) (hj : j≠0) :
    RecoveryFocus.pick (slots i) (slots k j)=none := by
  have hn : ¬∃ l,slots i l=slots k j := by
    rintro ⟨l,hl⟩
    have hjv : j.val≠0 := fun h => hj (Fin.ext h)
    have hikv : i.val≠k.val := fun h => hik (Fin.ext h)
    by_cases hl0 : l=0
    · subst l
      exact slots_nonzero k j hj hl.symm
    · have hlv : l.val≠0 := fun h => hl0 (Fin.ext h)
      have hv := congrArg Fin.val hl
      simp only [slots,hl0,hj,ite_false] at hv
      change l.val+10*i.val=j.val+10*k.val at hv
      have hlt := l.isLt
      have hjt := j.isLt
      omega
  simp only [RecoveryFocus.pick,dif_neg hn]

theorem stage_run {z : ℕ} (ambient : Configuration 31 z) (i : Fin 3)
    (pre tail : List Bool) (n : ℕ)
    (hsource : ambient.tapes 0=pre++natWord n++tail) (hpos : ambient.heads 0=pre.length)
    (hfresh : ∀ j : Fin 11,j≠0 → ambient.tapes (slots i j)=[] ∧ ambient.heads (slots i j)=0) :
    ∃ r,runFrom (field i) (PCPPQueryNatural.budget n)
      (Composition.restart ambient (field i).start)=some r ∧
      r.steps≤PCPPQueryNatural.budget n ∧
      r.final.tapes (outputSlot i)=UnaryTemplate.tape n ∧ r.final.heads (outputSlot i)=1 ∧
      r.final.tapes 0=pre++natWord n++tail ∧ r.final.heads 0=pre.length+(natWord n).length ∧
      (∀ k : Fin 3,i≠k → ∀ j : Fin 11,j≠0 →
        r.final.tapes (slots k j)=ambient.tapes (slots k j) ∧ r.final.heads (slots k j)=ambient.heads (slots k j)) := by
  obtain ⟨r,hr,rs,r0,rh0,rt,rh,rkeep⟩ := PCPPQueryNatural.focus_run
    (slots i) (slots_injective i) ambient pre tail n
    (by intro j; by_cases hj : j=0
        · subst j; exact hsource
        · rw [if_neg hj]; exact (hfresh j hj).1)
    (by intro j; by_cases hj : j=0
        · subst j; exact hpos
        · rw [if_neg hj]; exact (hfresh j hj).2)
  refine ⟨r,hr,rs,rt,rh,r0,?_,?_⟩
  · have hs0 : slots i 0=0 := by simp [slots]
    rw [hs0] at rh0
    simpa only [DecompositionSource.natWord_length,Nat.add_assoc] using rh0
  · intro k hik j hj
    exact rkeep _ (other_bank i k hik j hj)

theorem cold_run (pre tail : List Bool) (a b c : ℕ) :
    ∃ r,runFrom machine (budget a b c) (entry (source pre tail a b c) pre.length)=some r ∧
      r.steps≤budget a b c ∧ r.final.tapes 0=source pre tail a b c ∧
      r.final.heads 0=pre.length+(natWord a).length+(natWord b).length+(natWord c).length ∧
      (∀ i : Fin 3,r.final.tapes (outputSlot i)=UnaryTemplate.tape (![a,b,c] i)) ∧
      (∀ i : Fin 3,r.final.heads (outputSlot i)=1) := by
  let initial := entry (source pre tail a b c) pre.length
  have fresh (i : Fin 3) (j : Fin 11) (hj : j≠0) :
      initial.tapes (slots i j)=[] ∧ initial.heads (slots i j)=0 := by
    have h := slots_nonzero i j hj
    simp only [initial,entry,h,ite_false,and_self]
  obtain ⟨first,hfirst,fs,fout,foh,f0,fh0,fkeep⟩ := stage_run initial 0 pre
    (natWord b++natWord c++tail) a (by simp [initial,entry,source,List.append_assoc])
    (by rfl) (fresh 0)
  obtain ⟨second,hsecond,ss,sout,soh,s0,sh0,skeep⟩ := stage_run first.final 1
    (pre++natWord a) (natWord c++tail) b (by simpa only [List.append_assoc] using f0)
    (by simpa only [List.length_append] using fh0) (by
      intro j hj
      exact ⟨((fkeep 1 (by decide) j hj).1).trans (fresh 1 j hj).1,
        ((fkeep 1 (by decide) j hj).2).trans (fresh 1 j hj).2⟩)
  obtain ⟨third,hthird,ts,tout,toh,t0,th0,tkeep⟩ := stage_run second.final 2
    (pre++natWord a++natWord b) tail c (by simpa only [List.append_assoc] using s0)
    (by simpa only [List.length_append] using sh0) (by
      intro j hj
      exact ⟨((skeep 2 (by decide) j hj).1).trans
          (((fkeep 2 (by decide) j hj).1).trans (fresh 2 j hj).1),
        ((skeep 2 (by decide) j hj).2).trans
          (((fkeep 2 (by decide) j hj).2).trans (fresh 2 j hj).2)⟩)
  obtain ⟨result,hresult,rheads,rtapes,rsteps⟩ := PCPPRequestNodeFields.join_three_run
    (field 0) (field 1) (field 2) _ _ _ _ first second third hfirst hsecond hthird
  refine ⟨result,hresult,?_,?_,?_,?_,?_⟩
  · rw [rsteps]; unfold budget; omega
  · rw [rtapes]; exact t0
  · rw [rheads]; simpa only [List.length_append] using th0
  · intro i
    rw [rtapes]
    fin_cases i
    · change third.final.tapes (slots 0 10)=_
      rw [(tkeep 0 (by decide) 10 (by decide)).1,(skeep 0 (by decide) 10 (by decide)).1]
      exact fout
    · change third.final.tapes (slots 1 10)=_
      rw [(tkeep 1 (by decide) 10 (by decide)).1]
      exact sout
    · exact tout
  · intro i
    rw [rheads]
    fin_cases i
    · change third.final.heads (slots 0 10)=1
      rw [(tkeep 0 (by decide) 10 (by decide)).2,(skeep 0 (by decide) 10 (by decide)).2]
      exact foh
    · change third.final.heads (slots 1 10)=1
      rw [(tkeep 1 (by decide) 10 (by decide)).2]
      exact soh
    · exact toh

end NearCubicWires.RepairOrdinary.PCPPNativeNodeRead
