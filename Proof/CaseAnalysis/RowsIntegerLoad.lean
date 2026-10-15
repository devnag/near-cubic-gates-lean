import Proof.CaseAnalysis.RowsIntegerRoundLayout

/-! The shared frame loader consumes one actual canonical integer field.
Its target and log are the paid reusable integer workspace. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsIntegerRound
open LocalBitMultitape RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def loader:=RecoveryFocus.machine loadSlots FrameLoad.machine
def loadPads (cap : ℕ) : Fin 3→ℕ:=![0,cap,cap]

theorem padded_load_run (cap : ℕ) (bits pre tail : List Bool)
    (hcap : 2*bits.length+1 ≤ cap) : ∃ p,
    runFrom FrameLoad.machine (4*bits.length+3)
      (ZeroPadding.config (loadPads cap) (FrameLoad.scan 0 (pre++frame bits++tail) pre.length [] []))=some p ∧
      p.steps=4*bits.length+3 ∧
      (∀ i : Fin 3,p.final.heads i=![pre.length+2*bits.length+1,0,0] i) ∧
      (∀ i : Fin 3,p.final.tapes i=![pre++frame bits++tail,ZeroPadding.pad cap (frame bits),List.replicate cap false] i):=by
  obtain ⟨r,hr,rf,rs,_⟩:=FrameLoad.load_run pre bits tail [] (by simp)
  obtain ⟨p,hp,pf,ps,_⟩:=ZeroPadding.run_config FrameLoad.machine (loadPads cap) _ _ r hr
  refine ⟨p,hp,ps.trans rs,?_,?_⟩
  · intro i
    rw [pf,rf]
    rfl
  · intro i
    rw [pf,rf]
    fin_cases i
    · exact ZeroPadding.pad_zero _
    · rfl
    · change ZeroPadding.pad cap (List.replicate (2*bits.length+1) false)=List.replicate cap false
      rw [Rewind.Workspace.pad_zeros,Nat.max_eq_left hcap]

theorem load_run (cap : ℕ) (bits out pre tail : List Bool) (flag : Bool)
    (hcap : 2*bits.length+1 ≤ cap) : ∃ result,
    runFrom loader (4*bits.length+3)
      (cfg loader.start cap pre.length [] out (pre++frame bits++tail) flag)=some result ∧
      result.steps=4*bits.length+3 ∧
      result.final.heads=heads out (pre.length+2*bits.length+1) ∧
      result.final.tapes=data cap bits out (pre++frame bits++tail) flag:=by
  let source:=pre++frame bits++tail
  obtain ⟨p,hp,ps,pheads,ptapes⟩:=padded_load_run cap bits pre tail hcap
  obtain ⟨a,ha,_,asteps,ah,atape,keep⟩:=RecoveryFocus.dock loadSlots (by decide) FrameLoad.machine _
    (heads out pre.length) (data cap [] out source flag) _
    (by intro i;fin_cases i <;> rfl)
    (by
      intro i
      fin_cases i
      · change source=ZeroPadding.pad 0 source
        exact (ZeroPadding.pad_zero source).symm
      · change ZeroPadding.pad cap (frame [])=ZeroPadding.pad cap []
        rw [CloseoutRowsIntegerReady.pad_empty_frame cap (by omega)]
        simp [ZeroPadding.pad]
      · change List.replicate cap false=ZeroPadding.pad cap []
        simp [ZeroPadding.pad]) p hp
  refine ⟨a,ha,asteps.trans ps,?_,?_⟩
  · funext i
    by_cases h0:i=217
    · subst i
      exact (ah 0).trans (pheads 0)
    by_cases h1:i=0
    · subst i
      exact (ah 1).trans (pheads 1)
    by_cases h2:i=218
    · subst i
      exact (ah 2).trans (pheads 2)
    rw [(keep i (by
      intro j;fin_cases j <;> first | exact Ne.symm h0 | exact Ne.symm h1 | exact Ne.symm h2)).1]
    simp only [heads,if_neg h0]
  · funext i
    by_cases h0:i=217
    · subst i
      exact (atape 0).trans (ptapes 0)
    by_cases h1:i=0
    · subst i
      have ht:data cap bits out source flag 0=ZeroPadding.pad cap (frame bits):=rfl
      exact (atape 1).trans ((ptapes 1).trans ht.symm)
    by_cases h2:i=218
    · subst i
      exact (atape 2).trans (ptapes 2)
    exact ((keep i (by
      intro j;fin_cases j <;> first | exact Ne.symm h0 | exact Ne.symm h1 | exact Ne.symm h2)).2).trans
      (data_bits_other cap [] bits out source flag i h1)

end NearCubicWires.RepairOrdinary.CloseoutRowsIntegerRound
