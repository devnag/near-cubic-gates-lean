import Proof.CaseAnalysis.WitnessNodeRoundLayout

/-! The existing frame loader advances the actual canonical-node stream and
fills the reused node input. Its bounded copy and local reset are both paid. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.NodeRound
open LocalBitMultitape RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def loader:=RecoveryFocus.machine loadSlots FrameLoad.machine
def loadPads (cap : ℕ) : Fin 3 → ℕ:=![0,cap,cap]

theorem load_run (cap w : ℕ) (left right bits out pre tail : List Bool) (flag : Bool)
    (hcap : 2*bits.length+1 ≤ cap) : ∃ result,
    runFrom loader (4*bits.length+3)
      (cfg loader.start cap w pre.length left right [] out (pre++frame bits++tail) flag)=some result ∧
      result.steps=4*bits.length+3 ∧
      result.final.heads=heads out (pre.length+2*bits.length+1) ∧
      result.final.tapes=data cap w left right bits out (pre++frame bits++tail) flag:=by
  let source:=pre++frame bits++tail
  obtain ⟨r,hr,rf,rs,_⟩:=FrameLoad.load_run pre bits tail [] (by simp)
  obtain ⟨p,hp,pf,ps,_⟩:=ZeroPadding.run_config FrameLoad.machine (loadPads cap) _ _ r hr
  have pheads (i : Fin 3) : p.final.heads i=![pre.length+2*bits.length+1,0,0] i:=by
    rw [pf,rf]
    rfl
  have ptapes (i : Fin 3) : p.final.tapes i=![source,ZeroPadding.pad cap (frame bits),List.replicate cap false] i:=by
    rw [pf,rf]
    fin_cases i
    · exact ZeroPadding.pad_zero source
    · rfl
    · exact PCPSerializerReuse.pad_zeros cap (2*bits.length+1) hcap
  obtain ⟨a,ha,_,asteps,ah,atape,keep⟩:=RecoveryFocus.dock loadSlots (by decide) FrameLoad.machine _
    (heads out pre.length) (data cap w left right [] out source flag) _
    (by intro i;fin_cases i <;> rfl)
    (by
      intro i
      fin_cases i
      · change source=ZeroPadding.pad 0 source
        exact (ZeroPadding.pad_zero source).symm
      · change (NodeReady.entry cap w left right [] out).tapes 1=ZeroPadding.pad cap []
        rw [NodeReady.entry_blank _ _ _ _ _ (by omega) 1 (by decide) (by intro j;fin_cases j <;> decide)]
        simp [ZeroPadding.pad]
      · change List.replicate cap false=ZeroPadding.pad cap []
        simp [ZeroPadding.pad]) p hp
  refine ⟨a,ha,asteps.trans (ps.trans rs),?_,?_⟩
  · funext i
    by_cases h0:i=751
    · subst i
      exact (ah 0).trans (pheads 0)
    by_cases h1:i=1
    · subst i
      exact (ah 1).trans (pheads 1)
    by_cases h2:i=752
    · subst i
      exact (ah 2).trans (pheads 2)
    rw [(keep i (by
      intro j;fin_cases j <;> first | exact Ne.symm h0 | exact Ne.symm h1 | exact Ne.symm h2)).1]
    simp only [heads,if_neg h0]
  · funext i
    by_cases h0:i=751
    · subst i
      exact (atape 0).trans (ptapes 0)
    by_cases h1:i=1
    · subst i
      have ht: data cap w left right bits out source flag 1=ZeroPadding.pad cap (frame bits):=
        NodeReady.entry_source cap w left right bits out
      exact (atape 1).trans ((ptapes 1).trans ht.symm)
    by_cases h2:i=752
    · subst i
      exact (atape 2).trans (ptapes 2)
    exact ((keep i (by
      intro j;fin_cases j <;> first | exact Ne.symm h0 | exact Ne.symm h1 | exact Ne.symm h2)).2).trans
      (data_bits_other cap w left right [] bits out source flag i h1)

end NearCubicWires.RepairOrdinary.CloseoutWitness.NodeRound
