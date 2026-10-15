import Proof.CaseAnalysis.RecoveryAddressRestore

/-! A retained bank for the literal address children. The same unary
compiler works beside the physical address cursor and outer OR stack. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedAddress
open LocalBitMultitape SourceInterfaces RepairRepresentation
open BoundedOracleStructuralCircuit FinitePredicateCircuit
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def heads (out stack : List Bool) (pos : ℕ) : Fin 40→ℕ:=
  Fin.addCases (m:=37) (n:=3) (motive:=fun _=>ℕ) (RecoveryBoundedUnaryReuse.heads out) ![pos,stack.length,0]
def data (index base C D value limit : ℕ) (flag : Bool) (out source stack : List Bool)
    (retained : ℕ) : Fin 40→List Bool:=
  Fin.addCases (m:=37) (n:=3) (motive:=fun _=>List Bool)
    (RecoveryBoundedUnaryReuse.data index base C D value limit flag out) ![source,stack,List.replicate retained true]
noncomputable def unary:=TapeEmbedding.machine 3 RecoveryBoundedUnaryReuse.machine
def writeSlot : Fin 1→Fin 40:=fun _=>20
noncomputable def seed:=RecoveryFocus.machine writeSlot (HierarchyFixedWord.raw RecoveryBoundedSelectorFinish.falseBits)

theorem unary_run {n bound : ℕ} (b : BooleanDAGBuilder (descriptionWidth n bound))
    (row : Fin (bound+1)) (start limit value W C D pos retained : ℕ) (out source stack : List Bool)
    (hblock : start+limit ≤ rowWidth n bound)
    (hi : RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start+limit ≤ W)
    (hp : b.nodes.length+3*limit ≤ W) (hC : 16384*(W+1)^2 ≤ C)
    (hD : RecoveryBoundedNativeUnaryJoin.budget limit C ≤ D) :
    let compiled:=compileExpr b (unaryEqualsExpr row start limit value hblock)
    let emitted:=out++compiled.extension.suffix.flatMap PCPPRequestNodeSchema.native
    ∃ r,runFrom unary (RecoveryBoundedUnaryReuse.budget limit C)
      ⟨unary.start,heads out stack pos,
        data (RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start) b.nodes.length C D value limit false out source stack retained⟩=some r ∧
      r.steps ≤ RecoveryBoundedUnaryReuse.budget limit C ∧ r.final.heads=heads emitted stack pos ∧
      r.final.tapes=data 0 compiled.output.val C D value limit
        (RecoveryBoundedUnaryReuse.forward (n:=n) row start b.nodes.length value limit out).flag emitted source stack retained := by
  obtain ⟨p,hpRun,ps,ph,pt⟩:=RecoveryBoundedUnaryReuse.literal_run b row start limit value W C D out hblock hi hp hC hD
  let eh : Fin 3→ℕ:=![pos,stack.length,0]
  let et : Fin 3→List Bool:=![source,stack,List.replicate retained true]
  let r:=TapeEmbedding.receipt eh et p
  have hr:=TapeEmbedding.run_embed RecoveryBoundedUnaryReuse.machine eh et _ _ p hpRun
  have he : TapeEmbedding.config eh et (RecoveryBoundedUnaryReuse.entry (n:=n) row start b.nodes.length C D value limit out)=
      (⟨unary.start,heads out stack pos,
        data (RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start) b.nodes.length C D value limit false out source stack retained⟩ : Configuration 40 _) := by
    apply configuration_ext
    · rfl
    · change Fin.addCases (m:=37) (n:=3) (motive:=fun _=>ℕ)
        (RecoveryBoundedUnaryReuse.entry (n:=n) row start b.nodes.length C D value limit out).heads eh=_
      rw [RecoveryBoundedUnaryReuse.entry_heads]
      rfl
    · change Fin.addCases (m:=37) (n:=3) (motive:=fun _=>List Bool)
        (RecoveryBoundedUnaryReuse.entry (n:=n) row start b.nodes.length C D value limit out).tapes et=_
      rw [RecoveryBoundedUnaryReuse.entry_tapes]
      rfl
  rw [he] at hr
  refine ⟨r,hr,ps,?_,?_⟩
  · change Fin.addCases (m:=37) (n:=3) (motive:=fun _=>ℕ) p.final.heads eh=_
    rw [ph]
    rfl
  · change Fin.addCases (m:=37) (n:=3) (motive:=fun _=>List Bool) p.final.tapes et=_
    rw [pt]
    rfl

theorem seed_run (index base C D value limit pos retained : ℕ) (out source stack : List Bool) :
    ∃ r,runFrom seed RecoveryBoundedSelectorFinish.falseBits.length
      ⟨seed.start,heads out stack pos,data index base C D value limit false out source stack retained⟩=some r ∧
      r.steps=RecoveryBoundedSelectorFinish.falseBits.length ∧
      r.final.heads=heads (out++RecoveryBoundedSelectorFinish.falseBits) stack pos ∧
      r.final.tapes=data index base C D value limit false (out++RecoveryBoundedSelectorFinish.falseBits) source stack retained := by
  let bits:=RecoveryBoundedSelectorFinish.falseBits
  obtain ⟨a,ha,af,as⟩:=RepairSource.ProjectionNormalization.Constants.write_run bits out
  obtain ⟨r,hr,_,rs,rh,rt,rkeep⟩:=RecoveryFocus.dock writeSlot (by decide) (HierarchyFixedWord.raw bits) _
    (heads out stack pos) (data index base C D value limit false out source stack retained)
    (RepairSource.ProjectionNormalization.Constants.cfg bits out 0 (by omega))
    (by intro j;fin_cases j;rfl) (by intro j;fin_cases j;change out=out++bits.take 0;simp) a ha
  refine ⟨r,hr,rs.trans as,?_,?_⟩
  · funext i
    by_cases hi : i=20
    · subst i
      have h:=rh 0
      change r.final.heads 20=a.final.heads 0 at h
      rw [h,af]
      change out.length+bits.length=(out++bits).length
      simp only [List.length_append]
    · rw [(rkeep i (by intro j;fin_cases j;exact fun h=>hi h.symm)).1]
      fin_cases i
      all_goals first | exact False.elim (hi rfl) | rfl
  · have hresult:=HierarchyWidth.install_eq writeSlot (by decide)
      (data index base C D value limit false out source stack retained) r.final.tapes (fun _=>out++bits)
      (by intro j;rw [rt j,af];fin_cases j;rfl) (by intro i hi;exact (rkeep i hi).2)
    rw [←hresult]
    apply HierarchyWidth.install_eq writeSlot (by decide)
    · intro j;fin_cases j;rfl
    · intro i hi
      have h:=hi 0
      fin_cases i
      all_goals first | exact False.elim (h rfl) | rfl

end NearCubicWires.RepairOrdinary.RecoveryBoundedAddress
