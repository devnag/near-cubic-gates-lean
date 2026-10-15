import Proof.CaseAnalysis.RecoverySelectorForwardMeaning

/-! Physically append the original false seed at the returned selector cursor.
All retained fields and the outer repeat sentinel remain available. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedSelectorFinish
open LocalBitMultitape SourceInterfaces RepairRepresentation RecoveryRootRound
open RecoveryBoundedSelectorLoop
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def heads (out stack : List Bool) (pos : ℕ) : Fin 43→ℕ :=
  Fin.addCases (m:=42) (n:=1) (motive:=fun _=>ℕ) (stateHeads out stack pos) (fun _=>1)
def data (index base C D value limit total : ℕ) (out source stack : List Bool) : Fin 43→List Bool :=
  Fin.addCases (m:=42) (n:=1) (motive:=fun _=>List Bool)
    (stateData index base C D value limit out source stack) (fun _=>RepairSource.VerifierDecoding.CompareMachine.word total)
def falseBits:=natWord 0++natWord 0++natWord 0
def writeSlot : Fin 1→Fin 43:=fun _=>20
noncomputable def seed:=RecoveryFocus.machine writeSlot (HierarchyFixedWord.raw falseBits)

theorem seed_run (index base C D value limit total pos : ℕ) (out source stack : List Bool) :
    ∃ r,runFrom seed falseBits.length
      ⟨seed.start,heads out stack pos,data index base C D value limit total out source stack⟩=some r ∧
      r.steps=falseBits.length ∧
      r.final.heads=heads (out++falseBits) stack pos ∧
      r.final.tapes=data index base C D value limit total (out++falseBits) source stack := by
  obtain ⟨a,ha,af,as⟩:=RepairSource.ProjectionNormalization.Constants.write_run falseBits out
  obtain ⟨r,hr,_,rs,rh,rt,rkeep⟩:=RecoveryFocus.dock writeSlot (by decide) (HierarchyFixedWord.raw falseBits) _
    (heads out stack pos) (data index base C D value limit total out source stack)
    (RepairSource.ProjectionNormalization.Constants.cfg falseBits out 0 (by omega))
    (by intro j; fin_cases j; rfl) (by intro j; fin_cases j; change out=out++falseBits.take 0; simp) a ha
  refine ⟨r,hr,rs.trans as,?_,?_⟩
  · funext i
    by_cases hi : i=20
    · subst i
      have h:=rh 0
      change r.final.heads 20=a.final.heads 0 at h
      rw [h,af]
      change out.length+falseBits.length=(out++falseBits).length
      simp only [List.length_append]
    · rw [(rkeep i (by intro j; fin_cases j; exact fun h=>hi h.symm)).1]
      fin_cases i
      all_goals first | exact False.elim (hi rfl) | rfl
  · have hresult:=HierarchyWidth.install_eq writeSlot (by decide)
      (data index base C D value limit total out source stack) r.final.tapes (fun _=>out++falseBits)
      (by intro j; rw [rt j,af]; fin_cases j; rfl) (by intro i hi; exact (rkeep i hi).2)
    rw [←hresult]
    apply HierarchyWidth.install_eq writeSlot (by decide)
    · intro j; fin_cases j; rfl
    · intro i hi
      have h:=hi 0
      fin_cases i
      all_goals first | exact False.elim (h rfl) | rfl

theorem forward_heads {n bound : ℕ} (row : Fin (bound+1)) (start limit W D total : ℕ)
    (a : RecoveryBoundedSelectorLoop.State) (source : List Bool) :
    (configuration (n:=n) 3 row start limit W D a source total 1).heads=heads a.out a.stack a.skipped.length := rfl

theorem forward_tapes {n bound : ℕ} (row : Fin (bound+1)) (start limit W D total : ℕ)
    (a : RecoveryBoundedSelectorLoop.State) (source : List Bool) :
    (configuration (n:=n) 3 row start limit W D a source total 1).tapes=
      data (RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start) a.position (capacity W) D a.value limit total
        a.out source a.stack := rfl

end NearCubicWires.RepairOrdinary.RecoveryBoundedSelectorFinish
