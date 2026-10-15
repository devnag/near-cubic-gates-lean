import Proof.Hierarchy.CompetitorSameBucketKeyWorkspace

/-! One fixed workspace joins copied-record classification and signed-key
appending. Tape34 is the sole growing output; supplied scalar fields are
bounded local tapes. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSameBucketPairEmit
open LocalBitMultitape SignedSortKey MatrixScoreBatch RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def extras (cap p k : ℕ) (coefficient : ℤ) (out : List Bool) : Fin 5 → List Bool :=
  ![ZeroPadding.pad cap (frame (signMagnitude p coefficient)),ZeroPadding.pad cap (frame (List.replicate (p+1) false)),
    ZeroPadding.pad cap (frame (binary k 0)),out,List.replicate cap false]
def extraHeads (out : List Bool) : Fin 5 → ℕ := ![0,0,0,out.length,0]
def heads (out : List Bool) : Fin 36 → ℕ := fun i => if i=34 then out.length else 0

def cfg {z : ℕ} (q : Fin z) (work : Fin 31 → List Bool) (cap p k : ℕ) (coefficient : ℤ) (out : List Bool) : Configuration 36 z :=
  ⟨q,heads out,Fin.addCases (m := 31) (n := 5) (motive := fun _ => List Bool) work (extras cap p k coefficient out)⟩
noncomputable def classify := TapeEmbedding.machine 5 CompetitorSameBucketPairGuard.machine

def appendSlots : Fin 8 → Fin 36 := ![31,32,22,7,10,33,34,35]
theorem append_injective : Function.Injective appendSlots := by decide
noncomputable def append := RecoveryFocus.machine appendSlots CompetitorSameBucketKeyAppend.machine

theorem embed (work : Fin 31 → List Bool) (cap p k : ℕ) (coefficient : ℤ) (out : List Bool)
    {s : ℕ} (q : Fin s) :
    TapeEmbedding.config (extraHeads out) (extras cap p k coefficient out)
      (⟨q,fun _ => 0,work⟩ : Configuration 31 s)=cfg q work cap p k coefficient out := by
  apply configuration_ext
  · rfl
  · funext i
    fin_cases i <;> rfl
  · rfl

theorem classify_present (cap s k u p : ℕ) (sa sb coefficient : ℤ) (a b ra rb : ℕ) (out : List Bool)
    (hc : 30*(k+s+2)≤cap) (hu : u<2^k) (ha : a<2^k) (hb : b<2^k)
    (hra : ra<2^(k+s+1)) (hrb : rb<2^(k+s+1)) :
    ∃ r,runFrom classify (CompetitorSameBucketPairGuard.budget s k)
        (cfg classify.start (CompetitorSameBucketPairFields.data cap s k u sa sb a b ra rb 0) cap p k coefficient out)=some r ∧
      r.final.heads=heads out ∧
      r.final.tapes=(cfg classify.start (CompetitorSameBucketPairFields.data cap s k u sa sb a b ra rb 3) cap p k coefficient out).tapes ∧
      r.steps≤CompetitorSameBucketPairGuard.budget s k := by
  obtain ⟨base,hb,bt,bh,bs⟩ := CompetitorSameBucketPairGuard.present_ready cap s k u sa sb a b ra rb hc hu ha hb hra hrb
  have hr := TapeEmbedding.run_embed CompetitorSameBucketPairGuard.machine (extraHeads out) (extras cap p k coefficient out) _ _ base hb
  have hi : TapeEmbedding.config (extraHeads out) (extras cap p k coefficient out)
      (initialConfiguration CompetitorSameBucketPairGuard.machine (CompetitorSameBucketPairFields.data cap s k u sa sb a b ra rb 0))=
      cfg classify.start (CompetitorSameBucketPairFields.data cap s k u sa sb a b ra rb 0) cap p k coefficient out := embed _ _ _ _ _ _ _
  rw [hi] at hr
  refine ⟨TapeEmbedding.receipt (extraHeads out) (extras cap p k coefficient out) base,hr,?_,?_,bs⟩
  · change (TapeEmbedding.config (extraHeads out) (extras cap p k coefficient out) base.final).heads=_
    have he : base.final=⟨base.final.control,fun _ => 0,CompetitorSameBucketPairFields.data cap s k u sa sb a b ra rb 3⟩ :=
      configuration_ext rfl (funext bh) bt
    rw [he,embed]
    rfl
  · change (TapeEmbedding.config (extraHeads out) (extras cap p k coefficient out) base.final).tapes=_
    have he : base.final=⟨base.final.control,fun _ => 0,CompetitorSameBucketPairFields.data cap s k u sa sb a b ra rb 3⟩ :=
      configuration_ext rfl (funext bh) bt
    rw [he,embed]
    rfl

theorem classify_absent (work : Fin 31 → List Bool) (cap p k : ℕ) (coefficient : ℤ) (out : List Bool)
    (habsent : work 0=List.replicate cap false ∨ work 13=List.replicate cap false) :
    ∃ r,runFrom classify 1 (cfg classify.start work cap p k coefficient out)=some r ∧
      r.final.heads=heads out ∧ r.final.tapes=(cfg classify.start work cap p k coefficient out).tapes ∧ r.steps≤1 := by
  obtain ⟨base,hb,bt,bh,bs⟩ := CompetitorSameBucketPairGuard.absent_zeros_ready work cap habsent
  have hr := TapeEmbedding.run_embed CompetitorSameBucketPairGuard.machine (extraHeads out) (extras cap p k coefficient out) _ _ base hb
  have hi : TapeEmbedding.config (extraHeads out) (extras cap p k coefficient out)
      (initialConfiguration CompetitorSameBucketPairGuard.machine work)=cfg classify.start work cap p k coefficient out := embed _ _ _ _ _ _ _
  rw [hi] at hr
  have he : base.final=⟨base.final.control,fun _ => 0,work⟩ := configuration_ext rfl (funext bh) bt
  refine ⟨TapeEmbedding.receipt (extraHeads out) (extras cap p k coefficient out) base,hr,?_,?_,bs⟩
  · change (TapeEmbedding.config (extraHeads out) (extras cap p k coefficient out) base.final).heads=_
    rw [he,embed]
    rfl
  · change (TapeEmbedding.config (extraHeads out) (extras cap p k coefficient out) base.final).tapes=_
    rw [he,embed]
    rfl

theorem append_slots (cap s k u p : ℕ) (sa sb coefficient : ℤ) (a b ra rb : ℕ) (out : List Bool) :
    ∀ i,(cfg append.start (CompetitorSameBucketPairFields.data cap s k u sa sb a b ra rb 3) cap p k coefficient out).heads (appendSlots i)=
      (CompetitorSameBucketKeyAppend.paddedCfg CompetitorSameBucketKeyAppend.machine.start (signMagnitude p coefficient) k b a cap out).heads i ∧
      (cfg append.start (CompetitorSameBucketPairFields.data cap s k u sa sb a b ra rb 3) cap p k coefficient out).tapes (appendSlots i)=
      (CompetitorSameBucketKeyAppend.paddedCfg CompetitorSameBucketKeyAppend.machine.start (signMagnitude p coefficient) k b a cap out).tapes i := by
  intro i
  fin_cases i <;> simp [cfg,heads,extras,appendSlots,Fin.addCases,CompetitorSameBucketPairFields.data,
    CompetitorSameBucketKeyAppend.paddedCfg,CompetitorSameBucketKeyAppend.cfg,CompetitorSameBucketKeyAppend.capacities,
    ZeroPadding.config,Rewind.Workspace.pad_zeros,ZeroPadding.pad_zero]

end NearCubicWires.RepairOrdinary.CompetitorSameBucketPairEmit
