import Proof.Hierarchy.CompetitorSameBucketCandidateNative

/-! Present and absent records use the same existing packet codec and the
same executable conditional emitter. The invariant exposes bounded scratch
and the retained fields required by the next candidate. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSameBucketCandidate
open LocalBitMultitape RecoveryExecution RecoveryRootRound MatrixBatchBucketEndpoints
open MatrixScoreBatch (Request dimension_positive)
open CompetitorSameBucketPackets (word width)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def Fits (r : Request) (e : Option KeyLoop.Record) : Prop :=
  ∀ v,e=some v → v.2.1<2^r.M ∧ v.2.2<2^(r.M+r.S+1)
def pairOutput (r : Request) (coefficient : ℤ) (left right : Option KeyLoop.Record) (out : List Bool) :=
  match left,right with
  | some a,some b => CompetitorSameBucketPairEmit.output r.p r.M r.U a.2.1 b.2.1 a.2.2 b.2.2 coefficient out
  | _,_ => out

theorem absent_local (cap k u p fuel : ℕ) (coefficient : ℤ) (left right out : List Bool)
    (habsent : ZeroPadding.pad cap left=List.replicate cap false ∨ ZeroPadding.pad cap right=List.replicate cap false)
    (hf : 2≤fuel) :
    ∃ b,runFrom CompetitorSameBucketPairEmit.machine fuel (part cap k u p coefficient left right out)=some b ∧
      b.final.heads=CompetitorSameBucketPairEmit.heads out ∧ b.final.tapes=(part cap k u p coefficient left right out).tapes ∧ b.steps≤fuel := by
  have ha : initialWork cap k u left right 0=List.replicate cap false ∨
      initialWork cap k u left right 13=List.replicate cap false := by
    simpa only [initialWork,ite_true,show (13 : Fin 31)≠0 from by decide,
      show (13 : Fin 31)≠7 from by decide,ite_false] using habsent
  obtain ⟨base,hb,bh,bt,bs⟩ := CompetitorSameBucketPairEmit.absent_run (initialWork cap k u left right)
    cap p k coefficient out ha (by simp [initialWork,readTapeBit])
  have hr := runFrom_moreFuel CompetitorSameBucketPairEmit.machine 2 (fuel-2) _ base hb
  rw [Nat.add_sub_of_le hf] at hr
  exact ⟨base,hr,bh,bt,bs.trans hf⟩

theorem pair_local_run (r : Request) (cap : ℕ) (coefficient : ℤ) (left right : Option KeyLoop.Record) (out : List Bool)
    (hc : 30*(H r+1)≤cap) (hp : 2*(r.p+1)+1≤cap) (hl : Fits r left) (hr : Fits r right) :
    ∃ b,runFrom CompetitorSameBucketPairEmit.machine (CompetitorSameBucketPairEmit.budget r.S r.M r.p)
        (part cap r.M r.U r.p coefficient (word r left) (word r right) out)=some b ∧
      b.final.heads=CompetitorSameBucketPairEmit.heads (pairOutput r coefficient left right out) ∧
      (∀ i : Fin 36,i≠34 → (b.final.tapes i).length≤cap) ∧
      (∀ i : Fin 7,b.final.tapes (⟨(fixedSlots i).val,by fin_cases i <;> decide⟩ : Fin 36)=
        fixed cap r.M r.U r.p coefficient (word r left) (pairOutput r coefficient left right out) i) ∧
      b.steps≤CompetitorSameBucketPairEmit.budget r.S r.M r.p := by
  have hc' : 30*(r.M+r.S+2)≤cap := by simpa only [H,Nat.add_assoc] using hc
  have hw : width r≤cap := by unfold width H; omega
  have hk : 2*r.M+1≤cap := by unfold H at hc; omega
  have hf : 2≤CompetitorSameBucketPairEmit.budget r.S r.M r.p := by
    rw [CompetitorSameBucketPairEmit.budget_eq]
    omega
  have hpresent : ∀ a b : KeyLoop.Record,left=some a → right=some b →
      ∃ z,runFrom CompetitorSameBucketPairEmit.machine (CompetitorSameBucketPairEmit.budget r.S r.M r.p)
          (part cap r.M r.U r.p coefficient (word r left) (word r right) out)=some z ∧
        z.final.heads=CompetitorSameBucketPairEmit.heads (pairOutput r coefficient left right out) ∧
        (∀ i : Fin 36,i≠34 → (z.final.tapes i).length≤cap) ∧
        (∀ i : Fin 7,z.final.tapes (⟨(fixedSlots i).val,by fin_cases i <;> decide⟩ : Fin 36)=
          fixed cap r.M r.U r.p coefficient (word r left) (pairOutput r coefficient left right out) i) ∧
        z.steps≤CompetitorSameBucketPairEmit.budget r.S r.M r.p := by
    intro a b ha hb
    obtain ⟨idA,rankA⟩ := hl a ha
    obtain ⟨idB,rankB⟩ := hr b hb
    have hu : r.U<2^r.M := by have h := MatrixScoreRawRanks.size_fit r; have hU := dimension_positive r; omega
    obtain ⟨base,hb0,bh,bt,bs⟩ := CompetitorSameBucketPairEmit.present_run cap r.S r.M r.U r.p
      a.1 b.1 coefficient a.2.1 b.2.1 a.2.2 b.2.2 out hc' hu idA idB rankA rankB (by omega)
    have hin : part cap r.M r.U r.p coefficient (word r left) (word r right) out=
        CompetitorSameBucketPairEmit.cfg CompetitorSameBucketPairEmit.machine.start
          (CompetitorSameBucketPairFields.data cap r.S r.M r.U a.1 b.1 a.2.1 b.2.1 a.2.2 b.2.2 0) cap r.p r.M coefficient out := by
      simp only [ha,hb,word,part,initial_present cap r.S r.M r.U a.1 b.1 a.2.1 b.2.1 a.2.2 b.2.2 (by omega)]
    rw [←hin] at hb0
    refine ⟨base,hb0,?_,?_,?_,bs⟩
    · simpa only [ha,hb,pairOutput] using bh
    · intro i hi
      rw [bt]
      exact present_support cap r.S r.M r.U r.p a.1 b.1 coefficient a.2.1 b.2.1 a.2.2 b.2.2 _ hc' hp i hi
    · intro i
      rw [bt]
      simpa only [ha,hb,pairOutput,word] using present_fields cap r.S r.M r.U r.p a.1 b.1 coefficient a.2.1 b.2.1 a.2.2 b.2.2 _ i
  by_cases ha : left=none
  · obtain ⟨base,hb,bh,bt,bs⟩ := absent_local cap r.M r.U r.p _ coefficient (word r left) (word r right) out
      (Or.inl (by simp [ha,word,Rewind.Workspace.pad_zeros,max_eq_left hw])) hf
    refine ⟨base,hb,?_,?_,?_,bs⟩
    · simpa only [ha,pairOutput] using bh
    · intro i hi
      rw [bt]
      exact part_support cap r.M r.U r.p coefficient _ _ out (by rw [CompetitorSameBucketPackets.word_length]; exact hw)
        (by rw [CompetitorSameBucketPackets.word_length]; exact hw) hk hp i hi
    · intro i
      rw [bt]
      simpa only [ha,pairOutput] using initial_fields cap r.M r.U r.p coefficient (word r left) (word r right) out i
  · cases left with
    | none => contradiction
    | some a =>
      cases right with
      | some b => exact hpresent a b rfl rfl
      | none =>
        obtain ⟨base,hb,bh,bt,bs⟩ := absent_local cap r.M r.U r.p _ coefficient (word r (some a)) (word r none) out
          (Or.inr (by simp [word,Rewind.Workspace.pad_zeros,max_eq_left hw])) hf
        refine ⟨base,hb,bh,?_,?_,bs⟩
        · intro i hi
          rw [bt]
          exact part_support cap r.M r.U r.p coefficient _ _ out (by rw [CompetitorSameBucketPackets.word_length]; exact hw)
            (by rw [CompetitorSameBucketPackets.word_length]; exact hw) hk hp i hi
        · intro i
          rw [bt]
          exact initial_fields cap r.M r.U r.p coefficient (word r (some a)) (word r none) out i

end NearCubicWires.RepairOrdinary.CompetitorSameBucketCandidate
