import Proof.Hierarchy.CompetitorSameBucketZeroCopyFields

/-! All six physical reference copies are consumed immediately by the
cold zero-grid initializer. Shared C logs are reset after every call. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSameBucketZeroPrepareCopies
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open CompetitorSameBucketZeroCopyFields (sourceSlot targetSlot slots copied cfg)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def values (p m u : ℕ) : Fin 6 → List Bool :=
  ![List.replicate (p+1) false,List.replicate (p+1) false,binary m u,binary m 0,binary m 0,binary m 0]
noncomputable def copies := Composition.machine (CompetitorSameBucketZeroCopyFields.machine 0) (Composition.machine (CompetitorSameBucketZeroCopyFields.machine 1) (Composition.machine (CompetitorSameBucketZeroCopyFields.machine 2) (Composition.machine (CompetitorSameBucketZeroCopyFields.machine 3) (Composition.machine (CompetitorSameBucketZeroCopyFields.machine 4) ((CompetitorSameBucketZeroCopyFields.machine 5))))))
def copyBudget (p m : ℕ):=16*p+32*m+69
private theorem joined {a b : ℕ} (p : Machine 19 a) (q : Machine 19 b)
    (c d : ℕ) (heads : Fin 19 → ℕ) (input middle final : Fin 19 → List Bool)
    (hp : ∃ actual,runFrom p c (cfg p.start heads input)=some actual ∧
      actual.final.heads=heads ∧ actual.final.tapes=middle ∧ actual.steps≤c)
    (hq : ∃ actual,runFrom q d (cfg q.start heads middle)=some actual ∧
      actual.final.heads=heads ∧ actual.final.tapes=final ∧ actual.steps≤d) :
    ∃ actual,runFrom (Composition.machine p q) (c+1+d)
        (cfg (Composition.machine p q).start heads input)=some actual ∧
      actual.final.heads=heads ∧ actual.final.tapes=final ∧ actual.steps≤c+1+d := by
  obtain ⟨first,hfirst,fh,ft,fs⟩:=hp
  obtain ⟨last,hlast,lh,lt,ls⟩:=hq
  have he : Composition.restart first.final q.start=cfg q.start heads middle := by
    apply configuration_ext
    · rfl
    · exact fh
    · exact ft
  rw [←he] at hlast
  have h:=Composition.run_join p q c d _ first last hfirst hlast
  refine ⟨Composition.joinedReceipt first last,h,lh,lt,?_⟩
  change first.steps+1+last.steps≤c+1+d
  omega

def initialized (p m u cap : ℕ) (out log : List Bool) : Fin 19 → List Bool :=
  ![UnaryTemplate.tape u,frame (binary m u),frame (binary m 0),frame (List.replicate (p+1) false),
    List.replicate cap true,out,ZeroPadding.pad cap (frame (List.replicate (p+1) false)),
    ZeroPadding.pad cap (frame (List.replicate (p+1) false)),ZeroPadding.pad cap (frame (binary m u)),
    ZeroPadding.pad cap (frame (binary m 0)),ZeroPadding.pad cap (frame (binary m 0)),
    ZeroPadding.pad cap (frame (binary m 0)),List.replicate cap false,List.replicate (cap+1) false,
    List.replicate cap false,List.replicate u true,List.replicate u true,UnaryTemplate.tape u,log]

theorem copies_run (p m u cap : ℕ) (out log : List Bool)
    (hp : 4*(p+1)+3≤cap) (hm : 4*m+3≤cap) :
    ∃ actual,runFrom copies (copyBudget p m)
        (cfg copies.start (CompetitorSameBucketZeroPrepareSpace.heads out)
          (CompetitorSameBucketZeroPrepareSpace.output p m u cap out log))=some actual ∧
      actual.final.heads=CompetitorSameBucketZeroPrepareSpace.heads out ∧
      actual.final.tapes=initialized p m u cap out log ∧ actual.steps≤copyBudget p m := by
  let ambient:=CompetitorSameBucketZeroPrepareSpace.output p m u cap out log
  let heads:=CompetitorSameBucketZeroPrepareSpace.heads out
  let mid1:=copied 0 cap (values p m u 0) ambient
  have h0:=CompetitorSameBucketZeroCopyFields.copy_run 0 cap (values p m u 0) heads ambient
    (by simpa [values] using hp)
    (by intro k; fin_cases k <;> rfl)
    (by simp [ambient, sourceSlot, values, CompetitorSameBucketZeroPrepareSpace.output])
    (by simp [ambient, targetSlot, CompetitorSameBucketZeroPrepareSpace.output])
    (by simp [ambient, CompetitorSameBucketZeroPrepareSpace.output])
    (by simp [ambient, CompetitorSameBucketZeroPrepareSpace.output])
  let mid2:=copied 1 cap (values p m u 1) mid1
  have h1:=CompetitorSameBucketZeroCopyFields.copy_run 1 cap (values p m u 1) heads mid1
    (by simpa [values] using hp)
    (by intro k; fin_cases k <;> rfl)
    (by simp [mid1, ambient, copied, sourceSlot, targetSlot, values, CompetitorSameBucketZeroPrepareSpace.output])
    (by simp [mid1, ambient, copied, targetSlot, values, CompetitorSameBucketZeroPrepareSpace.output])
    (by simp [mid1, ambient, copied, targetSlot, values, CompetitorSameBucketZeroPrepareSpace.output])
    (by simp [mid1, ambient, copied, targetSlot, values, CompetitorSameBucketZeroPrepareSpace.output])
  let mid3:=copied 2 cap (values p m u 2) mid2
  have h2:=CompetitorSameBucketZeroCopyFields.copy_run 2 cap (values p m u 2) heads mid2
    (by simpa [values] using hm)
    (by intro k; fin_cases k <;> rfl)
    (by simp [mid2, mid1, ambient, copied, sourceSlot, targetSlot, values, CompetitorSameBucketZeroPrepareSpace.output])
    (by simp [mid2, mid1, ambient, copied, targetSlot, values, CompetitorSameBucketZeroPrepareSpace.output])
    (by simp [mid2, mid1, ambient, copied, targetSlot, values, CompetitorSameBucketZeroPrepareSpace.output])
    (by simp [mid2, mid1, ambient, copied, targetSlot, values, CompetitorSameBucketZeroPrepareSpace.output])
  let mid4:=copied 3 cap (values p m u 3) mid3
  have h3:=CompetitorSameBucketZeroCopyFields.copy_run 3 cap (values p m u 3) heads mid3
    (by simpa [values] using hm)
    (by intro k; fin_cases k <;> rfl)
    (by simp [mid3, mid2, mid1, ambient, copied, sourceSlot, targetSlot, values, CompetitorSameBucketZeroPrepareSpace.output])
    (by simp [mid3, mid2, mid1, ambient, copied, targetSlot, values, CompetitorSameBucketZeroPrepareSpace.output])
    (by simp [mid3, mid2, mid1, ambient, copied, targetSlot, values, CompetitorSameBucketZeroPrepareSpace.output])
    (by simp [mid3, mid2, mid1, ambient, copied, targetSlot, values, CompetitorSameBucketZeroPrepareSpace.output])
  let mid5:=copied 4 cap (values p m u 4) mid4
  have h4:=CompetitorSameBucketZeroCopyFields.copy_run 4 cap (values p m u 4) heads mid4
    (by simpa [values] using hm)
    (by intro k; fin_cases k <;> rfl)
    (by simp [mid4, mid3, mid2, mid1, ambient, copied, sourceSlot, targetSlot, values, CompetitorSameBucketZeroPrepareSpace.output])
    (by simp [mid4, mid3, mid2, mid1, ambient, copied, targetSlot, values, CompetitorSameBucketZeroPrepareSpace.output])
    (by simp [mid4, mid3, mid2, mid1, ambient, copied, targetSlot, values, CompetitorSameBucketZeroPrepareSpace.output])
    (by simp [mid4, mid3, mid2, mid1, ambient, copied, targetSlot, values, CompetitorSameBucketZeroPrepareSpace.output])
  let mid6:=copied 5 cap (values p m u 5) mid5
  have h5:=CompetitorSameBucketZeroCopyFields.copy_run 5 cap (values p m u 5) heads mid5
    (by simpa [values] using hm)
    (by intro k; fin_cases k <;> rfl)
    (by simp [mid5, mid4, mid3, mid2, mid1, ambient, copied, sourceSlot, targetSlot, values, CompetitorSameBucketZeroPrepareSpace.output])
    (by simp [mid5, mid4, mid3, mid2, mid1, ambient, copied, targetSlot, values, CompetitorSameBucketZeroPrepareSpace.output])
    (by simp [mid5, mid4, mid3, mid2, mid1, ambient, copied, targetSlot, values, CompetitorSameBucketZeroPrepareSpace.output])
    (by simp [mid5, mid4, mid3, mid2, mid1, ambient, copied, targetSlot, values, CompetitorSameBucketZeroPrepareSpace.output])
  have tail4:=joined _ _ _ _ heads mid4 mid5 mid6 h4 h5
  have tail3:=joined _ _ _ _ heads mid3 mid4 mid6 h3 tail4
  have tail2:=joined _ _ _ _ heads mid2 mid3 mid6 h2 tail3
  have tail1:=joined _ _ _ _ heads mid1 mid2 mid6 h1 tail2
  have tail0:=joined _ _ _ _ heads ambient mid1 mid6 h0 tail1
  have total : (8*(values p m u 0).length+8)+1+((8*(values p m u 1).length+8)+1+((8*(values p m u 2).length+8)+1+((8*(values p m u 3).length+8)+1+((8*(values p m u 4).length+8)+1+((8*(values p m u 5).length+8))))))=copyBudget p m := by
    simp [values,copyBudget]
    omega
  rw [total] at tail0
  obtain ⟨actual,ha,ah,atapes,ast⟩:=tail0
  refine ⟨actual,ha,ah,?_,ast⟩
  rw [atapes]
  funext i
  fin_cases i <;> simp [mid6,mid5,mid4,mid3,mid2,mid1,ambient,copied,targetSlot,values,
    initialized,CompetitorSameBucketZeroPrepareSpace.output]

noncomputable def machine:=Composition.machine CompetitorSameBucketZeroPrepareSpace.machine copies
def budget (p m u cap : ℕ):=CompetitorSameBucketZeroPrepareSpace.budget u cap+1+copyBudget p m

theorem prepared_run (p m u cap : ℕ) (out : List Bool)
    (hp : 4*(p+1)+3≤cap) (hm : 4*m+3≤cap) :
    ∃ actual log,runFrom machine (budget p m u cap)
        (CompetitorSameBucketZeroPrepareSpace.cfg machine.start out
          (CompetitorSameBucketZeroPrepareSpace.input p m u cap out))=some actual ∧
      actual.final.heads=CompetitorSameBucketZeroPrepareSpace.heads out ∧
      actual.final.tapes=initialized p m u cap out log ∧ actual.steps≤budget p m u cap := by
  obtain ⟨space,log,hs,sh,st,ss⟩:=CompetitorSameBucketZeroPrepareSpace.space_run p m u cap out
  obtain ⟨copied,hc,ch,ct,cs⟩:=copies_run p m u cap out log hp hm
  have he : Composition.restart space.final copies.start=
      cfg copies.start (CompetitorSameBucketZeroPrepareSpace.heads out)
        (CompetitorSameBucketZeroPrepareSpace.output p m u cap out log) := by
    apply configuration_ext
    · rfl
    · exact sh
    · exact st
  rw [←he] at hc
  have joined:=Composition.run_join CompetitorSameBucketZeroPrepareSpace.machine copies _ _ _ space copied hs hc
  refine ⟨Composition.joinedReceipt space copied,log,joined,ch,ct,?_⟩
  change space.steps+1+copied.steps≤budget p m u cap
  unfold budget
  omega

end NearCubicWires.RepairOrdinary.CompetitorSameBucketZeroPrepareCopies
