import Proof.MachineModel.OrdinaryMatrixScoreLeftFields

/-! Complete actual right score from the original cut: skip its left fields
using the d-driver, then evaluate the actual right weights and subtract. -/
namespace NearCubicWires.RepairOrdinary.MatrixScoreRight
open LocalBitMultitape SignedSortKey MatrixScoreLeftFields
open MatrixScoreWeight (zeros scalar)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def linear := TapeEmbedding.machine 2 MatrixScoreLinear.machine
noncomputable def machine := Composition.machine MatrixScoreLeftFields.skip linear
def budget (d p s c : ℕ) := (d*(2*p+6)+3)+1+MatrixScoreLinear.budget d p s c

theorem right_run (left right : List ℤ) (pre suffix apre asuffix : List Bool)
    (p n s c cap : ℕ) (work : Fin 12 → List Bool) (driver counter : List Bool)
    (hlen : right.length=left.length) (hf : ∀ z ∈ right,z.natAbs<2^p)
    (hw : p≤ s+1) (hc : 4*(s+1)+5≤c) (hcap : cap≤c+1) (hs : ∀ i,(work i).length≤c)
    (hp : MatrixScoreBatch.part false right n<2^s) (hn : MatrixScoreBatch.part true right n<2^s) :
    ∃ finalWork : Fin 12 → List Bool,(∀ i,(finalWork i).length≤c) ∧
      finalWork 0=scalar c (s+1) (shifted s (MatrixScoreBatch.linearForm right n)) ∧
      ∃ actual,runFrom machine (budget left.length p s c)
        (RecoveryCalls.restarted machine (heads pre.length apre.length)
          (tapes (pre++MatrixScoreCanonical.fields p left++MatrixScoreCanonical.fields p right++suffix)
            (apre++frame (binary left.length n)++asuffix) left.length c cap (s+1) (2^s) 0 work driver counter))=some actual ∧
        actual.final.heads=heads (pre.length+(MatrixScoreCanonical.fields p left).length+(MatrixScoreCanonical.fields p right).length)
          (apre.length+2*left.length) ∧
        actual.final.tapes=tapes (pre++MatrixScoreCanonical.fields p left++MatrixScoreCanonical.fields p right++suffix)
          (apre++frame (binary left.length n)++asuffix) left.length c (c+1) (s+1) (2^s) 0 finalWork driver counter ∧
        actual.steps≤budget left.length p s c := by
  let source := pre++MatrixScoreCanonical.fields p left++MatrixScoreCanonical.fields p right++suffix
  let assignment := apre++frame (binary left.length n)++asuffix
  let rightPre := pre++MatrixScoreCanonical.fields p left
  obtain ⟨skipped,hk,kh,kt,ks⟩ := MatrixScoreLeftFields.skip_run left pre (MatrixScoreCanonical.fields p right++suffix)
    assignment driver counter p apre.length c cap (s+1) (2^s) 0 work
  have heSource : pre++MatrixScoreCanonical.fields p left++(MatrixScoreCanonical.fields p right++suffix)=source := by
    simp [source,List.append_assoc]
  rw [heSource] at hk kt
  obtain ⟨finalWork,hws,hw0,base,hb,bh,bt,bs⟩ := MatrixScoreLinear.linear_run right rightPre suffix apre asuffix p n s c cap work
    hf hw hc hcap hs hp hn
  simp only [hlen] at hb bh bt bs
  have he := TapeEmbedding.run_embed MatrixScoreLinear.machine (fun _ : Fin 2 => 0) ![driver,counter] _ _ base hb
  let expanded := TapeEmbedding.receipt (fun _ : Fin 2 => 0) ![driver,counter] base
  have hi : TapeEmbedding.config (fun _ : Fin 2 => 0) ![driver,counter]
      (RecoveryCalls.restarted MatrixScoreLinear.machine (MatrixScoreFoldEntry.heads rightPre.length apre.length)
        (MatrixScoreFoldEntry.tapes (rightPre++MatrixScoreCanonical.fields p right++suffix) assignment left.length c cap (s+1) (2^s) 0 work))=
      Composition.restart skipped.final linear.start := by
    apply configuration_ext
    · rfl
    · change heads rightPre.length apre.length=skipped.final.heads
      rw [kh]
      simp [rightPre]
    · exact kt.symm
  rw [hi] at he
  have joined := Composition.run_join MatrixScoreLeftFields.skip linear _ _ _ skipped expanded hk he
  refine ⟨finalWork,hws,hw0,Composition.joinedReceipt skipped expanded,joined,?_,?_,?_⟩
  · change expanded.final.heads=_
    funext i
    fin_cases i <;> simp [expanded,TapeEmbedding.receipt,TapeEmbedding.config,Fin.addCases,bh,heads,
      MatrixScoreFoldEntry.heads,rightPre,Nat.add_assoc]
  · change expanded.final.tapes=_
    funext i
    fin_cases i <;> simp [expanded,TapeEmbedding.receipt,TapeEmbedding.config,Fin.addCases,bt,tapes,
      MatrixScoreFoldEntry.tapes,rightPre]
  · change skipped.steps+1+base.steps≤_
    unfold budget
    omega

end NearCubicWires.RepairOrdinary.MatrixScoreRight
