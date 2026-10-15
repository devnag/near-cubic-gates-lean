import Proof.MachineModel.OrdinaryMatrixScoreFoldEntry

/-! Paid post-fold clear and shifted-score subtraction in the same reusable
twenty-tape assignment carrier. The source and assignment cursors survive. -/
namespace NearCubicWires.RepairOrdinary.MatrixScoreFinish
open LocalBitMultitape SignedSortKey MatrixScoreFoldEntry
open MatrixScoreWeight (zeros scalar)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 4 → Fin 20 := ![10,11,2,3]
def pick : Fin 20 → Option (Fin 4) := ![none,none,some 2,some 3,none,none,none,none,none,none,
  some 0,some 1,none,none,none,none,none,none,none,none]
theorem pick_slots (i : Fin 20) : RecoveryFocus.pick slots i=pick i := by
  fin_cases i
  all_goals first
    | decide
    | exact RecoveryFocus.pick_slot slots (by decide) 0
    | exact RecoveryFocus.pick_slot slots (by decide) 1
    | exact RecoveryFocus.pick_slot slots (by decide) 2
    | exact RecoveryFocus.pick_slot slots (by decide) 3
noncomputable def first := TapeEmbedding.machine 3 MatrixScoreWeightClear.machine
noncomputable def last := RecoveryFocus.machine slots CompetitorSignedResidue.subtractProgram
noncomputable def machine := Composition.machine first last
def budget (s c : ℕ) := (2*c+4)+1+(4*(s+1)+4)
def work (c w p n : ℕ) (score counter : List Bool) : Fin 12 → List Bool :=
  ![score,counter,zeros c,zeros c,zeros c,zeros c,zeros c,scalar c w p,scalar c w n,zeros c,zeros c,zeros c]

theorem finish_run (source assignment : List Bool) (pos apos d c s p n x y : ℕ)
    (scratch : Fin 10 → List Bool) (hs : ∀ i,(scratch i).length≤c)
    (hp : p<2^s) (hn : n<2^s) (hc : 4*(s+1)+5≤c) :
    ∃ finalWork : Fin 12 → List Bool,(∀ i,(finalWork i).length≤c) ∧
      finalWork 0=scalar c (s+1) (shifted s ((p : ℤ)-n)) ∧
      ∃ actual,runFrom machine (budget s c)
        (RecoveryCalls.restarted machine (heads pos apos)
          (tapes source assignment d c (c+1) (s+1) x y
            (accumulators c (s+1) (2^s+p) n scratch)))=some actual ∧
        actual.final.heads=heads pos apos ∧
        actual.final.tapes=tapes source assignment d c (c+1) (s+1) x y finalWork ∧
        actual.steps≤budget s c := by
  obtain ⟨cleared,hcRun,hch,hct,hcs⟩ := MatrixScoreWeightClear.clear_run source assignment pos apos c (s+1) (2^s+p) n scratch hs
  have he := TapeEmbedding.run_embed MatrixScoreWeightClear.machine ![1,0,0]
    ![UnaryTemplate.tape d,frame (binary (s+1) x),frame (binary (s+1) y)] _ _ cleared hcRun
  let expanded := TapeEmbedding.receipt ![1,0,0]
    ![UnaryTemplate.tape d,frame (binary (s+1) x),frame (binary (s+1) y)] cleared
  have eh : expanded.final.heads=heads pos apos := by
    funext i
    fin_cases i <;> simp [expanded,TapeEmbedding.receipt,TapeEmbedding.config,Fin.addCases,hch,
      MatrixScoreWeightClear.heads,heads]
  have et : expanded.final.tapes=tapes source assignment d c (c+1) (s+1) x y
      (accumulators c (s+1) (2^s+p) n (fun _ => zeros c)) := by
    funext i
    fin_cases i <;> simp [expanded,TapeEmbedding.receipt,TapeEmbedding.config,Fin.addCases,hct,
      MatrixScoreWeightClear.tapes,tapes,accumulators]
  obtain ⟨difference,hd,d0,d1,d2,dh,db,ds⟩ := MatrixScoreShifted.shifted_run s p n c hp hn hc
  let localInput := initialConfiguration CompetitorSignedResidue.subtractProgram
    ![scalar c (s+1) (2^s+p),scalar c (s+1) n,zeros c,zeros c]
  have hi : RecoveryFocus.config slots expanded.final.heads expanded.final.tapes localInput=
      Composition.restart expanded.final last.start := by
    apply WilliamsSourceCrop.focus_same
    · intro i; rw [eh]; fin_cases i <;> rfl
    · intro i; rw [et]; fin_cases i <;> rfl
  obtain ⟨focused,hf,hff,hfs⟩ := RecoveryFocus.run_config slots (by decide) CompetitorSignedResidue.subtractProgram
    expanded.final.heads expanded.final.tapes _ localInput difference hd
  rw [hi] at hf
  have hj := Composition.run_join first last (2*c+4) (4*(s+1)+4) _ expanded focused he hf
  have hin : Composition.leftConfig _ (TapeEmbedding.config ![1,0,0]
      ![UnaryTemplate.tape d,frame (binary (s+1) x),frame (binary (s+1) y)]
      (RecoveryCalls.restarted MatrixScoreWeightClear.machine (MatrixScoreWeightClear.heads pos apos)
        (MatrixScoreWeightClear.tapes source assignment c (s+1) (2^s+p) n scratch)))=
      RecoveryCalls.restarted machine (heads pos apos)
        (tapes source assignment d c (c+1) (s+1) x y (accumulators c (s+1) (2^s+p) n scratch)) := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  rw [hin] at hj
  let finalWork := work c (s+1) (2^s+p) n (difference.final.tapes 2) (difference.final.tapes 3)
  have workBound (i : Fin 12) : (finalWork i).length≤c := by
    have dp := db 0
    have dn := db 1
    rw [d0] at dp
    rw [d1] at dn
    fin_cases i <;> first | exact db 2 | exact db 3 | exact dp | exact dn | simp [finalWork,work,zeros]
  refine ⟨finalWork,workBound,d2,Composition.joinedReceipt expanded focused,hj,?_,?_,?_⟩
  · funext i
    change focused.final.heads i=_
    rw [hff]
    cases h : RecoveryFocus.pick slots i <;> simp [RecoveryFocus.config,h,eh,dh]
    rename_i j
    have hij := RecoveryFocus.slot_of_pick slots h
    rw [← hij]
    fin_cases j <;> rfl
  · funext i
    change focused.final.tapes i=_
    rw [hff]
    fin_cases i <;> simp [RecoveryFocus.config,pick_slots,pick,et,tapes,accumulators,finalWork,work,d0,d1]
  · change cleared.steps+1+focused.steps≤_
    rw [hcs,hfs]
    unfold budget
    omega

end NearCubicWires.RepairOrdinary.MatrixScoreFinish
