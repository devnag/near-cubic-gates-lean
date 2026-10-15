import Proof.Hierarchy.CompetitorCountMaskMeaning

/-! Actual offset-selection pass using the accepted mask expansion and
bitwise-AND machines. Each complete Q-bit cell is retained or replaced by
zero. Both count streams are rewound once after the full column scan. -/
namespace NearCubicWires.RepairOrdinary.CompetitorCountMask
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 6 → Fin 11 := ![6,2,8,9,7,10]
noncomputable def first := TapeEmbedding.machine 5 MatrixMaskPad.machine
noncomputable def last := RecoveryFocus.machine slots MatrixMaskAndPass.machine
noncomputable def machine := Composition.machine first last
def extraHeads : Fin 5 → ℕ := ![1,1,0,0,0]
def extraTapes (Q : ℕ) (xs : List (Bool × ℕ)) : Fin 5 → List Bool :=
  ![UnaryTemplate.tape (Q*xs.length),UnaryTemplate.tape 1,CompetitorCountFold.raw Q (counts xs),[],[]]
noncomputable def input (Q : ℕ) (xs : List (Bool × ℕ)) :=
  Composition.leftConfig (Fintype.card (RepairSource.VerifierDecoding.RepeatMachine.Control (2+3))+2)
    (TapeEmbedding.config extraHeads (extraTapes Q xs) (MatrixMaskPad.input Q 0 (mask xs)))
def budget (Q n : ℕ) := MatrixMaskPad.budget Q 0 n+1+MatrixMaskAndPass.budget (Q*n) 1
def heads (n : ℕ) : Fin 11 → ℕ := ![1,n,0,1,1,0,1,1,0,0,0]

theorem native_run (Q : ℕ) (xs : List (Bool × ℕ)) : ∃ actual,
    runFrom machine (budget Q xs.length) (input Q xs)=some actual ∧ actual.steps≤budget Q xs.length ∧
    actual.final.heads=heads xs.length ∧
    actual.final.tapes 9=CompetitorCountFold.raw Q (selected xs) ∧
    actual.final.tapes 8=CompetitorCountFold.raw Q (counts xs) ∧ actual.final.tapes 1=mask xs ∧
    actual.final.tapes 0=UnaryTemplate.tape Q ∧ actual.final.tapes 3=UnaryTemplate.tape xs.length := by
  let expanded := MatrixMaskExpand.output Q (mask xs)
  let raw := CompetitorCountFold.raw Q (counts xs)
  have hm : expanded.length=Q*xs.length := by
    simp [expanded,MatrixMaskExpand.output_length,mask_length,Nat.mul_comm]
  have hc : raw.length=Q*xs.length := by simp [raw,CompetitorCountFold.raw_length,counts_length]
  obtain ⟨base,hb,bt,bh,blh,⟨nb,blt,_⟩,bs⟩ := MatrixMaskPad.mask_run Q 0 (mask xs)
  simp only [mask_length] at hb bs
  have hf := TapeEmbedding.run_embed MatrixMaskPad.machine extraHeads (extraTapes Q xs) _ _ base hb
  let prepared := TapeEmbedding.receipt extraHeads (extraTapes Q xs) base
  have pt (i : Fin 11) : prepared.final.tapes i=
      (![UnaryTemplate.tape Q,mask xs,expanded,UnaryTemplate.tape xs.length,UnaryTemplate.tape 0,
        List.replicate nb false,UnaryTemplate.tape (Q*xs.length),UnaryTemplate.tape 1,raw,[],[]] : Fin 11 → List Bool) i := by
    fin_cases i
    · exact bt 0
    · exact bt 1
    · change base.final.tapes 2=expanded
      simpa [MatrixMaskPad.cfg,MatrixMaskPad.output,expanded] using bt 2
    · change base.final.tapes 3=UnaryTemplate.tape xs.length
      simpa [MatrixMaskPad.cfg,mask_length] using bt 3
    · exact bt 4
    · exact blt
    all_goals rfl
  have ph (i : Fin 11) : prepared.final.heads i=heads xs.length i := by
    fin_cases i
    · exact bh 0
    · exact (bh 1).trans (mask_length xs)
    · exact bh 2
    · exact bh 3
    · exact bh 4
    · exact blh
    all_goals rfl
  obtain ⟨child,ch,ct,chh,clh,⟨nc,clt,_⟩,cs⟩ := MatrixMaskAndPass.pass_run expanded [raw]
    (by intro row hr;simpa using (List.mem_singleton.mp hr ▸ hc.trans hm.symm))
  simp only [hm,List.length_singleton] at ch cs
  let entry := MatrixMaskAndPass.input expanded [raw]
  have hi : RecoveryFocus.config slots prepared.final.heads prepared.final.tapes entry=
      Composition.restart prepared.final last.start := by
    apply WilliamsSourceCrop.focus_same
    · intro i
      rw [ph]
      fin_cases i <;> rfl
    · intro i
      rw [pt]
      fin_cases i <;>
        simp [entry,slots,MatrixMaskAndPass.input,Rewind.recording,Rewind.config,
          MatrixMaskAndLoop.native_tapes,hm,Fin.addCases]
  obtain ⟨lastRun,hl,lf,ls⟩ := RecoveryFocus.run_config slots (by decide) MatrixMaskAndPass.machine
    prepared.final.heads prepared.final.tapes _ entry child ch
  rw [hi] at hl
  have hj := Composition.run_join first last _ _ _ prepared lastRun hf hl
  have pick (i : Fin 11) : RecoveryFocus.pick slots i=
      (![none,none,some 1,none,none,none,some 0,some 4,some 2,some 3,some 5] : Fin 11 → Option (Fin 6)) i := by
    fin_cases i <;> first
      | decide
      | exact RecoveryFocus.pick_slot slots (by decide) 0
      | exact RecoveryFocus.pick_slot slots (by decide) 1
      | exact RecoveryFocus.pick_slot slots (by decide) 2
      | exact RecoveryFocus.pick_slot slots (by decide) 3
      | exact RecoveryFocus.pick_slot slots (by decide) 4
      | exact RecoveryFocus.pick_slot slots (by decide) 5
  have cout : child.final.tapes 3=CompetitorCountFold.raw Q (selected xs) := by
    have h := ct 3
    change child.final.tapes 3=MatrixMaskAndLoop.output expanded [raw] at h
    simpa only [MatrixMaskAndLoop.output,List.flatMap_cons,List.flatMap_nil,List.append_nil,
      expanded,raw,selected_word] using h
  have csource : child.final.tapes 2=raw := by simpa using ct 2
  have ch' (i : Fin 6) : child.final.heads i=(![1,0,0,0,1,0] : Fin 6 → ℕ) i := by
    fin_cases i <;> first | exact chh 0 | exact chh 1 | exact chh 2 | exact chh 3 | exact chh 4 | exact clh
  refine ⟨Composition.joinedReceipt prepared lastRun,hj,?_,?_,?_,?_,?_,?_,?_⟩
  · change base.steps+1+lastRun.steps≤budget Q xs.length
    rw [ls]
    unfold budget
    omega
  · change lastRun.final.heads=_
    rw [lf]
    funext i
    simp only [RecoveryFocus.config,pick]
    fin_cases i <;> simp [ph,ch',heads]
  · change lastRun.final.tapes 9=_
    rw [lf]
    simpa [RecoveryFocus.config,pick] using cout
  · change lastRun.final.tapes 8=_
    rw [lf]
    simpa [RecoveryFocus.config,pick] using csource
  · change lastRun.final.tapes 1=_
    rw [lf]
    simpa [RecoveryFocus.config,pick] using pt 1
  · change lastRun.final.tapes 0=_
    rw [lf]
    simpa [RecoveryFocus.config,pick] using pt 0
  · change lastRun.final.tapes 3=_
    rw [lf]
    simpa [RecoveryFocus.config,pick] using pt 3

end NearCubicWires.RepairOrdinary.CompetitorCountMask
