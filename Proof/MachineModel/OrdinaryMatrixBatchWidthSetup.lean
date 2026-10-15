import Proof.MachineModel.OrdinaryMatrixBatchSetup
import Proof.MachineModel.OrdinaryMatrixBatchColumnsCopy
import Proof.MachineModel.OrdinaryMatrixScoreTemplateEntry
import Proof.MachineModel.ClockScalarFields

namespace NearCubicWires.RepairOrdinary.MatrixBatchWidthSetup
open LocalBitMultitape SignedSortKey MatrixScoreBatch RepairRepresentation MatrixBatchSetup
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-- One focused stage appended to a composed run. -/
theorem stage {u a b t : ℕ} (P : Machine u a) (slots : Fin t → Fin u) (hinj : Function.Injective slots)
    (Q : Machine t b) (fp fq : ℕ) (c : Configuration u a) (r : ExecutionReceipt u a)
    (hp : runFrom P fp c = some r) (entry : Configuration t b) (s : ExecutionReceipt t b)
    (hq : runFrom Q fq entry = some s) (hstart : entry.control = Q.start)
    (hh : ∀ i, r.final.heads (slots i) = entry.heads i) (ht : ∀ i, r.final.tapes (slots i) = entry.tapes i) :
    ∃ res : ExecutionReceipt u (a + b),
      runFrom (Composition.machine P (RecoveryFocus.machine slots Q)) (fp + 1 + fq)
        (Composition.leftConfig b c) = some res ∧
      (∀ i, res.final.heads (slots i) = s.final.heads i) ∧
      (∀ i, res.final.tapes (slots i) = s.final.tapes i) ∧
      (∀ j, RecoveryFocus.pick slots j = none →
        res.final.heads j = r.final.heads j ∧ res.final.tapes j = r.final.tapes j) ∧
      res.steps = r.steps + 1 + s.steps := by
  have hi : RecoveryFocus.config slots r.final.heads r.final.tapes entry =
      Composition.restart r.final (RecoveryFocus.machine slots Q).start := by
    rw [WilliamsSourceCrop.focus_same slots r.final entry hh ht, hstart]
    rfl
  obtain ⟨focused, hf, hff, hfs⟩ := RecoveryFocus.run_config slots hinj Q r.final.heads r.final.tapes fq entry s hq
  rw [hi] at hf
  refine ⟨Composition.joinedReceipt r focused, Composition.run_join P _ fp fq c r focused hp hf, ?_, ?_, ?_, ?_⟩
  · intro i
    change focused.final.heads (slots i) = _
    rw [hff]
    simp only [RecoveryFocus.config, RecoveryFocus.pick_slot slots hinj]
  · intro i
    change focused.final.tapes (slots i) = _
    rw [hff]
    simp only [RecoveryFocus.config, RecoveryFocus.pick_slot slots hinj]
  · intro j hj
    constructor
    · change focused.final.heads j = _
      rw [hff]
      simp only [RecoveryFocus.config, hj]
    · change focused.final.tapes j = _
      rw [hff]
      simp only [RecoveryFocus.config, hj]
  · change r.steps + 1 + focused.steps = _
    rw [hfs]

/-- Move one head one cell to the right. -/
def advance : Machine 1 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 1
  rule := fun q _ => if q.val = 0 then some ⟨1, fun _ => none, fun _ => .right⟩ else none

theorem advance_run (tape : List Bool) (h : ℕ) :
    ∃ res : ExecutionReceipt 1 2,
      runFrom advance 1 ⟨0, fun _ => h, fun _ => tape⟩ = some res ∧
      res.final.heads 0 = h + 1 ∧ res.final.tapes 0 = tape ∧ res.steps = 1 := by
  have hs : step advance ⟨0, fun _ => h, fun _ => tape⟩ = some ⟨1, fun _ => h + 1, fun _ => tape⟩ := by
    simp [step, advance]
    apply configuration_ext
    · rfl
    · funext i; fin_cases i; simp [applyAction, HeadMove.apply]
    · funext i; fin_cases i; simp [applyAction]
  obtain ⟨res, hr, hf, hsteps⟩ := (RecoveryExecution.Timed.single (p := advance) (by rfl) hs).run (by rfl)
  exact ⟨res, hr, by rw [hf], by rw [hf], hsteps⟩

def slots2 : Fin 4 → Fin 26 := ![0,12,13,11]
def slots3 : Fin 5 → Fin 26 := ![10,14,15,16,17]
def slots4 : Fin 5 → Fin 26 := ![14,18,20,19,21]
def slots5 : Fin 5 → Fin 26 := ![14,22,24,23,25]
def slots6 : Fin 1 → Fin 26 := ![16]

noncomputable def parse := TapeEmbedding.machine 15 MatrixDimensionPrepare.machine
noncomputable def copy := RecoveryFocus.machine slots2 MatrixBatchColumnsCopy.machine
noncomputable def unary := RecoveryFocus.machine slots3 MatrixScoreTemplateEntry.machine
noncomputable def zero1 := RecoveryFocus.machine slots4 ClockNormalize.machine
noncomputable def zero2 := RecoveryFocus.machine slots5 ClockNormalize.machine
noncomputable def shift := RecoveryFocus.machine slots6 advance
noncomputable def machine :=
  Composition.machine (Composition.machine (Composition.machine (Composition.machine
    (Composition.machine parse copy) unary) zero1) zero2) shift

def parseBudget (r : Request) := MatrixDimensionPrepare.budget (natBitLength r.width) r.width
def budget (r : Request) :=
  parseBudget r+1+MatrixBatchColumnsCopy.budget r.d (MatrixScorePhi.columnsWord r.width r.cols)+1+
    (4*r.width+14)+1+(4*r.width+4)+1+(4*r.width+4)+1+1

/-- The states of the width parse's unary stage. -/
abbrev U := 8+Fintype.card (RecoveryCalls.Control MatrixUnary.sizes)

/-- The ambient tapes beside the width parse: the frame counter on tape 11, the rest blank. -/
def extra (r : Request) : Fin 15 → List Bool := fun j => if j = 0 then UnaryTemplate.tape r.d else []

/-- The start configuration: the copied word with its cursor after the gate count, and the frame counter;
every other tape blank and every other head at cell 0. -/
def entry (r : Request) :=
  Composition.leftConfig 2 (Composition.leftConfig 6 (Composition.leftConfig 6 (Composition.leftConfig 10
    (Composition.leftConfig 8 (TapeEmbedding.config (fun _ : Fin 15 => 0) (extra r)
      (Composition.leftConfig U (MatrixDimensionPrepare.input (word r) (gatesEnd r))))))))

theorem entry_heads (r : Request) (i : Fin 26) : (entry r).heads i = if i = 0 then gatesEnd r else 0 := by
  fin_cases i <;> simp [entry, Composition.leftConfig, MatrixDimensionPrepare.input, TapeEmbedding.config,
    MatrixDimensionField.input, MatrixDimensionHeader.input, Fin.addCases]

theorem entry_tapes (r : Request) (i : Fin 26) :
    (entry r).tapes i = if i = 0 then word r else if i = 11 then UnaryTemplate.tape r.d else [] := by
  fin_cases i <;> simp [entry, Composition.leftConfig, MatrixDimensionPrepare.input, TapeEmbedding.config,
    MatrixDimensionField.input, MatrixDimensionHeader.input, Fin.addCases, extra]

/-- The header prefix up to the columns: `natWord d ++ natWord p ++ natWord Gates ++ natWord width`. -/
def columnsStart (r : Request) : List Bool := natWord r.d++natWord r.p++natWord r.Gates++natWord r.width

theorem word_columns (r : Request) :
    columnsStart r++MatrixScorePhi.columnsWord r.width r.cols++r.cuts.flatMap (cutWord r.p)=word r := by
  simp only [columnsStart,word,header,List.append_assoc]

theorem word_parse (r : Request) :
    (natWord r.d++natWord r.p++natWord r.Gates)++List.replicate (natBitLength r.width) true++
      false::(binary (natBitLength r.width) r.width++
        (MatrixScorePhi.columnsWord r.width r.cols++r.cuts.flatMap (cutWord r.p)))=word r := by
  rw [←word_columns r]
  simp [columnsStart,WilliamsInputHeader.natWord_eq,List.append_assoc]

theorem header_length (r : Request) :
    (columnsStart r).length+(MatrixScorePhi.columnsWord r.width r.cols).length=(header r).length := by
  simp only [columnsStart,header,List.length_append]

/-- **The width setup.** From the cursor after the gate count, the weight count and the columns are
parsed, the columns retained, and the unary width, the width sentinel and two zero assignments produced; the
cursor ends at the end of the header. -/
theorem width_run (r : Request) :
    ∃ actual,runFrom machine (budget r) (entry r)=some actual ∧
      actual.final.tapes 0=word r ∧ actual.final.heads 0=(header r).length ∧
      actual.final.tapes 11=UnaryTemplate.tape r.d ∧ actual.final.heads 11=0 ∧
      actual.final.tapes 12=MatrixScorePhi.columnsWord r.width r.cols ∧ actual.final.heads 12=0 ∧
      actual.final.tapes 14=List.replicate r.width true ∧ actual.final.heads 14=0 ∧
      actual.final.tapes 15=List.replicate r.width true ∧ actual.final.heads 15=0 ∧
      actual.final.tapes 16=UnaryTemplate.tape r.width ∧ actual.final.heads 16=1 ∧
      actual.final.tapes 20=frame (binary r.width 0) ∧ actual.final.heads 20=0 ∧
      actual.final.tapes 24=frame (binary r.width 0) ∧ actual.final.heads 24=0 ∧
      (actual.final.tapes 18).length≤1 ∧ actual.final.heads 18=0 ∧
      actual.final.tapes 19=[true] ∧ actual.final.heads 19=0 ∧
      actual.final.tapes 21=List.replicate (2*r.width+1) false ∧ actual.final.heads 21=0 ∧
      (actual.final.tapes 22).length≤1 ∧ actual.final.heads 22=0 ∧
      actual.final.tapes 23=[true] ∧ actual.final.heads 23=0 ∧
      actual.final.tapes 25=List.replicate (2*r.width+1) false ∧ actual.final.heads 25=0 ∧
      actual.steps≤budget r := by
  let cw := MatrixScorePhi.columnsWord r.width r.cols
  -- the width parse
  obtain ⟨dp,hdp,d0,dh0,_,_,_,_,_,_,d10,dh10,ds⟩ := MatrixDimensionPrepare.prepare_run
    (natWord r.d++natWord r.p++natWord r.Gates) (cw++r.cuts.flatMap (cutWord r.p))
    (natBitLength r.width) r.width (Nat.lt_pow_succ_log_self (by decide) _)
  rw [word_parse] at hdp d0
  have he := TapeEmbedding.run_embed MatrixDimensionPrepare.machine (fun _ : Fin 15 => 0) (extra r) _ _ dp hdp
  let r1 := TapeEmbedding.receipt (fun _ : Fin 15 => 0) (extra r) dp
  have r1T (i : Fin 11) : r1.final.tapes (i.castAdd 15)=dp.final.tapes i := by
    simp [r1,TapeEmbedding.receipt,TapeEmbedding.config,Fin.addCases]
  have r1H (i : Fin 11) : r1.final.heads (i.castAdd 15)=dp.final.heads i := by
    simp [r1,TapeEmbedding.receipt,TapeEmbedding.config,Fin.addCases]
  have r1XT (j : Fin 15) : r1.final.tapes (j.natAdd 11)=extra r j := by
    simp only [r1,TapeEmbedding.receipt,TapeEmbedding.config,Fin.addCases_right]
  have r1XH (j : Fin 15) : r1.final.heads (j.natAdd 11)=0 := by
    simp [r1,TapeEmbedding.receipt,TapeEmbedding.config,Fin.addCases]
  -- the columns copy
  obtain ⟨cc,hcc,hccf,hccs⟩ := MatrixBatchColumnsCopy.copy_run r.width r.cols (columnsStart r)
    (r.cuts.flatMap (cutWord r.p))
  rw [word_columns,cols_length] at hcc hccf
  rw [cols_length] at hccs
  have hstart0 : dp.final.heads 0=(columnsStart r).length := by
    rw [dh0]
    simp only [columnsStart,List.length_append,MatrixScoreRawGateBounds.natWord_length]
    omega
  obtain ⟨r2,hr2,s2H,s2T,s2O,s2s⟩ := stage parse slots2 (by decide) MatrixBatchColumnsCopy.machine _ _ _ r1 he
    _ cc hcc rfl
    (by
      intro i
      fin_cases i
      · exact (r1H 0).trans hstart0
      · exact r1XH 1
      · exact r1XH 2
      · exact r1XH 0)
    (by
      intro i
      fin_cases i
      · exact (r1T 0).trans d0
      · exact r1XT 1
      · exact r1XT 2
      · exact r1XT 0)
  -- the unary copies of the width
  obtain ⟨te,hte,te0,te1,te2,te3,teh,tes⟩ := MatrixScoreTemplateEntry.entry_run r.width
  obtain ⟨r3,hr3,s3H,s3T,s3O,s3s⟩ := stage (Composition.machine parse copy) slots3 (by decide)
    MatrixScoreTemplateEntry.machine _ _ _ r2 hr2 _ te hte rfl
    (by
      intro i
      fin_cases i
      · exact ((s2O 10 (by decide)).1.trans (r1H 10)).trans dh10
      · exact (s2O 14 (by decide)).1.trans (r1XH 3)
      · exact (s2O 15 (by decide)).1.trans (r1XH 4)
      · exact (s2O 16 (by decide)).1.trans (r1XH 5)
      · exact (s2O 17 (by decide)).1.trans (r1XH 6))
    (by
      intro i
      fin_cases i
      · exact ((s2O 10 (by decide)).2.trans (r1T 10)).trans d10
      · exact (s2O 14 (by decide)).2.trans (r1XT 3)
      · exact (s2O 15 (by decide)).2.trans (r1XT 4)
      · exact (s2O 16 (by decide)).2.trans (r1XT 5)
      · exact (s2O 17 (by decide)).2.trans (r1XT 6))
  -- the first zero assignment
  obtain ⟨z1,hz1,z10,z11,z12,z13,z14,z1h,z1s⟩ := ClockScalarFields.zero_run r.width
  obtain ⟨r4,hr4,s4H,s4T,s4O,s4s⟩ := stage (Composition.machine (Composition.machine parse copy) unary) slots4
    (by decide) ClockNormalize.machine _ _ _ r3 hr3 _ z1 hz1 rfl
    (by
      intro i
      fin_cases i
      · exact (s3H 1).trans (teh 1)
      · exact ((s3O 18 (by decide)).1.trans (s2O 18 (by decide)).1).trans (r1XH 7)
      · exact ((s3O 20 (by decide)).1.trans (s2O 20 (by decide)).1).trans (r1XH 9)
      · exact ((s3O 19 (by decide)).1.trans (s2O 19 (by decide)).1).trans (r1XH 8)
      · exact ((s3O 21 (by decide)).1.trans (s2O 21 (by decide)).1).trans (r1XH 10))
    (by
      intro i
      fin_cases i
      · exact (s3T 1).trans te1
      · exact ((s3O 18 (by decide)).2.trans (s2O 18 (by decide)).2).trans (r1XT 7)
      · exact ((s3O 20 (by decide)).2.trans (s2O 20 (by decide)).2).trans (r1XT 9)
      · exact ((s3O 19 (by decide)).2.trans (s2O 19 (by decide)).2).trans (r1XT 8)
      · exact ((s3O 21 (by decide)).2.trans (s2O 21 (by decide)).2).trans (r1XT 10))
  -- the second zero assignment
  obtain ⟨z2,hz2,z20,z21,z22,z23,z24,z2h,z2s⟩ := ClockScalarFields.zero_run r.width
  obtain ⟨r5,hr5,s5H,s5T,s5O,s5s⟩ := stage (Composition.machine (Composition.machine
    (Composition.machine parse copy) unary) zero1) slots5
    (by decide) ClockNormalize.machine _ _ _ r4 hr4 _ z2 hz2 rfl
    (by
      intro i
      fin_cases i
      · exact (s4H 0).trans (z1h 0)
      · exact (((s4O 22 (by decide)).1.trans (s3O 22 (by decide)).1).trans (s2O 22 (by decide)).1).trans (r1XH 11)
      · exact (((s4O 24 (by decide)).1.trans (s3O 24 (by decide)).1).trans (s2O 24 (by decide)).1).trans (r1XH 13)
      · exact (((s4O 23 (by decide)).1.trans (s3O 23 (by decide)).1).trans (s2O 23 (by decide)).1).trans (r1XH 12)
      · exact (((s4O 25 (by decide)).1.trans (s3O 25 (by decide)).1).trans (s2O 25 (by decide)).1).trans (r1XH 14))
    (by
      intro i
      fin_cases i
      · exact (s4T 0).trans z10
      · exact (((s4O 22 (by decide)).2.trans (s3O 22 (by decide)).2).trans (s2O 22 (by decide)).2).trans (r1XT 11)
      · exact (((s4O 24 (by decide)).2.trans (s3O 24 (by decide)).2).trans (s2O 24 (by decide)).2).trans (r1XT 13)
      · exact (((s4O 23 (by decide)).2.trans (s3O 23 (by decide)).2).trans (s2O 23 (by decide)).2).trans (r1XT 12)
      · exact (((s4O 25 (by decide)).2.trans (s3O 25 (by decide)).2).trans (s2O 25 (by decide)).2).trans (r1XT 14))
  -- the width sentinel's head to cell 1
  obtain ⟨ad,had,adh,adt,ads⟩ := advance_run (UnaryTemplate.tape r.width) 0
  obtain ⟨r6,hr6,s6H,s6T,s6O,s6s⟩ := stage (Composition.machine (Composition.machine (Composition.machine
    (Composition.machine parse copy) unary) zero1) zero2) slots6
    (by decide) advance _ _ _ r5 hr5 _ ad had rfl
    (by
      intro i
      fin_cases i
      exact ((s5O 16 (by decide)).1.trans (s4O 16 (by decide)).1).trans ((s3H 3).trans (teh 3)))
    (by
      intro i
      fin_cases i
      exact ((s5O 16 (by decide)).2.trans (s4O 16 (by decide)).2).trans ((s3T 3).trans te3))
  have pad1 (x : List Bool) (hx : ZeroPadding.pad 1 x=[false]) : x.length≤1 := by
    have h := congrArg List.length hx
    simp only [ZeroPadding.pad,List.length_append,List.length_replicate,List.length_cons,List.length_nil] at h
    omega
  refine ⟨r6,hr6,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,
    ?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact ((((s6O 0 (by decide)).2.trans (s5O 0 (by decide)).2).trans (s4O 0 (by decide)).2).trans
      (s3O 0 (by decide)).2).trans ((s2T 0).trans (by rw [hccf]; rfl))
  · refine ((((s6O 0 (by decide)).1.trans (s5O 0 (by decide)).1).trans (s4O 0 (by decide)).1).trans
      (s3O 0 (by decide)).1).trans ((s2H 0).trans ?_)
    rw [hccf]
    exact header_length r
  · exact ((((s6O 11 (by decide)).2.trans (s5O 11 (by decide)).2).trans (s4O 11 (by decide)).2).trans
      (s3O 11 (by decide)).2).trans ((s2T 3).trans (by rw [hccf]; rfl))
  · exact ((((s6O 11 (by decide)).1.trans (s5O 11 (by decide)).1).trans (s4O 11 (by decide)).1).trans
      (s3O 11 (by decide)).1).trans ((s2H 3).trans (by rw [hccf]; rfl))
  · exact ((((s6O 12 (by decide)).2.trans (s5O 12 (by decide)).2).trans (s4O 12 (by decide)).2).trans
      (s3O 12 (by decide)).2).trans ((s2T 1).trans (by rw [hccf]; rfl))
  · exact ((((s6O 12 (by decide)).1.trans (s5O 12 (by decide)).1).trans (s4O 12 (by decide)).1).trans
      (s3O 12 (by decide)).1).trans ((s2H 1).trans (by rw [hccf]; rfl))
  · exact (s6O 14 (by decide)).2.trans ((s5T 0).trans z20)
  · exact (s6O 14 (by decide)).1.trans ((s5H 0).trans (z2h 0))
  · exact (((s6O 15 (by decide)).2.trans (s5O 15 (by decide)).2).trans (s4O 15 (by decide)).2).trans ((s3T 2).trans te2)
  · exact (((s6O 15 (by decide)).1.trans (s5O 15 (by decide)).1).trans (s4O 15 (by decide)).1).trans ((s3H 2).trans (teh 2))
  · exact (s6T 0).trans adt
  · exact (s6H 0).trans adh
  · exact ((s6O 20 (by decide)).2.trans (s5O 20 (by decide)).2).trans ((s4T 2).trans z12)
  · exact ((s6O 20 (by decide)).1.trans (s5O 20 (by decide)).1).trans ((s4H 2).trans (z1h 2))
  · exact (s6O 24 (by decide)).2.trans ((s5T 2).trans z22)
  · exact (s6O 24 (by decide)).1.trans ((s5H 2).trans (z2h 2))
  · have h := ((s6O 18 (by decide)).2.trans (s5O 18 (by decide)).2).trans (s4T 1)
    rw [h]
    exact pad1 _ z11
  · exact ((s6O 18 (by decide)).1.trans (s5O 18 (by decide)).1).trans ((s4H 1).trans (z1h 1))
  · exact ((s6O 19 (by decide)).2.trans (s5O 19 (by decide)).2).trans ((s4T 3).trans z13)
  · exact ((s6O 19 (by decide)).1.trans (s5O 19 (by decide)).1).trans ((s4H 3).trans (z1h 3))
  · exact ((s6O 21 (by decide)).2.trans (s5O 21 (by decide)).2).trans ((s4T 4).trans z14)
  · exact ((s6O 21 (by decide)).1.trans (s5O 21 (by decide)).1).trans ((s4H 4).trans (z1h 4))
  · have h := (s6O 22 (by decide)).2.trans (s5T 1)
    rw [h]
    exact pad1 _ z21
  · exact (s6O 22 (by decide)).1.trans ((s5H 1).trans (z2h 1))
  · exact (s6O 23 (by decide)).2.trans ((s5T 3).trans z23)
  · exact (s6O 23 (by decide)).1.trans ((s5H 3).trans (z2h 3))
  · exact (s6O 25 (by decide)).2.trans ((s5T 4).trans z24)
  · exact (s6O 25 (by decide)).1.trans ((s5H 4).trans (z2h 4))
  · rw [s6s,s5s,s4s,s3s,s2s,ads,z2s,z1s,tes,hccs]
    change dp.steps+1+_+1+_+1+_+1+_+1+1≤_
    unfold budget parseBudget
    omega

end NearCubicWires.RepairOrdinary.MatrixBatchWidthSetup
