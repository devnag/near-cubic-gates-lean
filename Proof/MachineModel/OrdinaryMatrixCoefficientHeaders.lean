import Proof.MachineModel.OrdinaryMatrixCoefficientNative
import Proof.MachineModel.OrdinaryMatrixHeaderScratch
import Proof.MachineModel.OrdinaryMatrixBatchColumnsCopy
import Proof.Amplification.RecoveryScratchErase

namespace NearCubicWires.RepairOrdinary.MatrixCoefficientHeaders
open LocalBitMultitape MatrixScoreBatch SignedSortKey RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-! ### The three-header parser (unchanged) -/

def slots : Fin 11 → Fin 33 := ![1,23,24,25,26,27,28,29,30,31,32]
theorem slots_injective : Function.Injective slots := by decide
noncomputable def first := TapeEmbedding.machine 10 MatrixScoreHeaders.machine
noncomputable def last := RecoveryFocus.machine slots MatrixDimensionPrepare.machine
noncomputable def machine := Composition.machine first last
def input (r : Request) : Fin 33 → List Bool := fun i => if i=0 then physicalInput r else []

/-! ### Cells -/

theorem allFalse_of_pad_one {t : List Bool} (h : ZeroPadding.pad 1 t=[false]) :
    t=List.replicate t.length false := by
  match t, h with
  | [], _ => rfl
  | [b], h =>
    have hb : b=false := by simpa [ZeroPadding.pad] using h
    simp [hb]
  | _::_::_, h => simp [ZeroPadding.pad] at h

theorem length_le_of_pad_one {t : List Bool} (h : ZeroPadding.pad 1 t=[false]) : t.length ≤ 1 := by
  have := congrArg List.length h
  simp only [ZeroPadding.pad_length, List.length_singleton] at this
  omega

theorem allFalse_replicate {t : List Bool} {n : ℕ} (h : t=List.replicate n false) :
    t=List.replicate t.length false := by
  subst h; simp

theorem pad_nil_self (t : List Bool) (h : t=List.replicate t.length false) :
    ZeroPadding.pad t.length []=t := by
  rw [h]; simp [ZeroPadding.pad]

theorem pad_long (c : ℕ) (t : List Bool) (h : c ≤ t.length) : ZeroPadding.pad c t=t := by
  simp [ZeroPadding.pad, Nat.sub_eq_zero_of_le h]

theorem pad_allFalse (c : ℕ) (t : List Bool) (h : t=List.replicate t.length false) :
    ZeroPadding.pad c t=List.replicate (ZeroPadding.pad c t).length false := by
  rw [h]; simp [ZeroPadding.pad]

theorem pad_self (t : List Bool) : ZeroPadding.pad t.length t=t := pad_long _ _ le_rfl

theorem template_length (n : ℕ) : (UnaryTemplate.tape n).length=n+2 := by
  simp [UnaryTemplate.tape]

/-! ### Stages -/

/-- One focused stage appended to a composed run. -/
theorem stage {u a b t : ℕ} (P : Machine u a) (sl : Fin t → Fin u) (hinj : Function.Injective sl)
    (Q : Machine t b) (fp fq : ℕ) (c : Configuration u a) (r : ExecutionReceipt u a)
    (hp : runFrom P fp c=some r) (entry : Configuration t b) (s : ExecutionReceipt t b)
    (hq : runFrom Q fq entry=some s) (hstart : entry.control=Q.start)
    (hh : ∀ i, r.final.heads (sl i)=entry.heads i) (ht : ∀ i, r.final.tapes (sl i)=entry.tapes i) :
    ∃ res : ExecutionReceipt u (a+b),
      runFrom (Composition.machine P (RecoveryFocus.machine sl Q)) (fp+1+fq)
        (Composition.leftConfig b c)=some res ∧
      (∀ i, res.final.heads (sl i)=s.final.heads i) ∧
      (∀ i, res.final.tapes (sl i)=s.final.tapes i) ∧
      (∀ j, RecoveryFocus.pick sl j=none →
        res.final.heads j=r.final.heads j ∧ res.final.tapes j=r.final.tapes j) ∧
      res.steps=r.steps+1+s.steps := by
  have hi : RecoveryFocus.config sl r.final.heads r.final.tapes entry=
      Composition.restart r.final (RecoveryFocus.machine sl Q).start := by
    rw [WilliamsSourceCrop.focus_same sl r.final entry hh ht, hstart]
    rfl
  obtain ⟨focused,hf,hff,hfs⟩ := RecoveryFocus.run_config sl hinj Q r.final.heads r.final.tapes fq entry s hq
  rw [hi] at hf
  refine ⟨Composition.joinedReceipt r focused,Composition.run_join P _ fp fq c r focused hp hf,?_,?_,?_,?_⟩
  · intro i
    change focused.final.heads (sl i)=_
    rw [hff]
    simp only [RecoveryFocus.config,RecoveryFocus.pick_slot sl hinj]
  · intro i
    change focused.final.tapes (sl i)=_
    rw [hff]
    simp only [RecoveryFocus.config,RecoveryFocus.pick_slot sl hinj]
  · intro j hj
    constructor
    · change focused.final.heads j=_
      rw [hff]
      simp only [RecoveryFocus.config,hj]
    · change focused.final.tapes j=_
      rw [hff]
      simp only [RecoveryFocus.config,hj]
  · change r.steps+1+focused.steps=_
    rw [hfs]

/-- Move one head one cell to the left. -/
def retreat : Machine 1 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==1
  rule := fun q _ => if q.val=0 then some ⟨1,fun _ => none,fun _ => .left⟩ else none

theorem retreat_run (tape : List Bool) (h : ℕ) :
    ∃ res : ExecutionReceipt 1 2,
      runFrom retreat 1 ⟨0,fun _ => h+1,fun _ => tape⟩=some res ∧
      res.final.heads 0=h ∧ res.final.tapes 0=tape ∧ res.steps=1 := by
  have hs : step retreat ⟨0,fun _ => h+1,fun _ => tape⟩=some ⟨1,fun _ => h,fun _ => tape⟩ := by
    simp [step,retreat]
    apply configuration_ext
    · rfl
    · funext i; fin_cases i; simp [applyAction,HeadMove.apply]
    · funext i; fin_cases i; simp [applyAction]
  obtain ⟨res,hr,hf,hsteps⟩ := (RecoveryExecution.Timed.single (p := retreat) (by rfl) hs).run (by rfl)
  exact ⟨res,hr,by rw [hf],by rw [hf],hsteps⟩

def eraseSlots1 : Fin 3 → Fin 33 := ![3,4,7]
def eraseSlots2 : Fin 3 → Fin 33 := ![13,14,17]
def eraseSlots3 : Fin 3 → Fin 33 := ![23,24,27]
def widthSlots : Fin 11 → Fin 33 := ![1,3,13,23,7,17,27,2,18,28,8]
def backSlots : Fin 1 → Fin 33 := ![12]
def copySlots : Fin 4 → Fin 33 := ![1,17,27,12]

noncomputable def erase1 := RecoveryFocus.machine eraseSlots1 (RecoveryScratchErase.resetMachine 1)
noncomputable def erase2 := RecoveryFocus.machine eraseSlots2 (RecoveryScratchErase.resetMachine 1)
noncomputable def erase3 := RecoveryFocus.machine eraseSlots3 (RecoveryScratchErase.resetMachine 1)
noncomputable def width := RecoveryFocus.machine widthSlots MatrixDimensionPrepare.machine
noncomputable def back := RecoveryFocus.machine backSlots retreat
noncomputable def columns := RecoveryFocus.machine copySlots MatrixBatchColumnsCopy.machine
/-- The whole header parse: the three headers, three zeroing sweeps, the weight-count parse, the counter
return and the columns pass. -/
noncomputable def full :=
  Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine
    (Composition.machine machine erase1) erase2) erase3) width) back) columns

/-- The three-header parse's budget on the request word. -/
def threeBudget (r : Request) :=
  MatrixScoreHeaders.budget r.d r.p
    (natWord r.Gates++natWord r.width++MatrixScorePhi.columnsWord r.width r.cols++r.cuts.flatMap (cutWord r.p))+
  1+MatrixDimensionPrepare.budget (natBitLength r.Gates) r.Gates

/-- The whole header budget: polynomial in the header, no `2^width` term. -/
def budget (r : Request) :=
  MatrixScoreHeaders.budget r.d r.p
    (natWord r.Gates++natWord r.width++MatrixScorePhi.columnsWord r.width r.cols++r.cuts.flatMap (cutWord r.p))+
  1+MatrixDimensionPrepare.budget (natBitLength r.Gates) r.Gates+
  1+(2*natBitLength r.d+4)+1+(2*natBitLength r.p+4)+1+(2*natBitLength r.Gates+4)+
  1+MatrixDimensionPrepare.budget (natBitLength r.width) r.width+1+1+
  1+MatrixBatchColumnsCopy.budget r.d (MatrixScorePhi.columnsWord r.width r.cols)

/-- The header up to the columns. -/
def columnsStart (r : Request) : List Bool := natWord r.d++natWord r.p++natWord r.Gates++natWord r.width

theorem word_three (r : Request) :
    natWord r.d++natWord r.p++(natWord r.Gates++natWord r.width++MatrixScorePhi.columnsWord r.width r.cols++
      r.cuts.flatMap (cutWord r.p))=word r := by
  simp only [word,header,List.append_assoc]

theorem word_columns (r : Request) :
    columnsStart r++MatrixScorePhi.columnsWord r.width r.cols++r.cuts.flatMap (cutWord r.p)=word r := by
  simp only [columnsStart,word,header,List.append_assoc]

theorem word_width (r : Request) :
    (natWord r.d++natWord r.p++natWord r.Gates)++List.replicate (natBitLength r.width) true++
      false::(binary (natBitLength r.width) r.width++
        (MatrixScorePhi.columnsWord r.width r.cols++r.cuts.flatMap (cutWord r.p)))=word r := by
  rw [←word_columns r]
  simp [columnsStart,WilliamsInputHeader.natWord_eq,List.append_assoc]

theorem header_length (r : Request) :
    (columnsStart r).length+(MatrixScorePhi.columnsWord r.width r.cols).length=(header r).length := by
  simp only [columnsStart,header,List.length_append]

/-- The three-header parse on the request word, with every cell the continuation reuses. -/
theorem three_run (r : Request) : ∃ actual,
    run machine (threeBudget r) (input r)=some actual ∧
    actual.final.tapes 0=physicalInput r ∧ actual.final.heads 0=0 ∧
    actual.final.tapes 1=word r ∧ actual.final.heads 1=(natWord r.d++natWord r.p++natWord r.Gates).length ∧
    actual.final.tapes 2=List.replicate (word r).length false ∧ actual.final.heads 2=0 ∧
    actual.final.tapes 3=List.replicate (natBitLength r.d) true ∧ actual.final.heads 3=0 ∧
    actual.final.tapes 4=List.replicate (natBitLength r.d) true ∧ actual.final.heads 4=0 ∧
    actual.final.tapes 7=List.replicate (2*natBitLength r.d+1) false ∧ actual.final.heads 7=0 ∧
    ZeroPadding.pad 1 (actual.final.tapes 8)=[false] ∧ actual.final.heads 8=0 ∧
    actual.final.tapes 12=UnaryTemplate.tape r.d ∧ actual.final.heads 12=1 ∧
    actual.final.tapes 13=List.replicate (natBitLength r.p) true ∧ actual.final.heads 13=0 ∧
    actual.final.tapes 14=List.replicate (natBitLength r.p) true ∧ actual.final.heads 14=0 ∧
    actual.final.tapes 17=List.replicate (2*natBitLength r.p+1) false ∧ actual.final.heads 17=0 ∧
    ZeroPadding.pad 1 (actual.final.tapes 18)=[false] ∧ actual.final.heads 18=0 ∧
    actual.final.tapes 22=UnaryTemplate.tape r.p ∧ actual.final.heads 22=1 ∧
    actual.final.tapes 23=List.replicate (natBitLength r.Gates) true ∧ actual.final.heads 23=0 ∧
    actual.final.tapes 24=List.replicate (natBitLength r.Gates) true ∧ actual.final.heads 24=0 ∧
    actual.final.tapes 27=List.replicate (2*natBitLength r.Gates+1) false ∧ actual.final.heads 27=0 ∧
    ZeroPadding.pad 1 (actual.final.tapes 28)=[false] ∧ actual.final.heads 28=0 ∧
    actual.final.tapes 32=UnaryTemplate.tape r.Gates ∧ actual.final.heads 32=1 ∧
    actual.steps≤threeBudget r := by
  obtain ⟨base,hb,bt0,bh0,bt1,bh1,bt2,bh2,bt3,bh3,bt4,bh4,_,_,bt7,bh7,bt8,bh8,bd,bdh,bt13,bh13,bt14,bh14,_,_,
    bt17,bh17,bt18,bh18,bp,bph,bs⟩ := MatrixScoreHeaders.scratch_run r.d r.p
      (natWord r.Gates++natWord r.width++MatrixScorePhi.columnsWord r.width r.cols++r.cuts.flatMap (cutWord r.p))
  have he := TapeEmbedding.run_embed MatrixScoreHeaders.machine (fun _ : Fin 10 => 0)
    (fun _ : Fin 10 => []) _ _ base hb
  let prepared := TapeEmbedding.receipt (fun _ : Fin 10 => 0) (fun _ : Fin 10 => []) base
  obtain ⟨body,hbody,sourceT,sourceH,g1,gh1,g2,gh2,_,_,_,_,g5,gh5,g6,gh6,gateT,gateH,bodyS⟩ :=
    MatrixDimensionPrepare.scratch_run (natWord r.d++natWord r.p)
      (natWord r.width++MatrixScorePhi.columnsWord r.width r.cols++r.cuts.flatMap (cutWord r.p))
      (natBitLength r.Gates) r.Gates (Nat.lt_pow_succ_log_self (by decide) r.Gates)
  have hsource : (natWord r.d++natWord r.p)++List.replicate (natBitLength r.Gates) true++
      false::(binary (natBitLength r.Gates) r.Gates++(natWord r.width++MatrixScorePhi.columnsWord r.width r.cols++
        r.cuts.flatMap (cutWord r.p)))=word r := by
    simp [word,header,WilliamsInputHeader.natWord_eq,List.append_assoc]
  have hpre : (natWord r.d++natWord r.p).length=2*natBitLength r.d+1+(2*natBitLength r.p+1) := by
    simp [WilliamsInputHeader.natWord_eq,Nat.add_assoc]
    omega
  rw [hsource] at hbody sourceT
  have hw3 := word_three r
  rw [hw3] at bt2
  let entry : Configuration 11 WilliamsInputHeader.dimensionStates :=
    Composition.leftConfig _ (MatrixDimensionPrepare.input (word r) (natWord r.d++natWord r.p).length)
  have hi : RecoveryFocus.config slots prepared.final.heads prepared.final.tapes entry=
      Composition.restart prepared.final last.start := by
    apply WilliamsSourceCrop.focus_same
    · intro j
      fin_cases j
      · simpa [prepared,TapeEmbedding.receipt,TapeEmbedding.config,slots,entry,Composition.leftConfig,
          MatrixDimensionPrepare.input,MatrixDimensionField.input,MatrixDimensionHeader.input,hpre,Fin.addCases] using bh1
      all_goals simp [prepared,TapeEmbedding.receipt,TapeEmbedding.config,slots,entry,Composition.leftConfig,
        MatrixDimensionPrepare.input,MatrixDimensionField.input,MatrixDimensionHeader.input,Fin.addCases]
    · intro j
      fin_cases j
      · simpa [prepared,TapeEmbedding.receipt,TapeEmbedding.config,slots,entry,Composition.leftConfig,
          MatrixDimensionPrepare.input,MatrixDimensionField.input,MatrixDimensionHeader.input,Fin.addCases,
          word,header,List.append_assoc] using bt1
      all_goals simp [prepared,TapeEmbedding.receipt,TapeEmbedding.config,slots,entry,Composition.leftConfig,
        MatrixDimensionPrepare.input,MatrixDimensionField.input,MatrixDimensionHeader.input,Fin.addCases]
  obtain ⟨focused,hf,ff,fs⟩ := RecoveryFocus.run_config slots slots_injective MatrixDimensionPrepare.machine
    prepared.final.heads prepared.final.tapes _ entry body hbody
  rw [hi] at hf
  have hj := Composition.run_join first last _ _ _ prepared focused he hf
  have hin : Composition.leftConfig _ (TapeEmbedding.config (fun _ : Fin 10 => 0) (fun _ : Fin 10 => [])
      (initialConfiguration MatrixScoreHeaders.machine (MatrixScoreHeaders.input
        (natWord r.d++natWord r.p++(natWord r.Gates++natWord r.width++MatrixScorePhi.columnsWord r.width r.cols++
          r.cuts.flatMap (cutWord r.p))))))=
      initialConfiguration machine (input r) := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> simp [Composition.leftConfig,TapeEmbedding.config,initialConfiguration,
        MatrixScoreHeaders.input,input,physicalInput,word,header,List.append_assoc,Fin.addCases]
  rw [hin] at hj
  have otherT (i : Fin 23) (hn : RecoveryFocus.pick slots (i.castAdd 10)=none) :
      focused.final.tapes (i.castAdd 10)=base.final.tapes i := by
    rw [ff]
    simp [RecoveryFocus.config,hn,prepared,TapeEmbedding.receipt,TapeEmbedding.config]
  have otherH (i : Fin 23) (hn : RecoveryFocus.pick slots (i.castAdd 10)=none) :
      focused.final.heads (i.castAdd 10)=base.final.heads i := by
    rw [ff]
    simp [RecoveryFocus.config,hn,prepared,TapeEmbedding.receipt,TapeEmbedding.config]
  have pick (j : Fin 11) : RecoveryFocus.pick slots (slots j)=some j := RecoveryFocus.pick_slot slots slots_injective j
  refine ⟨Composition.joinedReceipt prepared focused,hj,?_,(otherH 0 (by decide)).trans bh0,?_,?_,
    (otherT 2 (by decide)).trans bt2,(otherH 2 (by decide)).trans bh2,
    (otherT 3 (by decide)).trans bt3,(otherH 3 (by decide)).trans bh3,
    (otherT 4 (by decide)).trans bt4,(otherH 4 (by decide)).trans bh4,
    (otherT 7 (by decide)).trans bt7,(otherH 7 (by decide)).trans bh7,
    (congrArg (ZeroPadding.pad 1) (otherT 8 (by decide))).trans bt8,(otherH 8 (by decide)).trans bh8,
    (otherT 12 (by decide)).trans bd,(otherH 12 (by decide)).trans bdh,
    (otherT 13 (by decide)).trans bt13,(otherH 13 (by decide)).trans bh13,
    (otherT 14 (by decide)).trans bt14,(otherH 14 (by decide)).trans bh14,
    (otherT 17 (by decide)).trans bt17,(otherH 17 (by decide)).trans bh17,
    (congrArg (ZeroPadding.pad 1) (otherT 18 (by decide))).trans bt18,(otherH 18 (by decide)).trans bh18,
    (otherT 22 (by decide)).trans bp,(otherH 22 (by decide)).trans bph,
    ?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact (otherT 0 (by decide)).trans (by simpa only [physicalInput,word,header,List.append_assoc] using bt0)
  · change focused.final.tapes (slots 0)=_
    rw [ff]
    simpa only [RecoveryFocus.config,pick] using sourceT
  · change focused.final.heads (slots 0)=_
    rw [ff]
    simp only [RecoveryFocus.config,pick]
    rw [sourceH]
    simp [WilliamsInputHeader.natWord_eq]
    omega
  · change focused.final.tapes (slots 1)=_
    rw [ff]; simpa only [RecoveryFocus.config,pick] using g1
  · change focused.final.heads (slots 1)=_
    rw [ff]; simpa only [RecoveryFocus.config,pick] using gh1
  · change focused.final.tapes (slots 2)=_
    rw [ff]; simpa only [RecoveryFocus.config,pick] using g2
  · change focused.final.heads (slots 2)=_
    rw [ff]; simpa only [RecoveryFocus.config,pick] using gh2
  · change focused.final.tapes (slots 5)=_
    rw [ff]; simpa only [RecoveryFocus.config,pick] using g5
  · change focused.final.heads (slots 5)=_
    rw [ff]; simpa only [RecoveryFocus.config,pick] using gh5
  · change ZeroPadding.pad 1 (focused.final.tapes (slots 6))=_
    rw [ff]; simpa only [RecoveryFocus.config,pick] using g6
  · change focused.final.heads (slots 6)=_
    rw [ff]; simpa only [RecoveryFocus.config,pick] using gh6
  · change focused.final.tapes (slots 10)=_
    rw [ff]; simpa only [RecoveryFocus.config,pick] using gateT
  · change focused.final.heads (slots 10)=_
    rw [ff]; simpa only [RecoveryFocus.config,pick] using gateH
  · change base.steps+1+focused.steps≤threeBudget r
    rw [fs]
    unfold threeBudget
    omega

/-- **The coefficient pass's header parse.** From the original framed request and blank work: the cursor
ends at the end of the header, the unary weight count `width` is on tape 8, the unary `d` (the columns'
frame counter), `p` and `Gates` are retained. -/
theorem headers_run (r : Request) : ∃ actual,
    run full (budget r) (input r)=some actual ∧
    actual.final.tapes 0=physicalInput r ∧ actual.final.heads 0=0 ∧
    actual.final.tapes 1=word r ∧ actual.final.heads 1=(header r).length ∧
    actual.final.tapes 8=UnaryTemplate.tape r.width ∧ actual.final.heads 8=1 ∧
    actual.final.tapes 12=UnaryTemplate.tape r.d ∧ actual.final.heads 12=0 ∧
    actual.final.tapes 22=UnaryTemplate.tape r.p ∧ actual.final.heads 22=1 ∧
    actual.final.tapes 32=UnaryTemplate.tape r.Gates ∧ actual.final.heads 32=1 ∧
    actual.steps≤budget r := by
  obtain ⟨t,ht,t0,th0,t1,th1,t2,th2,t3,th3,t4,th4,t7,th7,t8,th8,t12,th12,t13,th13,t14,th14,t17,th17,
    t18,th18,t22,th22,t23,th23,t24,th24,t27,th27,t28,th28,t32,th32,ts⟩ := three_run r
  -- zero one unary copy per bank, driven by its twin
  obtain ⟨e1,he1,e1T,e1H,e1s⟩ := RecoveryScratchErase.erase_ready (t := 1) (natBitLength r.d)
    (2*natBitLength r.d+1) (fun _ => List.replicate (natBitLength r.d) true) (by simp)
  obtain ⟨r1,hr1,s1H,s1T,s1O,s1s⟩ := stage machine eraseSlots1 (by decide) (RecoveryScratchErase.resetMachine 1)
    _ _ _ t ht _ e1 he1 rfl
    (by intro i; fin_cases i; exacts [th3,th4,th7])
    (by intro i; fin_cases i; exacts [t3,t4,t7])
  obtain ⟨e2,he2,e2T,e2H,e2s⟩ := RecoveryScratchErase.erase_ready (t := 1) (natBitLength r.p)
    (2*natBitLength r.p+1) (fun _ => List.replicate (natBitLength r.p) true) (by simp)
  obtain ⟨r2,hr2,s2H,s2T,s2O,s2s⟩ := stage (Composition.machine machine erase1) eraseSlots2 (by decide)
    (RecoveryScratchErase.resetMachine 1) _ _ _ r1 hr1 _ e2 he2 rfl
    (by
      intro i; fin_cases i
      exacts [(s1O 13 (by decide)).1.trans th13,(s1O 14 (by decide)).1.trans th14,(s1O 17 (by decide)).1.trans th17])
    (by
      intro i; fin_cases i
      exacts [(s1O 13 (by decide)).2.trans t13,(s1O 14 (by decide)).2.trans t14,(s1O 17 (by decide)).2.trans t17])
  obtain ⟨e3,he3,e3T,e3H,e3s⟩ := RecoveryScratchErase.erase_ready (t := 1) (natBitLength r.Gates)
    (2*natBitLength r.Gates+1) (fun _ => List.replicate (natBitLength r.Gates) true) (by simp)
  obtain ⟨r3,hr3,s3H,s3T,s3O,s3s⟩ := stage (Composition.machine (Composition.machine machine erase1) erase2)
    eraseSlots3 (by decide) (RecoveryScratchErase.resetMachine 1) _ _ _ r2 hr2 _ e3 he3 rfl
    (by
      intro i; fin_cases i
      exacts [((s2O 23 (by decide)).1.trans (s1O 23 (by decide)).1).trans th23,
        ((s2O 24 (by decide)).1.trans (s1O 24 (by decide)).1).trans th24,
        ((s2O 27 (by decide)).1.trans (s1O 27 (by decide)).1).trans th27])
    (by
      intro i; fin_cases i
      exacts [((s2O 23 (by decide)).2.trans (s1O 23 (by decide)).2).trans t23,
        ((s2O 24 (by decide)).2.trans (s1O 24 (by decide)).2).trans t24,
        ((s2O 27 (by decide)).2.trans (s1O 27 (by decide)).2).trans t27])
  -- the ten all-false cells after the sweeps, heads at 0
  have z2 : r3.final.tapes 2=List.replicate (r3.final.tapes 2).length false := allFalse_replicate
    ((((s3O 2 (by decide)).2.trans (s2O 2 (by decide)).2).trans (s1O 2 (by decide)).2).trans t2)
  have z3 : r3.final.tapes 3=List.replicate (r3.final.tapes 3).length false := allFalse_replicate
    (((s3O 3 (by decide)).2.trans (s2O 3 (by decide)).2).trans ((s1T 0).trans (congrFun e1T 0)))
  have z7 : r3.final.tapes 7=List.replicate (r3.final.tapes 7).length false := allFalse_replicate
    (((s3O 7 (by decide)).2.trans (s2O 7 (by decide)).2).trans ((s1T 2).trans (congrFun e1T 2)))
  have z8 : r3.final.tapes 8=List.replicate (r3.final.tapes 8).length false := allFalse_of_pad_one (by
    rw [(((s3O 8 (by decide)).2.trans (s2O 8 (by decide)).2).trans (s1O 8 (by decide)).2)]; exact t8)
  have z13 : r3.final.tapes 13=List.replicate (r3.final.tapes 13).length false := allFalse_replicate
    ((s3O 13 (by decide)).2.trans ((s2T 0).trans (congrFun e2T 0)))
  have z17 : r3.final.tapes 17=List.replicate (r3.final.tapes 17).length false := allFalse_replicate
    ((s3O 17 (by decide)).2.trans ((s2T 2).trans (congrFun e2T 2)))
  have z18 : r3.final.tapes 18=List.replicate (r3.final.tapes 18).length false := allFalse_of_pad_one (by
    rw [(((s3O 18 (by decide)).2.trans (s2O 18 (by decide)).2).trans (s1O 18 (by decide)).2)]; exact t18)
  have z23 : r3.final.tapes 23=List.replicate (r3.final.tapes 23).length false := allFalse_replicate
    ((s3T 0).trans (congrFun e3T 0))
  have z27 : r3.final.tapes 27=List.replicate (r3.final.tapes 27).length false := allFalse_replicate
    ((s3T 2).trans (congrFun e3T 2))
  have z28 : r3.final.tapes 28=List.replicate (r3.final.tapes 28).length false := allFalse_of_pad_one (by
    rw [(((s3O 28 (by decide)).2.trans (s2O 28 (by decide)).2).trans (s1O 28 (by decide)).2)]; exact t28)
  have len8 : (r3.final.tapes 8).length ≤ 1 := length_le_of_pad_one (by
    rw [(((s3O 8 (by decide)).2.trans (s2O 8 (by decide)).2).trans (s1O 8 (by decide)).2)]; exact t8)
  have w1 : r3.final.tapes 1=word r :=
    (((s3O 1 (by decide)).2.trans (s2O 1 (by decide)).2).trans (s1O 1 (by decide)).2).trans t1
  have wh1 : r3.final.heads 1=(natWord r.d++natWord r.p++natWord r.Gates).length :=
    (((s3O 1 (by decide)).1.trans (s2O 1 (by decide)).1).trans (s1O 1 (by decide)).1).trans th1
  -- the weight-count parse on the zeroed cells
  obtain ⟨dp,hdp,d0,dh0,_,_,_,_,_,_,_,_,d5,dh5,d6,dh6,d10,dh10,ds⟩ := MatrixDimensionPrepare.scratch_run
    (natWord r.d++natWord r.p++natWord r.Gates) (MatrixScorePhi.columnsWord r.width r.cols++r.cuts.flatMap (cutWord r.p))
    (natBitLength r.width) r.width (Nat.lt_pow_succ_log_self (by decide) _)
  rw [word_width] at hdp d0
  let cap : Fin 11 → ℕ := fun i => (r3.final.tapes (widthSlots i)).length
  obtain ⟨dz,hdz,dzf,dzs,_⟩ := ZeroPadding.run_config MatrixDimensionPrepare.machine cap _ _ dp hdp
  have dIn (i : Fin 11) : (MatrixDimensionPrepare.input (word r) (natWord r.d++natWord r.p++natWord r.Gates).length).tapes i=
      if i=0 then word r else [] := by
    fin_cases i <;> simp [MatrixDimensionPrepare.input,TapeEmbedding.config,MatrixDimensionField.input,
      MatrixDimensionHeader.input,Fin.addCases,Composition.leftConfig]
  have dInH (i : Fin 11) : (MatrixDimensionPrepare.input (word r) (natWord r.d++natWord r.p++natWord r.Gates).length).heads i=
      if i=0 then (natWord r.d++natWord r.p++natWord r.Gates).length else 0 := by
    fin_cases i <;> simp [MatrixDimensionPrepare.input,TapeEmbedding.config,MatrixDimensionField.input,
      MatrixDimensionHeader.input,Fin.addCases,Composition.leftConfig]
  have zh (j : Fin 33) (h1 : j ≠ 1) (h : RecoveryFocus.pick eraseSlots1 j=none ∧ RecoveryFocus.pick eraseSlots2 j=none ∧
      RecoveryFocus.pick eraseSlots3 j=none) : r3.final.heads j=t.final.heads j :=
    (((s3O j h.2.2).1.trans (s2O j h.2.1).1).trans (s1O j h.1).1)
  obtain ⟨r4,hr4,s4H,s4T,s4O,s4s⟩ := stage (Composition.machine (Composition.machine (Composition.machine
    machine erase1) erase2) erase3) widthSlots (by decide) MatrixDimensionPrepare.machine _ _ _ r3 hr3 _ dz hdz rfl
    (by
      intro i
      change r3.final.heads (widthSlots i)=(MatrixDimensionPrepare.input (word r)
        (natWord r.d++natWord r.p++natWord r.Gates).length).heads i
      rw [dInH]
      fin_cases i
      · exact wh1
      · exact ((s3O 3 (by decide)).1.trans (s2O 3 (by decide)).1).trans ((s1H 0).trans (e1H 0))
      · exact (s3O 13 (by decide)).1.trans ((s2H 0).trans (e2H 0))
      · exact (s3H 0).trans (e3H 0)
      · exact ((s3O 7 (by decide)).1.trans (s2O 7 (by decide)).1).trans ((s1H 2).trans (e1H 2))
      · exact (s3O 17 (by decide)).1.trans ((s2H 2).trans (e2H 2))
      · exact (s3H 2).trans (e3H 2)
      · exact (zh 2 (by decide) ⟨by decide,by decide,by decide⟩).trans th2
      · exact (zh 18 (by decide) ⟨by decide,by decide,by decide⟩).trans th18
      · exact (zh 28 (by decide) ⟨by decide,by decide,by decide⟩).trans th28
      · exact (zh 8 (by decide) ⟨by decide,by decide,by decide⟩).trans th8)
    (by
      intro i
      change r3.final.tapes (widthSlots i)=ZeroPadding.pad (cap i) ((MatrixDimensionPrepare.input (word r)
        (natWord r.d++natWord r.p++natWord r.Gates).length).tapes i)
      rw [dIn]
      fin_cases i
      · change r3.final.tapes 1=ZeroPadding.pad (r3.final.tapes 1).length (word r)
        rw [w1]; exact (pad_self _).symm
      · exact (pad_nil_self _ z3).symm
      · exact (pad_nil_self _ z13).symm
      · exact (pad_nil_self _ z23).symm
      · exact (pad_nil_self _ z7).symm
      · exact (pad_nil_self _ z17).symm
      · exact (pad_nil_self _ z27).symm
      · exact (pad_nil_self _ z2).symm
      · exact (pad_nil_self _ z18).symm
      · exact (pad_nil_self _ z28).symm
      · exact (pad_nil_self _ z8).symm)
  have r4t1 : r4.final.tapes 1=word r := by
    rw [show r4.final.tapes 1=dz.final.tapes 0 from s4T 0,dzf]
    change ZeroPadding.pad (r3.final.tapes 1).length (dp.final.tapes 0)=_
    rw [d0,w1]; exact pad_self _
  have r4h1 : r4.final.heads 1=(columnsStart r).length := by
    rw [show r4.final.heads 1=dz.final.heads 0 from s4H 0,dzf]
    change dp.final.heads 0=_
    rw [dh0]
    simp [columnsStart,WilliamsInputHeader.natWord_eq]
    omega
  have r4t8 : r4.final.tapes 8=UnaryTemplate.tape r.width := by
    rw [show r4.final.tapes 8=dz.final.tapes 10 from s4T 10,dzf]
    change ZeroPadding.pad (r3.final.tapes 8).length (dp.final.tapes 10)=_
    rw [d10]
    exact pad_long _ _ (by rw [template_length]; omega)
  have r4h8 : r4.final.heads 8=1 := by
    rw [show r4.final.heads 8=dz.final.heads 10 from s4H 10,dzf]
    exact dh10
  have z17' : r4.final.tapes 17=List.replicate (r4.final.tapes 17).length false := by
    rw [show r4.final.tapes 17=dz.final.tapes 5 from s4T 5,dzf]
    exact pad_allFalse _ _ (allFalse_replicate d5)
  have zh17 : r4.final.heads 17=0 := by
    rw [show r4.final.heads 17=dz.final.heads 5 from s4H 5,dzf]
    exact dh5
  have z27' : r4.final.tapes 27=List.replicate (r4.final.tapes 27).length false := by
    rw [show r4.final.tapes 27=dz.final.tapes 6 from s4T 6,dzf]
    exact pad_allFalse _ _ (allFalse_of_pad_one d6)
  have zh27 : r4.final.heads 27=0 := by
    rw [show r4.final.heads 27=dz.final.heads 6 from s4H 6,dzf]
    exact dh6
  -- return the frame counter's head to cell 0
  obtain ⟨ad,had,adh,adt,ads⟩ := retreat_run (UnaryTemplate.tape r.d) 0
  have keep12 : r4.final.heads 12=1 ∧ r4.final.tapes 12=UnaryTemplate.tape r.d := by
    have h4 := s4O 12 (by decide)
    have h3 := s3O 12 (by decide)
    have h2 := s2O 12 (by decide)
    have h1 := s1O 12 (by decide)
    exact ⟨((((h4.1.trans h3.1).trans h2.1).trans h1.1).trans th12),((((h4.2.trans h3.2).trans h2.2).trans h1.2).trans t12)⟩
  obtain ⟨r5,hr5,s5H,s5T,s5O,s5s⟩ := stage (Composition.machine (Composition.machine (Composition.machine
    (Composition.machine machine erase1) erase2) erase3) width) backSlots (by decide) retreat _ _ _ r4 hr4 _ ad had rfl
    (by intro i; fin_cases i; exact keep12.1)
    (by intro i; fin_cases i; exact keep12.2)
  -- the columns of φ, counted by the unary d
  obtain ⟨cc,hcc,hccf,hccs⟩ := MatrixBatchColumnsCopy.copy_run r.width r.cols (columnsStart r)
    (r.cuts.flatMap (cutWord r.p))
  rw [word_columns,cols_length] at hcc hccf
  rw [cols_length] at hccs
  let capC : Fin 4 → ℕ := fun i => (r5.final.tapes (copySlots i)).length
  obtain ⟨cz,hcz,czf,czs,_⟩ := ZeroPadding.run_config MatrixBatchColumnsCopy.machine capC _ _ cc hcc
  have r5t1 : r5.final.tapes 1=word r := (s5O 1 (by decide)).2.trans r4t1
  have r5t12 : r5.final.tapes 12=UnaryTemplate.tape r.d := (s5T 0).trans adt
  obtain ⟨r6,hr6,s6H,s6T,s6O,s6s⟩ := stage (Composition.machine (Composition.machine (Composition.machine
    (Composition.machine (Composition.machine machine erase1) erase2) erase3) width) back) copySlots (by decide)
    MatrixBatchColumnsCopy.machine _ _ _ r5 hr5 _ cz hcz rfl
    (by
      intro i; fin_cases i
      · exact (s5O 1 (by decide)).1.trans r4h1
      · exact (s5O 17 (by decide)).1.trans zh17
      · exact (s5O 27 (by decide)).1.trans zh27
      · exact (s5H 0).trans adh)
    (by
      intro i; fin_cases i
      · change r5.final.tapes 1=ZeroPadding.pad (r5.final.tapes 1).length (word r)
        rw [r5t1]; exact (pad_self _).symm
      · change r5.final.tapes 17=ZeroPadding.pad (r5.final.tapes 17).length []
        rw [(s5O 17 (by decide)).2]; exact (pad_nil_self _ z17').symm
      · change r5.final.tapes 27=ZeroPadding.pad (r5.final.tapes 27).length []
        rw [(s5O 27 (by decide)).2]; exact (pad_nil_self _ z27').symm
      · change r5.final.tapes 12=ZeroPadding.pad (r5.final.tapes 12).length (UnaryTemplate.tape r.d)
        rw [r5t12]; exact (pad_self _).symm)
  -- everything else is carried from the three-header parse
  have carry (j : Fin 33) (h : RecoveryFocus.pick eraseSlots1 j=none ∧ RecoveryFocus.pick eraseSlots2 j=none ∧
      RecoveryFocus.pick eraseSlots3 j=none ∧ RecoveryFocus.pick widthSlots j=none ∧
      RecoveryFocus.pick backSlots j=none ∧ RecoveryFocus.pick copySlots j=none) :
      r6.final.heads j=t.final.heads j ∧ r6.final.tapes j=t.final.tapes j := by
    obtain ⟨h1,h2,h3,h4,h5,h6⟩ := h
    exact ⟨(((((s6O j h6).1.trans (s5O j h5).1).trans (s4O j h4).1).trans (s3O j h3).1).trans (s2O j h2).1).trans
        (s1O j h1).1,
      (((((s6O j h6).2.trans (s5O j h5).2).trans (s4O j h4).2).trans (s3O j h3).2).trans (s2O j h2).2).trans
        (s1O j h1).2⟩
  have c0 := carry 0 ⟨by decide,by decide,by decide,by decide,by decide,by decide⟩
  have c22 := carry 22 ⟨by decide,by decide,by decide,by decide,by decide,by decide⟩
  have c32 := carry 32 ⟨by decide,by decide,by decide,by decide,by decide,by decide⟩
  refine ⟨r6,hr6,c0.2.trans t0,c0.1.trans th0,?_,?_,?_,?_,?_,?_,c22.2.trans t22,c22.1.trans th22,
    c32.2.trans t32,c32.1.trans th32,?_⟩
  · rw [show r6.final.tapes 1=cz.final.tapes 0 from s6T 0,czf]
    change ZeroPadding.pad (r5.final.tapes 1).length (cc.final.tapes 0)=_
    rw [hccf,r5t1]
    exact pad_self _
  · rw [show r6.final.heads 1=cz.final.heads 0 from s6H 0,czf]
    change cc.final.heads 0=_
    rw [hccf]
    exact header_length r
  · exact ((s6O 8 (by decide)).2.trans (s5O 8 (by decide)).2).trans r4t8
  · exact ((s6O 8 (by decide)).1.trans (s5O 8 (by decide)).1).trans r4h8
  · rw [show r6.final.tapes 12=cz.final.tapes 3 from s6T 3,czf]
    change ZeroPadding.pad (r5.final.tapes 12).length (cc.final.tapes 3)=_
    rw [hccf,r5t12]
    exact pad_self _
  · rw [show r6.final.heads 12=cz.final.heads 3 from s6H 3,czf]
    change cc.final.heads 3=_
    rw [hccf]
    rfl
  · rw [s6s,s5s,s4s,s3s,s2s,s1s,czs,hccs,ads,dzs,e1s,e2s,e3s]
    have hd := ds
    have htb := ts
    unfold budget
    unfold threeBudget at htb
    omega

end NearCubicWires.RepairOrdinary.MatrixCoefficientHeaders
