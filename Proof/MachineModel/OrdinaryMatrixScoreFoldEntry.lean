import Proof.MachineModel.OrdinaryMatrixScoreInitialize

/-! One complete reusable assignment fold: real work clearing, real constant
copies, then every literal signed weight against the framed assignment. -/
namespace NearCubicWires.RepairOrdinary.MatrixScoreFoldEntry
open LocalBitMultitape RecoveryRootRound SignedSortKey MatrixScoreWeight
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def initSlots : Fin 16 → Fin 20 := ![2,3,4,5,7,8,9,10,11,12,13,14,15,16,18,19]
theorem init_injective : Function.Injective initSlots := by decide
def initPick : Fin 20 → Option (Fin 16) := ![none,none,some 0,some 1,some 2,some 3,none,
  some 4,some 5,some 6,some 7,some 8,some 9,some 10,some 11,some 12,some 13,none,some 14,some 15]
theorem pick_init (i : Fin 20) : RecoveryFocus.pick initSlots i=initPick i := by
  fin_cases i
  all_goals first
    | decide
    | exact RecoveryFocus.pick_slot initSlots init_injective 0
    | exact RecoveryFocus.pick_slot initSlots init_injective 1
    | exact RecoveryFocus.pick_slot initSlots init_injective 2
    | exact RecoveryFocus.pick_slot initSlots init_injective 3
    | exact RecoveryFocus.pick_slot initSlots init_injective 4
    | exact RecoveryFocus.pick_slot initSlots init_injective 5
    | exact RecoveryFocus.pick_slot initSlots init_injective 6
    | exact RecoveryFocus.pick_slot initSlots init_injective 7
    | exact RecoveryFocus.pick_slot initSlots init_injective 8
    | exact RecoveryFocus.pick_slot initSlots init_injective 9
    | exact RecoveryFocus.pick_slot initSlots init_injective 10
    | exact RecoveryFocus.pick_slot initSlots init_injective 11
    | exact RecoveryFocus.pick_slot initSlots init_injective 12
    | exact RecoveryFocus.pick_slot initSlots init_injective 13
    | exact RecoveryFocus.pick_slot initSlots init_injective 14
    | exact RecoveryFocus.pick_slot initSlots init_injective 15
noncomputable def first : Machine 20 16 := RecoveryFocus.machine initSlots MatrixScoreInitialize.machine
noncomputable def last : Machine 20 49 := TapeEmbedding.machine 2 MatrixScoreWeightList.machine
noncomputable def machine := Composition.machine first last
def heads (pos apos : ℕ) : Fin 20 → ℕ := ![pos,apos,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0]
def tapes (source assignment : List Bool) (d c cap w x y : ℕ) (work : Fin 12 → List Bool) : Fin 20 → List Bool :=
  ![source,assignment,work 0,work 1,work 2,work 3,List.replicate w true,work 4,work 5,work 6,
    work 7,work 8,work 9,work 10,work 11,List.replicate c true,zeros cap,UnaryTemplate.tape d,
    frame (binary w x),frame (binary w y)]
def accumulators (c w p n : ℕ) (scratch : Fin 10 → List Bool) : Fin 12 → List Bool :=
  ![scratch 0,scratch 1,scratch 2,scratch 3,scratch 4,scratch 5,scratch 6,
    scalar c w p,scalar c w n,scratch 7,scratch 8,scratch 9]
def budget (d c p w : ℕ) := (2*c+16*w+22)+1+(d*(2*c+4*p+16*w+34)+3)
noncomputable def input (source assignment : List Bool) (pos apos d c cap w x y : ℕ) (work : Fin 12 → List Bool) :
    Configuration 20 65 := ⟨machine.start,heads pos apos,tapes source assignment d c cap w x y work⟩

theorem entry_run (weights : List ℤ) (pre suffix apre asuffix : List Bool) (p n c cap w x y : ℕ)
    (work : Fin 12 → List Bool) (hf : ∀ z ∈ weights,z.natAbs<2^p)
    (hw : p≤w) (hc : 4*w+3≤c) (hcap : cap≤c+1) (hs : ∀ i,(work i).length≤c)
    (hx : x+MatrixScoreBatch.part false weights n<2^w)
    (hy : y+MatrixScoreBatch.part true weights n<2^w) :
    ∃ scratch : Fin 10 → List Bool,(∀ i,(scratch i).length≤c) ∧
      ∃ actual,runFrom machine (budget weights.length c p w)
        (input (pre++MatrixScoreCanonical.fields p weights++suffix)
          (apre++frame (binary weights.length n)++asuffix) pre.length apre.length
          weights.length c cap w x y work)=some actual ∧
        actual.final.heads=heads (pre.length+(MatrixScoreCanonical.fields p weights).length)
          (apre.length+2*weights.length) ∧
        actual.final.tapes=tapes (pre++MatrixScoreCanonical.fields p weights++suffix)
          (apre++frame (binary weights.length n)++asuffix) weights.length c (c+1) w x y
          (accumulators c w (x+MatrixScoreBatch.part false weights n)
            (y+MatrixScoreBatch.part true weights n) scratch) ∧ actual.steps≤budget weights.length c p w := by
  let source := pre++MatrixScoreCanonical.fields p weights++suffix
  let assignment := apre++frame (binary weights.length n)++asuffix
  have ready := MatrixScoreInitialize.initialize_ready c cap w x y work hc hcap hs
  obtain ⟨initialized,hi,hih,hit,his⟩ := HierarchyBinary.focused_run initSlots init_injective
    MatrixScoreInitialize.machine _ _ ready (heads pre.length apre.length)
    (tapes source assignment weights.length c cap w x y work)
    (by intro i; fin_cases i <;> rfl) (by intro i; fin_cases i <;> rfl)
  have initializedTapes : initialized.final.tapes=tapes source assignment weights.length c (c+1) w x y
      (accumulators c w x y (fun _ => zeros c)) := by
    rw [hit]
    funext i
    fin_cases i <;> simp [install,pick_init,initPick,tapes,accumulators,
      MatrixScoreInitialize.tapes,MatrixScoreInitialize.prepared]
  obtain ⟨scratch,hss,folded,hfRun,hff,hfs⟩ := MatrixScoreCanonical.fold_run weights pre suffix apre asuffix
    p n c w x y (fun _ => zeros c) hf hw hc (by intro i; simp [zeros]) hx hy
  let padding : Fin 18 → ℕ := fun i => if i=17 then weights.length+2 else 0
  obtain ⟨padded,hp,hpf,hps,_⟩ := ZeroPadding.run_config MatrixScoreWeightList.machine padding _ _ folded hfRun
  have he := TapeEmbedding.run_embed MatrixScoreWeightList.machine (fun _ : Fin 2 => 0)
    ![frame (binary w x),frame (binary w y)] _ _ padded hp
  let expanded := TapeEmbedding.receipt (fun _ : Fin 2 => 0) ![frame (binary w x),frame (binary w y)] padded
  have hrestart : TapeEmbedding.config (fun _ : Fin 2 => 0) ![frame (binary w x),frame (binary w y)]
      (ZeroPadding.config padding (RepeatMachine.cfg 0 (MatrixScoreWeightCycle.input source assignment pre.length apre.length c w x y
        (fun _ => zeros c)) weights.length 1))=Composition.restart initialized.final last.start := by
    apply configuration_ext
    · rfl
    · funext i
      fin_cases i <;> simp [Composition.restart,hih,TapeEmbedding.config,Fin.addCases,
        ZeroPadding.config,RepeatMachine.cfg,controlConfig,MatrixScoreWeightCycle.input,MatrixScoreWeightClear.heads,heads]
    · rw [show (Composition.restart initialized.final last.start).tapes=initialized.final.tapes by rfl,initializedTapes]
      funext i
      fin_cases i <;> simp [TapeEmbedding.config,Fin.addCases,RepeatMachine.cfg,controlConfig,
        MatrixScoreWeightCycle.input,MatrixScoreWeightClear.tapes,tapes,accumulators,
        ZeroPadding.config,padding,ZeroPadding.pad,CompareMachine.word,UnaryTemplate.tape]
  rw [hrestart] at he
  have joined := Composition.run_join first last (2*c+16*w+22)
    (weights.length*(2*c+4*p+16*w+34)+3) _ initialized expanded hi he
  refine ⟨scratch,hss,Composition.joinedReceipt initialized expanded,joined,?_,?_,?_⟩
  · funext i
    fin_cases i <;> simp [Composition.joinedReceipt,Composition.rightConfig,expanded,TapeEmbedding.receipt,
      TapeEmbedding.config,Fin.addCases,hpf,ZeroPadding.config,hff,RepeatMachine.cfg,controlConfig,MatrixScoreWeightCycle.input,
      MatrixScoreWeightClear.heads,heads]
  · funext i
    fin_cases i <;> simp [Composition.joinedReceipt,Composition.rightConfig,expanded,TapeEmbedding.receipt,
      TapeEmbedding.config,Fin.addCases,hpf,ZeroPadding.config,hff,RepeatMachine.cfg,controlConfig,MatrixScoreWeightCycle.input,
      MatrixScoreWeightClear.tapes,tapes,accumulators,padding,ZeroPadding.pad,CompareMachine.word,UnaryTemplate.tape]
  · change initialized.steps+1+padded.steps≤_
    rw [his,hps]
    unfold budget
    omega

end NearCubicWires.RepairOrdinary.MatrixScoreFoldEntry
