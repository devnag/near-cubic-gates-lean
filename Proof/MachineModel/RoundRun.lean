import Proof.MachineModel.Round

/-! P25: one complete occurrence round, stated by its ports.

Five docked stages: framed request copy, the SAME selected decomposition
constructor on the reusable bank, the actual child-count word, the actual child
body, and the running unary total. Every stage is `RecoveryFocus`-docked and
every junction is a `Composition.run_join`. -/
namespace NearCubicWires.ExtDecompositionBatch
open LocalBitMultitape RepairOrdinary RepairRepresentation ExecutableInterfaces
open RepairOrdinary.DecompositionSource RepairOrdinary.RecoveryRootRound SupplierPipeline
open RepairOrdinary.CloseoutRowsCircuitBottom
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

variable (a : DecompositionAlgorithm)

theorem ne_of_val {i j : Fin (T a)} (h : i.val ≠ j.val) : i ≠ j := fun he => h (congrArg Fin.val he)

theorem bk_ne_named (i : Fin (SB a)) (j : Fin 12) : bk a i ≠ ex a j := bk_ne_ex a i j

/-! ## The five stage machines -/

noncomputable def stage1 := RecoveryFocus.machine (copySlots a) FrameCopy.machine
noncomputable def stage2 := RecoveryFocus.machine (bk a) (Counted.machine a)
noncomputable def stage3 := RecoveryFocus.machine (fieldSlots a) (PCPPQueryField.machine true)
noncomputable def stage4 := RecoveryFocus.machine (recSlots a) Records.machine
noncomputable def stage5 := RecoveryFocus.machine (totSlots a) TotalsAppend.machine

noncomputable def bodyM :=
  Composition.machine (Composition.machine (Composition.machine
    (Composition.machine (stage1 a) (stage2 a)) (stage3 a)) (stage4 a)) (stage5 a)

def bodyCost (q : ℕ) (g : SupportedNormalizedGate q) : ℕ :=
  (2*(frame (nativeWord g)).length+2) + 1 + Counted.budget a (request g) + 1 +
    (2*natBitLength (children a g).length+3) + 1 +
    (((children a g).flatMap exactWord).length + (6*q+10)*(children a g).length + 3) + 1 +
    (2*(children a g).length+2)

/-! ## Stage 1: the framed native request is copied into the reusable bank -/

theorem stage1_step (C q : ℕ) (g : SupportedNormalizedGate q) (pre rest : List Bool)
    (H : Fin (T a) → ℕ) (A : Fin (T a) → List Bool)
    (hbankT : ∀ i, A (bk a i) = List.replicate C false)
    (hbankH : ∀ i, H (bk a i) = 0)
    (hstrT : A (str a) = pre ++ frame (nativeWord g) ++ rest) (hstrH : H (str a) = pre.length)
    (hfcpT : A (fcp a) = List.replicate C false) (hfcpH : H (fcp a) = 0)
    (hL : (frame (nativeWord g)).length ≤ C) :
    Step (stage1 a) (2*(frame (nativeWord g)).length+2) H A
      (dockH (copySlots a) H ![pre.length + (frame (nativeWord g)).length, 0, 0])
      (install (copySlots a) A
        ![pre ++ frame (nativeWord g) ++ rest, ZeroPadding.pad C (frame (nativeWord g)),
          List.replicate C false]) := by
  classical
  set w := nativeWord g with hw
  set S := pre ++ frame w ++ rest with hS
  obtain ⟨r1, hr1, hf1, hs1⟩ := FrameCopy.copy_run pre w rest
  have base1 : Step FrameCopy.machine (2*(frame w).length+2) ![pre.length, 0, 0] ![S, [], []]
      ![pre.length + (frame w).length, 0, 0] ![S, frame w, List.replicate (frame w).length false] :=
    ⟨r1, hr1, by rw [hf1]; funext i; fin_cases i <;> rfl, by rw [hf1]; funext i; fin_cases i <;> rfl,
      le_of_eq hs1⟩
  have pad1 := base1.pad ![0, C, C]
  have e1a : (fun i : Fin 3 => ZeroPadding.pad (![0, C, C] i) (![S, [], []] i)) =
      ![S, List.replicate C false, List.replicate C false] := by
    funext i; fin_cases i
    · exact ZeroPadding.pad_zero S
    · simp [ZeroPadding.pad]
    · simp [ZeroPadding.pad]
  have e1b : (fun i : Fin 3 => ZeroPadding.pad (![0, C, C] i)
        (![S, frame w, List.replicate (frame w).length false] i)) =
      ![S, ZeroPadding.pad C (frame w), List.replicate C false] := by
    funext i; fin_cases i
    · exact ZeroPadding.pad_zero S
    · rfl
    · exact pad_replicate_false C _ hL
  rw [e1a, e1b] at pad1
  exact pad1.dock (copySlots a) (copy_injective a) H A
    (by intro j; fin_cases j
        · exact hstrH
        · exact hbankH (Counted.localTape a 0)
        · exact hfcpH)
    (by intro j; fin_cases j
        · exact hstrT
        · exact hbankT (Counted.localTape a 0)
        · exact hfcpT)

/-! ## Ports of the stage-1 ambient -/

theorem stage1_bankT (C q : ℕ) (g : SupportedNormalizedGate q) (pre rest : List Bool)
    (A : Fin (T a) → List Bool) (hbankT : ∀ i, A (bk a i) = List.replicate C false) (i : Fin (SB a)) :
    install (copySlots a) A
        ![pre ++ frame (nativeWord g) ++ rest, ZeroPadding.pad C (frame (nativeWord g)),
          List.replicate C false] (bk a i) =
      ZeroPadding.pad C (Counted.input a (request g) i) := by
  classical
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13⟩ := port_facts a
  by_cases h0 : i.val = 0
  · have hbin : bk a i = copySlots a 1 := by
      change bk a i = bin a
      refine congrArg (bk a) (Fin.ext ?_)
      rw [local_val a 0]
      exact h0
    rw [hbin, install_slot (copySlots a) (copy_injective a) A _ 1]
    rw [counted_input_val a (request g) i, if_pos h0, nativeWord_input g]
    rfl
  · have hne : ∀ j : Fin 3, copySlots a j ≠ bk a i := by
      intro j
      apply ne_of_val
      unfold copySlots
      have hi := i.isLt
      split_ifs <;> simp only [str, fcp, ex_val, bk_val, p1] <;> omega
    rw [install_other (copySlots a) A _ (bk a i) hne, hbankT i,
      counted_input_val a (request g) i, if_neg h0]
    simp [ZeroPadding.pad]

theorem stage1_bankH (q : ℕ) (g : SupportedNormalizedGate q) (pre : ℕ)
    (H : Fin (T a) → ℕ) (hbankH : ∀ i, H (bk a i) = 0) (i : Fin (SB a)) :
    dockH (copySlots a) H ![pre + (frame (nativeWord g)).length, 0, 0] (bk a i) = 0 := by
  classical
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13⟩ := port_facts a
  by_cases h0 : i.val = 0
  · have hbin : bk a i = copySlots a 1 := by
      change bk a i = bin a
      refine congrArg (bk a) (Fin.ext ?_)
      rw [local_val a 0]
      exact h0
    rw [hbin, dockH_slot (copySlots a) (copy_injective a) H _ 1]
    rfl
  · have hne : ∀ j : Fin 3, copySlots a j ≠ bk a i := by
      intro j
      apply ne_of_val
      unfold copySlots
      have hi := i.isLt
      split_ifs <;> simp only [str, fcp, ex_val, bk_val, p1] <;> omega
    rw [dockH_other (copySlots a) H _ (bk a i) hne, hbankH i]

theorem copy_other (i : Fin (T a)) (hb : ∀ j, bk a j ≠ i) (hs : i ≠ str a) (hf : i ≠ fcp a) :
    ∀ j : Fin 3, copySlots a j ≠ i := by
  intro j
  unfold copySlots
  split_ifs
  · exact Ne.symm hs
  · exact hb (Counted.localTape a 0)
  · exact Ne.symm hf

/-! ## Stage 2: the SAME selected decomposition constructor, once -/

theorem stage2_step (C q : ℕ) (g : SupportedNormalizedGate q)
    (H : Fin (T a) → ℕ) (A : Fin (T a) → List Bool)
    (hbankT : ∀ i, A (bk a i) = ZeroPadding.pad C (Counted.input a (request g) i))
    (hbankH : ∀ i, H (bk a i) = 0)
    (hC : (frame (nativeWord g)).length + Counted.budget a (request g) ≤ C) :
    ∃ (K : Fin (SB a) → List Bool) (KH : Fin (SB a) → ℕ),
      Step (stage2 a) (Counted.budget a (request g)) H A (dockH (bk a) H KH) (install (bk a) A K) ∧
      K (Counted.sourceTape a) = ZeroPadding.pad C (exactListWord (children a g)) ∧
      KH (Counted.sourceTape a) = 0 ∧
      K (Counted.fresh a 9) = ZeroPadding.pad C (UnaryTemplate.tape (children a g).length) ∧
      KH (Counted.fresh a 9) = 1 ∧ KH (Counted.localTape a 14) = 0 ∧
      (∀ i, (K i).length ≤ C) := by
  classical
  obtain ⟨rc, hrun, hsteps, hsrc, hsrcH, hcnt9, hcnt9H, harity, harityH, hback, hbackH, hout, houtH⟩ :=
    Counted.counted_run a (request g)
  have base : Step (Counted.machine a) (Counted.budget a (request g)) (fun _ => 0)
      (Counted.input a (request g)) rc.final.heads rc.final.tapes := ⟨rc, hrun, rfl, rfl, hsteps⟩
  have padded := base.pad (fun _ => C)
  have hlen : ∀ i, (rc.final.tapes i).length ≤
      (frame (nativeWord g)).length + Counted.budget a (request g) := by
    intro i
    have h1 := one_tape_support (Counted.machine a) (Counted.budget a (request g))
      (initialConfiguration (Counted.machine a) (Counted.input a (request g))) rc i
      ((frame (nativeWord g)).length) hrun (by simp [initialConfiguration]) (by
        simp only [initialConfiguration]
        rw [counted_input_val a (request g) i]
        split_ifs with hh
        · rw [nativeWord_input g]
        · simp)
    exact h1.trans (Nat.add_le_add_left hsteps _)
  refine ⟨fun i => ZeroPadding.pad C (rc.final.tapes i), rc.final.heads, padded.dock (bk a)
      (bk_injective a) H A (by intro j; exact hbankH j) (by intro j; exact hbankT j),
    ?_, hsrcH, ?_, hcnt9H, hbackH, ?_⟩
  · show ZeroPadding.pad C (rc.final.tapes (Counted.sourceTape a)) = _
    rw [hsrc]; rfl
  · show ZeroPadding.pad C (rc.final.tapes (Counted.fresh a 9)) = _
    rw [hcnt9]; rfl
  · intro i
    show (ZeroPadding.pad C (rc.final.tapes i)).length ≤ C
    rw [ZeroPadding.pad_length]
    exact max_le le_rfl ((hlen i).trans hC)

/-! ## Stage 3: the actual child-count word is appended to the counts port -/

theorem stage3_step (C q : ℕ) (g : SupportedNormalizedGate q) (c1 : List Bool)
    (H : Fin (T a) → ℕ) (A : Fin (T a) → List Bool)
    (hsrcT : A (bsrc a) = ZeroPadding.pad C (exactListWord (children a g))) (hsrcH : H (bsrc a) = 0)
    (hfldH : H (bfld a) = 0)
    (hcntT : A (cnt a) = c1) (hcntH : H (cnt a) = c1.length) :
    Step (stage3 a) (2*natBitLength (children a g).length+3) H A
      (dockH (fieldSlots a) H
        ![2*natBitLength (children a g).length+1, 0, (c1 ++ natWord (children a g).length).length])
      (install (fieldSlots a) A
        ![ZeroPadding.pad C (exactListWord (children a g)),
          StablePartition.Workspace.overlay
            (UnaryTemplate.tape (natBitLength (children a g).length)) (A (bfld a)),
          c1 ++ natWord (children a g).length]) := by
  classical
  obtain ⟨r3, hr3, hf3⟩ := PCPPQueryField.nat_run true []
    ((children a g).flatMap exactWord ++
      List.replicate (C - (exactListWord (children a g)).length) false) (A (bfld a)) c1
    (children a g).length
  have hsplit : ([] ++ natWord (children a g).length ++
      ((children a g).flatMap exactWord ++
        List.replicate (C - (exactListWord (children a g)).length) false)) =
      ZeroPadding.pad C (exactListWord (children a g)) := by
    simp only [ZeroPadding.pad, exactListWord, List.nil_append, List.append_assoc]
  rw [hsplit] at hr3 hf3
  have base : Step (PCPPQueryField.machine true) (2*natBitLength (children a g).length+3)
      ![0, 0, c1.length]
      ![ZeroPadding.pad C (exactListWord (children a g)), A (bfld a), c1]
      ![2*natBitLength (children a g).length+1, 0, (c1 ++ natWord (children a g).length).length]
      ![ZeroPadding.pad C (exactListWord (children a g)),
        StablePartition.Workspace.overlay
          (UnaryTemplate.tape (natBitLength (children a g).length)) (A (bfld a)),
        c1 ++ natWord (children a g).length] := by
    refine ⟨r3, hr3, ?_, ?_, le_of_eq hf3.2⟩
    · rw [hf3.1]
      funext i
      fin_cases i <;>
        simp [PCPPQueryField.payload, PCPPQueryField.cfg, PCPPQueryField.selected]
    · rw [hf3.1]
      funext i
      fin_cases i <;>
        simp [PCPPQueryField.payload, PCPPQueryField.cfg, PCPPQueryField.selected]
  exact base.dock (fieldSlots a) (field_injective a) H A
    (by intro j; fin_cases j
        · exact hsrcH
        · exact hfldH
        · exact hcntH)
    (by intro j; fin_cases j
        · exact hsrcT
        · rfl
        · exact hcntT)

/-! ## Stage 4: the actual child body is appended to the cache-body port -/

theorem stage4_step (C q : ℕ) (g : SupportedNormalizedGate q) (c2 : List Bool)
    (H : Fin (T a) → ℕ) (A : Fin (T a) → List Bool)
    (hsrcT : A (bsrc a) = ZeroPadding.pad C (exactListWord (children a g)))
    (hsrcH : H (bsrc a) = 2*natBitLength (children a g).length+1)
    (hfldH : H (bfld a) = 0)
    (hbodT : A (bod a) = c2) (hbodH : H (bod a) = c2.length)
    (hdomT : A (dom a) = UnaryTemplate.tape q) (hdomH : H (dom a) = 1)
    (hcntT : A (bcnt a) = ZeroPadding.pad C (UnaryTemplate.tape (children a g).length))
    (hcntH : H (bcnt a) = 1)
    (hk : (children a g).length + 2 ≤ C) :
    Step (stage4 a)
      (((children a g).flatMap exactWord).length + (6*q+10)*(children a g).length + 3) H A
      (dockH (recSlots a) H
        ![2*natBitLength (children a g).length+1 + ((children a g).flatMap exactWord).length, 0,
          (c2 ++ (children a g).flatMap exactWord).length, 1, 1])
      (install (recSlots a) A
        ![ZeroPadding.pad C (exactListWord (children a g)),
          Records.savedList (children a g) (A (bfld a)),
          c2 ++ (children a g).flatMap exactWord, UnaryTemplate.tape q,
          ZeroPadding.pad C (UnaryTemplate.tape (children a g).length)]) := by
  classical
  obtain ⟨r4, hr4, hf4, hs4⟩ := Records.records_run (children a g) (natWord (children a g).length)
    (List.replicate (C - (exactListWord (children a g)).length) false) (A (bfld a)) c2
  have hsplit : (natWord (children a g).length ++ (children a g).flatMap exactWord ++
      List.replicate (C - (exactListWord (children a g)).length) false) =
      ZeroPadding.pad C (exactListWord (children a g)) := by
    simp only [ZeroPadding.pad, exactListWord, List.append_assoc]
  rw [hsplit] at hr4 hf4
  have hnat : (natWord (children a g).length).length = 2*natBitLength (children a g).length+1 :=
    DecompositionSource.natWord_length _
  have base : Step Records.machine
      (((children a g).flatMap exactWord).length + (6*q+10)*(children a g).length + 3)
      ![2*natBitLength (children a g).length+1, 0, c2.length, 1, 1]
      ![ZeroPadding.pad C (exactListWord (children a g)), A (bfld a), c2,
        RepairSource.VerifierDecoding.CompareMachine.word q,
        RepairSource.VerifierDecoding.CompareMachine.word (children a g).length]
      ![2*natBitLength (children a g).length+1 + ((children a g).flatMap exactWord).length, 0,
        (c2 ++ (children a g).flatMap exactWord).length, 1, 1]
      ![ZeroPadding.pad C (exactListWord (children a g)), Records.savedList (children a g) (A (bfld a)),
        c2 ++ (children a g).flatMap exactWord,
        RepairSource.VerifierDecoding.CompareMachine.word q,
        RepairSource.VerifierDecoding.CompareMachine.word (children a g).length] := by
    refine ⟨r4, ?_, ?_, ?_, le_of_eq hs4⟩
    · have hentry : (⟨Records.machine.start,
          ![2*natBitLength (children a g).length+1, 0, c2.length, 1, 1],
          ![ZeroPadding.pad C (exactListWord (children a g)), A (bfld a), c2,
            RepairSource.VerifierDecoding.CompareMachine.word q,
            RepairSource.VerifierDecoding.CompareMachine.word (children a g).length]⟩ :
            Configuration 5 _) =
          Records.cfg 0 (ZeroPadding.pad C (exactListWord (children a g)))
            (natWord (children a g).length).length (A (bfld a)) c2 q (children a g).length 1 := by
        apply configuration_ext
        · rfl
        · funext i; fin_cases i <;> simp [Records.cfg, Records.store, RepairSource.VerifierDecoding.RepeatMachine.cfg, controlConfig, TapeEmbedding.config, Fin.addCases, hnat]
        · funext i; fin_cases i <;> rfl
      rw [hentry]; exact hr4
    · rw [hf4]; funext i; fin_cases i <;> simp [Records.cfg, Records.store, RepairSource.VerifierDecoding.RepeatMachine.cfg, controlConfig, TapeEmbedding.config, Fin.addCases, hnat]
    · rw [hf4]; funext i; fin_cases i <;> rfl
  have padded := base.pad ![0, 0, 0, q+2, C]
  have e4a : (fun i : Fin 5 => ZeroPadding.pad (![0, 0, 0, q+2, C] i)
        (![ZeroPadding.pad C (exactListWord (children a g)), A (bfld a), c2,
          RepairSource.VerifierDecoding.CompareMachine.word q,
          RepairSource.VerifierDecoding.CompareMachine.word (children a g).length] i)) =
      ![ZeroPadding.pad C (exactListWord (children a g)), A (bfld a), c2, UnaryTemplate.tape q,
        ZeroPadding.pad C (UnaryTemplate.tape (children a g).length)] := by
    funext i; fin_cases i
    · exact ZeroPadding.pad_zero _
    · exact ZeroPadding.pad_zero _
    · exact ZeroPadding.pad_zero _
    · exact Records.template_pad q
    · exact pad_template C (children a g).length hk
  have e4b : (fun i : Fin 5 => ZeroPadding.pad (![0, 0, 0, q+2, C] i)
        (![ZeroPadding.pad C (exactListWord (children a g)),
          Records.savedList (children a g) (A (bfld a)), c2 ++ (children a g).flatMap exactWord,
          RepairSource.VerifierDecoding.CompareMachine.word q,
          RepairSource.VerifierDecoding.CompareMachine.word (children a g).length] i)) =
      ![ZeroPadding.pad C (exactListWord (children a g)),
        Records.savedList (children a g) (A (bfld a)), c2 ++ (children a g).flatMap exactWord,
        UnaryTemplate.tape q, ZeroPadding.pad C (UnaryTemplate.tape (children a g).length)] := by
    funext i; fin_cases i
    · exact ZeroPadding.pad_zero _
    · exact ZeroPadding.pad_zero _
    · exact ZeroPadding.pad_zero _
    · exact Records.template_pad q
    · exact pad_template C (children a g).length hk
  rw [e4a, e4b] at padded
  exact padded.dock (recSlots a) (rec_injective a) H A
    (by intro j; fin_cases j
        · exact hsrcH
        · exact hfldH
        · exact hbodH
        · exact hdomH
        · exact hcntH)
    (by intro j; fin_cases j
        · exact hsrcT
        · rfl
        · exact hbodT
        · exact hdomT
        · exact hcntT)

/-! ## Stage 5: the running unary total -/

theorem stage5_step (C q : ℕ) (g : SupportedNormalizedGate q) (c3 : List Bool)
    (H : Fin (T a) → ℕ) (A : Fin (T a) → List Bool)
    (hcntT : A (bcnt a) = ZeroPadding.pad C (UnaryTemplate.tape (children a g).length))
    (hcntH : H (bcnt a) = 1)
    (htotT : A (tot a) = c3) (htotH : H (tot a) = c3.length) :
    Step (stage5 a) (2*(children a g).length+2) H A
      (dockH (totSlots a) H ![1, (c3 ++ List.replicate (children a g).length true).length])
      (install (totSlots a) A
        ![ZeroPadding.pad C (UnaryTemplate.tape (children a g).length),
          c3 ++ List.replicate (children a g).length true]) := by
  classical
  obtain ⟨r5, hr5, hf5, hs5⟩ := TotalsAppend.append_run (children a g).length c3
  have base : Step TotalsAppend.machine (2*(children a g).length+2)
      ![1, c3.length] ![UnaryTemplate.tape (children a g).length, c3]
      ![1, (c3 ++ List.replicate (children a g).length true).length]
      ![UnaryTemplate.tape (children a g).length, c3 ++ List.replicate (children a g).length true] := by
    refine ⟨r5, ?_, ?_, ?_, le_of_eq hs5⟩
    · have hentry : (⟨TotalsAppend.machine.start, ![1, c3.length],
          ![UnaryTemplate.tape (children a g).length, c3]⟩ : Configuration 2 3) =
          TotalsAppend.cfg 0 (children a g).length 1 c3 := by
        apply configuration_ext
        · rfl
        · funext i; fin_cases i <;> rfl
        · funext i; fin_cases i <;> rfl
      rw [hentry]; exact hr5
    · rw [hf5]; funext i; fin_cases i <;> rfl
    · rw [hf5]; funext i; fin_cases i <;> rfl
  have padded := base.pad ![C, 0]
  have e5a : (fun i : Fin 2 => ZeroPadding.pad (![C, 0] i)
        (![UnaryTemplate.tape (children a g).length, c3] i)) =
      ![ZeroPadding.pad C (UnaryTemplate.tape (children a g).length), c3] := by
    funext i; fin_cases i
    · rfl
    · exact ZeroPadding.pad_zero _
  have e5b : (fun i : Fin 2 => ZeroPadding.pad (![C, 0] i)
        (![UnaryTemplate.tape (children a g).length,
          c3 ++ List.replicate (children a g).length true] i)) =
      ![ZeroPadding.pad C (UnaryTemplate.tape (children a g).length),
        c3 ++ List.replicate (children a g).length true] := by
    funext i; fin_cases i
    · rfl
    · exact ZeroPadding.pad_zero _
  rw [e5a, e5b] at padded
  exact padded.dock (totSlots a) (tot_injective a) H A
    (by intro j; fin_cases j
        · exact hcntH
        · exact htotH)
    (by intro j; fin_cases j
        · exact hcntT
        · exact htotT)

/-! ## Port separation: which stage touches which port -/

theorem ex_ne {i j : Fin 12} (h : i.val ≠ j.val) : ex a i ≠ ex a j := by
  intro he
  exact h (by simpa using congrArg (fun k : Fin (T a) => k.val) he)

theorem notin_copy (i : Fin (T a)) (hb : ∀ j, bk a j ≠ i) (hs : i ≠ str a) (hf : i ≠ fcp a) :
    ∀ j, copySlots a j ≠ i := by
  intro j
  unfold copySlots
  split_ifs
  · exact Ne.symm hs
  · exact hb (Counted.localTape a 0)
  · exact Ne.symm hf

theorem notin_field (i : Fin (T a)) (hb : ∀ j, bk a j ≠ i) (hc : i ≠ cnt a) :
    ∀ j, fieldSlots a j ≠ i := by
  intro j
  unfold fieldSlots
  split_ifs
  · exact hb (Counted.sourceTape a)
  · exact hb (Counted.localTape a 14)
  · exact Ne.symm hc

theorem notin_rec (i : Fin (T a)) (hb : ∀ j, bk a j ≠ i) (hbo : i ≠ bod a) (hd : i ≠ dom a) :
    ∀ j, recSlots a j ≠ i := by
  intro j
  unfold recSlots
  split_ifs
  · exact hb (Counted.sourceTape a)
  · exact hb (Counted.localTape a 14)
  · exact Ne.symm hbo
  · exact Ne.symm hd
  · exact hb (Counted.fresh a 9)

theorem notin_tot (i : Fin (T a)) (hb : ∀ j, bk a j ≠ i) (ht : i ≠ tot a) :
    ∀ j, totSlots a j ≠ i := by
  intro j
  unfold totSlots
  split_ifs
  · exact hb (Counted.fresh a 9)
  · exact Ne.symm ht

/-- The count template port is disjoint from every field-stage port. -/
theorem field_ne_bcnt : ∀ j, fieldSlots a j ≠ bcnt a := by
  intro j
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13⟩ := port_facts a
  apply ne_of_val
  unfold fieldSlots
  split_ifs <;> simp only [cnt, ex_val] at * <;> omega

/-- The source and backing ports are disjoint from the totals-stage ports. -/
theorem tot_ne_bank (i : Fin (SB a)) (h : i ≠ Counted.fresh a 9) : ∀ j, totSlots a j ≠ bk a i := by
  intro j
  unfold totSlots
  split_ifs
  · exact fun he => h (bk_injective a he.symm)
  · exact fun he => (bk_ne_ex a i 3) he.symm

end NearCubicWires.ExtDecompositionBatch
