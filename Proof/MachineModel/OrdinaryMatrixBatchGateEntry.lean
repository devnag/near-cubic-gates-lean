import Proof.MachineModel.OrdinaryMatrixBatchGateLayout

namespace NearCubicWires.RepairOrdinary.MatrixBatchGateColdEntry
open LocalBitMultitape SignedSortKey MatrixScoreBatch
open MatrixBatchGateLayout (slots widthSlots width_injective)
open MatrixScoreLeftLoop (C)
open MatrixScoreReusableRanks (D)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def first := TapeEmbedding.machine 34 MatrixBatchWorkspace.machine
noncomputable def widthCall := RecoveryFocus.machine widthSlots MatrixBatchWidthSetup.machine
noncomputable def setup := Composition.machine first widthCall
noncomputable def machine := Composition.machine setup MatrixBatchGateColdCopy.machine
def input (r : Request) : Fin 166 → List Bool := fun i => if i=0 then physicalInput r else []
def budget (r : Request) :=
  MatrixBatchWorkspace.budget r+1+MatrixBatchWidthSetup.budget r+1+MatrixBatchGateColdCopy.budget r

theorem small_fits (r : Request) :
    1≤D r ∧ r.d+2≤D r ∧ 2*r.d+1≤D r ∧ 2*r.width+1≤D r ∧
      max (C r) (MatrixScoreColdFields.budget r.d r.M (C r)+1)≤D r := by
  have hm := common_width r
  have hw := r.widthLe
  have hu : 1≤r.U := Nat.one_le_two_pow
  have hc : r.d+2≤C r ∧ 2*r.width+1≤C r ∧ 30≤C r := by unfold C; omega
  have hb : MatrixScoreColdFields.budget r.d r.M (C r)+1≤6*C r+60 := by
    unfold MatrixScoreColdFields.budget C; omega
  have hsq : 6*C r+60≤(C r+1)^2 := by nlinarith
  have hD : (C r+1)^2≤D r := by
    unfold D MatrixBatchCapacity.capacity
    nlinarith
  have hc1 : C r+1≤(C r+1)^2 := by nlinarith
  refine ⟨by omega,by omega,by omega,by omega,?_⟩
  rw [max_le_iff]
  constructor <;> omega

theorem entry_run (r : Request) :
    ∃ actual,run machine (budget r) (input r)=some actual ∧
      ∃ s : MatrixBatchGateStore.Store r,
      (∀ i,actual.final.heads (slots i)=(MatrixBatchGateNativeLoop.cfg r 0 (word r) (header r).length [] s).heads i) ∧
      (∀ i,actual.final.tapes (slots i)=(MatrixBatchGateNativeLoop.cfg r 0 (word r) (header r).length [] s).tapes i) ∧
      actual.final.tapes 0=physicalInput r ∧ actual.final.heads 0=0 ∧
      actual.final.tapes 40=List.replicate r.p true ∧ actual.final.heads 40=0 ∧
      actual.final.tapes 80=List.replicate (natBitLength r.Gates) true ∧ actual.final.heads 80=0 ∧
      actual.final.tapes 83=frame (binary (natBitLength r.Gates) r.Gates) ∧ actual.final.heads 83=0 ∧
      actual.steps≤budget r := by
  obtain ⟨base,hb,b0,h0,b1,h1,b32,h32,b39,h39,b40,h40,b49,h49,b61,h61,b65,h65,b77,h77,
    b80,h80,b83,h83,b89,h89,b92,h92,b95,h95,b99,h99,b103,h103,b106,h106,b107,h107,bs⟩ :=
    MatrixBatchNativeFields.setup_run r
  obtain ⟨dead,hd,dh,dl⟩ := MatrixBatchNativeFields.setup_run_dead r
  have e : base=dead := Option.some.inj (hb.symm.trans hd)
  subst e
  obtain ⟨hD1,hDd,hD2d,hD2w,fits4⟩ := small_fits r
  have hUd : (UnaryTemplate.tape r.d).length≤D r := by simp [UnaryTemplate.tape]; omega
  have hfd : (frame (binary r.d 0)).length≤D r := by simp [frame_length,binary_length]; omega
  have hwt : (List.replicate r.width true).length≤D r := by simp; omega
  have hzf : (List.replicate (2*r.width+1) false).length≤D r := by simp; omega
  obtain ⟨workspace,hw,wt,wh,w130,wh130,ws⟩ := MatrixBatchWorkspace.workspace_run r base hb b77 h77 b39 h39 bs
  have he := TapeEmbedding.run_embed MatrixBatchWorkspace.machine
    (fun _ : Fin 34 => 0) (fun _ : Fin 34 => []) _ _ workspace hw
  let prepared := TapeEmbedding.receipt (fun _ : Fin 34 => 0) (fun _ : Fin 34 => []) workspace
  obtain ⟨wd,hwd,x0,xh0,x11,xh11,x12,xh12,x14,xh14,x15,xh15,x16,xh16,x20,xh20,x24,xh24,
    x18,xh18,x19,xh19,x21,xh21,x22,xh22,x23,xh23,x25,xh25,xs⟩ := MatrixBatchWidthSetup.width_run r
  obtain ⟨res,hres,sH,sT,sO,ss⟩ := MatrixBatchWidthSetup.stage first widthSlots width_injective
    MatrixBatchWidthSetup.machine _ _ _ prepared he (MatrixBatchWidthSetup.entry r) wd hwd rfl
    (by
      intro i
      rw [MatrixBatchWidthSetup.entry_heads]
      fin_cases i <;> first | rfl | exact (wh 1).trans h1 | exact (wh 92).trans h92)
    (by
      intro i
      rw [MatrixBatchWidthSetup.entry_tapes]
      fin_cases i <;> first | rfl | exact (wt 1).trans b1 | exact (wt 92).trans b92)
  obtain ⟨moved,hm,mh,mt,ms⟩ := MatrixBatchGateColdCopy.prepare_run r res.final.heads res.final.tapes
    (by
      intro i
      fin_cases i
      · exact (sO 103 (by decide)).1.trans ((wh 103).trans h103)
      · exact (sO 147 (by decide)).1
      · exact (sO 106 (by decide)).1.trans ((wh 106).trans h106)
      · exact (sO 107 (by decide)).1.trans ((wh 107).trans h107))
    ((sO 103 (by decide)).2.trans ((wt 103).trans b103)) (sO 147 (by decide)).2
    ((sO 106 (by decide)).2.trans ((wt 106).trans b106)) ((sO 107 (by decide)).2.trans ((wt 107).trans b107))
  have joined := Composition.run_join setup MatrixBatchGateColdCopy.machine _ _ _ res moved hres hm
  have hin : Composition.leftConfig _ (Composition.leftConfig _ (TapeEmbedding.config (fun _ : Fin 34 => 0)
      (fun _ : Fin 34 => []) (initialConfiguration MatrixBatchWorkspace.machine (MatrixBatchWorkspace.input r))))=
      initialConfiguration machine (input r) := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  rw [hin] at joined
  have T (j : Fin 166) : moved.final.tapes j=MatrixBatchGateColdCopy.updated r res.final.tapes j := congrFun mt j
  have H (j : Fin 166) : moved.final.heads j=MatrixBatchGateColdCopy.shifted res.final.heads j := congrFun mh j
  let actualB : Fin 48 → List Bool := fun b => moved.final.tapes (slots b.castSucc)
  have hfixed : ∀ b,MatrixBatchGateClear.scratchPick b=none →
      actualB b=MatrixBatchGateClear.stable r 0 0 0 (word r) [] b := by
    intro b hb'
    fin_cases b <;> simp [MatrixBatchGateClear.scratchPick] at hb'
    · exact (T 151).trans ((sT 20).trans x20)
    · exact (T 49).trans ((sO 49 (by decide)).2.trans ((wt 49).trans b49))
    · exact (T 77).trans ((sO 77 (by decide)).2.trans ((wt 77).trans b77))
    · exact (T 107).trans ((sO 107 (by decide)).2.trans ((wt 107).trans b107))
    · exact (T 146).trans ((sT 16).trans x16)
    · exact (T 61).trans ((sO 61 (by decide)).2.trans ((wt 61).trans b61))
    · exact (T 65).trans ((sO 65 (by decide)).2.trans ((wt 65).trans b65))
    · exact T 147
    · exact (T 32).trans ((sO 32 (by decide)).2.trans ((wt 32).trans b32))
    · exact (T 106).trans ((sO 106 (by decide)).2.trans ((wt 106).trans b106))
    · exact (T 39).trans ((sO 39 (by decide)).2.trans ((wt 39).trans b39))
    · exact (T 155).trans ((sT 24).trans x24)
    · exact (T 162).trans (sO 162 (by decide)).2
    · exact (T 142).trans ((sT 12).trans x12)
    · exact (T 103).trans ((sO 103 (by decide)).2.trans ((wt 103).trans b103))
    · exact (T 130).trans ((sO 130 (by decide)).2.trans w130)
    · exact (T 164).trans (sO 164 (by decide)).2
    · exact (T 1).trans ((sT 0).trans x0)
  have bounded : ∀ j,(actualB (MatrixBatchGateClear.scratchSlots j)).length≤D r := by
    intro j
    fin_cases j
    · exact (congrArg List.length ((T 157).trans (sO 157 (by decide)).2)).trans_le (Nat.zero_le _)
    · exact (congrArg List.length ((T 158).trans (sO 158 (by decide)).2)).trans_le (Nat.zero_le _)
    · exact (congrArg List.length ((T 159).trans (sO 159 (by decide)).2)).trans_le (Nat.zero_le _)
    · exact (congrArg List.length ((T 160).trans (sO 160 (by decide)).2)).trans_le (Nat.zero_le _)
    · exact (congrArg List.length ((T 161).trans (sO 161 (by decide)).2)).trans_le (Nat.zero_le _)
    · exact (congrArg List.length ((T 163).trans (sO 163 (by decide)).2)).trans_le (Nat.zero_le _)
    · exact (congrArg List.length ((T 165).trans (sO 165 (by decide)).2)).trans_le (Nat.zero_le _)
    · exact (congrArg List.length ((T 92).trans ((sT 11).trans x11))).trans_le hUd
    · exact (congrArg List.length ((T 95).trans ((sO 95 (by decide)).2.trans ((wt 95).trans b95)))).trans_le hfd
    · exact (congrArg List.length ((T 99).trans ((sO 99 (by decide)).2.trans ((wt 99).trans b99)))).trans_le hfd
    · exact (congrArg List.length ((T 144).trans ((sT 14).trans x14))).trans_le hwt
    · exact (congrArg List.length ((T 145).trans ((sT 15).trans x15))).trans_le hwt
    · exact (congrArg List.length ((T 149).trans (sT 18))).trans_le (x18.trans hD1)
    · exact (congrArg List.length ((T 153).trans (sT 22))).trans_le (x22.trans hD1)
    · exact (congrArg List.length ((T 150).trans ((sT 19).trans x19))).trans_le hD1
    · exact (congrArg List.length ((T 154).trans ((sT 23).trans x23))).trans_le hD1
    · exact (congrArg List.length ((T 152).trans ((sT 21).trans x21))).trans_le hzf
    · exact (congrArg List.length ((T 156).trans ((sT 25).trans x25))).trans_le hzf
    · exact (congrArg List.length ((T 23).trans ((sO 23 (by decide)).2.trans (wt 23)))).trans_le ((dl 0).trans fits4)
    · exact (congrArg List.length ((T 90).trans ((sO 90 (by decide)).2.trans (wt 90)))).trans_le ((dl 1).trans fits4)
    · exact (congrArg List.length ((T 91).trans ((sO 91 (by decide)).2.trans (wt 91)))).trans_le ((dl 2).trans fits4)
    · exact (congrArg List.length ((T 93).trans ((sO 93 (by decide)).2.trans (wt 93)))).trans_le ((dl 4).trans fits4)
    · exact (congrArg List.length ((T 28).trans ((sO 28 (by decide)).2.trans (wt 28)))).trans_le ((dl 5).trans fits4)
    · exact (congrArg List.length ((T 94).trans ((sO 94 (by decide)).2.trans (wt 94)))).trans_le ((dl 6).trans fits4)
    · exact (congrArg List.length ((T 96).trans ((sO 96 (by decide)).2.trans (wt 96)))).trans_le ((dl 8).trans fits4)
    · exact (congrArg List.length ((T 97).trans ((sO 97 (by decide)).2.trans (wt 97)))).trans_le ((dl 9).trans fits4)
    · exact (congrArg List.length ((T 98).trans ((sO 98 (by decide)).2.trans (wt 98)))).trans_le ((dl 11).trans fits4)
    · exact (congrArg List.length ((T 100).trans ((sO 100 (by decide)).2.trans (wt 100)))).trans_le ((dl 13).trans fits4)
    · exact (congrArg List.length ((T 101).trans ((sO 101 (by decide)).2.trans (wt 101)))).trans_le ((dl 14).trans fits4)
    · exact (congrArg List.length ((T 102).trans ((sO 102 (by decide)).2.trans (wt 102)))).trans_le ((dl 15).trans fits4)
  let s : MatrixBatchGateStore.Store r := ⟨0,0,0,fun j => actualB (MatrixBatchGateClear.scratchSlots j),bounded⟩
  refine ⟨Composition.joinedReceipt res moved,joined,s,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro i
    change moved.final.heads (slots i)=_
    rw [MatrixBatchGateNativeLoop.cfg_heads]
    fin_cases i
    · exact (H 157).trans (sO 157 (by decide)).1
    · exact (H 151).trans ((sH 20).trans xh20)
    · exact (H 158).trans (sO 158 (by decide)).1
    · exact (H 159).trans (sO 159 (by decide)).1
    · exact (H 160).trans (sO 160 (by decide)).1
    · exact (H 161).trans (sO 161 (by decide)).1
    · exact (H 49).trans ((sO 49 (by decide)).1.trans ((wh 49).trans h49))
    · exact (H 163).trans (sO 163 (by decide)).1
    · exact (H 165).trans (sO 165 (by decide)).1
    · exact (H 92).trans ((sH 11).trans xh11)
    · exact (H 95).trans ((sO 95 (by decide)).1.trans ((wh 95).trans h95))
    · exact (H 99).trans ((sO 99 (by decide)).1.trans ((wh 99).trans h99))
    · exact (H 144).trans ((sH 14).trans xh14)
    · exact (H 145).trans ((sH 15).trans xh15)
    · exact (H 149).trans ((sH 18).trans xh18)
    · exact (H 77).trans ((sO 77 (by decide)).1.trans ((wh 77).trans h77))
    · exact (H 107).trans ((sO 107 (by decide)).1.trans ((wh 107).trans h107))
    · exact (H 146).trans ((sH 16).trans xh16)
    · exact (H 61).trans ((sO 61 (by decide)).1.trans ((wh 61).trans h61))
    · exact (H 65).trans ((sO 65 (by decide)).1.trans ((wh 65).trans h65))
    · exact (H 153).trans ((sH 22).trans xh22)
    · exact (H 150).trans ((sH 19).trans xh19)
    · exact (H 147).trans (sO 147 (by decide)).1
    · exact (H 32).trans ((sO 32 (by decide)).1.trans ((wh 32).trans h32))
    · exact (H 154).trans ((sH 23).trans xh23)
    · exact (H 106).trans ((sO 106 (by decide)).1.trans ((wh 106).trans h106))
    · exact (H 152).trans ((sH 21).trans xh21)
    · exact (H 39).trans (congrArg (fun n => n+1) ((sO 39 (by decide)).1.trans (wh 39)))
    · exact (H 155).trans ((sH 24).trans xh24)
    · exact (H 156).trans ((sH 25).trans xh25)
    · exact (H 23).trans ((sO 23 (by decide)).1.trans ((wh 23).trans (dh 0)))
    · exact (H 90).trans ((sO 90 (by decide)).1.trans ((wh 90).trans (dh 1)))
    · exact (H 91).trans ((sO 91 (by decide)).1.trans ((wh 91).trans (dh 2)))
    · exact (H 93).trans ((sO 93 (by decide)).1.trans ((wh 93).trans (dh 4)))
    · exact (H 28).trans ((sO 28 (by decide)).1.trans ((wh 28).trans (dh 5)))
    · exact (H 94).trans ((sO 94 (by decide)).1.trans ((wh 94).trans (dh 6)))
    · exact (H 96).trans ((sO 96 (by decide)).1.trans ((wh 96).trans (dh 8)))
    · exact (H 97).trans ((sO 97 (by decide)).1.trans ((wh 97).trans (dh 9)))
    · exact (H 98).trans ((sO 98 (by decide)).1.trans ((wh 98).trans (dh 11)))
    · exact (H 100).trans ((sO 100 (by decide)).1.trans ((wh 100).trans (dh 13)))
    · exact (H 101).trans ((sO 101 (by decide)).1.trans ((wh 101).trans (dh 14)))
    · exact (H 162).trans (sO 162 (by decide)).1
    · exact (H 142).trans ((sH 12).trans xh12)
    · exact (H 103).trans ((sO 103 (by decide)).1.trans ((wh 103).trans h103))
    · exact (H 130).trans ((sO 130 (by decide)).1.trans wh130)
    · exact (H 164).trans (sO 164 (by decide)).1
    · exact (H 1).trans ((sH 0).trans xh0)
    · exact (H 102).trans ((sO 102 (by decide)).1.trans ((wh 102).trans (dh 15)))
    · exact (H 89).trans ((sO 89 (by decide)).1.trans ((wh 89).trans h89))
  · intro i
    change moved.final.tapes (slots i)=_
    rw [MatrixBatchGateNativeLoop.cfg_tapes]
    refine Fin.addCases (m := 48) (n := 1) (motive := fun i => moved.final.tapes (slots i)=
      Fin.addCases (m := 48) (n := 1) (motive := fun _ => List Bool)
        (MatrixBatchGateClear.tapes r s.assignment s.id s.cap (word r) [] s.backing)
        (fun _ => UnaryTemplate.tape r.Gates) i) ?_ ?_ i
    · intro b
      rw [Fin.addCases_left]
      exact congrFun (MatrixBatchGateStore.rebuild r 0 0 0 (word r) [] actualB hfixed) b
    · intro k
      fin_cases k
      rw [Fin.addCases_right]
      exact (T 89).trans ((sO 89 (by decide)).2.trans ((wt 89).trans b89))
  · exact (T 0).trans ((sO 0 (by decide)).2.trans ((wt 0).trans b0))
  · exact (H 0).trans ((sO 0 (by decide)).1.trans ((wh 0).trans h0))
  · exact (T 40).trans ((sO 40 (by decide)).2.trans ((wt 40).trans b40))
  · exact (H 40).trans ((sO 40 (by decide)).1.trans ((wh 40).trans h40))
  · exact (T 80).trans ((sO 80 (by decide)).2.trans ((wt 80).trans b80))
  · exact (H 80).trans ((sO 80 (by decide)).1.trans ((wh 80).trans h80))
  · exact (T 83).trans ((sO 83 (by decide)).2.trans ((wt 83).trans b83))
  · exact (H 83).trans ((sO 83 (by decide)).1.trans ((wh 83).trans h83))
  · change res.steps+1+moved.steps≤_
    rw [ms,ss]
    change workspace.steps+1+wd.steps+1+MatrixBatchGateColdCopy.budget r≤budget r
    unfold budget
    omega

end NearCubicWires.RepairOrdinary.MatrixBatchGateColdEntry
