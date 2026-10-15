import Proof.MachineModel.OrdinaryMatrixScoreWeightList

/-! Actual sequential fold over all weights of one assignment, including
scratch clearing on every entry and the physical repetition-driver rewind. -/
namespace NearCubicWires.RepairOrdinary.MatrixScoreWeightList
open LocalBitMultitape RecoveryExecution MatrixScoreWeight
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def cost (c b w : ℕ) := 2*c+4*b+16*w+31
noncomputable def machine := RepeatMachine.machine MatrixScoreWeightCycle.machine (fun _ _ => true)

theorem driver_run (es : List Item) (pre suffix apre asuffix : List Bool)
    (total pos c b w p n : ℕ) (scratch : Fin 10 → List Bool)
    (hd : pos+es.length=total) (hw : ∀ e ∈ es,e.magnitude.length≤b) (hbw : b≤w)
    (hc : 4*w+3≤c) (hs : ∀ i,(scratch i).length≤c)
    (hp : p+positive es<2^w) (hn : n+negative es<2^w) :
    ∃ finalScratch : Fin 10 → List Bool,(∀ i,(finalScratch i).length≤c) ∧
      ∃ actual,runFrom machine (es.length*(cost c b w+2)+total+3)
        (RepeatMachine.cfg 0 (MatrixScoreWeightCycle.input (pre++word es++suffix)
          (apre++assignment es++asuffix) pre.length apre.length c w p n scratch) total (pos+1))=some actual ∧
        actual.final=RepeatMachine.cfg 3 (MatrixScoreWeightCycle.input (pre++word es++suffix)
          (apre++assignment es++asuffix) (pre.length+(word es).length)
          (apre.length+2*es.length) c w (p+positive es) (n+negative es) finalScratch) total 1 ∧
        actual.steps≤es.length*(cost c b w+2)+total+3 := by
  induction es generalizing pre apre pos p n scratch with
  | nil =>
    have he : pos=total := by simpa using hd
    subst pos
    obtain ⟨actual,hr,hf,has⟩ := (RepeatMachine.exhaust MatrixScoreWeightCycle.machine (fun _ _ => true)
      (MatrixScoreWeightCycle.input (pre++word []++suffix) (apre++assignment []++asuffix)
        pre.length apre.length c w p n scratch) total).run
      (by simp [RepeatMachine.machine,RepeatMachine.cfg,controlConfig,RepeatMachine.phaseCode])
    refine ⟨scratch,hs,actual,?_,?_,?_⟩
    · simpa [machine] using hr
    · simpa using hf
    · simpa using has.le
  | cons e es ih =>
    have hew := hw e (by simp)
    obtain ⟨middle,hms,body,hbody,hbh,hbt,hbs⟩ := MatrixScoreWeightCycle.cycle_run
      pre (word es++suffix) apre (assignment es++asuffix) e.magnitude c w p n e.sign e.selected
      scratch hs (hew.trans hbw) hc (selected_fit e es w p n hp hn)
    let nextP := nextPositive p (RadixSemantics.value e.magnitude) e.sign e.selected
    let nextN := nextNegative n (RadixSemantics.value e.magnitude) e.sign e.selected
    obtain ⟨final,hfs,tail,htail,htf,hts⟩ := ih (pre++e.word) (apre++e.assignment) (pos+1) nextP nextN middle
      (by simp only [List.length_cons] at hd; omega) (by intro x hx; exact hw x (by simp [hx])) hms
      (by rw [positive_tail]; exact hp) (by rw [negative_tail]; exact hn)
    have hsource : pre++frame (e.sign::e.magnitude)++(word es++suffix)=pre++word (e::es)++suffix := by
      simp [Item.word,List.append_assoc]
    have hassignment : apre++[true,e.selected]++(assignment es++asuffix)=apre++assignment (e::es)++asuffix := by
      simp [Item.assignment,List.append_assoc]
    rw [hsource,hassignment] at hbody hbt
    have hstart := RepeatMachine.iteration MatrixScoreWeightCycle.machine (fun _ _ => true)
      (MatrixScoreWeightCycle.input (pre++word (e::es)++suffix) (apre++assignment (e::es)++asuffix)
        pre.length apre.length c w p n scratch) total pos body rfl (by simp only [List.length_cons] at hd; omega) hbody
    simp only [↓reduceIte] at hstart
    have hpre : (pre++e.word).length=pre.length+2*e.magnitude.length+3 := by simp [Item.word]; omega
    have hapre : (apre++e.assignment).length=apre.length+2 := by simp [Item.assignment]
    have hend : RepeatMachine.cfg 0 body.final total (pos+2)=
        RepeatMachine.cfg 0 (MatrixScoreWeightCycle.input ((pre++e.word)++word es++suffix)
          ((apre++e.assignment)++assignment es++asuffix) (pre++e.word).length (apre++e.assignment).length
          c w nextP nextN middle) total ((pos+1)+1) := by
      apply configuration_ext
      · rfl
      · funext i
        refine Fin.addCases (m := 17) (n := 1) (fun j => ?_) (fun j => ?_) i
        · simp [RepeatMachine.cfg,controlConfig,TapeEmbedding.config,hbh,MatrixScoreWeightCycle.input,hpre,hapre]
        · simp [RepeatMachine.cfg,controlConfig,TapeEmbedding.config,Nat.add_assoc]
      · funext i
        refine Fin.addCases (m := 17) (n := 1) (fun j => ?_) (fun j => ?_) i
        · simp [RepeatMachine.cfg,controlConfig,TapeEmbedding.config,hbt,MatrixScoreWeightCycle.input,
            nextP,nextN,Item.word,Item.assignment,List.append_assoc]
        · simp [RepeatMachine.cfg,controlConfig,TapeEmbedding.config,Nat.add_assoc]
    rw [hend] at hstart
    rcases hstart with ⟨space,hstart⟩
    obtain ⟨actual,har,haf,has,_⟩ := hstart.followedBy tail htail
    have hbodyBound : body.steps≤cost c b w := by unfold cost; omega
    have hbound : body.steps+2+(es.length*(cost c b w+2)+total+3)≤
        (e::es).length*(cost c b w+2)+total+3 := by simp only [List.length_cons]; nlinarith
    have hmore := runFrom_moreFuel machine _
      ((e::es).length*(cost c b w+2)+total+3-(body.steps+2+(es.length*(cost c b w+2)+total+3))) _ actual har
    rw [Nat.add_sub_of_le hbound] at hmore
    refine ⟨final,hfs,actual,hmore,?_,?_⟩
    · rw [haf,htf]
      have hp' : nextP+positive es=p+positive (e::es) := positive_tail e es p
      have hn' : nextN+negative es=n+negative (e::es) := negative_tail e es n
      rw [hp',hn']
      apply congrArg (fun data => RepeatMachine.cfg 3 data total 1)
      apply configuration_ext
      · rfl
      · funext i
        simp [MatrixScoreWeightCycle.input,MatrixScoreWeightClear.heads,hapre,Item.word]
        fin_cases i <;> simp <;> omega
      · simp [MatrixScoreWeightCycle.input,Item.word,Item.assignment,List.append_assoc]
    · rw [has]
      simp only [List.length_cons]
      nlinarith only [hbodyBound,hts]

end NearCubicWires.RepairOrdinary.MatrixScoreWeightList
