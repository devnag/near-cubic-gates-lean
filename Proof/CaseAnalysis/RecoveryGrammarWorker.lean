import Proof.CaseAnalysis.RecoveryGrammarFold
import Proof.CaseAnalysis.RecoveryRowReusable

/-! Shared ordinary composition for original grammar workers. A paid step
positions their fixed driver ports, and one recorded reset restores work
cursors while retaining graph and nested-stack cursors. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedGrammarWorker
open LocalBitMultitape RecoveryExecution Composition
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def heads (out stack : List Bool) (i : Fin 78):=
  if i=20 then out.length else if i=74 then stack.length else 0
def positioned (driver : Fin 78→Bool) (out stack : List Bool) (i : Fin 78):=
  if driver i then 1 else heads out stack i
def position (driver : Fin 78→Bool) : Machine 78 2 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>q.val==1
  rule:=fun q _=>if q.val=0 then some ⟨1,fun _=>none,fun i=>if driver i then .right else .stay⟩ else none

theorem position_run (driver : Fin 78→Bool) (out stack : List Bool) (A : Fin 78→List Bool)
    (h20 : driver 20=false) (h74 : driver 74=false) :
    ∃ r,runFrom (position driver) 1 ⟨(position driver).start,heads out stack,A⟩=some r ∧
      r.steps=1 ∧ r.final.heads=positioned driver out stack ∧ r.final.tapes=A := by
  have hs : step (position driver) ⟨0,heads out stack,A⟩=
      some ⟨1,positioned driver out stack,A⟩ := by
    change some (applyAction (⟨0,heads out stack,A⟩ : Configuration 78 2)
      ⟨1,fun _=>none,fun i=>if driver i then .right else .stay⟩)=_
    congr 1
    apply configuration_ext
    · rfl
    · funext i
      by_cases a : i=20
      · subst i;simp only [applyAction,positioned,h20,Bool.false_eq_true,↓reduceIte,HeadMove.apply]
      by_cases b : i=74
      · subst i;simp only [applyAction,positioned,h74,Bool.false_eq_true,↓reduceIte,HeadMove.apply]
      · simp only [applyAction,positioned,heads,if_neg a,if_neg b]
        cases driver i <;> rfl
    · rfl
  obtain ⟨r,rr,rf,rs⟩:=(Timed.single (by rfl) hs).run (by rfl)
  exact ⟨r,rr,rs,congrArg Configuration.heads rf,congrArg Configuration.tapes rf⟩

variable {s : ℕ}
def prepare (p : Machine 78 s) (driver : Fin 78→Bool):=Composition.machine (position driver) p
def selected (i : Fin 78):=decide (i≠20 ∧ i≠74)
noncomputable def machine (p : Machine 78 s) (driver : Fin 78→Bool):=MaskedReset.machine (prepare p driver) selected
noncomputable def entry (p : Machine 78 s) (driver : Fin 78→Bool)
    (out stack : List Bool) (A : Fin 78→List Bool) (B : ℕ):=
  ZeroPadding.config (Rewind.Workspace.capacities 78 B)
    (Rewind.recording (⟨(prepare p driver).start,heads out stack,A⟩ : Configuration 78 _) 0)
def resultHeads (graphPosition stackPosition : ℕ) : Fin 79→ℕ:=
  Fin.addCases (m:=78) (n:=1) (motive:=fun _=>ℕ)
    (fun i=>if i=20 then graphPosition else if i=74 then stackPosition else 0) (fun _=>0)
def resultData (A : Fin 78→List Bool) (B : ℕ) : Fin 79→List Bool:=
  Fin.addCases (m:=78) (n:=1) (motive:=fun _=>List Bool) A (fun _=>List.replicate B false)

theorem enter (p : Machine 78 s) (driver : Fin 78→Bool)
    (out stack : List Bool) (A : Fin 78→List Bool) (u : ℕ)
    (h20 : driver 20=false) (h74 : driver 74=false)
    (r : ExecutionReceipt 78 s)
    (hr : runFrom p u ⟨p.start,positioned driver out stack,A⟩=some r) (hs : r.steps≤u) :
    ∃ q,runFrom (prepare p driver) (u+2)
      ⟨(prepare p driver).start,heads out stack,A⟩=some q ∧ q.steps≤u+2 ∧
      q.final.heads=r.final.heads ∧ q.final.tapes=r.final.tapes := by
  obtain ⟨a,ar,as,ah,aData⟩:=position_run driver out stack A h20 h74
  have hr' : runFrom p u (restart a.final p.start)=some r := by
    change runFrom _ _ ⟨_,a.final.heads,a.final.tapes⟩=some r
    rw [ah,aData]
    exact hr
  have full:=Composition.run_join (position driver) p _ _ _ a r ar hr'
  have he : 1+1+u=u+2:=by omega
  rw [he] at full
  refine ⟨joinedReceipt a r,full,?_,rfl,rfl⟩
  change a.steps+1+r.steps≤u+2
  omega

theorem reset_run (p : Machine 78 s) (driver : Fin 78→Bool)
    (out stack : List Bool) (A : Fin 78→List Bool) (u S B : ℕ)
    (h20 : driver 20=false) (h74 : driver 74=false)
    (r : ExecutionReceipt 78 s)
    (hr : runFrom p u ⟨p.start,positioned driver out stack,A⟩=some r)
    (hs : r.steps≤u) (hS : 1≤S) (ho : out.length≤S) (hk : stack.length≤S)
    (hA : ∀ i,(A i).length≤B) (hB : S+u+3≤B) :
    ∃ q,runFrom (machine p driver) (2*(u+2)+2) (entry p driver out stack A B)=some q ∧
      q.steps≤2*(u+2)+2 ∧ q.final.heads=resultHeads (r.final.heads 20) (r.final.heads 74) ∧
      q.final.tapes=resultData r.final.tapes B ∧ (∀ i,(r.final.tapes i).length≤B) := by
  obtain ⟨a,ar,as,ah,aData⟩:=enter p driver out stack A u h20 h74 r hr hs
  obtain ⟨q,qr,qf,qs,_⟩:=MaskedReset.workspace_run (prepare p driver) selected _ B _ a ar
    (by intro i hi
        have hn : i≠20 ∧ i≠74:=of_decide_eq_true hi
        simp only [heads,if_neg hn.1,if_neg hn.2]) (by omega)
  have hb : 2*a.steps+2≤2*(u+2)+2:=by omega
  have more:=runFrom_moreFuel (machine p driver) _ (2*(u+2)+2-(2*a.steps+2)) _ q qr
  rw [Nat.add_sub_of_le hb] at more
  have hh : ∀ i,positioned driver out stack i≤S := by
    intro i
    unfold positioned heads
    split_ifs <;> omega
  have support:=RecoveryTapeSupport.run_support p u _ r hr B S hh
    (fun i=>(hA i).trans (Nat.le_max_left _ _))
  refine ⟨q,more,by omega,?_,?_,?_⟩
  · rw [qf]
    funext i
    refine Fin.addCases (m:=78) (n:=1) ?_ ?_ i
    · intro j
      simp only [SelectiveReset.finished,Rewind.config,resultHeads,Fin.addCases_left]
      by_cases j20 : j=20
      · subst j
        simpa only [selected,ne_eq,not_true_eq_false,false_and,decide_false,Bool.false_eq_true,↓reduceIte] using congrFun ah 20
      by_cases j74 : j=74
      · subst j
        simpa only [selected,ne_eq,not_true_eq_false,and_false,decide_false,Bool.false_eq_true,↓reduceIte,
          show (74 : Fin 78)≠20 by decide] using congrFun ah 74
      · simp only [selected,if_neg j20,if_neg j74,show decide (j≠20 ∧ j≠74)=true from decide_eq_true ⟨j20,j74⟩,↓reduceIte]
    · intro j;fin_cases j;rfl
  · rw [qf]
    change resultData a.final.tapes B=resultData r.final.tapes B
    rw [aData]
  · intro i
    exact (support i).trans (max_le (by omega) (by omega))

def capacity (B : ℕ) (i : Fin 78):=
  if i=77 then B+1 else if i.val<73 ∧ i≠20 ∧ i≠25 ∧ i≠70 then B else 0
def paddedData (B : ℕ) (A : Fin 78→List Bool) (i : Fin 78):=ZeroPadding.pad (capacity B i) (A i)
def paddedCapacity (B : ℕ) : Fin 79→ℕ:=
  Fin.addCases (m:=78) (n:=1) (motive:=fun _=>ℕ) (capacity B) (fun _=>0)

theorem padding_entry (p : Machine 78 s) (driver : Fin 78→Bool)
    (out stack : List Bool) (A : Fin 78→List Bool) (B : ℕ) :
    ZeroPadding.config (paddedCapacity B) (entry p driver out stack A B)=
      entry p driver out stack (paddedData B A) B := by
  apply configuration_ext
  · rfl
  · rfl
  · funext i
    refine Fin.addCases (m:=78) (n:=1) ?_ ?_ i
    · intro j
      simp only [ZeroPadding.config,entry,paddedCapacity,Rewind.recording,Rewind.config,
        Rewind.Workspace.capacities,Fin.addCases_left,ZeroPadding.pad_zero,paddedData]
    · intro j;fin_cases j;exact ZeroPadding.pad_zero _

theorem padded_reset_run (p : Machine 78 s) (driver : Fin 78→Bool)
    (out stack : List Bool) (A : Fin 78→List Bool) (u S B : ℕ)
    (h20 : driver 20=false) (h74 : driver 74=false)
    (r : ExecutionReceipt 78 s)
    (hr : runFrom p u ⟨p.start,positioned driver out stack,A⟩=some r)
    (hs : r.steps≤u) (hS : 1≤S) (ho : out.length≤S) (hk : stack.length≤S)
    (hA : ∀ i,(A i).length≤B) (hB : S+u+3≤B) :
    ∃ q,runFrom (machine p driver) (2*(u+2)+2)
      (entry p driver out stack (paddedData B A) B)=some q ∧
      q.steps≤2*(u+2)+2 ∧ q.final.heads=resultHeads (r.final.heads 20) (r.final.heads 74) ∧
      q.final.tapes=resultData (paddedData B r.final.tapes) B ∧
      (∀ i,i.val<73 → (paddedData B r.final.tapes i).length≤B) := by
  obtain ⟨a,ar,as,ah,aData,ab⟩:=reset_run p driver out stack A u S B h20 h74 r hr hs hS ho hk hA hB
  obtain ⟨q,qr,qf,qs,_⟩:=ZeroPadding.run_config (machine p driver) (paddedCapacity B) _ _ a ar
  rw [padding_entry] at qr
  refine ⟨q,qr,qs.le.trans as,?_,?_,?_⟩
  · rw [qf];exact ah
  · rw [qf]
    change (fun i=>ZeroPadding.pad (paddedCapacity B i) (a.final.tapes i))=_
    rw [aData]
    funext i
    refine Fin.addCases (m:=78) (n:=1) ?_ ?_ i
    · intro j;simp only [paddedCapacity,resultData,Fin.addCases_left,paddedData]
    · intro j;simp only [paddedCapacity,resultData,Fin.addCases_right,ZeroPadding.pad_zero]
  · intro i hi
    change (ZeroPadding.pad (capacity B i) (r.final.tapes i)).length≤B
    rw [ZeroPadding.pad_length]
    refine max_le ?_ (ab i)
    have hn : i≠77 := by
      intro he
      have hv:=congrArg Fin.val he
      change i.val=77 at hv
      omega
    unfold capacity
    rw [if_neg hn]
    split <;> omega

end NearCubicWires.RepairOrdinary.RecoveryBoundedGrammarWorker
