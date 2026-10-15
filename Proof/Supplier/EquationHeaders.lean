import Proof.Supplier.EquationHeaderAppend

/-! Three canonical headers are produced from their actual raw counts and
appended in order. Fresh local banks avoid an unnecessary reuse/erase stage. -/
namespace NearCubicWires.RepairOrdinary.EquationHeaders
open LocalBitMultitape RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slot (j : Fin 3) (i : Fin 18) : Fin 52 :=
  if i.val<17 then ⟨17*j.val+i.val,by omega⟩ else 51
theorem slot_injective (j : Fin 3) : Function.Injective (slot j) := by
  intro a b h
  have ha := a.isLt
  have hb := b.isLt
  have hj := j.isLt
  have hv := congrArg Fin.val h
  simp only [slot] at hv
  split_ifs at hv <;> dsimp at hv
  all_goals apply Fin.ext; omega

theorem slot_other (j k : Fin 3) (hne : j≠k) (i : Fin 17) :
    RecoveryFocus.pick (slot j) (slot k (i.castAdd 1))=none := by
  have no : ¬∃ l,slot j l=slot k (i.castAdd 1) := by
    rintro ⟨l,he⟩
    have hl := l.isLt
    have hi := i.isLt
    have hj := j.isLt
    have hk := k.isLt
    have hval : j.val≠k.val := fun h => hne (Fin.ext h)
    have hv := congrArg Fin.val he
    simp only [slot,Fin.val_castAdd,hi,ite_true] at hv
    split_ifs at hv <;> dsimp at hv <;> omega
  simp [RecoveryFocus.pick,no]

noncomputable def program (j : Fin 3) := RecoveryFocus.machine (slot j) EquationHeaderAppend.machine
noncomputable def first := Composition.machine (program 0) (program 1)
noncomputable def machine := Composition.machine first (program 2)

def heads (out : List Bool) (i : Fin 52) := if i=51 then out.length else 0
def input (values : Fin 3 → ℕ) (out : List Bool) (i : Fin 52) :=
  if i=0 then List.replicate (values 0) true
  else if i=17 then List.replicate (values 1) true
  else if i=34 then List.replicate (values 2) true
  else if i=51 then out else []
noncomputable def entry (values : Fin 3 → ℕ) (out : List Bool) :=
  (⟨machine.start,heads out,input values out⟩ : Configuration 52 _)

structure Prepared {s : ℕ} (values : Fin 3 → ℕ) (next : ℕ) (out : List Bool)
    (c : Configuration 52 s) : Prop where
  output : c.tapes 51=out
  outputHead : c.heads 51=out.length
  fresh : ∀ k : Fin 3,next ≤ k.val → ∀ i : Fin 17,
    c.tapes (slot k (i.castAdd 1))=(if i=0 then List.replicate (values k) true else []) ∧
    c.heads (slot k (i.castAdd 1))=0

theorem initial {s : ℕ} (q : Fin s) (values : Fin 3 → ℕ) (out : List Bool) :
    Prepared values 0 out (⟨q,heads out,input values out⟩ : Configuration 52 s) := by
  refine ⟨rfl,rfl,?_⟩
  intro k _ i
  fin_cases k <;> fin_cases i <;> exact ⟨rfl,rfl⟩

theorem stage {s : ℕ} (values : Fin 3 → ℕ) (j : Fin 3) (out : List Bool)
    (ambient : Configuration 52 s) (h : Prepared values j.val out ambient) : ∃ actual,
    runFrom (program j) (EquationHeaderAppend.budget (values j))
      (Composition.restart ambient (program j).start)=some actual ∧
    Prepared values (j.val+1) (out++natWord (values j)) actual.final ∧
    actual.steps ≤ EquationHeaderAppend.budget (values j) := by
  obtain ⟨base,hb,bt,bh,_br,_brh,bs⟩ := EquationHeaderAppend.append_run (values j) out
  have hi : RecoveryFocus.config (slot j) ambient.heads ambient.tapes
      (EquationHeaderAppend.entry (values j) out)=Composition.restart ambient (program j).start := by
    apply WilliamsSourceCrop.focus_same
    · intro i
      fin_cases i
      · exact (h.fresh j (by omega) 0).2
      · exact (h.fresh j (by omega) 1).2
      · exact (h.fresh j (by omega) 2).2
      · exact (h.fresh j (by omega) 3).2
      · exact (h.fresh j (by omega) 4).2
      · exact (h.fresh j (by omega) 5).2
      · exact (h.fresh j (by omega) 6).2
      · exact (h.fresh j (by omega) 7).2
      · exact (h.fresh j (by omega) 8).2
      · exact (h.fresh j (by omega) 9).2
      · exact (h.fresh j (by omega) 10).2
      · exact (h.fresh j (by omega) 11).2
      · exact (h.fresh j (by omega) 12).2
      · exact (h.fresh j (by omega) 13).2
      · exact (h.fresh j (by omega) 14).2
      · exact (h.fresh j (by omega) 15).2
      · exact (h.fresh j (by omega) 16).2
      · exact h.outputHead
    · intro i
      fin_cases i
      · exact (h.fresh j (by omega) 0).1
      · exact (h.fresh j (by omega) 1).1
      · exact (h.fresh j (by omega) 2).1
      · exact (h.fresh j (by omega) 3).1
      · exact (h.fresh j (by omega) 4).1
      · exact (h.fresh j (by omega) 5).1
      · exact (h.fresh j (by omega) 6).1
      · exact (h.fresh j (by omega) 7).1
      · exact (h.fresh j (by omega) 8).1
      · exact (h.fresh j (by omega) 9).1
      · exact (h.fresh j (by omega) 10).1
      · exact (h.fresh j (by omega) 11).1
      · exact (h.fresh j (by omega) 12).1
      · exact (h.fresh j (by omega) 13).1
      · exact (h.fresh j (by omega) 14).1
      · exact (h.fresh j (by omega) 15).1
      · exact (h.fresh j (by omega) 16).1
      · exact h.output
  obtain ⟨actual,ha,hf,hs⟩ := RecoveryFocus.run_config (slot j) (slot_injective j) EquationHeaderAppend.machine
    ambient.heads ambient.tapes _ _ base hb
  rw [hi] at ha
  have pick (i : Fin 18) : RecoveryFocus.pick (slot j) (slot j i)=some i :=
    RecoveryFocus.pick_slot (slot j) (slot_injective j) i
  have ht : actual.final.tapes 51=out++natWord (values j) := by
    change actual.final.tapes (slot j 17)=_
    rw [hf]
    simpa only [RecoveryFocus.config,pick] using bt
  have hh : actual.final.heads 51=(out++natWord (values j)).length := by
    change actual.final.heads (slot j 17)=_
    rw [hf]
    simpa only [RecoveryFocus.config,pick] using bh
  refine ⟨actual,ha,⟨ht,hh,?_⟩,hs.trans_le bs⟩
  intro k hk i
  have hjk : j≠k := by intro he; subst k; omega
  rw [hf]
  simp only [RecoveryFocus.config,slot_other j k hjk i]
  exact h.fresh k (by omega) i

def budget (values : Fin 3 → ℕ) :=
  EquationHeaderAppend.budget (values 0)+1+EquationHeaderAppend.budget (values 1)+1+
    EquationHeaderAppend.budget (values 2)
def output (values : Fin 3 → ℕ) :=
  natWord (values 0)++natWord (values 1)++natWord (values 2)

theorem headers_run (values : Fin 3 → ℕ) (out : List Bool) : ∃ actual,
    runFrom machine (budget values) (entry values out)=some actual ∧
    actual.final.tapes 51=out++output values ∧
    actual.final.heads 51=(out++output values).length ∧ actual.steps ≤ budget values := by
  let start : Configuration 52 _ := ⟨(program 0).start,heads out,input values out⟩
  obtain ⟨a,ha,ap,as⟩ := stage values 0 out start (initial _ values out)
  obtain ⟨b,hb,bp,bs⟩ := stage values 1 (out++natWord (values 0)) a.final ap
  obtain ⟨c,hc,cp,cs⟩ := stage values 2 ((out++natWord (values 0))++natWord (values 1)) b.final bp
  have h1 := Composition.run_join (program 0) (program 1) _ _ _ a b ha hb
  have h2 := Composition.run_join first (program 2) _ _ _
    (Composition.joinedReceipt a b) c h1 hc
  have he : Composition.leftConfig _ (Composition.leftConfig _
      (Composition.restart start (program 0).start))=entry values out := rfl
  rw [he] at h2
  refine ⟨Composition.joinedReceipt (Composition.joinedReceipt a b) c,h2,?_,?_,?_⟩
  · change c.final.tapes 51=_
    simpa only [output,List.append_assoc] using cp.output
  · change c.final.heads 51=_
    simpa only [output,List.append_assoc] using cp.outputHead
  · change a.steps+1+b.steps+1+c.steps ≤ _
    unfold budget
    omega

end NearCubicWires.RepairOrdinary.EquationHeaders
