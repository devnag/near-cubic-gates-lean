import Proof.CaseAnalysis.WitnessSumPrefix
import Proof.CaseAnalysis.WitnessSumBodyRun

/-! The complete sum prefix and term body share their actual field stream,
count driver and verdict. All other parser fields occupy one separate
reusable bank; the retained coefficient and native streams are untouched. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.SumDock
open LocalBitMultitape RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots (i : Fin 528) : Fin 3061 :=
  ⟨if i.val=357 then 722 else if i.val=368 then 2532 else if i.val=499 then 724 else 2533+i.val,
    by split_ifs <;> omega⟩
noncomputable def reader := RecoveryFocus.machine slots SumPrefix.machine
noncomputable def body {s : ℕ} (circuit : Machine 1703 s) (k : ℕ) (q : ℚ) :=
  TapeEmbedding.machine 528 (SumBody.machine circuit k q)
def coreHeads (position driver : ℕ) (out native : List Bool) : Fin 2533 → ℕ :=
  Fin.addCases (m:=2532) (n:=1) (motive:=fun _=>ℕ)
    (TermRound.heads position out (TermEnvironment.heads native)) (fun _=>driver)
def coreData (P H b core W L : ℕ) (source out native driver : List Bool) (flag : Bool)
    (ambient : Fin 94 → List Bool) : Fin 2533 → List Bool :=
  Fin.addCases (m:=2532) (n:=1) (motive:=fun _=>List Bool)
    (TermRound.data P (TermRead.data P b [] source flag) ambient out (TermEnvironment.tapes H core W L native))
    (fun _=>driver)
def extra (H T : ℕ) (bits arityBits counts : List Bool) (i : Fin 528) :=
  if i.val=1 then ZeroPadding.pad H (frame bits) else if i.val=501 then frame arityBits
  else if i.val=502 then List.replicate T true else if i.val=526 then counts else List.replicate H false
def heads (out native counts : List Bool) : Fin 3061 → ℕ :=
  Fin.addCases (m:=2533) (n:=528) (motive:=fun _=>ℕ) (coreHeads 0 0 out native) (SumCountStream.heads counts)
def input (P H b core W L T : ℕ) (bits arityBits out native counts : List Bool)
    (ambient : Fin 94 → List Bool) : Fin 3061 → List Bool :=
  Fin.addCases (m:=2533) (n:=528) (motive:=fun _=>List Bool)
    (coreData P H b core W L (List.replicate H false) out native (List.replicate H false) false ambient)
    (extra H T bits arityBits counts)

theorem slots_injective : Function.Injective slots := by
  intro i j h
  have hv := congrArg (fun z : Fin 3061=>z.val) h
  dsimp only [slots] at hv
  split_ifs at hv <;> apply Fin.ext <;> omega

theorem core_outside (i : Fin 2533) (h722 : i≠722) (h724 : i≠724) (h2532 : i≠2532) :
    ∀ j,slots j≠i.castAdd 528 := by
  intro j h
  have hv := congrArg (fun z : Fin 3061=>z.val) h
  dsimp only [slots,Fin.val_castAdd] at hv
  split_ifs at hv
  · exact h722 (Fin.ext hv.symm)
  · exact h2532 (Fin.ext hv.symm)
  · exact h724 (Fin.ext hv.symm)
  · omega

theorem heads_reader (out native counts : List Bool) (i : Fin 528) :
    heads out native counts (slots i)=SumCountStream.heads counts i := by
  by_cases h357 : i=357
  · subst i;rfl
  by_cases h368 : i=368
  · subst i;rfl
  by_cases h499 : i=499
  · subst i;rfl
  have h357' : i.val≠357 := by intro h;exact h357 (Fin.ext h)
  have h368' : i.val≠368 := by intro h;exact h368 (Fin.ext h)
  have h499' : i.val≠499 := by intro h;exact h499 (Fin.ext h)
  have he : slots i=i.natAdd 2533 := by simp only [slots,if_neg h357',if_neg h368',if_neg h499'];rfl
  rw [he,heads,Fin.addCases_right]

theorem input_reader (P H b core W L T : ℕ) (bits arityBits out native counts : List Bool)
    (ambient : Fin 94 → List Bool) (i : Fin 528) :
    input P H b core W L T bits arityBits out native counts ambient (slots i)=
      SumCountStream.input H (SumHeader.input H bits arityBits T) counts i := by
  by_cases h357 : i=357
  · subst i;rfl
  by_cases h368 : i=368
  · subst i;rfl
  by_cases h499 : i=499
  · subst i;rfl
  have h357' : i.val≠357 := by intro h;exact h357 (Fin.ext h)
  have h368' : i.val≠368 := by intro h;exact h368 (Fin.ext h)
  have h499' : i.val≠499 := by intro h;exact h499 (Fin.ext h)
  have he : slots i=i.natAdd 2533 := by simp only [slots,if_neg h357',if_neg h368',if_neg h499'];rfl
  rw [he,input,Fin.addCases_right]
  revert h499'
  refine Fin.addCases (m:=510) (n:=18) ?_ ?_ i
  · intro j hj
    change j.val≠499 at hj
    simp only [SumCountStream.input,Fin.addCases_left,extra,Fin.val_castAdd,SumHeader.input,
      SumHeader.capacity,SumGuard.input]
    by_cases h1 : j.val=1
    · simp [h1]
    by_cases h501 : j.val=501
    · simp [h501]
    by_cases h502 : j.val=502
    · simp [h502]
    simp [h1,h501,h502,hj,show j.val≠526 by omega,ZeroPadding.pad]
  · intro j _
    fin_cases j <;> rfl

end NearCubicWires.RepairOrdinary.CloseoutWitness.SumDock
