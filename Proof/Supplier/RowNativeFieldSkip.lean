import Proof.Circuits.DecompositionSourceFields

/-! Skip native signed fields at the retained source cursor. The existing
natural-field parser reads their actual widths; skipped fields are not copied. -/
namespace NearCubicWires.RepairOrdinary.RowNativeFieldSkip
open LocalBitMultitape RepairRepresentation RecoveryExecution Streaming PCPPQueryField
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def sign : Machine 3 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==1
  rule := fun _ _ => some ⟨1,fun _ => none,![.right,.stay,.stay]⟩
def machine := Composition.machine sign (PCPPQueryField.machine false)
def cost (z : ℤ) := 2*natBitLength z.natAbs+5
def saved := DecompositionSource.Fields.saved

theorem sign_run (source backing out : List Bool) (pos : ℕ) :
    ∃ r,runFrom sign 1 (store 0 source pos backing out)=some r ∧
      r.final=store 1 source (pos+1) backing out ∧ r.steps=1 := by
  have hs : step sign (store 0 source pos backing out)=some (store 1 source (pos+1) backing out) := by
    apply congrArg some
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · rfl
  exact (Timed.single (by rfl) hs).run (by rfl)

theorem int_run (pre tail backing out : List Bool) (z : ℤ) :
    ∃ r,runFrom machine (cost z)
      (store 0 (pre++intWord z++tail) pre.length backing out)=some r ∧
      r.final=store 5 (pre++intWord z++tail) (pre.length+(intWord z).length)
        (saved z backing) out ∧ r.steps=cost z := by
  let b := decide (z<0)
  let source := pre++intWord z++tail
  obtain ⟨first,hfirst,hff,hfs⟩ := sign_run source backing out pre.length
  obtain ⟨last,hl,hlf,hls⟩ := nat_run false (pre++[b]) tail backing out z.natAbs
  have hsource : (pre++[b])++natWord z.natAbs++tail=source := by
    simp [source,intWord,b,List.append_assoc]
  rw [hsource] at hl hlf
  have hi : PCPPQueryField.cfg 0 source (pre++[b]).length backing 0 out=
      Composition.restart first.final (PCPPQueryField.machine false).start := by
    rw [hff]
    simp [PCPPQueryField.cfg,store,Composition.restart,PCPPQueryField.machine]
  rw [hi] at hl
  have hj := Composition.run_join sign (PCPPQueryField.machine false) 1
    (2*natBitLength z.natAbs+3) _ first last hfirst hl
  have ht : 1+1+(2*natBitLength z.natAbs+3)=cost z := by unfold cost; omega
  rw [ht] at hj
  change runFrom machine (cost z) (store 0 source pre.length backing out)=_ at hj
  refine ⟨Composition.joinedReceipt first last,hj,?_,?_⟩
  · change Composition.rightConfig 2 last.final=_
    rw [hlf]
    simp only [selected,Bool.false_eq_true,↓reduceIte,List.append_nil,List.length_append,List.length_singleton]
    have hp : pre.length+1+2*natBitLength z.natAbs+1=pre.length+(intWord z).length := by
      rw [intWord,List.length_cons,DecompositionSource.natWord_length]
      omega
    rw [hp]
    rfl
  · change first.steps+1+last.steps=_
    rw [hfs,hls]
    exact ht

noncomputable def loop := RepeatMachine.machine machine (fun _ _ => true)
noncomputable def cfg (phase : Fin 5) (source : List Bool) (pos : ℕ)
    (backing out : List Bool) (total driver : ℕ) :=
  RepeatMachine.cfg phase (store (s:=6) 0 source pos backing out) total driver
def savedList (zs : List ℤ) (backing : List Bool) := zs.foldl (fun bs z => saved z bs) backing

theorem remaining (pre tail backing out : List Bool) (zs : List ℤ) (total pos : ℕ)
    (hn : pos+zs.length=total) :
    Timed loop ((zs.flatMap intWord).length+5*zs.length+total+3)
      (cfg 0 (pre++zs.flatMap intWord++tail) pre.length backing out total (pos+1))
      (cfg 3 (pre++zs.flatMap intWord++tail) (pre.length+(zs.flatMap intWord).length)
        (savedList zs backing) out total 1) := by
  induction zs generalizing pre backing pos with
  | nil =>
    have hp : pos=total := by simpa using hn
    subst pos
    simpa [loop,cfg,savedList] using RepeatMachine.exhaust machine (fun _ _ => true)
      (store 0 (pre++tail) pre.length backing out) total
  | cons z zs ih =>
    obtain ⟨r,hr,hf,hs⟩ := int_run pre (zs.flatMap intWord++tail) backing out z
    have hb := RepeatMachine.iteration machine (fun _ _ => true)
      (store 0 (pre++intWord z++(zs.flatMap intWord++tail)) pre.length backing out)
      total pos r (by rfl) (by simp only [List.length_cons] at hn; omega) hr
    rw [hf,hs] at hb
    have ht := ih (pre++intWord z) (saved z backing) (pos+1)
      (by simp only [List.length_cons] at hn; omega)
    have hsource : (pre++intWord z)++zs.flatMap intWord++tail=
        pre++intWord z++(zs.flatMap intWord++tail) := by simp [List.append_assoc]
    rw [hsource,List.length_append] at ht
    change Timed loop (cost z+2) _ _ at hb
    simp only [↓reduceIte] at hb
    have hmid : RepeatMachine.cfg 0 (store (s:=6) 5
        (pre++intWord z++(zs.flatMap intWord++tail)) (pre.length+(intWord z).length)
        (saved z backing) out) total (pos+2)=
        cfg 0 (pre++intWord z++(zs.flatMap intWord++tail)) (pre.length+(intWord z).length)
          (saved z backing) out total ((pos+1)+1) := rfl
    rw [hmid] at hb
    have hall := hb.trans ht
    have hc : cost z=(intWord z).length+3 := by
      simp [cost,DecompositionSource.intWord_length,natBitLength,intBitLength]
    rw [hc] at hall
    have htime : (intWord z).length+3+2+((zs.flatMap intWord).length+5*zs.length+total+3)=
        ((z::zs).flatMap intWord).length+5*(z::zs).length+total+3 := by
      simp only [List.flatMap_cons,List.length_append,List.length_cons]
      omega
    rw [htime] at hall
    simpa [cfg,List.flatMap_cons,List.append_assoc,savedList,Nat.add_assoc] using hall

theorem list_run (pre tail backing out : List Bool) (zs : List ℤ) :
    ∃ r,runFrom loop ((zs.flatMap intWord).length+6*zs.length+3)
      (cfg 0 (pre++zs.flatMap intWord++tail) pre.length backing out zs.length 1)=some r ∧
      r.final=cfg 3 (pre++zs.flatMap intWord++tail) (pre.length+(zs.flatMap intWord).length)
        (savedList zs backing) out zs.length 1 ∧
      r.steps=(zs.flatMap intWord).length+6*zs.length+3 := by
  have h := remaining pre tail backing out zs zs.length 0 (by omega)
  have ht : (zs.flatMap intWord).length+5*zs.length+zs.length+3=
      (zs.flatMap intWord).length+6*zs.length+3 := by omega
  rw [ht] at h
  exact h.run (by simp [loop,cfg,RepeatMachine.machine,RepeatMachine.cfg,controlConfig,RepeatMachine.phaseCode])

end NearCubicWires.RepairOrdinary.RowNativeFieldSkip
