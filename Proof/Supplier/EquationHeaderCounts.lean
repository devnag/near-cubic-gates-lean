import Proof.Supplier.EquationHeader

/-! Strengthened receipts for the equation header producer (paper3 printer front end, the
Theorem 2.5 instance of the φ header): the same machines and budgets as `EquationHeaders` and
`EquationHeaderCold`, now also exporting the unary count that the first header program retains
(`replicate d true` on its local tape 1, tape 62 of the cold producer). The φ header phase of
`EquationRowPrepare` appends `natWord d` from it. -/
namespace NearCubicWires.RepairOrdinary.EquationHeaderCounts
open LocalBitMultitape RepairRepresentation EquationHeaders
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-- The first header program's retained count, once that program has run. -/
def Counted {s : ℕ} (values : Fin 3 → ℕ) (next : ℕ) (c : Configuration 52 s) : Prop :=
  1 ≤ next → c.tapes (EquationHeaders.slot 0 1)=List.replicate (values 0) true ∧
    c.heads (EquationHeaders.slot 0 1)=0

theorem stageCounts {s : ℕ} (values : Fin 3 → ℕ) (j : Fin 3) (out : List Bool)
    (ambient : Configuration 52 s) (h : EquationHeaders.Prepared values j.val out ambient)
    (hc : Counted values j.val ambient) : ∃ actual,
    runFrom (EquationHeaders.program j) (EquationHeaderAppend.budget (values j))
      (Composition.restart ambient (EquationHeaders.program j).start)=some actual ∧
    EquationHeaders.Prepared values (j.val+1) (out++natWord (values j)) actual.final ∧
    Counted values (j.val+1) actual.final ∧
    actual.steps ≤ EquationHeaderAppend.budget (values j) := by
  obtain ⟨base,hb,bt,bh,br,brh,bs⟩ := EquationHeaderAppend.append_run (values j) out
  have hi : RecoveryFocus.config (EquationHeaders.slot j) ambient.heads ambient.tapes
      (EquationHeaderAppend.entry (values j) out)=Composition.restart ambient (EquationHeaders.program j).start := by
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
  obtain ⟨actual,ha,hf,hs⟩ := RecoveryFocus.run_config (EquationHeaders.slot j) (EquationHeaders.slot_injective j) EquationHeaderAppend.machine
    ambient.heads ambient.tapes _ _ base hb
  rw [hi] at ha
  have pick (i : Fin 18) : RecoveryFocus.pick (EquationHeaders.slot j) (slot j i)=some i :=
    RecoveryFocus.pick_slot (EquationHeaders.slot j) (EquationHeaders.slot_injective j) i
  have ht : actual.final.tapes 51=out++natWord (values j) := by
    change actual.final.tapes (slot j 17)=_
    rw [hf]
    simpa only [RecoveryFocus.config,pick] using bt
  have hh : actual.final.heads 51=(out++natWord (values j)).length := by
    change actual.final.heads (slot j 17)=_
    rw [hf]
    simpa only [RecoveryFocus.config,pick] using bh
  refine ⟨actual,ha,⟨ht,hh,?_⟩,?_,hs.trans_le bs⟩
  · intro k hk i
    have hjk : j≠k := by intro he; subst k; omega
    rw [hf]
    simp only [RecoveryFocus.config,EquationHeaders.slot_other j k hjk i]
    exact h.fresh k (by omega) i
  · intro _
    by_cases hj0 : j=0
    · subst j
      have p1 : RecoveryFocus.pick (EquationHeaders.slot 0) (EquationHeaders.slot 0 1)=some 1 :=
        RecoveryFocus.pick_slot (EquationHeaders.slot 0) (EquationHeaders.slot_injective 0) 1
      constructor
      · rw [hf]; simp only [RecoveryFocus.config,p1]; exact br
      · rw [hf]; simp only [RecoveryFocus.config,p1]; exact brh
    · have hpos : 1 ≤ j.val := by
        rcases Nat.eq_zero_or_pos j.val with h0 | h0
        · exact absurd (Fin.ext h0) hj0
        · exact h0
      have hn := EquationHeaders.slot_other j 0 hj0 1
      have he : EquationHeaders.slot 0 ((1 : Fin 17).castAdd 1)=EquationHeaders.slot 0 1 := rfl
      rw [he] at hn
      obtain ⟨c1,c2⟩ := hc hpos
      constructor
      · rw [hf]; simp only [RecoveryFocus.config,hn]; exact c1
      · rw [hf]; simp only [RecoveryFocus.config,hn]; exact c2

theorem headers_counts (values : Fin 3 → ℕ) (out : List Bool) : ∃ actual,
    runFrom EquationHeaders.machine (EquationHeaders.budget values) (EquationHeaders.entry values out)=some actual ∧
    actual.final.tapes 51=out++output values ∧
    actual.final.heads 51=(out++output values).length ∧
    actual.final.tapes 1=List.replicate (values 0) true ∧ actual.final.heads 1=0 ∧
    actual.steps ≤ EquationHeaders.budget values := by
  let start : Configuration 52 _ := ⟨(EquationHeaders.program 0).start,EquationHeaders.heads out,EquationHeaders.input values out⟩
  obtain ⟨a,ha,ap,ac,as⟩ := stageCounts values 0 out start (EquationHeaders.initial _ values out) (by intro h; simp at h)
  obtain ⟨b,hb,bp,bc,bs⟩ := stageCounts values 1 (out++natWord (values 0)) a.final ap ac
  obtain ⟨c,hc,cp,cc,cs⟩ := stageCounts values 2 ((out++natWord (values 0))++natWord (values 1)) b.final bp bc
  have h1 := Composition.run_join (EquationHeaders.program 0) (EquationHeaders.program 1) _ _ _ a b ha hb
  have h2 := Composition.run_join EquationHeaders.first (EquationHeaders.program 2) _ _ _
    (Composition.joinedReceipt a b) c h1 hc
  have he : Composition.leftConfig _ (Composition.leftConfig _
      (Composition.restart start (EquationHeaders.program 0).start))=EquationHeaders.entry values out := rfl
  rw [he] at h2
  refine ⟨Composition.joinedReceipt (Composition.joinedReceipt a b) c,h2,?_,?_,
    (cc (by decide)).1,(cc (by decide)).2,?_⟩
  · change c.final.tapes 51=_
    simpa only [EquationHeaders.output,List.append_assoc] using cp.output
  · change c.final.heads 51=_
    simpa only [EquationHeaders.output,List.append_assoc] using cp.outputHead
  · change a.steps+1+b.steps+1+c.steps ≤ _
    unfold EquationHeaders.budget
    omega

end NearCubicWires.RepairOrdinary.EquationHeaderCounts

namespace NearCubicWires.RepairOrdinary.EquationHeaderCold
open LocalBitMultitape RepairRepresentation

theorem cold_counts (d p g : ℕ) (odd : Bool) (suffix : List Bool) : ∃ actual,
    run machine (budget d p g odd suffix) (input d p g odd suffix)=some actual ∧
    actual.final.tapes 0=frame (EquationHeaderRead.word d p g (odd::suffix)) ∧ actual.final.heads 0=0 ∧
    actual.final.tapes 1=EquationHeaderRead.word d p g (odd::suffix) ∧
      actual.final.heads 1=(EquationHeaderRead.header d p g).length+1 ∧
    actual.final.tapes 110=EquationHeaderRead.header d (p+1) (2*g) ∧
      actual.final.heads 110=(EquationHeaderRead.header d (p+1) (2*g)).length ∧
    (∀ j,j≠12 → j≠14 → j≠20 →
      actual.final.tapes (bank j)=EquationCountCapacity.data8 d p g odd j ∧ actual.final.heads (bank j)=0) ∧
    actual.final.tapes 62=List.replicate d true ∧ actual.final.heads 62=0 ∧
    actual.steps ≤ budget d p g odd suffix := by
  obtain ⟨base,hb,bt0,bh0,bt1,bh1,fields,bs⟩ := EquationCountCold.cold_run d p g odd suffix
  let prepared := TapeEmbedding.receipt (fun _ : Fin 49 => 0) (fun _ : Fin 49 => []) base
  have he := TapeEmbedding.run_embed EquationCountCold.machine (fun _ : Fin 49 => 0)
    (fun _ : Fin 49 => []) _ _ base hb
  have oldT (i : Fin 62) : prepared.final.tapes (i.castAdd 49)=base.final.tapes i := by
    change (Fin.addCases (m := 62) (n := 49) (motive := fun _ => List Bool)
      base.final.tapes (fun _ => [])) (i.castAdd 49)=_
    rw [Fin.addCases_left]
  have oldH (i : Fin 62) : prepared.final.heads (i.castAdd 49)=base.final.heads i := by
    change (Fin.addCases (m := 62) (n := 49) (motive := fun _ => ℕ)
      base.final.heads (fun _ => 0)) (i.castAdd 49)=_
    rw [Fin.addCases_left]
  obtain ⟨body,hbody,bodyT,bodyH,bodyC,bodyCH,bodyS⟩ := EquationHeaderCounts.headers_counts (values d p g) []
  have hi : RecoveryFocus.config slots prepared.final.heads prepared.final.tapes
      (EquationHeaders.entry (values d p g) [])=Composition.restart prepared.final last.start := by
    apply WilliamsSourceCrop.focus_same
    · intro j
      fin_cases j
      · exact (oldH (EquationCountCold.slots 12)).trans (fields 12).2
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · exact (oldH (EquationCountCold.slots 14)).trans (fields 14).2
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · exact (oldH (EquationCountCold.slots 20)).trans (fields 20).2
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
    · intro j
      fin_cases j
      · exact (oldT (EquationCountCold.slots 12)).trans (fields 12).1
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · exact (oldT (EquationCountCold.slots 14)).trans (fields 14).1
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · exact (oldT (EquationCountCold.slots 20)).trans (fields 20).1
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
  obtain ⟨focused,hf,ff,fs⟩ := RecoveryFocus.run_config slots slots_injective EquationHeaders.machine
    prepared.final.heads prepared.final.tapes _ _ body hbody
  rw [hi] at hf
  have hj := Composition.run_join first last _ _ _ prepared focused he hf
  have hin : Composition.leftConfig _
      (TapeEmbedding.config (fun _ : Fin 49 => 0) (fun _ : Fin 49 => [])
        (initialConfiguration EquationCountCold.machine (EquationCountCold.input d p g odd suffix)))=
      initialConfiguration machine (input d p g odd suffix) := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  rw [hin] at hj
  have otherT (i : Fin 62) (hn : RecoveryFocus.pick slots (i.castAdd 49)=none) :
      focused.final.tapes (i.castAdd 49)=base.final.tapes i := by
    rw [ff]
    simp only [RecoveryFocus.config,hn]
    exact oldT i
  have otherH (i : Fin 62) (hn : RecoveryFocus.pick slots (i.castAdd 49)=none) :
      focused.final.heads (i.castAdd 49)=base.final.heads i := by
    rw [ff]
    simp only [RecoveryFocus.config,hn]
    exact oldH i
  have pick : RecoveryFocus.pick slots (slots 51)=some 51 := RecoveryFocus.pick_slot slots slots_injective 51
  have pick1 : RecoveryFocus.pick slots (slots 1)=some 1 := RecoveryFocus.pick_slot slots slots_injective 1
  refine ⟨Composition.joinedReceipt prepared focused,hj,
    (otherT 0 (by decide)).trans bt0,(otherH 0 (by decide)).trans bh0,
    (otherT 1 (by decide)).trans bt1,(otherH 1 (by decide)).trans bh1,?_,?_,?_,?_,?_,?_⟩
  · change focused.final.tapes (slots 51)=_
    rw [ff]
    simp only [RecoveryFocus.config,pick]
    have ht : body.final.tapes 51=[]++EquationHeaderRead.header d (p+1) (2*g) := bodyT
    simpa only [List.nil_append] using ht
  · change focused.final.heads (slots 51)=_
    rw [ff]
    simp only [RecoveryFocus.config,pick]
    have hh : body.final.heads 51=([]++EquationHeaderRead.header d (p+1) (2*g)).length := bodyH
    simpa only [List.nil_append] using hh
  · intro j h12 h14 h20
    exact ⟨(otherT (EquationCountCold.slots j) (bank_other j h12 h14 h20)).trans (fields j).1,
      (otherH (EquationCountCold.slots j) (bank_other j h12 h14 h20)).trans (fields j).2⟩
  · change focused.final.tapes (slots 1)=_
    rw [ff]
    simp only [RecoveryFocus.config,pick1]
    exact bodyC
  · change focused.final.heads (slots 1)=_
    rw [ff]
    simp only [RecoveryFocus.config,pick1]
    exact bodyCH
  · change base.steps+1+focused.steps ≤ _
    rw [fs]
    unfold budget
    omega

end NearCubicWires.RepairOrdinary.EquationHeaderCold
