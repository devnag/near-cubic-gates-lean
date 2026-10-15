import Proof.PCP.PCPPQueryField
import Proof.Hierarchy.CompetitorRawScalarEmit
import Proof.MachineModel.OrdinaryWilliamsSourceCropLayout

/-! The exact source-request word copies the actual native arity field and
appends the raw bits of the physically produced canonical circuit frame. -/
namespace NearCubicWires.RepairOrdinary.PCPPRequestWord
open LocalBitMultitape RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def headerSlots : Fin 3 → Fin 5 := ![0,2,3]
def codeSlots : Fin 3 → Fin 5 := ![1,3,4]
theorem header_injective : Function.Injective headerSlots := by decide
theorem code_injective : Function.Injective codeSlots := by decide
noncomputable def first := RecoveryFocus.machine headerSlots (PCPPQueryField.machine true)
noncomputable def second := RecoveryFocus.machine codeSlots CompetitorRawScalarEmit.machine
noncomputable def machine := Composition.machine first second
def input (n : ℕ) (tail bits suffix : List Bool) : Fin 5 → List Bool :=
  ![natWord n++tail,frame bits++suffix,[],[],[]]
def budget (n : ℕ) (bits : List Bool) := 2*natBitLength n+4*bits.length+7

theorem word_run (n : ℕ) (tail bits suffix : List Bool) :
    ∃ r,run machine (budget n bits) (input n tail bits suffix)=some r ∧
      r.final.tapes 3=natWord n++bits ∧ r.final.heads 3=(natWord n++bits).length ∧
      r.steps=budget n bits := by
  obtain ⟨base,hb,bf,bs⟩ := PCPPQueryField.nat_run true [] tail [] [] n
  simp only [List.nil_append,List.length_nil] at hb
  obtain ⟨prep,hp,pf,ps⟩ := RecoveryFocus.run_config headerSlots header_injective
    (PCPPQueryField.machine true) (fun _ => 0) (input n tail bits suffix) _ _ base hb
  have hi : RecoveryFocus.config headerSlots (fun _ => 0) (input n tail bits suffix)
      (PCPPQueryField.cfg 0 (natWord n++tail) 0 [] 0 [])=
      initialConfiguration first (input n tail bits suffix) := by
    exact WilliamsSourceCrop.focus_same headerSlots (initialConfiguration first (input n tail bits suffix))
      (PCPPQueryField.cfg 0 (natWord n++tail) 0 [] 0 [])
      (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  rw [hi] at hp
  have ph : prep.final.heads 3=(natWord n).length := by
    rw [pf,bf]
    simp only [RecoveryFocus.config,show (3 : Fin 5)=headerSlots 2 from rfl,
      RecoveryFocus.pick_slot headerSlots header_injective,PCPPQueryField.payload,PCPPQueryField.cfg]
    simp [PCPPQueryField.selected]
  have pt : prep.final.tapes 3=natWord n := by
    rw [pf,bf]
    simp only [RecoveryFocus.config,show (3 : Fin 5)=headerSlots 2 from rfl,
      RecoveryFocus.pick_slot headerSlots header_injective,PCPPQueryField.payload,PCPPQueryField.cfg]
    simp [PCPPQueryField.selected]
  have untouched (i : Fin 5) (hn : ∀ j,headerSlots j≠i) :
      prep.final.heads i=0 ∧ prep.final.tapes i=input n tail bits suffix i := by
    have hpick : RecoveryFocus.pick headerSlots i=none := by
      have he : ¬∃ j,headerSlots j=i := by rintro ⟨j,hj⟩; exact hn j hj
      simp only [RecoveryFocus.pick,dif_neg he]
    rw [pf]
    simp only [RecoveryFocus.config,hpick,and_self]
  obtain ⟨ph1,pt1⟩ := untouched 1 (by decide)
  obtain ⟨ph4,pt4⟩ := untouched 4 (by decide)
  obtain ⟨last,hl,lf,ls⟩ := CompetitorRawScalarEmit.append_run bits suffix (natWord n)
  obtain ⟨called,hcall,cf,cs⟩ := RecoveryFocus.run_config codeSlots code_injective
    CompetitorRawScalarEmit.machine prep.final.heads prep.final.tapes _ _ last hl
  have hc : RecoveryFocus.config codeSlots prep.final.heads prep.final.tapes
      (CompetitorRawScalarEmit.scan 0 (frame bits++suffix) 0 (natWord n))=
      Composition.restart prep.final second.start := by
    apply WilliamsSourceCrop.focus_same
    · intro j; fin_cases j
      · exact ph1
      · exact ph
      · exact ph4
    · intro j; fin_cases j
      · exact pt1
      · exact pt
      · exact pt4
  rw [hc] at hcall
  have whole := Composition.run_join first second _ _ _ prep called hp hcall
  have initial : Composition.leftConfig _ (initialConfiguration first (input n tail bits suffix))=
      initialConfiguration machine (input n tail bits suffix) := rfl
  rw [initial] at whole
  have time : (2*natBitLength n+3)+1+(4*bits.length+3)=budget n bits := by unfold budget; omega
  rw [time] at whole
  refine ⟨Composition.joinedReceipt prep called,whole,?_,?_,?_⟩
  · change called.final.tapes 3=_
    rw [cf,lf]
    simp only [RecoveryFocus.config,show (3 : Fin 5)=codeSlots 1 from rfl,
      RecoveryFocus.pick_slot codeSlots code_injective,CompetitorRawScalarEmit.reset]
    rfl
  · change called.final.heads 3=_
    rw [cf,lf]
    simp only [RecoveryFocus.config,show (3 : Fin 5)=codeSlots 1 from rfl,
      RecoveryFocus.pick_slot codeSlots code_injective,CompetitorRawScalarEmit.reset]
    rfl
  · change prep.steps+1+called.steps=_
    rw [ps,bs,cs,ls,time]

end NearCubicWires.RepairOrdinary.PCPPRequestWord
