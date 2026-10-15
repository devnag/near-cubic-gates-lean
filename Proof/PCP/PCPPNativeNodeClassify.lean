import Proof.PCP.PCPPNativeNodeRead
import Proof.PCP.PCPPNativeTag
import Proof.Amplification.RecoveryFocusDock

/-! One original native node is parsed and physically classified. The
source cursor advances across exactly its three native natural fields;
both actual argument templates remain available to the chosen branch. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeNodeClassify
open LocalBitMultitape RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

abbrev readerStates := PCPPQueryNatural.states+PCPPQueryNatural.states+PCPPQueryNatural.states
def tagSlots : Fin 1 → Fin 31 := fun _ => 10
noncomputable def tagMachine := RecoveryFocus.machine tagSlots PCPPNativeTag.machine
noncomputable def machine := Composition.machine PCPPNativeNodeRead.machine tagMachine
noncomputable def entry (word : List Bool) (pos : ℕ) :=
  Composition.leftConfig 10 (PCPPNativeNodeRead.entry word pos)
def budget (tag : Fin 5) (a b : ℕ) := PCPPNativeNodeRead.budget tag.val a b+1+(tag.val+1)

theorem classify_run (pre tail : List Bool) (tag : Fin 5) (a b : ℕ) :
    ∃ r,runFrom machine (budget tag a b)
      (entry (PCPPNativeNodeRead.source pre tail tag.val a b) pre.length)=some r ∧
      r.steps ≤ budget tag a b ∧ r.final.control.val=readerStates+(tag.val+5) ∧
      r.final.tapes 0=PCPPNativeNodeRead.source pre tail tag.val a b ∧
      r.final.heads 0=pre.length+(natWord tag.val).length+(natWord a).length+(natWord b).length ∧
      r.final.tapes 10=UnaryTemplate.tape tag.val ∧ r.final.heads 10=tag.val+1 ∧
      r.final.tapes 20=UnaryTemplate.tape a ∧ r.final.heads 20=1 ∧
      r.final.tapes 30=UnaryTemplate.tape b ∧ r.final.heads 30=1 := by
  obtain ⟨first,hfirst,fs,f0,fh0,ft,fh⟩ := PCPPNativeNodeRead.cold_run pre tail tag.val a b
  have htag := PCPPNativeTag.tag_run tag
  obtain ⟨second,hsecond,sc,ss,sh,st,keep⟩ := RecoveryFocus.dock tagSlots
    (by intro i j _; exact Subsingleton.elim i j) PCPPNativeTag.machine _ first.final.heads first.final.tapes
    (PCPPNativeTag.entry tag)
    (by intro i; fin_cases i; exact fh 0)
    (by intro i; fin_cases i; exact ft 0) (PCPPNativeTag.receipt tag) htag
  let result := Composition.joinedReceipt first second
  have hr := Composition.run_join PCPPNativeNodeRead.machine tagMachine _ _ _ first second hfirst hsecond
  refine ⟨result,hr,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · change first.steps+1+second.steps ≤ _
    rw [ss]
    change first.steps+1+(tag.val+1) ≤ _
    unfold budget
    omega
  · change readerStates+second.final.control.val=_
    rw [sc]
    rfl
  · change second.final.tapes 0=_
    rw [(keep 0 (by decide)).2]
    exact f0
  · change second.final.heads 0=_
    rw [(keep 0 (by decide)).1]
    exact fh0
  · exact st 0
  · exact sh 0
  · change second.final.tapes 20=_
    rw [(keep 20 (by decide)).2]
    exact ft 1
  · change second.final.heads 20=_
    rw [(keep 20 (by decide)).1]
    exact fh 1
  · change second.final.tapes 30=_
    rw [(keep 30 (by decide)).2]
    exact ft 2
  · change second.final.heads 30=_
    rw [(keep 30 (by decide)).1]
    exact fh 2

end NearCubicWires.RepairOrdinary.PCPPNativeNodeClassify
