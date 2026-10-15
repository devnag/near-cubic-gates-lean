import Proof.CaseAnalysis.CaseTwoTagObserve
import Proof.CaseAnalysis.CaseTwoAdvance

/-! A complete private-tag call starts and ends with all heads at zero.
The source offset advances past its six tag bits. Private buffer allocation
and the complete rewind log are explicit and reusable. -/
namespace NearCubicWires.RepairOrdinary.CloseoutCaseTwo.TagReady
open LocalBitMultitape RepairRepresentation OuterPCPRecovery RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def advanceSlots : Fin 3→Fin 26:=![3,2,22]
noncomputable def advance:=RecoveryFocus.machine advanceSlots Advance.machine
noncomputable def raw:=Composition.machine TagObserve.machine advance
def rawBudget (offset tag C : ℕ):=TagObserve.budget offset tag C+2*(6+offset)+7
def capacity (C : ℕ):=16*(C+1)
def pads (C : ℕ) (i : Fin 26):=if i=21 then C else 0
def localData (C : ℕ) (source : List Bool) (offset : ℕ) (out : List Bool) (flag : Bool) :=
  fun i : Fin 26=>ZeroPadding.pad (pads C i) (TagObserve.data C source offset out flag i)
def data (C : ℕ) (source : List Bool) (offset : ℕ) (out : List Bool) (flag : Bool) : Fin 27→List Bool:=
  Fin.addCases (m:=26) (n:=1) (localData C source offset out flag)
    (fun _ : Fin 1=>List.replicate (capacity C) false)
noncomputable def machine:=Rewind.machine raw
def budget (C : ℕ):=2*capacity C+2

theorem raw_run (pre tail : List Bool) (tag : Fin 6) (C : ℕ) (flag : Bool)
    (hsource : 2*(pre++orderedNatBits 6 tag.val++tail).length+1≤C)
    (hoffset : pre.length+8≤C)
    (hbudget : FieldNative.budget pre.length 6 tag.val+1≤C) :
    let source:=pre++orderedNatBits 6 tag.val++tail
    ∃ r,run raw (rawBudget pre.length tag.val C)
      (TagObserve.data C source pre.length [] flag)=some r ∧
      r.steps≤capacity C ∧
      r.final.tapes=TagObserve.data C source (pre.length+6) (natWord tag.val) (decide (tag.val=5)) := by
  let source:=pre++orderedNatBits 6 tag.val++tail
  obtain ⟨a,ar,asteps,ah,atapes⟩:=TagObserve.tag_run pre tail tag C [] flag hsource
    (by omega) (by omega) hbudget
  obtain ⟨b,br,bh,bt,bs⟩:=(Advance.ready 6 pre.length C (by omega)).focus_at advanceSlots
    (by decide) a.final.heads a.final.tapes
    (by intro j;rw [atapes];fin_cases j <;> rfl)
    (by intro j;rw [ah];fin_cases j <;> rfl)
  have whole:=Composition.run_join TagObserve.machine advance _ _ _ a b ar br
  have hb : TagObserve.budget pre.length tag.val C+1+(2*(6+pre.length)+6)=rawBudget pre.length tag.val C:=by
    unfold rawBudget;omega
  rw [hb] at whole
  have hin : (⟨raw.start,TagObserve.heads [],TagObserve.data C source pre.length [] flag⟩ : Configuration 26 _)=
      initialConfiguration raw (TagObserve.data C source pre.length [] flag):=by
    apply configuration_ext
    · rfl
    · funext i;simp [TagObserve.heads,initialConfiguration]
    · rfl
  change runFrom raw _ ⟨raw.start,TagObserve.heads [],TagObserve.data C source pre.length [] flag⟩=some _ at whole
  rw [hin] at whole
  refine ⟨Composition.joinedReceipt a b,whole,?_,?_⟩
  · change a.steps+1+b.steps≤capacity C
    unfold capacity TagObserve.budget FieldReady.budget at *
    omega
  · change b.final.tapes=_
    rw [bt]
    apply HierarchyAllocation.install_eq advanceSlots (by decide)
    · intro j;fin_cases j <;> rfl
    · intro i hi
      rw [atapes]
      have hn : i≠2:=fun h=>hi 1 h.symm
      simp only [TagObserve.data,hn,if_false,List.nil_append]

theorem tag_ready (pre tail : List Bool) (tag : Fin 6) (C : ℕ) (flag : Bool)
    (hsource : 2*(pre++orderedNatBits 6 tag.val++tail).length+1≤C)
    (hoffset : pre.length+8≤C)
    (hbudget : FieldNative.budget pre.length 6 tag.val+1≤C) :
    ClockJoin.ReadyRun machine (budget C)
      (data C (pre++orderedNatBits 6 tag.val++tail) pre.length [] flag)
      (data C (pre++orderedNatBits 6 tag.val++tail) (pre.length+6) (natWord tag.val) (decide (tag.val=5))) := by
  let source:=pre++orderedNatBits 6 tag.val++tail
  obtain ⟨base,hr,hs,ht⟩:=raw_run pre tail tag C flag hsource hoffset hbudget
  obtain ⟨p,hp,pf,ps,_⟩:=ZeroPadding.run_config raw (pads C) _ _ base hr
  have hi : ZeroPadding.config (pads C) (initialConfiguration raw (TagObserve.data C source pre.length [] flag))=
      initialConfiguration raw (localData C source pre.length [] flag):=by rfl
  rw [hi] at hp
  obtain ⟨r,rr,rt,rl,rh,rs,_⟩:=Rewind.Workspace.reset_workspace raw _ _ p hp (capacity C)
  have hc : p.steps≤capacity C:=ps.trans_le hs
  have hb : 2*p.steps+2≤budget C:=by unfold budget;omega
  have more:=run_moreFuel machine _ (budget C-(2*p.steps+2))
    (data C source pre.length [] flag) r rr
  rw [Nat.add_sub_of_le hb] at more
  refine ⟨r,more,?_,rh,rs.le.trans hb⟩
  funext i
  refine Fin.addCases (m:=26) (n:=1) (fun j=>?_) (fun j=>?_) i
  · simp only [data,Fin.addCases_left]
    rw [rt j,pf]
    change ZeroPadding.pad (pads C j) (base.final.tapes j)=_
    rw [ht]
    rfl
  · fin_cases j
    have he : (0 : Fin 1).natAdd 26=(26 : Fin 27):=by decide
    rw [he,Nat.max_eq_left hc] at rl
    exact rl

end NearCubicWires.RepairOrdinary.CloseoutCaseTwo.TagReady
