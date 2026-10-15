import Proof.Hierarchy.CompetitorDenominator
import Proof.Amplification.RecoveryScratchErase

/-! Bounded reusable scalar workspace for the validity-list consumer.
Padding records actual retained zero cells; the local machine executes the
same transitions on them, and its output support fits the next paid erase.
The framed scalar loader retains the global stream cursor. -/
namespace NearCubicWires.RepairOrdinary.CompetitorReusableDecision
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open CompetitorRationalDecision
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def capacity (b : ℕ) := 4096*(b+1)^2
def padding (b : ℕ) (i : Fin 67) := if i.val=6 then 0 else capacity b
def paddedInput (b : ℕ) (nums : Fin 4 → ℕ) (d e : ℕ) : Fin 67 → List Bool :=
  fun i => ZeroPadding.pad (padding b i) (CompetitorRationalProducts.input (width b) b nums d e i)

theorem input_support (b : ℕ) (nums : Fin 4 → ℕ) (d e : ℕ) (i : Fin 67) :
    (CompetitorRationalProducts.input (width b) b nums d e i).length≤capacity b := by
  have hw : 2*width b+1≤capacity b := by unfold width capacity; nlinarith
  have hb : 2*b+1≤capacity b := by unfold capacity; nlinarith
  have hw' : width b≤capacity b := by omega
  simp only [CompetitorRationalProducts.input]
  split
  · simpa using hw
  · split
    · simpa using hb
    · split
      · simpa using hb
      · split
        · simpa using hw'
        · simp

theorem padded_decision_run (b : ℕ) (nums : Fin 4 → ℕ) (d e : ℕ)
    (hn : ∀ i,nums i<2^b) (hd : d<2^b) (he : e<2^b) (hdpos : 0<d) (hepos : 0<e) :
    ∃ out,ClockJoin.ReadyRun machine (2000*(b+1)^2) (paddedInput b nums d e) out ∧
      (∀ i,(out i).length≤capacity b) ∧
      out 6=List.replicate (width b) true ∧
      (readTapeBit (out 65) 0=true ↔
        ((nums 2 : ℚ)-nums 3)/e≤((nums 0 : ℚ)-nums 1)/d) := by
  obtain ⟨raw,hraw,hshared,hflag⟩ := rational_decision_run b nums d e hn hd he hdpos hepos
  obtain ⟨base,hr,ht,hh,hs⟩ := hraw
  have hsupport := RecoveryTapeSupport.run_support machine _ _ base hr (capacity b) 0
    (by intro i; exact Nat.zero_le _) (by
      intro i
      exact (input_support b nums d e i).trans (Nat.le_max_left _ _))
  have hbound (i : Fin 67) : (base.final.tapes i).length≤capacity b := by
    have hm : base.steps+1≤capacity b := by
      have hp : 0<(b+1)^2 := by positivity
      unfold capacity
      omega
    simpa only [Nat.zero_add,max_eq_left hm] using hsupport i
  obtain ⟨r,hrun,hf,hsteps,_⟩ := ZeroPadding.run_config machine (padding b) _ _ base hr
  have hi : ZeroPadding.config (padding b)
      (initialConfiguration machine (CompetitorRationalProducts.input (width b) b nums d e))=
      initialConfiguration machine (paddedInput b nums d e) := rfl
  rw [hi] at hrun
  refine ⟨r.final.tapes,⟨r,hrun,rfl,?_,hsteps.trans_le hs⟩,?_,?_,?_⟩
  · intro i
    rw [hf]
    exact hh i
  · intro i
    rw [hf]
    simp only [ZeroPadding.config,ZeroPadding.pad_length]
    exact max_le (by unfold padding; split <;> omega) (hbound i)
  · have h6 : raw 6=List.replicate (width b) true := hshared 6
    simpa [hf,ZeroPadding.config,padding,ht] using h6
  · simpa only [hf,ZeroPadding.config,ZeroPadding.read_pad,ht] using hflag

theorem bounded_focused_run {t u s time : ℕ} (slot : Fin t → Fin u)
    (hi : Function.Injective slot) (p : Machine t s)
    (input output : Fin t → List Bool) (h : ClockJoin.ReadyRun p time input output)
    (heads : Fin u → ℕ) (ambient : Fin u → List Bool)
    (hh : ∀ j,heads (slot j)=0) (ht : ∀ j,ambient (slot j)=input j) :
    ∃ r : ExecutionReceipt u s,
      runFrom (RecoveryFocus.machine slot p) time
        (RecoveryCalls.restarted (RecoveryFocus.machine slot p) heads ambient)=some r ∧
      r.final.heads=heads ∧ r.final.tapes=install slot ambient output ∧ r.steps≤time := by
  obtain ⟨base,hr,hout,hheads,hs⟩ := h
  obtain ⟨r,hrun,hf,hsteps⟩ := RecoveryFocus.run_config slot hi p heads ambient time
    (initialConfiguration p input) base hr
  have hin : RecoveryFocus.config slot heads ambient (initialConfiguration p input)=
      RecoveryCalls.restarted (RecoveryFocus.machine slot p) heads ambient := by
    apply configuration_ext
    · rfl
    · funext i
      cases hp : RecoveryFocus.pick slot i with
      | none => simp [RecoveryFocus.config,hp,RecoveryCalls.restarted]
      | some j =>
        have he := RecoveryFocus.slot_of_pick slot hp
        simp only [RecoveryFocus.config,hp,initialConfiguration,RecoveryCalls.restarted]
        exact (hh j).symm.trans (congrArg heads he)
    · exact install_existing slot ambient input ht
  rw [hin] at hrun
  refine ⟨r,hrun,?_,?_,hsteps.trans_le hs⟩
  · rw [hf]
    funext i
    cases hp : RecoveryFocus.pick slot i with
    | none => simp [RecoveryFocus.config,hp]
    | some j =>
      have he := RecoveryFocus.slot_of_pick slot hp
      simp only [RecoveryFocus.config,hp]
      exact (hheads j).trans ((hh j).symm.trans (congrArg heads he))
  · rw [hf]
    change install slot ambient base.final.tapes=install slot ambient output
    rw [hout]

theorem pad_zeros (cap n : ℕ) :
    ZeroPadding.pad cap (List.replicate n false)=List.replicate (max cap n) false := by
  simp only [ZeroPadding.pad,List.length_replicate,← List.replicate_add]
  congr 1
  omega

def loadCfg (q : Fin 4) (source : List Bool) (pos cap : ℕ) (target : List Bool) : Configuration 3 4 :=
  ⟨q,![pos,0,0],![source,target,List.replicate cap false]⟩

theorem padded_load_run (pre bits suffix : List Bool) (cap : ℕ) (hc : 2*bits.length+1≤cap) :
    ∃ r : ExecutionReceipt 3 4,
      runFrom FrameLoad.machine (4*bits.length+3)
        (loadCfg 0 (pre++frame bits++suffix) pre.length cap (List.replicate cap false))=some r ∧
      r.final=loadCfg 3 (pre++frame bits++suffix) (pre.length+2*bits.length+1) cap
        (ZeroPadding.pad cap (frame bits)) ∧ r.steps=4*bits.length+3 := by
  obtain ⟨base,hr,hf,hs,_⟩ := FrameLoad.load_run pre bits suffix [] (by simp)
  obtain ⟨r,hrun,hfinal,hsteps,_⟩ := ZeroPadding.run_config FrameLoad.machine ![0,cap,cap] _ _ base hr
  have hi : ZeroPadding.config ![0,cap,cap]
      (FrameLoad.scan 0 (pre++frame bits++suffix) pre.length [] [])=
      loadCfg 0 (pre++frame bits++suffix) pre.length cap (List.replicate cap false) := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> simp [ZeroPadding.config,FrameLoad.scan,loadCfg,
        ZeroPadding.pad,StablePartition.Workspace.overlay]
  rw [hi] at hrun
  refine ⟨r,hrun,?_,hsteps.trans hs⟩
  rw [hfinal,hf]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> simp [ZeroPadding.config,FrameLoad.reset,loadCfg,pad_zeros,max_eq_left hc]

end NearCubicWires.RepairOrdinary.CompetitorReusableDecision
