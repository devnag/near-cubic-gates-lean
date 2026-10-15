import Proof.PCP.PCPPNativeQueryIteration

/-! The complete query bank is driven by its actual Q sentinel. Each
iteration consumes one real R-field projection row and reuses the whole
original-query bank; every return and final Q rewind is paid. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeQueryLoop
open LocalBitMultitape SourceInterfaces RecoveryExecution PCPPNativeNodeMachine
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def accepted {s : ℕ} (_ : Fin s) (_ : Fin 173 → Bool) := true
noncomputable def machine := RepeatMachine.machine PCPPNativeQueryIteration.machine accepted
def stream {n r : ℕ} (rows : List (Fin n → ProjectedRandomBit r)) := rows.flatMap rowCache
def source {n r : ℕ} (pre suffix : List Bool) (rows : List (Fin n → ProjectedRandomBit r)) := pre++stream rows++suffix
def emitted {n r : ℕ} (base index : ℕ) (oracle : BooleanCircuit n) : List (Fin n → ProjectedRandomBit r) → List Bool
  | [] => []
  | projection::rows => PCPPNativeQuery.emitted (base+index*(2*oracle.size+1)) oracle projection++emitted base (index+1) oracle rows
def requirements {n r : ℕ} (base index C F G : ℕ) (oracle : BooleanCircuit n) : List (Fin n → ProjectedRandomBit r) → Prop
  | [] => True
  | projection::rows => PCPPNativeQueryIteration.capacity (base+index*(2*oracle.size+1)) C F G oracle projection ∧
      requirements base (index+1) C F G oracle rows
noncomputable def configuration (phase : Fin 5) (bits fields : List Bool)
    (cursor base C F G : ℕ) (out : List Bool) (width total driverHead : ℕ) :=
  RepeatMachine.cfg phase (PCPPNativeQueryIteration.entry bits fields cursor base C F G out width) total driverHead

theorem phase_equal {s : ℕ} (phase : Fin 5) (a b : Configuration 173 s) (total pos : ℕ)
    (hh : a.heads=b.heads) (ht : a.tapes=b.tapes) :
    RepeatMachine.cfg phase a total pos=RepeatMachine.cfg phase b total pos := by
  apply configuration_ext
  · rfl
  · simp only [RepeatMachine.cfg,controlConfig,TapeEmbedding.config,hh]
  · simp only [RepeatMachine.cfg,controlConfig,TapeEmbedding.config,ht]

theorem loop_run {n r : ℕ} (rows : List (Fin n → ProjectedRandomBit r)) (pre suffix : List Bool)
    (base index C F G : ℕ) (oracle : BooleanCircuit n) (out : List Bool)
    (hCF : C+1 ≤ F) (hFG : F+1 ≤ G) (hreq : requirements base index C F G oracle rows)
    (total pos : ℕ) (hcount : pos+rows.length=total) :
    ∃ result,runFrom machine (rows.length*(6*G+8)+total+3)
      (configuration 0 (PCPPNative.descriptor oracle) (source pre suffix rows) pre.length
        (base+index*(2*oracle.size+1)) C F G out n total (pos+1))=some result ∧
      result.steps ≤ rows.length*(6*G+8)+total+3 ∧
      result.final=configuration 3 (PCPPNative.descriptor oracle) (source pre suffix rows)
        (pre.length+(stream rows).length) (base+(index+rows.length)*(2*oracle.size+1)) C F G
        (out++emitted base index oracle rows) n total 1 := by
  induction rows generalizing pre index out pos with
  | nil =>
    have hp : pos=total := by simpa only [List.length_nil,Nat.add_zero] using hcount
    subst pos
    have endRun := RepeatMachine.exhaust PCPPNativeQueryIteration.machine accepted
      (PCPPNativeQueryIteration.entry (PCPPNative.descriptor oracle) (source (n := n) (r := r) pre suffix []) pre.length
        (base+index*(2*oracle.size+1)) C F G out n) total
    obtain ⟨result,hr,rf,rs⟩ := endRun.run (by
      simp [RepeatMachine.machine,RepeatMachine.cfg,controlConfig,RepeatMachine.phaseCode])
    refine ⟨result,?_,?_,?_⟩
    · simpa only [machine,List.length_nil,Nat.zero_mul,Nat.zero_add,configuration] using hr
    · simpa only [List.length_nil,Nat.zero_mul,Nat.zero_add] using rs.le
    · simpa only [configuration,stream,List.flatMap_nil,List.length_nil,Nat.add_zero,emitted,List.append_nil] using rf
  | cons projection rows ih =>
    rcases hreq with ⟨hcap,hrest⟩
    have sourceFirst : source pre suffix (projection::rows)=pre++rowCache projection++(stream rows++suffix) := by
      simp only [source,stream,List.flatMap_cons,List.append_assoc]
    have sourceNext : source (pre++rowCache projection) suffix rows=source pre suffix (projection::rows) := by
      simp only [source,stream,List.flatMap_cons,List.append_assoc]
    have hbase : base+index*(2*oracle.size+1)+2*oracle.size+1=base+(index+1)*(2*oracle.size+1) := by ring
    obtain ⟨a,ha,as,ah,atapes⟩ := PCPPNativeQueryIteration.iteration_run pre (stream rows++suffix)
      (base+index*(2*oracle.size+1)) C F G oracle projection out hCF hFG hcap
    rw [←sourceFirst] at ha atapes
    have hcost := PCPPNativeQueryIteration.budget_bound (base+index*(2*oracle.size+1)) C F G oracle projection hcap
    have iteration := RepeatMachine.iteration PCPPNativeQueryIteration.machine accepted
      (PCPPNativeQueryIteration.entry (PCPPNative.descriptor oracle) (source pre suffix (projection::rows)) pre.length
        (base+index*(2*oracle.size+1)) C F G out n) total pos a (by rfl)
      (by simp only [List.length_cons] at hcount; omega) ha
    simp only [accepted,ite_true] at iteration
    have mid : RepeatMachine.cfg 0 a.final total (pos+2)=
        configuration 0 (PCPPNative.descriptor oracle) (source (pre++rowCache projection) suffix rows)
          (pre++rowCache projection).length (base+(index+1)*(2*oracle.size+1)) C F G
          (out++PCPPNativeQuery.emitted (base+index*(2*oracle.size+1)) oracle projection) n total ((pos+1)+1) := by
      apply phase_equal
      · simpa only [PCPPNativeQueryIteration.entry,List.length_append] using ah
      · simpa only [PCPPNativeQueryIteration.entry,sourceNext,hbase] using atapes
    rw [mid] at iteration
    obtain ⟨b,hb,bs,bf⟩ := ih (pre++rowCache projection) (index+1)
      (out++PCPPNativeQuery.emitted (base+index*(2*oracle.size+1)) oracle projection) hrest (pos+1)
      (by simp only [List.length_cons] at hcount; omega)
    rcases iteration with ⟨space,hprefix⟩
    obtain ⟨result,hr,rf,rs,_⟩ := hprefix.followedBy b hb
    have timeBound : (a.steps+2)+(rows.length*(6*G+8)+total+3) ≤ (projection::rows).length*(6*G+8)+total+3 := by
      simp only [List.length_cons]
      nlinarith
    have more := runFrom_moreFuel machine _
      ((projection::rows).length*(6*G+8)+total+3-((a.steps+2)+(rows.length*(6*G+8)+total+3))) _ result hr
    rw [Nat.add_sub_of_le timeBound] at more
    refine ⟨result,more,?_,?_⟩
    · rw [rs]
      nlinarith
    · have finalEq := rf.trans bf
      simpa only [configuration,source,stream,List.flatMap_cons,emitted,List.length_cons,
        List.length_append,List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using finalEq

end NearCubicWires.RepairOrdinary.PCPPNativeQueryLoop
