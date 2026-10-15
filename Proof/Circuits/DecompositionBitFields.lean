import Proof.Circuits.DecompositionSourceRealization
import Proof.PCP.PCPTriple

/-! Physical expansion of a binary field into the shared serializer's
Boolean-atom stream. The source cursor and destination append cursor stay
live; the flag records whether any payload bit is true. No value is expanded
into unary. The native header reader supplies the separate bit-count driver. -/
namespace NearCubicWires.RepairOrdinary.DecompositionBitFields
open LocalBitMultitape RecoveryExecution Streaming
open RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def fields (bits : List Bool) : List (List Bool) := bits.map (fun b => [b])
def stream (bits : List Bool) : List Bool := FieldList.stream (fields bits)
def present (bits : List Bool) : Bool := bits.any id

@[simp] theorem stream_nil : stream []=[] := rfl
@[simp] theorem stream_cons (b : Bool) (bits : List Bool) :
    stream (b::bits)=[true,b,false]++stream bits := rfl
theorem stream_length (bits : List Bool) : (stream bits).length=3*bits.length := by
  induction bits with
  | nil => rfl
  | cons b bits ih => simp only [stream_cons,List.length_append,List.length_cons,List.length_nil,ih]; omega
theorem mass (bits : List Bool) : PCPSerializerMass.mass (fields bits)=3*bits.length := by
  induction bits with
  | nil => rfl
  | cons b bits ih =>
    simp only [fields,List.map_cons,PCPSerializerMass.mass,List.sum_cons,
      List.length_cons,List.length_nil] at ih ⊢
    omega
theorem values (bits : List Bool) :
    PCPSerializerMass.values (fields bits)=bits.map CanonicalBinary.boolCode := by
  induction bits with
  | nil => rfl
  | cons b bits ih =>
    simp only [fields,PCPSerializerMass.values,List.map_cons] at ih ⊢
    rw [ih]
    cases b <;> rfl
theorem code (bits : List Bool) : PCPTraversal.code (fields bits)=CanonicalBinary.encodeBits bits := by
  unfold PCPTraversal.code
  rw [values]
  rfl

def machine : Machine 3 6 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==5
  rule := fun q bs => if q.val=0 then
      some ⟨if bs 0 then 1 else 5,fun _ => none,![.right,.stay,.stay]⟩
    else if q.val=1 then
      some ⟨if bs 0 then 3 else 2,![none,some true,some (bs 2 || bs 0)],![.right,.right,.stay]⟩
    else if q.val=2 ∨ q.val=3 then
      some ⟨4,![none,some (q.val==3),none],![.stay,.right,.stay]⟩
    else if q.val=4 then
      some ⟨0,![none,some false,none],![.stay,.right,.stay]⟩
    else none

def cfg (q : Fin 6) (source : List Bool) (pos : ℕ) (out : List Bool) (flag : Bool) :
    Configuration 3 6 := ⟨q,![pos,out.length,0],![source,out,[flag]]⟩

theorem bit_steps (pre suffix out : List Bool) (b flag : Bool) :
    Timed machine 4
      (cfg 0 (pre++true::b::suffix) pre.length out flag)
      (cfg 0 (pre++true::b::suffix) (pre.length+2) (out++[true,b,false]) (flag || b)) := by
  let source := pre++true::b::suffix
  have h0 : step machine (cfg 0 source pre.length out flag)=
      some (cfg 1 source (pre.length+1) out flag) := by
    simp [step,machine,cfg,source,Configuration.scanned,read_append]
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
    · rfl
  have hb : readTapeBit source (pre.length+1)=b := by
    have h := read_append (pre++[true]) suffix b
    simpa [source,List.append_assoc] using h
  have h1 : step machine (cfg 1 source (pre.length+1) out flag)=
      some (cfg (if b then 3 else 2) source (pre.length+2) (out++[true]) (flag || b)) := by
    simp [step,machine,cfg,Configuration.scanned,hb]
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
    · funext i; fin_cases i <;> simp [applyAction,write_append,readTapeBit,writeTapeBit]
  have h2 : step machine (cfg (if b then 3 else 2) source (pre.length+2) (out++[true]) (flag || b))=
      some (cfg 4 source (pre.length+2) (out++[true,b]) (flag || b)) := by
    have hw := write_append (out++[true]) b
    simp only [List.length_append,List.length_singleton,List.append_assoc,List.cons_append,List.nil_append] at hw
    cases b <;> simp [step,machine,cfg]
    all_goals apply configuration_ext
    all_goals try rfl
    all_goals funext i; fin_cases i <;> simp only [applyAction,HeadMove.apply]
    all_goals simp [hw]
  have h3 : step machine (cfg 4 source (pre.length+2) (out++[true,b]) (flag || b))=
      some (cfg 0 source (pre.length+2) (out++[true,b,false]) (flag || b)) := by
    have hw := write_append (out++[true,b]) false
    simp only [List.length_append,List.length_cons,List.length_nil,List.append_assoc,List.cons_append,List.nil_append] at hw
    simp [step,machine,cfg]
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
    · funext i; fin_cases i <;> simp [applyAction,hw]
  exact ((Timed.single (by rfl) h0).trans (Timed.single (by rfl) h1)).trans
    ((Timed.single (by cases b <;> rfl) h2).trans (Timed.single (by rfl) h3))

theorem stop_step (pre suffix out : List Bool) (flag : Bool) :
    step machine (cfg 0 (pre++false::suffix) pre.length out flag)=
      some (cfg 5 (pre++false::suffix) (pre.length+1) out flag) := by
  simp [step,machine,cfg,Configuration.scanned,read_append]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
  · rfl

theorem timed (pre bits suffix out : List Bool) (flag : Bool) :
    Timed machine (4*bits.length+1)
      (cfg 0 (pre++frame bits++suffix) pre.length out flag)
      (cfg 5 (pre++frame bits++suffix) (pre.length+2*bits.length+1)
        (out++stream bits) (flag || present bits)) := by
  induction bits generalizing pre out flag with
  | nil => simpa [frame,RepairOrdinary.frame,present] using
      Timed.single (by rfl) (stop_step pre suffix out flag)
  | cons b bits ih =>
    have hs := bit_steps pre (frame bits++suffix) out b flag
    have ht := ih (pre++[true,b]) (out++[true,b,false]) (flag || b)
    have hsource : (pre++[true,b])++frame bits++suffix=pre++true::b::(frame bits++suffix) := by
      simp only [List.append_assoc,List.cons_append,List.nil_append]
    rw [hsource] at ht
    have hall := hs.trans (by simpa only [List.length_append,List.length_cons,List.length_nil] using ht)
    have htime : 4+(4*bits.length+1)=4*(b::bits).length+1 := by simp; omega
    rw [htime] at hall
    simp only [frame,RepairOrdinary.frame,List.cons_append,
      List.nil_append,List.append_assoc,List.length_cons,stream_cons,present,List.any_cons,
      Bool.or_assoc,Nat.mul_add,Nat.mul_one,Nat.add_assoc,Nat.zero_add,Nat.add_comm,
      Nat.add_left_comm,id_eq] at hall ⊢
    convert hall using 1
    congr 1
    omega

theorem field_run (pre bits suffix out : List Bool) (flag : Bool) :
    ∃ r,runFrom machine (4*bits.length+1)
      (cfg 0 (pre++frame bits++suffix) pre.length out flag)=some r ∧
      r.final=cfg 5 (pre++frame bits++suffix) (pre.length+2*bits.length+1)
        (out++stream bits) (flag || present bits) ∧ r.steps=4*bits.length+1 :=
  (timed pre bits suffix out flag).run (by rfl)

end NearCubicWires.RepairOrdinary.DecompositionBitFields
