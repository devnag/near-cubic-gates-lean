import Proof.Hierarchy.CompetitorPlanePacketFields

/-! One complete serialized P3 packet becomes the three literal fields of
the signed-plane caller. The sign is physically read, and the packet cursor
advances exactly past all raw counts without rewinding the packet stream. -/
namespace NearCubicWires.RepairOrdinary.CompetitorPlanePacketLoad
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open CompetitorPlanePacketFields
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def signProgram : Machine 6 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==1
  rule := fun q bits => if q.val=0 then some ⟨1,
    fun i => if i=1 then some (bits 0) else none,
    fun i => if i=0 then .right else .stay⟩ else none
noncomputable def machine := Composition.machine signProgram CompetitorPlanePacketFields.machine
def packet (sign : Bool) (bits counts : List Bool) := [sign]++frame bits++counts
def budget (bits counts : List Bool) := 4*bits.length+2*counts.length+8

theorem sign_run (pre suffix : List Bool) (sign : Bool) (D n : ℕ) :
    ∃ r,runFrom signProgram 1
      (cfg 0 pre.length (contents (pre++sign::suffix) (List.replicate D false)
        (List.replicate D false) (List.replicate D false) D n))=some r ∧
      r.final=cfg 1 (pre.length+1) (contents (pre++sign::suffix) (ZeroPadding.pad D [sign])
        (List.replicate D false) (List.replicate D false) D n) ∧ r.steps=1 := by
  have hwrite : writeTapeBit (List.replicate D false) 0 sign=ZeroPadding.pad D [sign] := by
    simpa [ZeroPadding.pad,writeTapeBit] using ZeroPadding.write_pad D [] 0 sign
  have hstep : step signProgram
      (cfg 0 pre.length (contents (pre++sign::suffix) (List.replicate D false)
        (List.replicate D false) (List.replicate D false) D n))=
      some (cfg 1 (pre.length+1) (contents (pre++sign::suffix) (ZeroPadding.pad D [sign])
        (List.replicate D false) (List.replicate D false) D n)) := by
    simp [step,signProgram,cfg,heads,contents,Configuration.scanned,Streaming.read_append]
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply,heads]
    · funext i; fin_cases i <;> simp [applyAction,heads,hwrite]
  exact (Timed.single (by rfl) hstep).run (by rfl)

theorem packet_run (pre suffix bits counts : List Bool) (sign : Bool) (D : ℕ)
    (hb : 2*bits.length+1≤D) (hc : counts.length≤D) :
    ∃ r,runFrom machine (budget bits counts)
      (cfg machine.start pre.length (contents (pre++packet sign bits counts++suffix)
        (List.replicate D false) (List.replicate D false) (List.replicate D false) D counts.length))=some r ∧
      r.final.heads=heads (pre.length+(packet sign bits counts).length) ∧
      r.final.tapes=contents (pre++packet sign bits counts++suffix) (ZeroPadding.pad D [sign])
        (ZeroPadding.pad D (frame bits)) (ZeroPadding.pad D counts) D counts.length ∧
      r.steps=budget bits counts := by
  obtain ⟨first,hfirst,hff,hfs⟩ := sign_run pre (frame bits++counts++suffix) sign D counts.length
  obtain ⟨second,hsecond,hsh,hst,hss⟩ := fields_run (pre++[sign]) bits counts suffix (ZeroPadding.pad D [sign]) D hb hc
  have hmid : Composition.restart first.final CompetitorPlanePacketFields.machine.start=
      cfg CompetitorPlanePacketFields.machine.start (pre++[sign]).length
        (contents ((pre++[sign])++frame bits++counts++suffix) (ZeroPadding.pad D [sign])
          (List.replicate D false) (List.replicate D false) D counts.length) := by
    rw [hff]
    simp [Composition.restart,cfg,List.append_assoc]
  have hsecond' : runFrom CompetitorPlanePacketFields.machine (4*bits.length+2*counts.length+6)
      (Composition.restart first.final CompetitorPlanePacketFields.machine.start)=some second := by rw [hmid]; exact hsecond
  have joined := Composition.run_join signProgram CompetitorPlanePacketFields.machine _ _ _ first second hfirst hsecond'
  have htime : 1+1+(4*bits.length+2*counts.length+6)=budget bits counts := by unfold budget; omega
  rw [htime] at joined
  refine ⟨Composition.joinedReceipt first second,?_,?_,?_,?_⟩
  · simpa only [machine,Composition.machine,signProgram,Composition.leftConfig,cfg,packet,
      List.append_assoc,List.singleton_append,List.cons_append,List.nil_append] using joined
  · change second.final.heads=_
    rw [hsh]
    have hp : (pre++[sign]).length+2*bits.length+1+counts.length=pre.length+(packet sign bits counts).length := by
      simp [packet,List.length_append,frame_length]
      omega
    exact congrArg heads hp
  · change second.final.tapes=_
    rw [hst]
    simp [packet,List.append_assoc]
  · change first.steps+1+second.steps=_
    unfold budget
    omega

end NearCubicWires.RepairOrdinary.CompetitorPlanePacketLoad
