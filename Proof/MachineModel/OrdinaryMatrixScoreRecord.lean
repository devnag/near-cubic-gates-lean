import Proof.MachineModel.OrdinaryMatrixScoreLinear

/-! Actual bounded append of the literal signed-score/id record. The native
id, its width template, padded score, zero template and erase counter are
retained; only the record output cursor advances. -/
namespace NearCubicWires.RepairOrdinary.MatrixScoreRecord
open LocalBitMultitape SignedSortKey
open MatrixScoreWeight (scalar)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def cfg (q : Fin 10) (m w c id template value : ℕ) (out : List Bool) : Configuration 6 10 :=
  KeyPair.config q (frame (binary m id)) (frame (binary m template))
    (scalar c w value) (frame (binary w 0)) out c

theorem pair_run (m w c id template value : ℕ) (out : List Bool)
    (hm : 2*m≤c) (hw : 2*w≤c) :
    ∃ actual,runFrom KeyPair.machine (4*(m+w)+7) (cfg 0 m w c id template value out)=some actual ∧
      actual.final=cfg 9 m w c id template value (out++frame (binary m id++binary w value)) ∧
      actual.steps≤4*(m+w)+7 := by
  obtain ⟨base,hb,hf,hs,_⟩ := KeyPair.pair_run (binary m id) [false] (binary m template)
    (binary w value) [false] (binary w 0) out c (by simp) (by simp)
    (by simpa using hm) (by simpa using hw)
  rw [RankBody.marks_frame,RankBody.marks_frame] at hb hf
  simp only [binary_length] at hb hs
  let padding : Fin 6 → ℕ := ![0,0,c,0,0,0]
  obtain ⟨actual,ha,haf,has,_⟩ := ZeroPadding.run_config KeyPair.machine padding _ _ base hb
  have transport (q : Fin 10) (out : List Bool) : ZeroPadding.config padding
      (KeyPair.config q (frame (binary m id)) (frame (binary m template))
        (frame (binary w value)) (frame (binary w 0)) out c)=cfg q m w c id template value out := by
    apply configuration_ext
    · rfl
    · rfl
    · funext i; fin_cases i <;> simp [ZeroPadding.config,padding,KeyPair.config,cfg,scalar,ZeroPadding.pad]
  rw [transport] at ha
  refine ⟨actual,ha,?_,has.trans_le hs⟩
  rw [haf,hf,transport]

theorem encoded_run (s m c id template : ℕ) (score : ℤ) (out : List Bool)
    (hm : 2*m≤c) (hw : 2*(s+1)≤c) :
    ∃ actual,runFrom KeyPair.machine (4*(m+(s+1))+7)
        (cfg 0 m (s+1) c id template (shifted s score) out)=some actual ∧
      actual.final=cfg 9 m (s+1) c id template (shifted s score)
        (out++StablePartition.recordBits (encode s m score id)) ∧
      actual.steps≤4*(m+(s+1))+7 := by
  have he : StablePartition.recordBits (encode s m score id)=
      frame (binary m id++binary (s+1) (shifted s score)) := by
    change frame (RadixSemantics.word (encode s m score id))=_
    rw [encode_word]
  rw [he]
  exact pair_run m (s+1) c id template (shifted s score) out hm hw

end NearCubicWires.RepairOrdinary.MatrixScoreRecord
