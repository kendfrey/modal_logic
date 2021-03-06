import modal_logic.classes
import modal_logic.axioms

-- This file provides a modal system with a universal accessibility relation.

open modal_logic

namespace modal_logic.universal

def has_acc [world] : has_acc World := ⟨λ w v, true⟩

localized "attribute [instance] modal_logic.universal.has_acc" in modal_frame.universal

instance [world] : is_refl World (≺) := ⟨λ w, trivial⟩
instance [world] : is_trans World (≺) := ⟨λ w v u h h', trivial⟩
instance [world] : is_dense World (≺) := ⟨λ w v h, ⟨w, trivial, trivial⟩⟩
instance [world] : is_serial World (≺) := ⟨λ w, ⟨w, trivial⟩⟩
instance [world] : is_symm World (≺) := ⟨λ w v h, trivial⟩
instance [world] : is_euclidean World (≺) := ⟨λ w v u h h', trivial⟩

end modal_logic.universal