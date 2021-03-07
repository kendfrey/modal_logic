import modal_logic.classes
import modal_logic.axioms

-- This file provides a modal system with a universal accessibility relation.

open modal_logic

namespace modal_logic.universal

def has_acc [world] : has_acc World := ⟨λ w v, true⟩

localized "attribute [instance] modal_logic.universal.has_acc" in modal_frame.universal

instance [world] : is_refl World (≺) := ⟨λ w, trivial⟩
instance [world] : is_trans World (≺) := ⟨λ w v u h h', trivial⟩
instance [world] : is_symm World (≺) := ⟨λ w v h, trivial⟩
instance [world] : is_preorder World (≺) := ⟨⟩
instance [world] : is_equiv World (≺) := ⟨⟩
instance [world] : is_per World (≺) := ⟨⟩

end modal_logic.universal