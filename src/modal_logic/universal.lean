import modal_logic.classes
import modal_logic.axioms

-- This file provides a modal system with a universal accessibility relation.

open modal_logic

namespace modal_logic

def universal.has_acc [world] : has_acc World := ⟨λ w v, true⟩
localized "attribute [instance] modal_logic.universal.has_acc" in modal_frame.universal

def universal_frame [world] : modal_frame := ⟨⟩
localized "attribute [instance] modal_logic.universal_frame" in modal_frame.universal

instance [modal_frame] : is_refl World (≺) := ⟨λ w, trivial⟩
instance [modal_frame] : is_trans World (≺) := ⟨λ w v u h h', trivial⟩
instance [modal_frame] : is_symm World (≺) := ⟨λ w v h, trivial⟩
instance [modal_frame] : is_preorder World (≺) := ⟨⟩
instance [modal_frame] : is_equiv World (≺) := ⟨⟩
instance [modal_frame] : is_per World (≺) := ⟨⟩

end modal_logic