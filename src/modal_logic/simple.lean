import modal_logic.classes

-- This file provides a simple definition of MProp, namely World → Prop.

open modal_logic

namespace modal_logic.simple

instance [world] [has_acc World] : modal_prop (World → Prop) :=
{
  not := λ p w, ¬p w,
  imp := λ p q w, p w → q w,
  nec := λ p w, ∀ v, w ≺ v → p v
}

def sat [world] [has_acc World] : has_sat World (World → Prop) := ⟨λ w p, p w⟩

localized "attribute [instance] modal_logic.simple.sat" in modal_model.simple

def logic [world] [has_acc World] : modal_logic World (World → Prop) :=
{
  sat_not := λ w p, iff.refl _,
  sat_imp := λ w p q, iff.refl _,
  sat_nec := λ w p, iff.refl _,
}

def model [world] [has_acc : has_acc World] : modal_model :=
{
  has_acc := has_acc,
  MProp := World → Prop,
  modal_logic := logic,
}

localized "attribute [instance] modal_logic.simple.model" in modal_model.simple

end modal_logic.simple